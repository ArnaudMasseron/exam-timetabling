# Load packages
using JuMP, Gurobi, JLD2

# Load source files
repo_path = String(@__DIR__) * "/../"
include(repo_path * "src/instance.jl")
include(repo_path * "src/model.jl")
include(repo_path * "src/solution.jl")
include(repo_path * "src/utils.jl")

save_dir = repo_path * "solutions/RSD_split/"

# Load the arguments given to the script
instance_name = nothing
n_splits = nothing
time_limit_sec = nothing
fill_rate = nothing
save_debug = true
save_solution = true
if isempty(ARGS)
    instance_name = "business_school"
    n_splits = 2
    time_limit_sec = 172
    fill_rate = 0.9
    save_debug = false
    save_solution = false
else
    @assert length(ARGS) == 4 "Incorrect amount of arguments given"
    instance_name = string(ARGS[1])
    n_splits = parse(Int, ARGS[2])
    time_limit_sec = parse(Int, ARGS[3])
    fill_rate = parse(Float64, ARGS[4])
end

# Print the message by adding dashes before and after
function println_dash(mystring::String)
    println(repeat("-", 30) * " " * mystring * " " * repeat("-", 30))
    flush(stdout)
end

# Read instance
instance_path =
    repo_path *
    "datasets/2023-2024/json_instances/2023-2024_dataset_" *
    instance_name *
    ".json"
instance = read_instance(instance_path)

# Perform basic preliminary infeasibility checks
check_infeasible_basic(instance)

# Split the instance into multiple subinstances
println_dash("Start solving instance splitting model")
split_instances, g_values_warmstart, completely_removed_exams = split_instance(
    instance,
    n_splits;
    fill_rate = fill_rate,
    time_limit_sec = (isnothing(time_limit_sec) ? nothing : time_limit_sec / 10),
    n_max_tries = 3,
)


# Solve the split instances
obj_evol = [
    Dict("objective" => Vector{Float64}(), "time" => Vector{Float64}()) for
    split = 1:n_splits
]
f_values = zeros(Bool, instance.n_j, instance.n_l)
!isnothing(time_limit_sec) && (time_limit_one_split = time_limit_sec * 0.7 / (2 * n_splits))

for (split_id, SplitI) in enumerate(split_instances)
    println_dash("Start solving RSD_jl_split submodel n°$split_id")
    # Declare model
    RSD_jl_split = Model(Gurobi.Optimizer)
    declare_RSD_jl_split(SplitI, RSD_jl_split)

    # Set warmstart values
    for ((i, j, l), var) in RSD_jl_split[:g].data
        set_start_value(var, Int(g_values_warmstart[i, j, l]))
    end

    # Set time limit
    !isnothing(time_limit_sec) &&
        set_optimizer_attribute(RSD_jl_split, "TimeLimit", time_limit_one_split)

    # Set objective value fetching callback function
    callback_f = get_objective_value_callback(split_id, obj_evol)
    MOI.set(RSD_jl_split, Gurobi.CallbackFunction(), callback_f)

    # Solve the model
    optimize!(RSD_jl_split)
    @assert termination_status(RSD_jl_split) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible or increase the time limit"

    # Get the values of the variable f
    curr_f_values = value.(RSD_jl_split[:f])
    for j in axes(curr_f_values)[1], l in axes(curr_f_values)[2]
        if curr_f_values[j, l] >= 0.5
            f_values[j, l] = true
        end
    end
end
if save_debug
    @save save_dir * "debug/f_values.jld2" f_values
    @save save_dir * "debug/obj_evol.jld2" obj_evol
end


# Add the rooms
b_values = zeros(Bool, instance.n_j, instance.n_l, instance.n_m)
let
    global b_values
    println_dash("Start solving RSD_jlm submodel")

    RSD_jlm = Model(Gurobi.Optimizer)
    declare_RSD_jlm(instance, f_values, RSD_jlm)
    !isnothing(time_limit_sec) &&
        set_optimizer_attribute(RSD_jlm, "TimeLimit", time_limit_sec / 10)

    optimize!(RSD_jlm)
    @assert termination_status(RSD_jlm) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible or increase the time limit"

    dict_b_values = value.(RSD_jlm[:b]).data
    for ((j, l, m), value) in dict_b_values
        if value >= 0.5
            b_values[j, l, m] = true
        end
    end
end
if save_debug
    @save save_dir * "debug/b_values.jld2" b_values
end


# Add the students
x_values = zeros(Bool, instance.n_i, instance.n_j, instance.n_l, instance.n_m)
let
    global x_values
    println_dash("Start solving RSD_ijlm submodel")

    RSD_ijlm = Model(Gurobi.Optimizer)
    declare_RSD_ijlm(instance, b_values, RSD_ijlm)
    !isnothing(time_limit_sec) &&
        set_optimizer_attribute(RSD_ijlm, "TimeLimit", time_limit_sec / 10)

    # Warmstart
    objective = objective_function(RSD_ijlm)
    @objective(RSD_ijlm, Min, 0)
    optimize!(RSD_ijlm)

    @objective(RSD_ijlm, Min, objective)
    optimize!(RSD_ijlm)
    @assert termination_status(RSD_ijlm) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible or increase the time limit"

    dict_x_values = value.(RSD_ijlm[:x]).data
    for ((i, j, l, m), value) in dict_x_values
        if value >= 0.5
            x_values[i, j, l, m] = true
        end
    end
end
if save_debug
    @save save_dir * "debug/x_values.jld2" x_values
end


# Reorder the students inside exam series according to their classes
reorder_students_inside_series(instance, x_values)

# Save the solution
if save_solution
    println_dash("Start saving the solution")
    save_radical =
        "RSDsplit_" *
        instance_name *
        "_" *
        string(n_splits) *
        "splits_" *
        (isnothing(time_limit_sec) ? "no" : string(time_limit_sec) * "sec") *
        "TimeLimit_" *
        string(fill_rate) *
        "FillRate"

    draw_objective_graphs(
        save_dir * "graphs/graph_" * save_radical * ".png",
        obj_evol,
        time_limit_one_split,
    )
    @save save_dir * "x_values/x_values_" * save_radical * ".jld2" x_values
    write_solution_json(
        instance,
        x_values,
        completely_removed_exams,
        save_dir * "json/sol_" * save_radical * ".json",
    )
    println_dash("Solution saved")
end
