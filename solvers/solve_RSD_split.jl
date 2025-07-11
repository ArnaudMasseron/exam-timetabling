# Load packages
using JuMP, Gurobi, JLD2

# Load source files
repo_path = String(@__DIR__) * "/../"
include(repo_path * "src/instance.jl")
include(repo_path * "src/model.jl")
include(repo_path * "src/solution.jl")
include(repo_path * "src/utils.jl")

# Load the arguments given to the script
year = "2023-2024"
instance_type = "business_school"
n_splits = 4
time_limit_sec = 60
fill_rate = 0.95
save_debug = false
save_solution = false
if !isempty(ARGS)
    @assert length(ARGS) == 5 "Incorrect amount of arguments given"
    year = string(ARGS[1])
    instance_type = string(ARGS[2])
    n_splits = parse(Int, ARGS[3])
    time_limit_sec = parse(Int, ARGS[4])
    fill_rate = parse(Float64, ARGS[5])
    save_debug = true
    save_solution = true
end

# Set solution saving parameters
save_dir = repo_path * "solutions/RSD_split/"
save_radical =
    "RSDsplit_" *
    "$(year)$(instance_type)_" *
    "$(n_splits)splits_" *
    "$(isnothing(time_limit_sec) ? "no" : string(time_limit_sec) * "sec")TimeLimit_" *
    "$(fill_rate)FillRate"

# Read instance
instance_path =
    repo_path * "datasets/$(year)/json_instances/$(year)_dataset_$(instance_type).json"
instance = read_instance(instance_path);

# Perform basic preliminary infeasibility checks
check_infeasible_basic(instance; fill_rate)

# Split the instance into multiple subinstances
n_max_tries = 3
SPLIT_obj_evol = [
    Dict("objective" => Vector{Float64}(), "time" => Vector{Float64}()) for
    try_id = 1:n_max_tries
]
time_limit_one_split = (!isnothing(time_limit_sec) ? time_limit_sec / n_splits : nothing)
println_dash("Start solving instance splitting model")
split_instances, g_values_warmstart, completely_removed_exams = split_instance(
    instance,
    n_splits,
    SPLIT_obj_evol;
    fill_rate = fill_rate,
    time_limit_warmstart = time_limit_one_split / 5,
)
if save_debug
    @save save_dir * "debug/SPLIT_obj_evol.jld2" SPLIT_obj_evol
end
if save_solution
    @save save_dir * "graphs/graph_data/SPLIT_obj_evol_" * save_radical * ".jld2" SPLIT_obj_evol
    draw_SPLIT_objective_graph(
        save_dir * "graphs/graph_SPLIT_" * save_radical * ".png",
        SPLIT_obj_evol,
        nothing,
    )
end

# Solve the RSD_jl submodel for each split instance
RSD_jl_obj_evol = [
    Dict("objective" => Vector{Float64}(), "time" => Vector{Float64}()) for
    split = 1:n_splits
]
f_values = zeros(Bool, instance.n_j, instance.n_l)
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
    !isnothing(time_limit_one_split) &&
        set_optimizer_attribute(RSD_jl_split, "TimeLimit", time_limit_one_split)

    # Set objective value fetching callback function
    callback_f = get_objective_value_callback(split_id, RSD_jl_obj_evol)
    MOI.set(RSD_jl_split, Gurobi.CallbackFunction(), callback_f)

    # Solve the model
    optimize!(RSD_jl_split)
    @assert termination_status(RSD_jl_split) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible or increase the time limit"

    push!(RSD_jl_obj_evol[split_id]["time"], JuMP.solve_time(RSD_jl_split))
    push!(
        RSD_jl_obj_evol[split_id]["objective"],
        RSD_jl_obj_evol[split_id]["objective"][end],
    )

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
    @save save_dir * "debug/RSD_jl_obj_evol.jld2" RSD_jl_obj_evol
end
if save_solution
    @save save_dir * "graphs/graph_data/RSD_jl_obj_evol_RSD_" * save_radical * ".jld2" RSD_jl_obj_evol
    draw_RSD_jl_objective_graphs(
        save_dir * "graphs/graph_RSD_jl_" * save_radical * ".png",
        RSD_jl_obj_evol,
        time_limit_one_split,
    )
end

# Add the rooms, i.e. solve RSD_jlm
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

# Add the students, i.e. solve RSD_ijlm
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

# Compute the cost of the solution
sol_cost = solution_cost(instance, x_values; compute_unwanted_breaks = true)

# Save the solution
if save_solution
    println_dash("Start saving the solution")

    @save save_dir * "x_values/x_values_" * save_radical * ".jld2" x_values
    write_solution_json(
        instance,
        x_values,
        completely_removed_exams,
        sol_cost,
        save_dir * "json/sol_" * save_radical * ".json",
    )

    println_dash("Solution saved")
end
