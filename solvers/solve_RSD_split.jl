# Load packages
using JuMP, Gurobi, JLD2

# Load source files
repo_path = String(@__DIR__) * "/../"
include(repo_path * "src/instance.jl")
include(repo_path * "src/model.jl")
include(repo_path * "src/solution.jl")

save_dir = repo_path * "solutions/RSD_split/"

# Load the arguments given to the script
instance_name = nothing
n_splits = nothing
time_limit_sec = nothing
fill_rate = nothing
if isempty(ARGS)
    instance_name = "tiny"
    n_splits = 3
    time_limit_sec = nothing
    fill_rate = 0.85
else
    @assert length(ARGS) == 4 "Incorrect amount of arguments given"
    instance_name = String(ARGS[1])
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
split_instances, g_values_warmstart = split_instance(
    instance,
    n_splits;
    fill_rate = fill_rate,
    time_limit_sec = time_limit_sec,
)


# Solve the split instances
f_values = zeros(Bool, instance.n_j, instance.n_l)
println_dash("Start solving RSD_jl_split submodels")
for SplitI in split_instances
    RSD_jl_split = Model(Gurobi.Optimizer)
    declare_RSD_jl_split(SplitI, RSD_jl_split)
    for ((i, j, l), var) in RSD_jl_split[:g].data
        set_start_value(var, Int(g_values_warmstart[i, j, l]))
    end

    if !isnothing(time_limit_sec)
        set_optimizer_attribute(RSD_jl_split, "TimeLimit", time_limit_sec)
    end
    optimize!(RSD_jl_split)
    @assert termination_status(RSD_jl_split) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible or increase the time limit"

    curr_f_values = value.(RSD_jl_split[:f])
    for j in axes(curr_f_values)[1], l in axes(curr_f_values)[2]
        if curr_f_values[j, l] >= 0.5
            f_values[j, l] = true
        end
    end
end
@save save_dir * "debug/f_values.jld2" f_values


# Add the rooms
b_values = zeros(Bool, instance.n_j, instance.n_l, instance.n_m)
let
    global b_values

    println_dash("Start solving RSD_jlm submodel")
    RSD_jlm = Model(Gurobi.Optimizer)
    declare_RSD_jlm(instance, f_values, RSD_jlm)
    if !isnothing(time_limit_sec)
        set_optimizer_attribute(RSD_jlm, "TimeLimit", time_limit_sec)
    end
    optimize!(RSD_jlm)

    @assert termination_status(RSD_jlm) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible or increase the time limit"
    dict_b_values = value.(RSD_jlm[:b]).data
    for ((j, l, m), value) in dict_b_values
        if value >= 0.5
            b_values[j, l, m] = true
        end
    end
end
@save save_dir * "debug/b_values.jld2" b_values


# Add the students
x_values = zeros(Bool, instance.n_i, instance.n_j, instance.n_l, instance.n_m)
let
    global x_values

    println_dash("Start solving RSD_ijlm submodel")
    RSD_ijlm = Model(Gurobi.Optimizer)
    declare_RSD_ijlm(instance, b_values, RSD_ijlm)
    if !isnothing(time_limit_sec)
        set_optimizer_attribute(RSD_ijlm, "TimeLimit", time_limit_sec)
    end

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
@save save_dir * "debug/x_values.jld2" x_values


# Reorder the students inside exam series according to their classes
reorder_students_inside_series(instance, x_values)

# Save the solution
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

@save save_dir * "x_values/x_values_" * save_radical * ".jld2" x_values
write_solution_json(instance, x_values, save_dir * "json/sol_" * save_radical * ".json")
println_dash("Solution saved")
