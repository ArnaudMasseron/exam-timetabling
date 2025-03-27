# Load packages
using JuMP, Gurobi

# Load source files
repo_path = String(@__DIR__) * "/../"
include(repo_path * "src/instance.jl")
include(repo_path * "src/model.jl")

# Load the arguments given to the script
instance_name = nothing
n_splits = nothing
time_limit_sec = nothing
if isempty(ARGS)
    instance_name = "tiny"
    n_splits = 3
    time_limit_sec = nothing
else
    @assert length(ARGS) == 3 "Incorrect amount of arguments given"
    instance_name = String(ARGS[1])
    n_splits = parse(Int, ARGS[2])
    time_limit_sec = parse(Int, ARGS[3])
end

# Read instance
instance_path =
    repo_path *
    "datasets/2023-2024/json_instances/2023-2024_dataset_" *
    instance_name *
    ".json"
instance = read_instance(instance_path)

# Split the instance into multiple subinstances
split_instances = split_instance(instance, n_splits)


# Solve the split instances
prev_RSD_jl = nothing
RSD_jl = nothing
for SplitI in split_instances
    global prev_RSD_jl, RSD_jl

    RSD_jl = Model(Gurobi.Optimizer)
    declare_RSD_jl_split(SplitI, RSD_jl, prev_RSD_jl)

    if !isnothing(time_limit_sec)
        set_optimizer_attribute(RSD_jl, "TimeLimit", time_limit_sec)
    end

    optimize!(RSD_jl)
    @assert termination_status(RSD_jl) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible"

    prev_RSD_jl = RSD_jl
end

# Add the rooms
RSD_jlm = Model(Gurobi.Optimizer)
declare_RSD_jlm(instance, RSD_jl, RSD_jlm)
if !isnothing(time_limit_sec)
    set_optimizer_attribute(RSD_jlm, "TimeLimit", time_limit_sec)
end
optimize!(RSD_jlm)

# Add the students
RSD_ijlm = Model(Gurobi.Optimizer)
declare_RSD_ijlm(instance, RSD_jlm, RSD_ijlm)
if !isnothing(time_limit_sec)
    set_optimizer_attribute(RSD_ijlm, "TimeLimit", time_limit_sec)
end
optimize!(RSD_ijlm)


# Save the solution
using JLD2
save_dir = repo_path * "solutions/RSD_split/"
save_name =
    "sol_RSDsplit_" *
    instance_name *
    "_" *
    string(n_splits) *
    "splits_" *
    string(time_limit_sec) *
    "secTimeLimit.jld2"
@save save_dir * save_name x_value = value.(RSD_ijlm[:x])