# Load packages
using JuMP
using Gurobi

# Load source files
repo_path = String(@__DIR__) * "/../"
include(repo_path * "src/instance.jl")
include(repo_path * "src/model.jl")

# Read instance
instance_path = repo_path * "datasets/2023-2024/2023-2024_dataset_tiny.json"
instance = read_instance(instance_path)

# Split the instance into multiple subinstances
n_splits = 3
split_instances = split_instance(instance, n_splits)

# Solve the split instances
prev_RSD_jl = nothing
RSD_jl = nothing
for SplitI in split_instances
    global prev_RSD_jl, RSD_jl

    RSD_jl = Model(Gurobi.Optimizer)
    declare_RSD_jl_split(SplitI, RSD_jl, prev_RSD_jl)

    optimize!(RSD_jl)
    @assert termination_status(RSD_jl) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible"

    prev_RSD_jl = RSD_jl
end

# Add the rooms
RSD_jlm = Model(Gurobi.Optimizer)
declare_RSD_jlm(instance, RSD_jl, RSD_jlm)
optimize!(RSD_jlm)

# Add the students
RSD_ijlm = Model(Gurobi.Optimizer)
declare_RSD_ijlm(instance, RSD_jlm, RSD_ijlm)
optimize!(RSD_ijlm)