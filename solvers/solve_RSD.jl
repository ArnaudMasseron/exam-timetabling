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

# Declare and solve models
RSD_jl = Model(Gurobi.Optimizer)
declare_RSD_jl(instance, RSD_jl)
optimize!(RSD_jl)

RSD_jlm = Model(Gurobi.Optimizer)
declare_RSD_jlm(instance, RSD_jl, RSD_jlm)
optimize!(RSD_jlm)

RSD_ijlm = Model(Gurobi.Optimizer)
declare_RSD_ijlm(instance, RSD_jlm, RSD_ijlm)
optimize!(RSD_ijlm)