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

# Declare model
model = Model(Gurobi.Optimizer)
declare_CM(instance, model)

# Solve
optimize!(model)
