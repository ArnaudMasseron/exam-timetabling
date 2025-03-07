# Load packages
using JuMP
using Gurobi
ENV["GUROBI_HOME"] = "/opt/gurobi1201/linux64"
ENV["GRB_LICENSE_FILE"] = "/home/arnaud/.gurobi/license/gurobi.lic"

# Load source files
dir_path = String(@__DIR__) * "/"
include(dir_path * "src/instance.jl")
include(dir_path * "src/model.jl")

# Read instance
instance_path = dir_path * "/datasets/2023-2024/2023-2024_dataset_tiny.json"
instance = read_instance(instance_path)

# Declare model
model = Model(Gurobi.Optimizer)
declare_RSD_jl(model, instance)

# Solve model
optimize!(model)