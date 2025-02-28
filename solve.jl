using JuMP

using Gurobi
ENV["GUROBI_HOME"] = "/opt/gurobi1201/linux64"
ENV["GRB_LICENSE_FILE"] = "/home/arnaud/.gurobi/license/gurobi.lic"

dir_path = String(@__DIR__) * "/"
include(dir_path * "src/instance.jl")
include(dir_path * "src/model.jl")


instance_path = dir_path * "/datasets/2023-2024/2023-2024_dataset_tiny.json"
instance = read_instance(instance_path)

model = Model(Gurobi.Optimizer)
@time declare_CM(model, instance)

optimize!(model)