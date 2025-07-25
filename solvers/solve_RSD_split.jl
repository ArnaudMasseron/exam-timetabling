# Load packages and source files
using JuMP, Gurobi, JLD2
repo_path = joinpath(@__DIR__, "../")
include(joinpath(repo_path, "src/instance.jl"))
include(joinpath(repo_path, "src/model.jl"))
include(joinpath(repo_path, "src/solution.jl"))
include(joinpath(repo_path * "src/utils.jl"))


# ---------- USER SET PARAMETERS ---------- #
# The following parameters must be set by the user
# These are useless if the script is launched from the terminal

instance_path = joinpath(repo_path, "instances/2024-2025_dataset_sampletiny_15min.json")

n_splits = 4                # Number of sub-instances wanted
time_limit_seconds = 60     # Maximum time limit for the whole solving process
fill_rate = 0.95            # Filling rate for the SPLIT MILP
save_debug = false          # Save data that can be useful while debugging
save_solution = false       # Save solution files

# Path toward a starting solution's x_values
# If one doesn't want to provide a starting solution, then this should be set to nothing
start_x_values_path = nothing

# Modalities of the exams that need to be rescheduled
# Only relevent if a starting solution is provided
# If equal to nothing, then all exams can be rescheduled
modalities_reschedule = nothing
# ----------------------------------------- #


# If solve_RSD_split.jl is launched from the terminal with some arguments
# load the terminal arguments instead
if !isempty(ARGS)
    @assert length(ARGS) == 4 "Incorrect amount of arguments given"
    instance_path = string(ARGS[1])
    n_splits = parse(Int, ARGS[2])
    time_limit_seconds = parse(Int, ARGS[3])
    fill_rate = parse(Float64, ARGS[4])
    save_debug = true
    save_solution = true
end

# Set solution saving parameters
year, instance_type, time_step_min = get_instance_arguments(instance_path)
save_dir = joinpath(repo_path, "solutions/RSD_split/") # directory were data will be saved
save_radical =
    "RSDsplit_" *
    "$(year)$(instance_type)_" *
    "$(time_step_min)minTimeStep_" *
    "$(n_splits)splits_" *
    "$(isnothing(time_limit_seconds) ? "no" : string(time_limit_seconds) * "sec")TimeLimit_" *
    "$(fill_rate)FillRate"

# Read instance
instance = read_instance(instance_path);

# Perform basic preliminary infeasibility tests
check_infeasible_basic(instance; fill_rate)

# Read the starting solution provided by the user
start_x_values = nothing
!isnothing(start_x_values_path) && (start_x_values = load(start_x_values_path, "x_values"))

# Get the exams that need to be frozen
frozen_ijlm = nothing
if !isnothing(modalities_reschedule)
    @assert(!isnothing(start_x_values))
    frozen_ijlm = get_frozen_exams(instance, modalities_reschedule, start_x_values)
end

# Split the instance into multiple subinstances
n_max_tries = 3
SPLIT_obj_evol = [
    Dict("objective" => Vector{Float64}(), "time" => Vector{Float64}()) for
    try_id = 1:n_max_tries
]
time_limit_one_split =
    (!isnothing(time_limit_seconds) ? time_limit_seconds * 0.9 / n_splits : nothing)
println_dash("Start solving instance splitting model")
split_instances, g_values_warmstart, completely_removed_exams = split_instance(
    instance,
    n_splits,
    SPLIT_obj_evol;
    fill_rate = fill_rate,
    time_limit_warmstart = time_limit_one_split / 5,
    time_limit_SPLIT = time_limit_seconds / 5,
    n_max_tries = n_max_tries,
    frozen_ijlm = frozen_ijlm,
    start_x_values = start_x_values,
)
if save_debug
    save_with_dir(
        joinpath(save_dir, "debug/SPLIT_obj_evol_" * save_radical * ".jld2"),
        SPLIT_obj_evol,
    )
    save_with_dir(
        joinpath(save_dir, "debug/g_values_warmstart_" * save_radical * ".jld2"),
        g_values_warmstart,
    )
    save_with_dir(
        joinpath(save_dir, "debug/completely_removed_exams_" * save_radical * ".jld2"),
        completely_removed_exams,
    )
    save_with_dir(joinpath(save_dir, "debug/instance_" * save_radical * ".jld2"), instance)
end
if save_solution
    save_with_dir(
        joinpath(save_dir, "graphs/graph_data/SPLIT_obj_evol_" * save_radical * ".jld2"),
        SPLIT_obj_evol,
    )
    draw_SPLIT_objective_graph(
        joinpath(save_dir, "graphs/graph_SPLIT_" * save_radical * ".png"),
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

    # Freeze certain exams if needed
    if !isnothing(frozen_ijlm)
        for (i, j, l, m) in frozen_ijlm
            (!((i, j) in completely_removed_exams)) &&
                fix(RSD_jl_split[:g][i, j, l], 1; force = true)
        end
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
    save_with_dir(joinpath(save_dir, "debug/f_values_" * save_radical * ".jld2"), f_values)
    save_with_dir(
        joinpath(save_dir, "debug/RSD_jl_obj_evol_" * save_radical * ".jld2"),
        RSD_jl_obj_evol,
    )
end
if save_solution
    save_with_dir(
        joinpath(
            save_dir,
            "graphs/graph_data/RSD_jl_obj_evol_RSD_" * save_radical * ".jld2",
        ),
        RSD_jl_obj_evol,
    )
    draw_RSD_jl_objective_graphs(
        joinpath(save_dir, "graphs/graph_RSD_jl_" * save_radical * ".png"),
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
    !isnothing(time_limit_seconds) &&
        set_optimizer_attribute(RSD_jlm, "TimeLimit", time_limit_seconds / 10)

    # Freeze certain exams if needed
    if !isnothing(frozen_ijlm)
        for (i, j, l, m) in frozen_ijlm
            (!((i, j) in completely_removed_exams)) &&
                fix(RSD_jlm[:b][j, l, m], 1; force = true)
        end
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
if save_debug
    save_with_dir(joinpath(save_dir, "debug/b_values_" * save_radical * ".jld2"), b_values)
end

# Add the students, i.e. solve RSD_ijlm
x_values = zeros(Bool, instance.n_i, instance.n_j, instance.n_l, instance.n_m)
RSD_ijlm_obj_evol = [Dict("objective" => Vector{Float64}(), "time" => Vector{Float64}())]
let
    global x_values
    println_dash("Start solving RSD_ijlm submodel")

    RSD_ijlm = Model(Gurobi.Optimizer)
    declare_RSD_ijlm(instance, b_values, RSD_ijlm)
    !isnothing(time_limit_seconds) &&
        set_optimizer_attribute(RSD_ijlm, "TimeLimit", time_limit_seconds / 10)

    # Freeze certain exams if needed
    if !isnothing(frozen_ijlm)
        for (i, j, l, m) in frozen_ijlm
            (!((i, j) in completely_removed_exams)) &&
                fix(RSD_ijlm[:x][i, j, l, m], 1; force = true)
        end
    end

    # Warmstart
    objective = objective_function(RSD_ijlm)
    @objective(RSD_ijlm, Min, 0)
    optimize!(RSD_ijlm)

    # Set objective value fetching callback function
    callback_f = get_objective_value_callback(1, RSD_ijlm_obj_evol)
    MOI.set(RSD_ijlm, Gurobi.CallbackFunction(), callback_f)

    @objective(RSD_ijlm, Min, objective)
    optimize!(RSD_ijlm)
    @assert termination_status(RSD_ijlm) != MOI.INFEASIBLE_OR_UNBOUNDED "Create a split that is feasible or increase the time limit"

    push!(RSD_ijlm_obj_evol[1]["time"], JuMP.solve_time(RSD_ijlm))
    push!(RSD_ijlm_obj_evol[1]["objective"], RSD_ijlm_obj_evol[1]["objective"][end])

    dict_x_values = value.(RSD_ijlm[:x]).data
    for ((i, j, l, m), value) in dict_x_values
        if value >= 0.5
            x_values[i, j, l, m] = true
        end
    end
end
if save_debug
    save_with_dir(joinpath(save_dir, "debug/x_values_" * save_radical * ".jld2"), x_values)
    save_with_dir(
        joinpath(save_dir, "debug/RSD_ijlm_obj_evol_" * save_radical * ".jld2"),
        RSD_ijlm_obj_evol,
    )
end
if save_solution
    save_with_dir(
        joinpath(
            save_dir,
            "graphs/graph_data/RSD_ijlm_obj_evol_RSD_" * save_radical * ".jld2",
        ),
        RSD_ijlm_obj_evol,
    )
    draw_RSD_ijlm_objective_graphs(
        joinpath(save_dir, "graphs/graph_RSD_ijlm_" * save_radical * ".png"),
        RSD_ijlm_obj_evol[1],
        (!isnothing(time_limit_seconds) ? time_limit_seconds / 10 : nothing),
    )
end

# Reorder the students inside exam series according to their classes
reorder_students_inside_series(instance, x_values)

# Compute the cost of the solution
@time sol_cost = solution_cost(instance, x_values; compute_unwanted_breaks = true)

# Save the solution
if save_solution
    println_dash("Start saving the solution")

    save_with_dir(
        joinpath(save_dir, "x_values/x_values_" * save_radical * ".jld2"),
        x_values,
    )
    write_solution_json(
        instance,
        x_values,
        completely_removed_exams,
        sol_cost,
        joinpath(save_dir, "json/sol_" * save_radical * ".json"),
    )

    println_dash("Solution saved")
end
