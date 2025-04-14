using JSON, Dates, JuMP, Gurobi

Base.@kwdef struct Group
    e::Vector{Int}
    s::Int
    c::Int
end

Base.@kwdef struct Instance
    Δ_l::Period

    n_i::Int
    n_e::Int
    n_s::Int
    n_j::Int
    n_l::Int
    n_m::Int
    n_d::Int
    n_w::Int
    n_c::Int

    ξ::Int
    τ_lun::Int
    τ_room::Int
    τ_seq::Int
    τ_stu::Int
    τ_swi::Int

    ε::Vector{Int}
    γ::Matrix{Bool}
    θ::Matrix{Bool}

    κ::Vector{Int}
    ζ::Vector{Int}
    α::Matrix{Bool}
    β::Matrix{Bool}
    λ::Matrix{Bool}

    η::Vector{Int}
    ρ::Vector{Int}
    μ::Vector{Int}
    ν::Vector{Int}

    σ::Matrix{Bool}

    δ::Array{Bool,3}

    S_exa::Vector{Set{Int}}
    S_stu::Vector{Set{Int}}
    U::Vector{Vector{Vector{Int}}}
    J::Vector{Set{Int}}
    L::Vector{Vector{Int}}
    V::Vector{Vector{Int}}
    Z::Vector{Set{Int}}

    groups::Vector{Group}

    dataset::Dict{String,Any}
    timeslots_start_datetime::Vector{DateTime}
end

Base.@kwdef struct SplitInstance
    I::Instance

    κ::Vector{Int}
    day_range::UnitRange{Int}
    exams::Set{Tuple{Int,Int}}
end

function read_instance(path::String)
    @assert endswith(path, ".json")
    dataset = JSON.parsefile(path)

    Δ_l = Minute(dataset["general_parameters"]["time_slot_length_minutes"])

    n_i = length(dataset["students"])
    n_e = length(dataset["examiners"])
    n_s = length(dataset["subjects"])
    n_j = length(dataset["groups"])
    n_m = length(dataset["rooms"])
    n_c = length(dataset["classes"])

    timeslots_start_datetime = Vector{DateTime}()
    for (start_datetime_str, end_datetime_str) in
        dataset["general_parameters"]["exam_time_windows"]
        start_datetime = DateTime(start_datetime_str)
        end_datetime = DateTime(end_datetime_str)

        @assert(
            isinteger((end_datetime - start_datetime) / Δ_l),
            "BAD DATASET: The time must be discretizable into whole Δ_l long time slots"
        )
        @assert(
            Time(start_datetime) < Time(end_datetime),
            "BAD DATASET: The start time must be smaller than then end time for each exam time window"
        )
        @assert(
            Date(start_datetime) == Date(end_datetime),
            "BAD DATASET: The start time and the end time of each exam time window must be on the same day"
        )

        curr_datetime = start_datetime
        while (curr_datetime < end_datetime)
            push!(timeslots_start_datetime, curr_datetime)
            curr_datetime += Δ_l
        end
    end
    sort(timeslots_start_datetime)
    for a = 1:length(timeslots_start_datetime)-1
        @assert(
            timeslots_start_datetime[a+1] - timeslots_start_datetime[a] >= Δ_l,
            "BAD DATASET: There must be no duplicates in the exam time windows"
        )
    end
    n_l = length(timeslots_start_datetime)

    L = Vector{Vector{Int}}([Vector{Int}()])
    V = Vector{Vector{Int}}([Vector{Int}()])
    Z = Vector{Set{Int}}([Set{Int}()])
    day = Date(timeslots_start_datetime[1])
    week_start =
        Date(timeslots_start_datetime[1] - Day(dayofweek(timeslots_start_datetime[1]) - 1))
    for (l, datetime) in enumerate(timeslots_start_datetime)
        if Date(datetime) != day
            push!(L, Vector{Int}())
            push!(V, Vector{Int}())
            day = Date(datetime)
        end
        if Date(datetime - Day(dayofweek(datetime) - 1)) != week_start
            push!(Z, Set{Int}())
            week_start = Date(datetime - Day(dayofweek(datetime) - 1))
        end

        push!(L[end], l)
        push!(Z[end], l)
        if (
            Time(dataset["general_parameters"]["lunch_time_window"][1]) <= Time(datetime) &&
            Time(dataset["general_parameters"]["lunch_time_window"][2]) > Time(datetime)
        )
            push!(V[end], l)
        end
    end
    n_d = length(L)
    n_w = length(Z)

    ξ = dataset["general_parameters"]["max_number_exams_student"]
    τ_lun = dataset["general_parameters"]["lunch_break_duration"]
    τ_room = dataset["general_parameters"]["room_break_duration"]
    τ_seq = dataset["general_parameters"]["exam_sequence_break_duration"]
    τ_stu = dataset["general_parameters"]["student_break_duration"]
    τ_swi = dataset["general_parameters"]["group_switch_break_duration"]

    γ = zeros(Bool, n_i, n_j)
    for item in dataset["exams"]
        γ[item["student_id"], item["group_id"]] = true
    end
    S_stu = [Set{Int}() for i = 1:n_i]
    for i = 1:n_i, j = 1:n_j
        if γ[i, j]
            push!(S_stu[i], dataset["groups"][j]["subject_id"])
        end
    end
    ε = vec(sum(γ, dims = 2))
    θ = ones(Bool, n_i, n_l)
    for (i, dict) in enumerate(dataset["students"])
        for (start_datetime_str, end_datetime_str) in dict["unavailabilities"]
            start_datetime = DateTime(start_datetime_str)
            end_datetime = DateTime(end_datetime_str)

            curr_datetime = start_datetime
            while (curr_datetime < end_datetime)
                l = searchsortedlast(timeslots_start_datetime, curr_datetime)
                if l != 0
                    θ[i, l] = false
                end
                curr_datetime += Δ_l
            end
        end
    end

    κ = -ones(Int, n_e)
    ζ = zeros(Int, n_e)
    α = ones(Bool, n_e, n_l)
    β = ones(Bool, n_e, n_l)
    U = Vector{Vector{Vector{Int}}}([Vector{Vector{Int}}() for e = 1:n_e])
    for (e, dict) in enumerate(dataset["examiners"])
        ζ[e] = dict["max_number_exams_per_day"]
        κ[e] = dict["max_number_days"]

        for (start_datetime_str, end_datetime_str) in dict["hard_unavailabilities"]
            start_datetime = DateTime(start_datetime_str)
            end_datetime = DateTime(end_datetime_str)

            curr_datetime = start_datetime
            while (curr_datetime < end_datetime)
                l = searchsortedlast(timeslots_start_datetime, curr_datetime)
                if l != 0
                    α[e, l] = false
                end
                curr_datetime += Δ_l
            end
        end

        for (start_datetime_str, end_datetime_str) in dict["soft_unavailabilities"]
            start_datetime = DateTime(start_datetime_str)
            end_datetime = DateTime(end_datetime_str)
            new_entry_added = false

            curr_datetime = start_datetime
            while (curr_datetime < end_datetime)
                l = searchsortedlast(timeslots_start_datetime, curr_datetime)
                if l != 0 && curr_datetime - timeslots_start_datetime[l] < Δ_l
                    if !new_entry_added
                        push!(U[e], [])
                        new_entry_added = true
                    end
                    β[e, l] = false
                    push!(U[e][end], l)
                end
                curr_datetime += Δ_l
            end
        end
    end


    η = -ones(Int, n_s)
    ρ = -ones(Int, n_s)
    μ = -ones(Int, n_s)
    ν = -ones(Int, n_s)
    for (s, dict) in enumerate(dataset["subjects"])
        η[s] = dict["number_of_students"]
        ρ[s] = dict["max_number_exams_row"]
        μ[s] = dict["preparation_time"]
        ν[s] = dict["duration_time"]
    end

    λ = zeros(Bool, n_e, n_j)
    J = Vector{Set{Int}}([Set{Int}() for s = 1:n_s])
    groups = Vector{Group}()
    S_exa = [Set{Int}() for e = 1:n_e]
    for (j, dict) in enumerate(dataset["groups"])
        s = dict["subject_id"]
        push!(J[s], j)

        for e in dict["examiner_ids"]
            λ[e, j] = true
            push!(S_exa[e], s)
        end

        push!(groups, Group(dict["examiner_ids"], s, dict["class_id"]))
    end
    σ = zeros(Bool, n_j, n_j)
    for e = 1:n_e
        group_ids = findall(x -> x, λ[e, :])

        for j in group_ids, k in group_ids
            σ[j, k] = true
        end
    end

    δ = ones(Bool, n_m, n_l, n_s)
    for (m, dict) in enumerate(dataset["rooms"])
        for s in dict["unsuported_subjects"], l = 1:n_l
            δ[m, l, s] = false
        end

        for (start_datetime_str, end_datetime_str) in dict["unavailabilities"]
            start_datetime = DateTime(start_datetime_str)
            end_datetime = DateTime(end_datetime_str)

            curr_datetime = start_datetime
            while (curr_datetime < end_datetime)
                l = searchsortedlast(timeslots_start_datetime, curr_datetime)
                if l != 0
                    for s = 1:n_s
                        δ[m, l, s] = false
                    end
                end
                curr_datetime += Δ_l
            end
        end
    end

    return Instance(;
        Δ_l,
        n_i,
        n_e,
        n_s,
        n_j,
        n_l,
        n_m,
        n_d,
        n_w,
        n_c,
        ξ,
        τ_lun,
        τ_room,
        τ_seq,
        τ_stu,
        τ_swi,
        ε,
        γ,
        θ,
        κ,
        ζ,
        α,
        β,
        λ,
        η,
        ρ,
        μ,
        ν,
        σ,
        δ,
        S_exa,
        S_stu,
        U,
        J,
        L,
        V,
        Z,
        groups,
        dataset,
        timeslots_start_datetime,
    )
end

function check_infeasible_basic(I::Instance)
    #= Perform basic preliminary tests in order to see if an instance is infeasible or not =#

    # Feasible amount of students for exams with multiple simultaneous students
    for j = 1:I.n_j
        s = I.groups[j].s
        if I.η[s] > 1
            nb_students_group = sum(I.γ[:, j])
            nb_leftover_students = nb_students_group % I.η[s]
            @assert nb_leftover_students == 0 "Group $j needs $(I.η[s] - nb_leftover_students) more students"
        end
    end

    # Student enough time
    for i = 1:I.n_i
        time_needed = 0
        for j = 1:I.n_j
            if I.γ[i, j]
                s = I.groups[j].s
                length_exam = I.ν[s] + I.μ[s]
                time_needed += length_exam + I.τ_stu
            end
        end

        available_time = I.n_l - sum(.!I.θ[i, :])

        @assert time_needed <= available_time "Not enough time to schedule all of student $(i)'s exams"
    end

    # Student enough days
    for i = 1:I.n_i
        nb_days_needed = sum(I.γ[i, :]) / I.ξ
        nb_days_available = sum(sum(I.θ[i, l] for l in I.L[d]) > 0 for d = 1:I.n_d)

        @assert nb_days_needed <= nb_days_available "Not enough days to schedule all of student $(i)'s exams"
    end

    # Examiner enough time or days
    for e = 1:I.n_e
        time_needed = 0
        nb_exams = 0
        for j = 1:I.n_j
            if I.λ[e, j]
                nb_exams += 1
                s = I.groups[j].s
                time_needed += I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]
            end
        end
        available_time = I.n_l - I.n_d * I.τ_lun - sum(.!I.α[e, :])
        days_needed = max(ceil(time_needed / available_time), ceil(nb_exams / I.ζ[e]))

        @assert time_needed <= available_time "Not enough time to schedule all of examiner $(e)'s exams"
        @assert days_needed <= I.κ[e] "Not enough days to schedule all of examiner $(e)'s exams"
    end
end

function declare_splitting_MILP(
    I::Instance,
    n_splits::Int,
    fill_rate::Float64,
    exams::Vector{Tuple{Int,Int}},
    days_split::Vector{UnitRange{Int}},
    model::Model,
)
    n_exams = length(exams)

    # --- Main decision variables --- #
    @variable(model, x[exam = 1:n_exams, split = 1:n_splits], binary = true)


    # --- Constraints --- #
    # Exam one split
    @constraint(
        model,
        exam_one_split[exam in 1:n_exams],
        sum(x[exam, split] for split = 1:n_splits) == 1
    )

    # Feasible amount of students in each split for exams with multiple simultaneous students
    @variable(model, r[j = 1:I.n_j, split = 1:n_splits] >= 0, integer = true)
    @constraint(
        model,
        group_feasible_amount_students[j = 1:I.n_j, split = 1:n_splits],
        sum(x[exam, split] for exam = 1:n_exams if exams[exam][2] == j; init = 0) ==
        r[j, split] * I.η[I.groups[j].s]
    )

    # Student enough time
    @constraint(
        model,
        student_enough_time[i = 1:I.n_i, split = 1:n_splits],
        sum(
            let s = I.groups[exams[exam][2]].s
                x[exam, split] * (I.ν[s] + I.μ[s] + I.τ_stu)
            end for exam = 1:n_exams if i == exams[exam][1];
            init = 0,
        ) <=
        fill_rate * (
            sum(length(I.L[d]) for d in days_split[split]) -
            sum(!I.θ[i, l] for d in days_split[split] for l in I.L[d])
        )
    )

    # Student max exams
    @constraint(
        model,
        student_max_exams[i = 1:I.n_i, split = 1:n_splits],
        sum(x[exam, split] for exam = 1:n_exams if exams[exam][1] == i; init = 0) <=
        sum(sum(I.θ[i, l] for l in I.L[d]) > 0 for d in days_split[split]) * I.ξ
    )

    # Examiner enough time
    @variable(model, t[e = 1:I.n_e, u = 1:length(I.U[e])], binary = true)

    function helper_examiner_available_time(e, split)
        expr = zero(AffExpr)
        for d in days_split[split]
            add_to_expression!(expr, length(I.L[d]) - I.τ_lun)

            for l in I.L[d]
                add_to_expression!(expr, -(!I.α[e, l] || !I.β[e, l]))
            end

            for u in eachindex(I.U[e])
                @assert issorted(I.U[e][u])
                for l in I.U[e][u]
                    idx = searchsortedlast(I.L[d], l)
                    if idx != 0 && I.L[d] == l
                        add_to_expression!(expr, length(I.U[e][u]) * t[e, u])
                        break
                    end
                end
            end
        end
        expr *= fill_rate

        return expr
    end
    @constraint(
        model,
        examiner_enough_time[e = 1:I.n_e, split = 1:n_splits],
        sum(
            let s = I.groups[exams[exam][2]].s
                x[exam, split] * (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]
            end for exam = 1:n_exams if e in I.groups[exams[exam][2]].e;
            init = 0,
        ) <= helper_examiner_available_time(e, split)
    )

    # Examiner max days
    @variable(
        model,
        0 <= z[e = 1:I.n_e, split = 1:n_splits] <= length(days_split[split]),
        integer = true
    )
    @constraint(
        model,
        examiner_max_days_1[e = 1:I.n_e, split = 1:n_splits],
        sum(
            x[exam, split] / I.η[I.groups[exams[exam][2]].s] for
            exam = 1:n_exams if e in I.groups[exams[exam][2]].e;
            init = 0,
        ) <= z[e, split] * I.ζ[e]
    )
    @constraint(
        model,
        examiner_max_days_2[e = 1:I.n_e, split = 1:n_splits],
        sum(
            let s = I.groups[exams[exam][2]].s
                x[exam, split] * (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]
            end for exam = 1:n_exams if e in I.groups[exams[exam][2]].e;
            init = 0,
        ) <=
        z[e, split] * fill_rate * sum(length(I.L[d]) - I.τ_lun for d in days_split[split]) /
        length(days_split[split])
    )
    @constraint(
        model,
        examiner_max_days_3[e = 1:I.n_e],
        sum(z[e, split] for split = 1:n_splits) <= I.κ[e]
    )

    # Harmonious exam distribution between splits
    @variable(model, p[split in 1:n_splits] >= 0)
    @constraint(
        model,
        split_harmonious_exams_1[split = 1:n_splits],
        p[split] >=
        sum(x[exam, split] for exam = 1:n_exams) -
        n_exams * length(days_split[split]) / I.n_d
    )
    @constraint(
        model,
        split_harmonious_exams_2[split = 1:n_splits],
        p[split] >=
        n_exams * length(days_split[split]) / I.n_d -
        sum(x[exam, split] for exam = 1:n_exams)
    )

    # Student harmonious exams
    @variable(model, q[i = 1:I.n_i, split = 1:n_splits])
    @constraint(
        model,
        student_harmonious_exams_1[i = 1:I.n_i, split = 1:n_splits],
        q[i, split] >=
        sum(x[exam, split] for exam = 1:n_exams if exams[exam][1] == i; init = 0) -
        I.ε[i] * length(days_split[split]) / I.n_d
    )
    @constraint(
        model,
        student_harmonious_exams_2[i = 1:I.n_i, split = 1:n_splits],
        q[i, split] >=
        I.ε[i] * length(days_split[split]) / I.n_d -
        sum(x[exam, split] for exam = 1:n_exams if exams[exam][1] == i; init = 0)
    )


    # --- Objective --- #
    z_coef = 50 / sum(I.κ)
    p_coef = 30 / n_exams
    q_coef = 20 / n_exams
    objective = z_coef * sum(z) + p_coef * sum(p) + q_coef * sum(q)
    @objective(model, Min, objective)
end

function create_split_instances(
    I::Instance,
    exams::Vector{Tuple{Int,Int}},
    days_split::Vector{UnitRange{Int}},
    x_values,
)
    n_exams = length(exams)

    nb_exams_examiner = zeros(Float64, I.n_e, n_splits)
    exam_splits = [Set{Tuple{Int,Int}}() for split = 1:n_splits]
    for exam = 1:n_exams, split = 1:n_splits
        if x_values[exam, split] >= 0.5
            push!(exam_splits[split], exams[exam])

            j = exams[exam][2]
            for e in I.groups[j].e
                nb_exams_examiner[e, split] += 1 / I.η[I.groups[j].s]
            end
        end
    end

    # Create the split instance kappa vectors
    κ_splits = zeros(Int, I.n_e, n_splits)
    for e = 1:I.n_e
        nb_total_exams_examiner = sum(I.λ[e, j] && I.γ[i, j] for i = 1:I.n_i, j = 1:I.n_j)
        nb_days_available_examiner = I.κ[e]
        exam_perc = nb_exams_examiner[e, :] / nb_total_exams_examiner

        while nb_days_available_examiner > 0
            days_perc = κ_splits[e, :] / I.κ[e]

            # Compute the days percentage to exam percentage ratio
            ratio = map(x -> (isnan(x) ? Inf : x), days_perc ./ exam_perc)
            split_id = argmin(ratio)

            # Add a day to the split with the lowest ratio
            κ_splits[e, split_id] += 1

            nb_days_available_examiner -= 1
        end

        # Check if a split containing an exam for e has a maximum days limit of at least 1 for e
        for split_id = 1:n_splits
            @assert nb_exams_examiner[e, split_id] == 0 || κ_splits[e, split_id] > 0
        end
    end

    # Create the split instances vector
    split_instances = [
        SplitInstance(
            I = I,
            κ = κ_splits[:, split],
            day_range = days_split[split],
            exams = exam_splits[split],
        ) for split = 1:n_splits
    ]

    return split_instances
end

function find_problematic_exams_ids(RSD_jl_split_warm::Model, exams::Vector{Tuple{Int,Int}})
    @assert issorted(exams)

    # Change exam needed into a soft constraint
    valid_ij = axes(RSD_jl_split_warm[:exam_needed], 1)
    delete(RSD_jl_split_warm, RSD_jl_split_warm[:exam_needed].data)

    @variable(RSD_jl_split_warm, c[(i, j) in valid_ij], binary = true)
    g = RSD_jl_split_warm[:g]
    println("Just before error")
    RSD_jl_split_warm[:exam_needed] = @constraint(
        RSD_jl_split_warm,
        [(i, j) in valid_ij],
        sum(g[i, j, :]) == 1 - c[(i, j)]
    )

    @objective(RSD_jl_split_warm, Min, sum(c))

    # Solve the problem with exam needed as a soft constraint
    optimize!(RSD_jl_split_warm)
    @assert termination_status(RSD_jl_split_warm) != MOI.INFEASIBLE_OR_UNBOUNDED "The time limit is too small."

    # Get the indexes of the problematic exams
    c_values = value.(c)
    pb_exams_ids = Set{Int}()
    for (i, j) in axes(c_values, 1)
        if c_values[(i, j)] >= 0.5
            exam = searchsortedlast(exams, (i, j))
            @assert(exam != 0 && exams[exam] == (i, j))
            push!(pb_exams_ids, exam)
        end
    end

    return pb_exams_ids
end

include(String(@__DIR__) * "/../src/utils.jl")
function split_instance(
    I::Instance,
    n_splits::Int;
    fill_rate = 0.85,
    time_limit_sec = nothing,
    n_max_tries = 5,
)
    #= 
    Split the instance into multiple subinstances until a feasible split has been found 

    Arguments:
    [input] I: original instance
    [input] n_splits: number of splits
    [input] fill_rate: parameter that controls how filled the splits can be
    [input] time_limit_sec: time limit in seconds for each MILP resolution
    [input] : maximum number of times where the splitting MILP can be solved

    Return value: (split_instances, g_values_warmstart) 
    split_instances: Vector{SplitInstance} containing the different subsinstances
    g_values_warmstart: values of the g variable for the original instance  fter the warmstarts
    =#

    @assert n_splits <= I.n_d "Can't have more splits than the number of days"
    @assert 0 <= fill_rate <= 1 "The filling rate must be between 0 and 1"

    # Initialize some data
    day_step = div(I.n_d, n_splits)
    days_split = vcat(
        [(split-1)*day_step+1:split*day_step for split = 1:n_splits-1],
        [day_step*(n_splits-1)+1:I.n_d],
    )

    exams = sort([(i, j) for i = 1:I.n_i, j = 1:I.n_j if I.γ[i, j]])
    n_exams = length(exams)

    # Declare the splitting model
    model = Model(Gurobi.Optimizer)
    declare_splitting_MILP(I, n_splits, fill_rate, exams, days_split, model)
    if !isnothing(time_limit_sec)
        set_optimizer_attribute(model, "TimeLimit", time_limit_sec)
    end

    # Solve the splitting problem until a feasible split has been found
    feasible_splits_found = false
    split_instances = nothing
    g_values_warmstart = nothing
    banned_x = zeros(Bool, n_exams, n_splits) # banned (exam, split) combinations
    try_id = 1
    while !feasible_splits_found && try_id <= n_max_tries
        # Solve the MILP splitting problem
        optimize!(model)

        # If the model is infeasible the print the problematic constraints
        if termination_status(model) == MOI.INFEASIBLE_OR_UNBOUNDED
            print_constraint_conflicts(model)
            error("Unable to split the instance. 
                  This can be the result of a time limit that is too small. 
                  The problematic constraints have been printed.")
        end

        # Read the results
        x_values = value.(model[:x])
        split_instances = create_split_instances(I, exams, days_split, x_values)

        # Check if the splits instances are feasible by warmstarting the different splits
        g_values_warmstart = zeros(Bool, I.n_i, I.n_j, I.n_l)
        feasible_splits_found = true
        for (split, SplitI) in enumerate(split_instances)
            RSD_jl_split_warm = Model(Gurobi.Optimizer)
            declare_RSD_jl_split(SplitI, RSD_jl_split_warm)
            @objective(RSD_jl_split_warm, Min, 0)
            if !isnothing(time_limit_sec)
                set_optimizer_attribute(RSD_jl_split_warm, "TimeLimit", time_limit_sec)
            end
            optimize!(RSD_jl_split_warm)

            # If the split is infeasible then find the exams that cause problem
            if termination_status(RSD_jl_split_warm) == MOI.INFEASIBLE_OR_UNBOUNDED
                feasible_splits_found = false

                pb_exams_ids = find_problematic_exams_ids(RSD_jl_split_warm, exams)

                # Ban the problematic exams in the splitting in the splitting MILP
                for exam in pb_exams_ids
                    banned_x[exam, split] = true
                    fix(x[exam, split], 0; force = true)
                end

                # If one exam has been banned in all splits then the splitting heuristic has failed and can't go on
                one_exam_banned_everywhere =
                    sum(
                        prod(banned_x[exam, split] for split = 1:n_splits) for
                        exam = 1:n_exams
                    ) > 0
                @assert !one_exam_banned_everywhere "One exam can't be placed in any split"
            else
                # Get the warmstart values
                g_values_dict = value.(RSD_jl_split_warm[:g]).data
                for ((i, j, l), value) in g_values_dict
                    if value >= 0.5
                        g_values_warmstart[i, j, l] = true
                    end
                end
            end
        end

        try_id += 1
    end

    if !feasible_splits_found
        error("No feasible solution has been found in under $n_max_tries tries")
    end

    return split_instances, g_values_warmstart
end