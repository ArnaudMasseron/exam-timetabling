using JSON, Dates, JuMP, Gurobi

Base.@kwdef struct Group
    e::Vector{Int}
    s::Int
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

    δ::Matrix{Bool}
    ψ::Matrix{Bool}

    S_exa::Vector{Set{Int}}
    S_stu::Vector{Set{Int}}
    U::Vector{Set{UnitRange{Int}}}
    J::Vector{Set{Int}}
    L::Vector{Vector{Int}}
    V::Vector{Vector{Int}}
    Z::Vector{Set{Int}}

    groups::Vector{Group}
    room_type_data::Dict{String,Dict{String,Any}}
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
        sort(dataset["general_parameters"]["exam_time_windows"])
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

            start_timeslot = searchsortedlast(timeslots_start_datetime, start_datetime)
            if start_timeslot == 0 ||
               Date(timeslots_start_datetime[start_timeslot]) < Date(start_datetime)
                start_timeslot += 1
            end

            end_timeslot = searchsortedlast(timeslots_start_datetime, end_datetime)
            (end_timeslot > 0 && timeslots_start_datetime[end_timeslot] == end_datetime) &&
                (end_timeslot -= 1)

            for l = start_timeslot:end_timeslot
                θ[i, l] = false
            end
        end
    end

    κ = -ones(Int, n_e)
    ζ = zeros(Int, n_e)
    α = ones(Bool, n_e, n_l)
    β = ones(Bool, n_e, n_l)
    U = Vector{Set{UnitRange{Int}}}([Set{UnitRange{Int}}() for e = 1:n_e])
    for (e, dict) in enumerate(dataset["examiners"])
        ζ[e] = dict["max_number_exams_per_day"]
        κ[e] = dict["max_number_days"]

        for (start_datetime_str, end_datetime_str) in dict["hard_unavailabilities"]
            start_datetime = DateTime(start_datetime_str)
            end_datetime = DateTime(end_datetime_str)

            start_timeslot = searchsortedlast(timeslots_start_datetime, start_datetime)
            if start_timeslot == 0 ||
               Date(timeslots_start_datetime[start_timeslot]) < Date(start_datetime)
                start_timeslot += 1
            end

            end_timeslot = searchsortedlast(timeslots_start_datetime, end_datetime)
            (end_timeslot > 0 && timeslots_start_datetime[end_timeslot] == end_datetime) &&
                (end_timeslot -= 1)


            for l = start_timeslot:end_timeslot
                α[e, l] = false
            end
        end

        for (start_datetime_str, end_datetime_str) in dict["soft_unavailabilities"]
            start_datetime = DateTime(start_datetime_str)
            end_datetime = DateTime(end_datetime_str)

            start_timeslot = searchsortedlast(timeslots_start_datetime, start_datetime)
            if start_timeslot == 0 ||
               Date(timeslots_start_datetime[start_timeslot]) < Date(start_datetime)
                start_timeslot += 1
            end

            end_timeslot = searchsortedlast(timeslots_start_datetime, end_datetime)
            (end_timeslot > 0 && timeslots_start_datetime[end_timeslot] == end_datetime) &&
                (end_timeslot -= 1)

            if start_timeslot <= end_timeslot
                obligation = start_timeslot:end_timeslot

                #= If the examiner isn't strongly available then the weak unavailability is considered
                to be a result of bad data and doesn't exist =#
                !prod(α[e, obligation]) && continue

                β[e, obligation] .= false
                push!(U[e], obligation)
            end
        end
    end


    η = -ones(Int, n_s)
    ρ = -ones(Int, n_s)
    μ = -ones(Int, n_s)
    ν = -ones(Int, n_s)
    room_type_data = Dict{String,Dict{String,Any}}()
    for (s, dict) in enumerate(dataset["subjects"])
        η[s] = dict["number_of_students"]
        ρ[s] = dict["max_number_exams_row"]
        μ[s] = dict["preparation_time"]
        ν[s] = dict["duration_time"]

        room_type = dict["room_type"]
        if !haskey(room_type_data, room_type)
            room_type_data[room_type] =
                Dict("subjects" => Set{Int}(), "rooms" => Set{Int}())
        end
        push!(room_type_data[room_type]["subjects"], s)
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

        push!(groups, Group(dict["examiner_ids"], s))
    end
    σ = zeros(Bool, n_j, n_j)
    for e = 1:n_e
        group_ids = findall(x -> x, λ[e, :])

        for j in group_ids, k in group_ids
            σ[j, k] = true
        end
    end

    δ = ones(Bool, n_m, n_l)
    ψ = zeros(Bool, n_m, n_s)
    for (m, dict) in enumerate(dataset["rooms"])
        room_type = dict["type"]
        if !haskey(room_type_data, room_type)
            room_type_data[room_type] =
                Dict("subjects" => Set{Int}(), "rooms" => Set{Int}())
        end
        push!(room_type_data[room_type]["rooms"], m)
        for s in room_type_data[room_type]["subjects"]
            ψ[m, s] = true
        end

        for (start_datetime_str, end_datetime_str) in dict["unavailabilities"]
            start_datetime = DateTime(start_datetime_str)
            end_datetime = DateTime(end_datetime_str)

            start_timeslot = searchsortedlast(timeslots_start_datetime, start_datetime)
            if start_timeslot == 0 ||
               Date(timeslots_start_datetime[start_timeslot]) < Date(start_datetime)
                start_timeslot += 1
            end

            end_timeslot = searchsortedlast(timeslots_start_datetime, end_datetime)
            (end_timeslot > 0 && timeslots_start_datetime[end_timeslot] == end_datetime) &&
                (end_timeslot -= 1)

            for l = start_timeslot:end_timeslot
                δ[m, l] = false
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
        ψ,
        S_exa,
        S_stu,
        U,
        J,
        L,
        V,
        Z,
        groups,
        room_type_data,
        dataset,
        timeslots_start_datetime,
    )
end

function check_infeasible_basic(I::Instance; fill_rate = 1)
    #= Perform basic preliminary tests in order to see if an instance is infeasible or not =#
    pb_constraints = Vector{String}()

    # Feasible amount of students for exams with multiple simultaneous students
    for j = 1:I.n_j
        s = I.groups[j].s
        if I.η[s] > 1
            nb_students_group = sum(I.γ[:, j])
            nb_leftover_students = nb_students_group % I.η[s]

            if nb_leftover_students == 0
                push!(
                    pb_constraints,
                    "Group $j needs $(I.η[s] - nb_leftover_students) more students",
                )
            end
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

        available_time = fill_rate * (I.n_l - sum(.!I.θ[i, :]))

        if time_needed <= available_time
            push!(
                pb_constraints,
                "Not enough time to schedule all of student $(i)'s exams. Time needed : $time_needed, available time $available_time",
            )
        end
    end

    # Student enough days
    for i = 1:I.n_i
        nb_days_needed = sum(I.γ[i, :]) / I.ξ
        nb_days_available = sum(sum(I.θ[i, l] for l in I.L[d]) > 0 for d = 1:I.n_d)

        if nb_days_needed <= nb_days_available
            push!(
                pb_constraints,
                "Not enough days to schedule all of student $(i)'s exams. Days needed : $nb_days_needed, available days : $nb_days_available",
            )
        end
    end

    # Examiner enough time or days
    for e = 1:I.n_e
        time_needed = 0
        nb_exams = 0
        for j = 1:I.n_j
            if I.λ[e, j]
                s = I.groups[j].s
                for i = 1:I.n_i
                    if I.γ[i, j]
                        nb_exams += 1
                        time_needed += (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]
                    end
                end
            end
        end
        available_time = fill_rate * sum(.!I.α[e, :])
        days_needed = max(ceil(time_needed / available_time), ceil(nb_exams / I.ζ[e]))

        if time_needed <= available_time
            push!(
                pb_constraints,
                "Not enough time to schedule all of examiner $(e)'s exams Time needed : $time_needed, filling rate * available time : $available_time",
            )
        end
        if days_needed <= I.κ[e]
            push!(
                pb_constraints,
                "Not enough days to schedule all of examiner $(e)'s exams. Days needed : $days_needed, available days : $(I.κ[e])",
            )
        end
    end

    # Group enough_time
    for j = 1:I.n_j
        s = I.groups[j].s
        exam_length = (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]

        # Compute the time needed for all of the exams
        time_needed = sum(I.γ[:, j]) * exam_length

        # Compute the available time
        group_alpha = [prod(I.α[e, l] for e in I.groups[j].e) for l = 1:I.n_l]
        group_nb_timeslots_avail = 0
        prev_l = 0
        for (l, val) in enumerate(group_alpha)
            val && continue
            time_in_bloc = l - prev_l - 1 + I.τ_seq
            group_nb_timeslots_avail +=
                time_in_bloc - (time_in_bloc % (exam_length * I.η[s]))
            prev_l = l
        end
        time_in_bloc = I.n_l - prev_l + I.τ_seq
        group_nb_timeslots_avail += time_in_bloc - (time_in_bloc % (exam_length * I.η[s]))

        if time_needed <= group_nb_timeslots_avail
            push!(
                pb_constraints,
                "Not enough time to schedule all of group $(j)'s exams. Time needed : $time_needed, filling rate * available time : $group_nb_timeslots_avail",
            )
        end
    end

    # Rooms enough time
    for (room_type, dict) in I.room_type_data
        exam_length(s) = (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]

        time_needed = sum(
            sum(I.γ[:, j]) * exam_length(I.groups[j].s) / I.η[I.groups[j].s] for
            j = 1:I.n_j if I.groups[j].s in dict["subjects"]
        )
        available_time = fill_rate * sum(I.δ[m, l] for l = 1:I.n_l, m in dict["rooms"])

        if time_needed <= available_time
            push!(
                pb_constraints,
                "Not enough time to schedule all the exams with type $(room_type). Time needed : $time_needed, filling rate * available time : $available_time",
            )
        end
    end

    if isempty(pb_constraints)
        println(pb_constraints)
        error(
            "The instance with the given filling rate is not feasible. The problematic constraints have been printed.",
        )
    end
end

function _create_split_instances(
    I::Instance,
    exams::Vector{Tuple{Int,Int}},
    days_split::Vector{UnitRange{Int}},
    y_values,
    z_values,
)
    nb_exams_examiner = zeros(Float64, I.n_e, n_splits)
    exam_splits = [Set{Tuple{Int,Int}}() for split = 1:n_splits]
    for exam in exams, split = 1:n_splits
        if sum(y_values[(exam, d)] for d in days_split[split]) >= 0.5
            push!(exam_splits[split], exam)

            j = exam[2]
            for e in I.groups[j].e
                nb_exams_examiner[e, split] += 1 / I.η[I.groups[j].s]
            end
        end
    end

    κ_splits = [
        Int(round(sum(z_values[(e, d)] for d in days_split[split]))) for e = 1:I.n_e,
        split = 1:n_splits
    ]

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

function _find_problematic_exams(RSD_jl_split_warm::Model)

    # Change exam needed into a soft constraint
    valid_ij = axes(RSD_jl_split_warm[:exam_needed], 1)
    delete(RSD_jl_split_warm, RSD_jl_split_warm[:exam_needed].data)

    @variable(RSD_jl_split_warm, c[(i, j) in valid_ij], binary = true)
    g = RSD_jl_split_warm[:g]
    RSD_jl_split_warm[:exam_needed] = @constraint(
        RSD_jl_split_warm,
        [(i, j) in valid_ij],
        sum(g[i, j, :]) == 1 - c[(i, j)]
    )

    @objective(RSD_jl_split_warm, Min, sum(c))

    # Solve the problem with exam needed as a soft constraint
    optimize!(RSD_jl_split_warm)
    @assert has_values(RSD_jl_split_warm) "The time limit is too small."

    # Get the indexes of the problematic exams
    c_values = value.(c)
    pb_exams = Set{Tuple{Int,Int}}()
    for (i, j) in axes(c_values, 1)
        if c_values[(i, j)] >= 0.5
            push!(pb_exams, (i, j))
        end
    end

    return pb_exams
end

include(String(@__DIR__) * "/../src/utils.jl")
function split_instance(
    I::Instance,
    n_splits::Int,
    SPLIT_obj_evol::Vector{Dict{String,Vector{Float64}}};
    fill_rate = 0.95,
    time_limit_warmstart = nothing,
    time_limit_SPLIT = nothing,
    mip_gap_SPLIT = 0.05,
    n_max_tries = 1,
    print_pb_constraints = false,
    frozen_ijlm = nothing,
    start_x_values = nothing,
)
    #= 
    Split the instance into multiple subinstances until a feasible split has been found.
    If some exams can't be placed in any split then they are completely removed from the
    original instance.

    Arguments:
    [input] I: original instance
    [input] n_splits: number of splits
    [input] fill_rate: parameter that controls how filled the splits can be
    [input] time_limit_warmstart: time limit in seconds for each warmstart resolution
    [input] time_limit_SPLIT: time limit in seconds for each SPLIT model resolution
    [input] mip_gap_SPLIT: goal gap for each SPLIT model resolution
    [input] : maximum number of times where the splitting MILP can be solved

    Return value: (split_instances, g_values_warmstart) 
    split_instances: Vector{SplitInstance} containing the different subsinstances
    g_values_warmstart: values of the g variable for the original instance  fter the warmstarts
    =#

    @assert n_splits >= 1
    @assert n_splits <= I.n_d "Can't have more splits than the number of days"
    @assert 0 < fill_rate <= 1 "The filling rate must be in (0, 1]"

    # Initialize some data
    days_split_size = zeros(Int, n_splits)
    for d = 1:I.n_d
        split_id = (d - 1) % n_splits + 1
        days_split_size[split_id] += 1
    end
    days_split = Vector{UnitRange{Int}}()
    let d = 0
        for split_size in days_split_size
            push!(days_split, d .+ (1:split_size))
            d += split_size
        end
    end

    exams = sort([(i, j) for i = 1:I.n_i, j = 1:I.n_j if I.γ[i, j]])

    # Declare the splitting model
    SPLIT_model = nothing
    if n_splits > 1
        SPLIT_model = Model(Gurobi.Optimizer)
        declare_splitting_MILP(I, n_splits, fill_rate, exams, days_split, SPLIT_model)
        !isnothing(time_limit_SPLIT) &&
            set_optimizer_attribute(SPLIT_model, "TimeLimit", time_limit_SPLIT)
        !isnothing(mip_gap_SPLIT) &&
            set_optimizer_attribute(SPLIT_model, "MIPGap", mip_gap_SPLIT)

        # Provide a starting solution if available
        if !isnothing(start_x_values)
            for (((i, j), d), var) in SPLIT_model[:y].data
                scheduled_in_start =
                    sum(start_x_values[i, j, l, m] for l in I.L[d], m = 1:I.n_m) > 0
                set_start_value(var, Int(scheduled_in_start))
            end
        end

        # Freeze the exams if needed
        if !isnothing(frozen_ijlm)
            days_start = [I.L[d][1] for d = 1:I.n_d]
            @assert issorted(days_start)
            get_day(l) = searchsortedfirst(days_start, l)

            for (i, j, l, m) in frozen_ijlm
                d = get_day(l)
                fix(SPLIT_model[:y][(i, j), d], 1; force = true)
            end
        end
    end

    # Solve the splitting problem until a feasible split has been found
    feasible_splits_found = false
    split_instances = nothing
    g_values_warmstart = nothing
    banned_exams = Dict{Tuple{Int,Int},Set{Int}}() # banned exam => banned splits
    completely_removed_exams = Set{Tuple{Int,Int}}()
    try_id = 1
    while !feasible_splits_found && try_id <= n_max_tries
        y_values = nothing
        z_values = nothing
        if n_splits == 1
            # If n_splits == 1 there is no need to solve the splitting MILP
            y_values = Dict((exam, 1) => Int((d == 1)) for exam in exams, d = 1:I.n_d)
            z_values = Dict((e, d) => (d == 1) * I.κ[e] for e = 1:I.n_e, d = 1:I.n_d)
        else
            # Warmstart
            let objective_splitting_MILP = objective_function(SPLIT_model)
                @objective(SPLIT_model, Min, 0)
                optimize!(SPLIT_model)

                # If the SPLIT_model is infeasible the print the problematic constraints
                if !has_values(SPLIT_model)
                    error_message = "Unable to split the instance.\nThis can be the result of a time limit that is too small, or a filling rate that is too low."
                    if termination_status(SPLIT_model) in
                       [MOI.INFEASIBLE, MOI.INFEASIBLE_OR_UNBOUNDED] && print_pb_constraints
                        error_message *= "\nThe problematic constraints have been printed."
                        print_constraint_conflicts(SPLIT_model)
                    end
                    error(error_message)
                end

                @objective(SPLIT_model, Min, objective_splitting_MILP)
            end

            # Set objective value fetching callback function
            callback_f = get_objective_value_callback(try_id, SPLIT_obj_evol)
            MOI.set(SPLIT_model, Gurobi.CallbackFunction(), callback_f)

            # Solve the MILP splitting problem
            optimize!(SPLIT_model)

            push!(SPLIT_obj_evol[try_id]["time"], JuMP.solve_time(SPLIT_model))
            push!(
                SPLIT_obj_evol[try_id]["objective"],
                SPLIT_obj_evol[try_id]["objective"][end],
            )

            # Read the results
            y_values_jump = value.(SPLIT_model[:y])
            z_values_jump = value.(SPLIT_model[:z])

            y_values =
                Dict((exam, d) => y_values_jump[exam, d] for exam in exams, d = 1:I.n_d)
            z_values = Dict((e, d) => z_values_jump[e, d] for e = 1:I.n_e, d = 1:I.n_d)
        end

        split_instances = _create_split_instances(I, exams, days_split, y_values, z_values)

        # Check if the splits instances are feasible by warmstarting the different splits
        g_values_warmstart = zeros(Bool, I.n_i, I.n_j, I.n_l)
        feasible_splits_found = true
        for (split, SplitI) in enumerate(split_instances)
            RSD_jl_split_warm = Model(Gurobi.Optimizer)
            declare_RSD_jl_split(SplitI, RSD_jl_split_warm)
            @objective(RSD_jl_split_warm, Min, 0)
            !isnothing(time_limit_warmstart) && set_optimizer_attribute(
                RSD_jl_split_warm,
                "TimeLimit",
                time_limit_warmstart,
            )

            # Provide a starting solution if available
            if !isnothing(start_x_values)
                for ((i, j, l), var) in RSD_jl_split_warm[:g].data
                    scheduled_in_start = sum(start_x_values[i, j, l, m] for m = 1:I.n_m) > 0
                    is_completely_removed = (i, j) in completely_removed_exams
                    set_start_value(var, Int(scheduled_in_start && !is_completely_removed))
                end
            end

            # Freeze certain exams if needed
            if !isnothing(frozen_ijlm)
                for (i, j, l, m) in frozen_ijlm
                    (!((i, j) in completely_removed_exams)) &&
                        fix(RSD_jl_split_warm[:g][i, j, l], 1; force = true)
                end
            end

            optimize!(RSD_jl_split_warm)

            # If the split is infeasible then find the exams that cause problem
            if !has_values(RSD_jl_split_warm)
                if n_splits == 1
                    error(
                        "Couldn't warmstart the RSD_jl submodel.
                  Either the instance is infeasible or the warmstart time limit is too low.",
                    )
                end

                feasible_splits_found = false

                if termination_status(RSD_jl_split_warm) in
                   [MOI.INFEASIBLE, MOI.INFEASIBLE_OR_UNBOUNDED] && print_pb_constraints
                    print_constraint_conflicts(RSD_jl_split_warm)
                    flush(stdout)
                end

                pb_exams = _find_problematic_exams(RSD_jl_split_warm)

                # Ban the problematic exams in the splitting MILP
                if try_id == n_max_tries
                    RSD_jl_split_warm = Model(Gurobi.Optimizer)
                    declare_RSD_jl_split(SplitI, RSD_jl_split_warm)
                    @objective(RSD_jl_split_warm, Min, 0)
                    !isnothing(time_limit_warmstart) && set_optimizer_attribute(
                        RSD_jl_split_warm,
                        "TimeLimit",
                        time_limit_warmstart,
                    )

                    for exam in pb_exams
                        push!(completely_removed_exams, exam)
                        delete!(split_instances[split].exams, exam)

                        delete(RSD_jl_split_warm, RSD_jl_split_warm[:exam_needed][exam])
                        RSD_jl_split_warm[:exam_needed][exam] = @constraint(
                            RSD_jl_split_warm,
                            sum(RSD_jl_split_warm[:g][exam[1], exam[2], :]) == 0
                        )
                    end

                    if !isnothing(frozen_ijlm)
                        for (i, j, l, m) in frozen_ijlm
                            (!((i, j) in completely_removed_exams)) &&
                                fix(RSD_jl_split_warm[:g][i, j, l], 1; force = true)
                        end
                    end

                    # Provide a starting solution if available
                    if !isnothing(start_x_values)
                        for ((i, j, l), var) in RSD_jl_split_warm[:g].data
                            scheduled_in_start =
                                sum(start_x_values[i, j, l, m] for m = 1:I.n_m) > 0
                            is_completely_removed = (i, j) in completely_removed_exams
                            set_start_value(
                                var,
                                Int(scheduled_in_start && !is_completely_removed),
                            )
                        end
                    end

                    optimize!(RSD_jl_split_warm)
                    @assert has_values(RSD_jl_split_warm)
                else
                    for exam in pb_exams
                        if !haskey(banned_exams, exam)
                            banned_exams[exam] = Set()
                        end
                        push!(banned_exams[exam], split)
                        for d in days_split[split]
                            fix(SPLIT_model[:y][exam, d], 0; force = true)
                        end

                        if length(banned_exams[exam]) == n_splits
                            push!(completely_removed_exams, exam)
                        end
                    end
                end
            end

            if has_values(RSD_jl_split_warm) || try_id == n_max_tries
                # Get the warmstart values
                g_values_dict = value.(RSD_jl_split_warm[:g]).data
                for ((i, j, l), value) in g_values_dict
                    if value >= 0.5
                        g_values_warmstart[i, j, l] = true
                    end
                end
            end
        end

        # Remove completely removed exams
        if !isempty(completely_removed_exams)
            remaining_exams = setdiff!(exams, completely_removed_exams)

            # Actualise the exam one split constraint
            delete(SPLIT_model, SPLIT_model[:exam_needed].data)
            SPLIT_model[:exam_needed] = @constraint(
                SPLIT_model,
                [exam in remaining_exams],
                sum(SPLIT_model[:y][exam, d] for d = 1:I.n_d) == 1
            )

            # Remove the exams from the instance
            for exam in completely_removed_exams
                I.γ[exam[1], exam[2]] = false
            end
        end

        try_id += 1
    end

    if !isempty(completely_removed_exams)
        println_dash(
            "$(length(completely_removed_exams)) exams have been completely removed",
        )
    else
        println_dash("All exams were kept. None were removed from the instance.")
    end

    return split_instances, g_values_warmstart, completely_removed_exams
end
