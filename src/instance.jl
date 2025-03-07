using JSON, Dates

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

    ζ::Vector{Int}
    α::Matrix{Bool}
    β::Matrix{Bool}
    λ::Matrix{Bool}

    η::Vector{Int}
    ρ::Vector{Int}
    μ::Vector{Int}
    ν::Vector{Int}

    κ::Vector{Int}
    σ::Matrix{Bool}

    δ::Array{Bool,3}

    U::Vector{Vector{Vector{Int}}}
    J::Vector{Set{Int}}
    L::Vector{Vector{Int}}
    V::Vector{Vector{Int}}
    Z::Vector{Set{Int}}

    groups::Vector{Group}
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

    timeslots_start_datetime = Vector{DateTime}([])
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

    ζ = zeros(Int, n_e)
    α = ones(Bool, n_e, n_l)
    β = ones(Bool, n_e, n_l)
    U = Vector{Vector{Vector{Int}}}([Vector{Vector{Int}}() for e = 1:n_e])
    for (e, dict) in enumerate(dataset["examiners"])
        ζ[e] = dict["max_number_exams_per_day"]

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

    κ = -ones(Int, n_j)
    λ = zeros(Bool, n_e, n_j)
    J = Vector{Set{Int}}([Set{Int}() for s = 1:n_s])
    groups = Vector{Group}()
    for (j, dict) in enumerate(dataset["groups"])
        s = dict["subject_id"]

        κ[j] = dict["max_number_days"]
        push!(J[s], j)

        for e in dict["examiner_ids"]
            λ[e, j] = true
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
        ζ,
        α,
        β,
        λ,
        η,
        ρ,
        μ,
        ν,
        κ,
        σ,
        δ,
        U,
        J,
        L,
        V,
        Z,
        groups,
    )
end
