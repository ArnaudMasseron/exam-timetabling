using JSON, XLSX, Plots

function write_solution_json(
    I::Instance,
    x_values::Array{Bool,4},
    unscheduled_exams_ids::Set{Tuple{Int,Int}},
    sol_cost::Tuple{Float64,Vector{Float64},Dict{String,Any}},
    solution_path::String,
)
    @assert endswith(solution_path, ".json")

    solution = Dict{String,Any}()

    exams = []
    for cart_id in keys(x_values)
        if x_values[cart_id] >= 0.5
            i, j, l, m = Tuple(cart_id)
            s = I.groups[j].s

            student_name = I.dataset["students"][i]["name"]
            student_class_id = I.dataset["students"][i]["class_id"]
            student_class_name = I.dataset["classes"][student_class_id]["acronym"]

            examiner_names = map(e -> I.dataset["examiners"][e]["name"], I.groups[j].e)
            examiner_acronyms =
                map(e -> I.dataset["examiners"][e]["acronym"], I.groups[j].e)

            subject_name = I.dataset["subjects"][s]["name"]
            room_acronym = I.dataset["rooms"][m]["acronym"]

            start_datetime = I.timeslots_start_datetime[l]
            date = Date(start_datetime)
            start_time = Time(start_datetime)

            exam_id = findfirst(
                x -> x["student_id"] == i && x["group_id"] == j,
                I.dataset["exams"],
            )
            modality = I.dataset["exams"][exam_id]["modality"]

            preparation_time_min = convert(Minute, I.μ[s] * I.Δ_l).value
            duration_time_min = convert(Minute, I.ν[s] * I.Δ_l).value

            exam_entry = Dict(
                "class_studentName" => student_class_name * "_" * student_name,
                "examiner_names" => examiner_names,
                "examiner_acronyms" => examiner_acronyms,
                "subject_name" => subject_name,
                "room_acronym" => room_acronym,
                "date" => date,
                "start_time" => start_time,
                "modality" => modality,
                "preparation_time_min" => preparation_time_min,
                "duration_time_min" => duration_time_min,
            )
            push!(exams, exam_entry)
        end
    end

    unscheduled_exams = []
    for (i, j) in unscheduled_exams_ids
        student_name = I.dataset["students"][i]["name"]
        student_class_id = I.dataset["students"][i]["class_id"]
        student_class_name = I.dataset["classes"][student_class_id]["acronym"]

        examiner_names = map(e -> I.dataset["examiners"][e]["name"], I.groups[j].e)
        examiner_acronyms = map(e -> I.dataset["examiners"][e]["acronym"], I.groups[j].e)

        s = I.groups[j].s
        subject_name = I.dataset["subjects"][s]["name"]

        exam_id =
            findfirst(x -> x["student_id"] == i && x["group_id"] == j, I.dataset["exams"])
        modality = I.dataset["exams"][exam_id]["modality"]

        preparation_time_min = convert(Minute, I.μ[s] * I.Δ_l).value
        duration_time_min = convert(Minute, I.ν[s] * I.Δ_l).value

        exam_entry = Dict(
            "class_studentName" => student_class_name * "_" * student_name,
            "examiner_names" => examiner_names,
            "examiner_acronyms" => examiner_acronyms,
            "subject_name" => subject_name,
            "modality" => modality,
            "preparation_time_min" => preparation_time_min,
            "duration_time_min" => duration_time_min,
        )
        push!(unscheduled_exams, exam_entry)
    end

    solution["exams"] = exams
    solution["unscheduled_exams"] = unscheduled_exams
    solution["cost"] = Dict{String,Any}(
        "total_cost" => sol_cost[1],
        "soft_constraints_costs" => sol_cost[2],
        "interpretable_KPIs" => sol_cost[3],
    )

    # If the save directory doesn't exist then create it
    dir_path = dirname(solution_path)
    isdir(dir_path) || mkpath(dir_path)

    # Save exams in a json file
    open(solution_path, "w") do file
        JSON.print(file, solution, 2)
    end
end

function is_solution_feasible(I::Instance, x::Array{Bool,4})
    is_feasible = true
    pb_constraints = Vector{String}()

    # --- Exam related constraints --- #
    # Exam needed
    for i = 1:I.n_i, j = 1:I.n_j
        LHS = sum(x[i, j, l, m] for l = 1:I.n_l, m = 1:I.n_m; init = 0)
        if LHS != Int(I.γ[i, j])
            push!(pb_constraints, "exam needed (i=$i, j=$j)")
            is_feasible = false
        end
    end

    # Exam student number
    for j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m
        LHS = sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]; init = 0)

        if !(LHS in [0, I.η[I.groups[j].s]])
            push!(pb_constraints, "exam student number (j=$j, l=$l, m=$m)")
            is_feasible = false
        end
    end

    # Exam start and end
    let big_sum = sum(
            x[i, j, l, m] for i = 1:I.n_i, j = 1:I.n_j, d = 1:I.n_d for l in
            vcat(I.L[d][1:I.μ[I.groups[j].s]], I.L[d][end-I.ν[I.groups[j].s]-1:end]),
            m = 1:I.n_m;
            init = 0,
        )
        if big_sum > 0
            push!(pb_constraints, "exam start and end")
            is_feasible = false
        end
    end

    # Exam break min duration
    let
        M = [ceil(max(I.τ_seq, I.μ[s]) / I.ν[s]) for s = 1:I.n_s]

        for j = 1:I.n_j, d = 1:I.n_d, l in I.L[d][1+I.ν[I.groups[j].s]:end]

            LHS =
                sum(
                    x[i, j, l+t, m] for i = 1:I.n_i if I.γ[i, j] for
                    t = 0:min(I.L[d][end] - l, max(I.τ_seq, I.μ[I.groups[j].s]) - 1),
                    m = 1:I.n_m;
                    init = 0,
                ) / I.η[I.groups[j].s]

            RHS =
                M[I.groups[j].s] * (
                    1 +
                    sum(
                        x[i, j, l, m] - x[i, j, l-I.ν[I.groups[j].s], m] for
                        i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m
                    ) / I.η[I.groups[j].s]
                )

            if LHS > RHS
                push!(pb_constraints, "exam break min duration (j=$j, d=$d, l=$l)")
                is_feasible = false
            end
        end
    end

    # Exam break series end

    for j = 1:I.n_j, d = 1:I.n_d, l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end]

        LHS = sum(x[i, j, l, m] for i = 1:I.n_i, m = 1:I.n_m) / I.η[I.groups[j].s]

        RHS =
            I.ρ[I.groups[j].s] -
            sum(
                x[i, j, l-a*I.ν[I.groups[j].s], m] for i = 1:I.n_i if I.γ[i, j] for
                m = 1:I.n_m, a = 1:I.ρ[I.groups[j].s];
                init = 0,
            ) / I.η[I.groups[j].s]

        if LHS > RHS
            push!(pb_constraints, "exam break series end (j=$j, d=$d, l=$l)")
            is_feasible = false
        end
    end

    # --- Student related constraints --- #
    # Student availability
    for s = 1:I.n_s, i = 1:I.n_i, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
        LHS = sum(x[i, j, l, m] for j in I.J[s] if I.γ[i, j] for m = 1:I.n_m; init = 0)
        RHS = prod(I.θ[i, l-I.μ[s]:l+I.ν[s]-1])

        if LHS > RHS
            push!(pb_constraints, "student availability (s=$s, i=$i, d=$d, l=$l)")
            is_feasible = false
        end
    end

    # Student one exam 1
    for i = 1:I.n_i, l = 1:I.n_l
        LHS = sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for m = 1:I.n_m; init = 0)

        if LHS > 1
            push!(pb_constraints, "student one exam 1 (i=$i, l=$l)")
            is_feasible = false
        end
    end

    # Student one exam 2
    let
        μ_max_stu = [maximum(I.μ[s] for s in I.S_stu[i]) for i = 1:I.n_i]
        ν_min_stu = [minimum(I.ν[s] for s in I.S_stu[i]) for i = 1:I.n_i]
        M = [
            ceil((I.ν[s] - 1 + I.τ_stu + μ_max_stu[i]) / ν_min_stu[i]) for s = 1:I.n_s,
            i = 1:I.n_i
        ]

        for i = 1:I.n_i, s = 1:I.n_s, d = 1:I.n_d, l in I.L[d]
            LHS = sum(
                x[i, k, l+t, m] for k = 1:I.n_j if I.γ[i, k] for
                t = 1:min(I.ν[s] - 1 + I.τ_stu + I.μ[I.groups[k].s], I.L[d][end] - l),
                m = 1:I.n_m;
                init = 0,
            )
            RHS =
                M[s, i] * (
                    1 - sum(
                        x[i, j, l, m_tilde] for j in I.J[s] if I.γ[i, j] for
                        m_tilde = 1:I.n_m;
                        init = 0,
                    )
                )

            if LHS > RHS
                push!(pb_constraints, "student one exam 2 (i=$i, s=$s, d=$d, l=$l)")
                is_feasible = false
            end
        end
    end

    # Student max exams
    for i = 1:I.n_i, d = 1:I.n_d
        LHS = sum(
            x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.L[d], m = 1:I.n_m;
            init = 0,
        )
        if LHS > I.ξ
            push!(pb_constraints, "student max exams (i=$i, d=$d)")
            is_feasible = false
        end
    end

    # --- Group related constraints --- #
    # Group availability
    for s = 1:I.n_s,
        j in I.J[s],
        e in I.groups[j].e,
        d = 1:I.n_d,
        l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]

        s = I.groups[j].s
        LHS =
            length(I.groups[j].e) *
            length(-I.μ[I.groups[j].s]:I.ν[I.groups[j].s]-1) *
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0)
        RHS =
            I.η[I.groups[j].s] * sum(
                I.α[e, l+t] for e in I.groups[j].e,
                t = -I.μ[I.groups[j].s]:I.ν[I.groups[j].s]-1
            )

        if LHS > RHS
            push!(pb_constraints, "group availaibility (s=$s, j=$j, e=$e, d=$d, l=$l)")
            is_feasible = false
        end
    end

    # Group one exam
    for s in (s for s = 1:I.n_s if I.ν[s] > 1),
        j in I.J[s],
        d = 1:I.n_d,
        l in I.L[d][1:end-(I.ν[s]-1)]

        LHS =
            sum(
                x[i, j, l+t, m] for i = 1:I.n_i if I.γ[i, j] for t = 1:I.ν[s]-1, m = 1:I.n_m;
                init = 0,
            ) / I.η[s]
        RHS =
            1 -
            sum(
                x[i, j, l, m_tilde] for i = 1:I.n_i if I.γ[i, j] for m_tilde = 1:I.n_m;
                init = 0,
            ) / I.η[s]

        if LHS > RHS
            push!(pb_constraints, "group one exam (s=$s, j=$j, d=$d, l=$l)")
            is_feasible = false
        end
    end

    # Examiner lunch break
    for e = 1:I.n_e, d = 1:I.n_d
        at_least_one_break = false
        valid_j = (j for j = 1:I.n_j if I.λ[e, j])

        for l in I.V[d]
            possible_break_l = true
            for j in valid_j
                LHS = sum(
                    x[i, j, l+t, m] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]
                    for i = 1:I.n_i if I.γ[i, j] for t =
                        max(I.L[d][1] - l, -I.ν[I.groups[j].s] + 1):min(
                            I.L[d][end] - l,
                            I.μ[I.groups[j].s] + I.τ_lun - 1,
                        ), m = 1:I.n_m;
                    init = 0,
                )
                if LHS > 0
                    possible_break_l = false
                end
            end
            if possible_break_l
                at_least_one_break = true
                break
            end
        end

        if !at_least_one_break
            push!(pb_constraints, "examiner lunch break (e=$e, d=$d)")
            is_feasible = false
        end
    end

    # Group switch break
    for j = 1:I.n_j,
        k in (k for k = 1:I.n_j if k != j && I.σ[j, k]),
        d = 1:I.n_d,
        l in I.L[d][1:end-(I.ν[I.groups[j].s]-1+I.τ_swi+I.μ[I.groups[k].s])],
        t = 0:min(I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s], I.L[d][end] - l)

        LHS =
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) /
            I.η[I.groups[j].s] +
            sum(x[i, k, l+t, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) /
            I.η[I.groups[k].s]
        if LHS > 1
            push!(pb_constraints, "group switch break (j=$j, k=$k, d=$d, l=$l, t=$t)")
            is_feasible = false
        end
    end

    # Examiner max exams
    for e = 1:I.n_e, d = 1:I.n_d
        LHS = sum(
            x[i, j, l, m] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j] for
            i = 1:I.n_i if I.γ[i, j] for l in I.L[d], m = 1:I.n_m;
            init = 0,
        )
        if LHS > I.ζ[e]
            push!(pb_constraints, "examiner max exams (e=$e, d=$d)")
            is_feasible = false
        end
    end

    # Group max days
    for e = 1:I.n_e
        nb_days = 0

        for d = 1:I.n_d
            LHS = sum(
                x[i, j, l, m] for j = 1:I.n_j if I.λ[e, j] for i = 1:I.n_i if I.γ[i, j]
                for l in I.L[d], m = 1:I.n_m;
                init = 0,
            )
            if LHS > 0
                nb_days += 1
            end
        end

        if nb_days == 0 || nb_days > I.κ[e]
            push!(pb_constraints, "group max days (e=$e, d=$d)")
            is_feasible = false
        end
    end

    # Room switch break
    let
        M(s) = ceil((I.μ[s] + I.τ_room) / I.ν[s])

        for j = 1:I.n_j, d = 1:I.n_d, l in I.L[d], m = 1:I.n_m
            LHS =
                sum(
                    x[i, j, l+I.ν[I.groups[j].s]+t, m_tilde] for
                    m_tilde = 1:I.n_m if m_tilde != m for i = 1:I.n_i if I.γ[i, j] for t =
                        0:min(
                            I.L[d][end] - l - I.ν[I.groups[j].s],
                            I.τ_room + I.μ[I.groups[j].s],
                        );
                    init = 0,
                ) / I.η[I.groups[j].s]

            RHS =
                M(I.groups[j].s) * (
                    1 -
                    sum(
                        x[i_prime, j, l, m] for i_prime = 1:I.n_i if I.γ[i_prime, j];
                        init = 0,
                    ) / I.η[I.groups[j].s]
                )

            if LHS > RHS
                push!(pb_constraints, "room switch break (j=$j, d=$d, l=$l, m=$m)")
                is_feasible = false
            end
        end
    end

    # --- Room related constraints --- #
    # Room availability
    for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)], m = 1:I.n_m
        LHS = sum(x[i, j, l, m] for i = 1:I.n_i, j in I.J[s] if I.γ[i, j]; init = 0)
        RHS = I.η[s] * I.ψ[m, s] * prod(I.δ[m, l-I.μ[s]:l+I.ν[s]-1])

        if LHS > RHS
            push!(pb_constraints, "room availability (s=$s, d=$d, l=$l, m=$m)")
            is_feasible = false
        end
    end

    # Room group occupation
    let
        a(s, u) = I.ν[s] - 1 + I.τ_room + I.μ[u]
        M(s, u) = ceil((a(s, u) + 1) / I.ν[u])
        for j = 1:I.n_j, k in setdiff(1:I.n_j, [j]), d = 1:I.n_d, l in I.L[d], m = 1:I.n_m
            LHS =
                sum(
                    x[i, k, l+t, m] for i = 1:I.n_i if I.γ[i, k] for
                    t = 0:min(I.L[d][end] - l, a(I.groups[j].s, I.groups[k].s));
                    init = 0,
                ) / I.η[I.groups[k].s]

            RHS =
                M(I.groups[j].s, I.groups[k].s) * (
                    1 -
                    sum(
                        x[i_prime, j, l, m] for i_prime = 1:I.n_i if I.γ[i_prime, j];
                        init = 0,
                    ) / I.η[I.groups[j].s]
                )

            if LHS > RHS
                push!(
                    pb_constraints,
                    "room group occupation (j=$j, k=$k, d=$d, l=$l, m=$m)",
                )
                is_feasible = false
            end
        end
    end

    return true, pb_constraints
end

function solution_cost(I::Instance, x::Array{Bool,4}; compute_unwanted_breaks = false)
    # Student harmonious exams
    y = zeros(Int, I.n_i)
    for i = 1:I.n_i, w = 1:I.n_w
        expr =
            sum(
                x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.Z[w], m = 1:I.n_m;
                init = 0,
            ) - ceil(I.ε[i] / I.n_w)

        y[i] = max(y[i], abs(expr))
    end

    # Group availability
    q = Vector{Dict{UnitRange{Int},Bool}}([
        Dict{UnitRange{Int},Bool}(zip(I.U[e], zeros(Bool, length(I.U[e])))) for e = 1:I.n_e
    ])
    for j = 1:I.n_j, e in I.groups[j].e, P in I.U[e]
        !prod(I.α[e, P]) && continue
        s = I.groups[j].s

        days_begginings = [I.L[d][1] for d = 1:I.n_d]
        @assert issorted(days_begginings)
        get_t_range(l) = begin
            d = searchsortedlast(days_begginings, l)
            return max(-I.μ[s], l - I.L[d][end]):min(I.ν[s] - 1, l - I.L[d][1])
        end

        if sum(
            x[i, j, l-t, m] for l in P for t in get_t_range(l), i = 1:I.n_i, m = 1:I.n_m;
            init = 0,
        ) > 0
            q[e][P] = true
        end
    end

    # Group max days
    w = zeros(Int, I.n_e)
    for e = 1:I.n_e
        nb_days = 0

        for d = 1:I.n_d
            LHS = sum(
                x[i, j, l, m] for j = 1:I.n_j if I.λ[e, j] for i = 1:I.n_i if I.γ[i, j]
                for l in I.L[d], m = 1:I.n_m;
                init = 0,
            )
            if LHS > 0
                nb_days += 1
            end
        end

        w[e] = nb_days - 1
    end

    # Exam grouped
    R = [I.L[d][1] for e = 1:I.n_e, d = 1:I.n_d]
    r = [I.L[d][end] for e = 1:I.n_e, d = 1:I.n_d]
    for j = 1:I.n_j, d = 1:I.n_d, l in I.L[d]
        exam_going_on =
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) > 0
        if exam_going_on
            for e in I.groups[j].e
                R[e, d] = max(R[e, d], l)
                r[e, d] = min(r[e, d], l)
            end
        end
    end
    for e = 1:I.n_e, d = 1:I.n_d
        if r[e, d] > R[e, d]
            r[e, d] = R[e, d]
        end
    end

    # Exam continuity
    z = zeros(Bool, I.n_j, I.n_l, I.n_m)
    for j = 1:I.n_j, d = 1:I.n_d, l in I.L[d][I.ν[I.groups[j].s]+1:end], m = 1:I.n_m
        s = I.groups[j].s
        nb_exams_before = sum(
            x[i, j, l-t, m] for i = 1:I.n_i if I.γ[i, j] for
            t in I.ν[s] * (1:I.ρ[s]) if l - t >= I.L[d][1];
            init = 0,
        )
        constraint_active = (nb_exams_before < I.ρ[s])

        if constraint_active
            LHS = sum(x[i, j, l-I.ν[s], m] for i = 1:I.n_i if I.γ[i, j]; init = 0)
            RHS = sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]; init = 0)

            if LHS > RHS
                z[j, l, m] = true
            end
        end
    end

    # Students same class together
    R_tilde = [I.L[d][1] for j = 1:I.n_j, c = 1:I.n_c, d = 1:I.n_d]
    r_tilde = [I.L[d][end] for j = 1:I.n_j, c = 1:I.n_c, d = 1:I.n_d]
    get_stu_class(i) = I.dataset["students"][i]["class_id"]
    for j = 1:I.n_j, c = 1:I.n_c, d = 1:I.n_d, l in I.L[d]
        exam_going_on =
            sum(
                x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] && get_stu_class(i) == c for
                m = 1:I.n_m;
                init = 0,
            ) > 0
        if exam_going_on
            R_tilde[j, c, d] = max(R_tilde[j, c, d], l)
            r_tilde[j, c, d] = min(r_tilde[j, c, d], l)
        end
    end
    for j = 1:I.n_j, c = 1:I.n_c, d = 1:I.n_d
        if r_tilde[j, c, d] > R_tilde[j, c, d]
            r_tilde[j, c, d] = R_tilde[j, c, d]
        end
    end


    # --- Objective function --- #
    # Soft constraints penalty coefficients
    y_coef = 30 * (I.n_w == 1 ? 0 : 1 / sum((1 - 1 / I.n_w) * I.ε)) # student harmonious exams
    q_coef = 80 / sum(length(P) for e = 1:I.n_e for P in I.U[e]; init = 0) # examiner availability
    !isfinite(q_coef) && (q_coef = 0)
    is_expert(e) = (I.dataset["examiners"][e]["type"] == "expert")
    w_coef = 60 / sum(is_expert(e) * I.κ[e] for e = 1:I.n_e) # examiner max days
    z_coef = 50 / sum(I.γ) # exam continuity
    R_coef = 10 / (I.n_l / I.n_d * sum(I.κ)) # exam grouped
    Rr_coef = 50 / (I.n_l / I.n_d * sum(I.κ)) # exam grouped
    group_κ = [minimum(I.κ[e] for e in I.groups[j].e) for j = 1:I.n_j]
    is_jc_valid = [
        sum(I.γ[i, j] && (I.dataset["students"][i]["class_id"] == c) for i = 1:I.n_i) > 0 for j = 1:I.n_j, c = 1:I.n_c
    ]
    is_j_multi_class = [sum(is_jc_valid[j, :]) >= 2 for j = 1:I.n_j]
    Rr_tilde_coef =
        30 / (
            I.n_l / I.n_d * sum(
                group_κ[j] * sum(is_jc_valid[j, :]) for j = 1:I.n_j if is_j_multi_class[j];
                init = 0,
            )
        ) # Student same class together

    detailed_objective = [
        y_coef * sum(y),
        q_coef * sum(
            is_P_canceled * length(P) for e = 1:I.n_e for (P, is_P_canceled) in q[e];
            init = 0,
        ),
        w_coef * sum(is_expert(e) * w[e] for e = 1:I.n_e),
        z_coef * sum(z),
        R_coef * sum(R[e, d] - I.L[d][1] for e = 1:I.n_e, d = 1:I.n_d),
        Rr_coef * sum(R .- r),
        Rr_tilde_coef * sum(
            R_tilde[j, c, d] .- r_tilde[j, c, d] for j = 1:I.n_j if is_j_multi_class[j]
            for c = 1:I.n_c if is_jc_valid[j, c] for d = 1:I.n_d;
            init = 0,
        ),
    ]
    objective = sum(detailed_objective)

    # --- Sot constraint interbretable details --- #
    detailed_soft_constraints = Dict{String,Any}()

    detailed_soft_constraints["nb_non_harmonious_students"] = sum(y .> 0)

    classes_canceled_timeslots = sum(
        is_P_canceled * length(P) for e = 1:I.n_e for (P, is_P_canceled) in q[e];
        init = 0,
    )
    classes_canceled_min = convert(Minute, classes_canceled_timeslots * I.Δ_l).value
    detailed_soft_constraints["nb_hours_cancelled"] = string(
        Hour(div(classes_canceled_min, 60)) + Minute(ceil(classes_canceled_min % 60)),
    )

    detailed_soft_constraints["examiner_canceled_obligations"] =
        Dict{String,Dict{String,Any}}()
    let get_datetime(l) = I.timeslots_start_datetime[l]
        for e = 1:I.n_e, (P, is_P_canceled) in q[e]
            !is_P_canceled && continue

            exa_acro = I.dataset["examiners"][e]["acronym"]
            datetime_window = (get_datetime(P[1]), get_datetime(P[end]) + I.Δ_l)
            if !haskey(detailed_soft_constraints["examiner_canceled_obligations"], exa_acro)
                detailed_soft_constraints["examiner_canceled_obligations"][exa_acro] =
                    Dict{String,Any}(
                        "time_slots" => Vector{UnitRange{Int}}(),
                        "real_datetimes" => Vector{Tuple{DateTime,DateTime}}(),
                    )
            end

            push!(
                detailed_soft_constraints["examiner_canceled_obligations"][exa_acro]["real_datetimes"],
                datetime_window,
            )
            push!(
                detailed_soft_constraints["examiner_canceled_obligations"][exa_acro]["time_slots"],
                P,
            )
        end
    end

    theoretical_min_days_needed = zeros(Int, I.n_e)
    for e = 1:I.n_e
        !is_expert(e) && continue

        nb_exams_e = Int(
            ceil(
                sum(
                    I.γ[i, j] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j] for
                    i = 1:I.n_i;
                    init = 0,
                ),
            ),
        )
        min_days_1 = Int(ceil(nb_exams_e / I.ζ[e]))

        day_timeslot_threhsolds = [sum(I.α[e, l] for l in I.L[d]) for d = 1:I.n_d]
        sort!(day_timeslot_threhsolds, rev = true)
        for d = 2:I.n_d
            day_timeslot_threhsolds[d] += day_timeslot_threhsolds[d-1]
        end

        total_time_needed_e = 0
        for j = 1:I.n_j
            if I.λ[e, j]
                s = I.groups[j].s
                total_time_needed_e +=
                    (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s] * sum(I.γ[:, j])
            end
        end
        min_days_2 = searchsortedfirst(day_timeslot_threhsolds, total_time_needed_e)

        theoretical_min_days_needed[e] = max(min_days_1, min_days_2)
    end
    detailed_soft_constraints["expert_mean_additional_days"] =
        sum(w[e] + 1 - theoretical_min_days_needed[e] for e = 1:I.n_e if is_expert(e)) /
        sum(is_expert.(1:I.n_e))

    detailed_soft_constraints["nb_penalized_exam_discontinuities"] = sum(z)

    # The code inside this if block runs very slowly, it may be improved
    if compute_unwanted_breaks
        has_exam = zeros(Bool, I.n_e, I.n_d)
        unwanted_breaks = zeros(Int, I.n_e, I.n_d)
        for e = 1:I.n_e, d = 1:I.n_d
            if sum(
                I.λ[e, j] * x[i, j, l, m] for i = 1:I.n_i, j = 1:I.n_j, l in I.L[d],
                m = 1:I.n_m
            ) == 0
                continue
            end
            has_exam[e, d] = true

            prev_exam_l = nothing
            prev_m = nothing
            prev_j = nothing
            prev_s = nothing
            lunch_pause_added = false
            for l = r[e, d]:R[e, d]
                if sum(
                    I.λ[e, j] * x[i, j, l, m] for i = 1:I.n_i, j = 1:I.n_j, m = 1:I.n_m
                ) > 0
                    j = nothing
                    m = nothing
                    for j_tilde = 1:I.n_j
                        if I.λ[e, j_tilde]
                            for m_tilde = 1:I.n_m
                                if sum(x[i, j_tilde, l, m_tilde] for i = 1:I.n_i) > 0
                                    j = j_tilde
                                    m = m_tilde
                                    break
                                end
                            end
                        end
                    end
                    s = I.groups[j].s

                    if !isnothing(prev_exam_l)
                        total_empty_time = l - prev_exam_l - 1

                        discontinuity_in_between = (total_empty_time > I.ν[prev_s] - 1)

                        class_time_in_between = sum(
                            sum(l in P for P in I.U[e]; init = 0) > 0 for
                            l_tilde = prev_exam_l+I.ν[prev_s]-1:l-I.μ[prev_s];
                            init = 0,
                        )
                        wanted_empty_time = I.ν[prev_s] - 1
                        wanted_empty_time += max(
                            discontinuity_in_between * max(I.τ_seq, I.μ[s]),
                            (prev_m != m) * I.τ_room,
                            (prev_j != j) * I.τ_swi,
                            class_time_in_between,
                        )

                        if !lunch_pause_added
                            prev_exam_end = prev_exam_l + I.ν[prev_s] - 1
                            end_in_lunch_window =
                                (I.V[d][1] <= prev_exam_end && prev_exam_end <= I.V[d][end])
                            lunch_wasted_time =
                                total_empty_time - (I.ν[prev_s] - 1 + I.τ_lun + I.μ[s])
                            enough_time_for_lunch =
                                lunch_wasted_time >= 0 &&
                                wanted_empty_time <= total_empty_time - lunch_wasted_time
                            if end_in_lunch_window && enough_time_for_lunch
                                @assert discontinuity_in_between
                                lunch_pause_added = true
                                wanted_empty_time = I.ν[prev_s] - 1 + I.τ_lun + I.μ[s]
                            end
                        end

                        unwanted_empty_time = total_empty_time - wanted_empty_time
                        if unwanted_empty_time > 0
                            unwanted_breaks[e, d] += unwanted_empty_time
                        end
                    end

                    prev_exam_l = l
                    prev_m = m
                    prev_j = j
                    prev_s = s
                end
            end
        end
        mean_unwanted_breaks_min =
            sum(unwanted_breaks; init = 0) / sum(has_exam; init = 0) *
            Int(round(I.Δ_l / Minute(1)))
        detailed_soft_constraints["mean_examiner_unwanted_breaks"] = string(
            Hour(div(mean_unwanted_breaks_min, 60)) +
            Minute(ceil(mean_unwanted_breaks_min % 60)),
        )
    end

    return objective, detailed_objective, detailed_soft_constraints
end

function draw_RSD_jl_objective_graphs(
    fig_path::String,
    obj_evol::Vector{Dict{String,Vector{Float64}}},
    time_limit,
)
    @assert endswith(fig_path, ".png")

    n_splits = length(obj_evol)
    end_time = (
        !isnothing(time_limit) ? time_limit :
        maximum([obj_evol[try_id]["time"][end] for split_id = 1:n_splits])
    )

    time = obj_evol[1]["time"]
    objective = obj_evol[1]["objective"]
    plot(
        time,
        objective,
        xlims = (0, end_time),
        title = "Best RSD_jl objective vs Time",
        xlabel = "Time (seconds)",
        ylabel = "Best objective",
        label = "split n°1",
        linetype = :steppost,
    )
    for split = 2:n_splits
        time = obj_evol[split]["time"]
        objective = obj_evol[split]["objective"]
        plot!(time, objective, label = "split n°$split", linetype = :steppost)
    end

    plot!(legend = :topright)
    savefig(fig_path)
end

function draw_SPLIT_objective_graph(
    fig_path::String,
    obj_evol::Vector{Dict{String,Vector{Float64}}},
    time_limit,
)
    @assert endswith(fig_path, ".png")

    n_tries = count(x -> !isempty(x["time"]) && !isempty(x["objective"]), obj_evol)
    end_time = (
        !isnothing(time_limit) ? time_limit :
        maximum([obj_evol[try_id]["time"][end] for try_id = 1:n_tries])
    )

    time = obj_evol[1]["time"]
    objective = obj_evol[1]["objective"]
    plot(
        time,
        objective,
        xlims = (0, end_time),
        title = "Best SPLIT objective vs Time",
        xlabel = "Time (seconds)",
        ylabel = "Best objective",
        label = "try n°1",
        linetype = :steppost,
    )
    for try_id = 2:n_tries
        time = obj_evol[try_id]["time"]
        objective = obj_evol[try_id]["objective"]
        plot!(time, objective, label = "try n°$try_id", linetype = :steppost)
    end

    plot!(legend = :topright)
    savefig(fig_path)
end


function draw_RSD_ijlm_objective_graphs(
    fig_path::String,
    obj_evol::Dict{String,Vector{Float64}},
    time_limit,
)
    @assert endswith(fig_path, ".png")

    end_time = (!isnothing(time_limit) ? time_limit : obj_evol["time"][end])

    time = obj_evol["time"]
    objective = obj_evol["objective"]
    plot(
        time,
        objective,
        xlims = (0, end_time),
        title = "Best RSD_ijlm objective vs Time",
        xlabel = "Time (seconds)",
        ylabel = "Best objective",
        linetype = :steppost,
    )

    savefig(fig_path)
end