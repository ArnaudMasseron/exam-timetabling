using JSON, XLSX, Plots

function write_solution_json(
    I::Instance,
    x_values::Array{Bool,4},
    unscheduled_exams_ids::Set{Tuple{Int,Int}},
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

        subject_name = I.dataset["subjects"][s]["acronym"]

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
    q = zeros(Bool, I.n_e, I.n_l)
    for j = 1:I.n_j, d = 1:I.n_d, l in I.L[d]
        LHS = sum(x[i, j, l, m] for i = 1:I.n_i, m = 1:I.n_m; init = 0)
        if LHS > 0
            s = I.groups[j].s
            for e in I.groups[j].e, t = max(I.L[d][1] - l, -I.μ[s]):I.ν[s]-1
                if !I.β[e, l+t]
                    q[e, l+t] = true
                end
            end
        end
    end

    # Group one block cancelation
    for e = 1:I.n_e, P in I.U[e]
        one_q_true = sum(q[e, P[a]] for a = 1:lastindex(P)-1; init = 0) > 0
        if one_q_true
            for a = 1:lastindex(P)-1
                q[e, P[a]] = true
            end
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
        exam_going_on = isapprox(
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) /
            I.η[I.groups[j].s],
            1,
            rtol = 0.01,
        )
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


    # --- Objective function --- #
    # Soft constraints penalty coefficients
    y_coef = 30 * (I.n_w == 1 ? 0 : 1 / sum((1 - 1 / I.n_w) * I.ε)) # student harmonious exams
    q_coef = 80 / sum(.!I.β) # examiner availability
    is_expert(e) = (I.dataset["examiners"][e]["type"] == "expert")
    w_coef = 60 / sum(is_expert(e) * I.κ[e] for e = 1:I.n_e) # examiner max days
    z_coef = 50 / sum(I.γ) # exam continuity
    R_coef = 10 / (I.n_l / I.n_d * sum(I.κ)) # exam grouped
    Rr_coef = 50 / (I.n_l / I.n_d * sum(I.κ)) # exam grouped

    detailed_objective = [
        y_coef * sum(y),
        q_coef * sum(q),
        w_coef * sum(is_expert(e) * w[e] for e = 1:I.n_e),
        z_coef * sum(z),
        R_coef * sum(R[e, d] - I.L[d][1] for e = 1:I.n_e, d = 1:I.n_d),
        Rr_coef * sum(R .- r),
    ]
    objective = sum(detailed_objective)

    # --- Sot constraint interbretable details --- #
    detailed_soft_constraints = Dict{String,Any}()

    detailed_soft_constraints["nb_non_harmonious_students"] = sum(y .> 0)

    classes_canceled_min = convert(Minute, sum(q) * I.Δ_l).value
    detailed_soft_constraints["nb_hours_cancelled"] =
        Hour(div(classes_canceled_min, 60)) + Minute(ceil(classes_canceled_min % 60))

    theoretical_min_days_needed = zeros(Int, I.n_e)
    for e = 1:I.n_e
        if !is_expert(e)
            continue
        end

        nb_exams_e = Int(
            ceil(
                sum(
                    I.γ[i, j] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j] for
                    i = 1:I.n_i
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
                            I.α[e, l_tilde] * !I.β[e, l_tilde] * (1 - q[e, l_tilde]) for
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
            sum(unwanted_breaks) / sum(has_exam) * Int(round(I.Δ_l / Minute(1)))
        detailed_soft_constraints["mean_examiner_unwanted_breaks"] =
            Hour(div(mean_unwanted_breaks_min, 60)) +
            Minute(ceil(mean_unwanted_breaks_min % 60))
    end

    return objective, detailed_objective, detailed_soft_constraints
end

function draw_objective_graphs(
    fig_path::String,
    objective_evolution::Vector{Dict{String,Vector{Float64}}},
    time_limit::Float64,
)
    @assert endswith(fig_path, ".png")
    n_splits = length(objective_evolution)

    plot(
        [],
        [],
        xlims = (0, time_limit),
        title = "Best RSD_jl objective vs Time",
        xlabel = "Time (seconds)",
        ylabel = "Best objective",
    )

    for split = 1:n_splits
        time = objective_evolution[split]["time"]
        objective = objective_evolution[split]["objective"]
        plot!(time, objective, label = "split n°$split", linetype = :steppost)
    end

    plot!(legend = :topright)
    savefig(fig_path)
end
