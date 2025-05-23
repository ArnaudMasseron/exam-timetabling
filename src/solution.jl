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

function is_solution_feasible(I::Instance, x::Array{Bool,4}; verbose::Bool = false)
    print_error(constraint_name::String) =
        (verbose ? println("Error in constraint " * constraint_name) : nothing)

    # --- Exam related constraints --- #
    # Exam needed
    for i = 1:I.n_i, j = 1:I.n_j
        LHS = sum(x[i, j, l, m] for l = 1:I.n_l, m = 1:I.n_m; init = 0)
        if LHS != Int(I.γ[i, j])
            print_error("exam needed (i=$i, j=$j)")
            return false
        end
    end

    # Exam student number
    for j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m
        LHS = sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]; init = 0)

        if !(LHS in [0, I.η[I.groups[j].s]])
            print_error("exam student number (j=$j, l=$l, m=$m)")
            return false
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
            print_error("exam start and end")
            return false
        end
    end

    # Exam break
    let
        M = [ceil((max(I.τ_seq, I.μ[s]) + 1) / I.ν[s]) for s = 1:I.n_s]

        for j = 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
            m = 1:I.n_m

            LHS =
                sum(
                    x[i, j, l+t, m] for i = 1:I.n_i if I.γ[i, j] for
                    t = 0:min(I.L[d][end] - l, max(I.τ_seq, I.μ[I.groups[j].s]));
                    init = 0,
                ) / I.η[I.groups[j].s]

            RHS =
                M[I.groups[j].s] * (
                    I.ρ[I.groups[j].s] -
                    sum(
                        x[i_prime, j, l-a*I.ν[I.groups[j].s], m_tilde] for
                        i_prime = 1:I.n_i if I.γ[i_prime, j] for m_tilde = 1:I.n_m,
                        a = 1:I.ρ[I.groups[j].s];
                        init = 0,
                    ) / I.η[I.groups[j].s]
                )

            if LHS > RHS
                print_error("exam break (j=$j, d=$d, l=$l, m=$m)")
                return false
            end
        end
    end

    # --- Student related constraints --- #
    # Student availability
    for s = 1:I.n_s, i = 1:I.n_i, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
        LHS = sum(x[i, j, l, m] for j in I.J[s] if I.γ[i, j] for m = 1:I.n_m; init = 0)
        RHS = prod(I.θ[i, l-I.μ[s]:l+I.ν[s]-1])

        if LHS > RHS
            print_error("student availability (s=$s, i=$i, d=$d, l=$l)")
            return false
        end
    end

    # Student one exam 1
    for i = 1:I.n_i, l = 1:I.n_l
        LHS = sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for m = 1:I.n_m; init = 0)

        if LHS > 1
            print_error("student one exam 1 (i=$i, l=$l)")
            return false
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
                print_error("student one exam 2 (i=$i, s=$s, d=$d, l=$l)")
                return false
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
            print_error("student max exams (i=$i, d=$d)")
            return false
        end
    end

    # --- Group related constraints --- #
    # Group availability
    for j = 1:I.n_j,
        d = 1:I.n_d,
        l in I.L[d][1+I.μ[I.groups[j].s]:end-(I.ν[I.groups[j].s]-1)]

        s = I.groups[j].s
        LHS = sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0)
        RHS = I.η[s] * prod(I.α[I.groups[j].e, l-I.μ[s]:l+I.ν[s]-1])

        if LHS > RHS
            print_error("group availaibility (j=$j, d=$d, l=$l)")
            return false
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
            print_error("group one exam (s=$s, j=$j, d=$d, l=$l)")
            return false
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
                    x[i, j, l+t, m] for i = 1:I.n_i if I.γ[i, j] for t =
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
            print_error("examiner lunch break (e=$e, d=$d)")
            return false
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
            print_error("group switch break (j=$j, k=$k, d=$d, l=$l, t=$t)")
            return false
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
            print_error("examiner max exams (e=$e, d=$d)")
            return false
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
            print_error("group max days (e=$e, d=$d)")
            return false
        end
    end

    # Room switch break
    let
        M(s) = ceil((I.μ[s] + I.τ_room + 1) / I.ν[s])

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
                print_error("room switch break (j=$j, d=$d, l=$l, m=$m)")
                return false
            end
        end
    end

    # --- Room related constraints --- #
    # Room availability
    for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)], m = 1:I.n_m
        LHS = sum(x[i, j, l, m] for i = 1:I.n_i, j in I.J[s] if I.γ[i, j]; init = 0)
        RHS = I.η[s] * I.ψ[m, s] * prod(I.δ[m, l-I.μ[s]:l+I.ν[s]-1])

        if LHS > RHS
            print_error("room availability (s=$s, d=$d, l=$l, m=$m)")
            return false
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
                print_error("room group occupation (j=$j, k=$k, d=$d, l=$l, m=$m)")
                return false
            end
        end
    end

    return true
end

function solution_cost(I::Instance, x::Array{Bool,4})
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
    for j = 1:I.n_j, l = 1:I.n_l
        LHS = sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0)
        if LHS > 0
            s = I.groups[j].s
            for e in I.groups[j].e, t = I.μ[s]:I.ν[s]-1
                if !I.β[e, l+t]
                    q[e, l+t] = true
                end
            end
        end
    end

    # Group one block cancelation
    for e = 1:I.n_e, P in I.U[e]
        one_q_true = prod(q[e, P[a]] for a = 1:lastindex(P)-1; init = true)
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
    r = [I.L[d][1] for e = 1:I.n_e, d = 1:I.n_d]
    for j = 1:I.n_j, e in I.groups[j].e, d = 1:I.n_d, l in I.L[d]
        exam_going_on = isapprox(
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) /
            I.η[I.groups[j].s],
            1,
            rtol = 0.01,
        )
        if exam_going_on
            R[e, d] = max(R[e, d], l)
            r[e, d] = min(r[e, d], l)
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
    q_coef = 80 / sum(I.β) # examiner availability
    is_expert(e) = (I.dataset["examiners"][e]["type"] == "expert")
    w_coef = 60 / sum((is_expert(e) ? 4 : 1) * I.κ[e] for e = 1:I.n_e) # examiner max days
    z_coef = 50 / sum(I.γ) # exam continuity
    R_coef = 10 / (I.n_l / I.n_d * sum(I.κ)) # exam grouped
    Rr_coef = 50 / (I.n_l / I.n_d * sum(I.κ)) # exam grouped

    detailed_objective = [
        y_coef * sum(y),
        q_coef * sum(q),
        w_coef * sum((is_expert(e) ? 4 : 1) * w[e] for e = 1:I.n_e),
        z_coef * sum(z),
        R_coef * sum(R[e, d] - I.L[d][1] for e = 1:I.n_e, d = 1:I.n_d),
        Rr_coef * sum(R[e, d] - r[e, d] for e = 1:I.n_e, d = 1:I.n_d),
    ]
    objective = sum(detailed_objective)

    # --- Sot constraint interbretable details --- #
    detailed_soft_constraints = Dict{String,Any}()

    detailed_soft_constraints["nb_non_harmonious_students"] = sum(y .> 0)

    classes_canceled_min = sum(q) * I.Δ_l.value
    detailed_soft_constraints["nb_hours_cancelled"] =
        Time(div(classes_canceled_min, 60), ceil(classes_canceled_min % 60))

    theoretical_min_days_needed = zeros(Int, I.n_e)
    for e = 1:I.n_e
        if !is_expert(e)
            continue
        end
        nb_exams_e =
            sum(I.γ[i, j] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j] for i = 1:I.n_i)
        min_days_1 = Int(ceil(nb_exams_e / I.ζ[e]))

        total_time_needed_e = 0
        for j = 1:I.n_j
            if I.λ[e, j]
                s = I.groups[j].s
                total_time_needed_e +=
                    (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s] * sum(I.γ[:, j])
            end
        end
        min_days_2 = Int(ceil(total_time_needed_e / (I.n_l / I.n_d - I.τ_lun)))

        theoretical_min_days_needed[e] = max(min_days_1, min_days_2)
    end
    detailed_soft_constraints["expert_mean_additional_days"] =
        sum(w[e] + 1 - theoretical_min_days_needed[e] for e = 1:I.n_e if is_expert(e)) /
        sum(is_expert.(1:I.n_e))

    detailed_soft_constraints["nb_unwanted_exam_discontinuities"] = sum(z)

    length_last_exam = zeros(Int, I.n_e, I.n_d)
    for e = 1:I.n_e, d = 1:I.n_d
        l = R[e, d]
        s = nothing
        for j = 1:I.n_j
            if I.λ[e, j] && sum(x[:, j, l, :]) > 0
                s = I.groups[j].s
                break
            end
        end
        length_last_exam[e, d] = (isnothing(s) ? 0 : I.ν[s])
    end
    mean_day_length_min =
        sum(R[e, d] - r[e, d] + length_last_exam[e, d] for e = 1:I.n_e, d = 1:I.n_d) /
        sum(1 for e = 1:I.n_e, d = 1:I.n_d if length_last_exam[e, d] > 0) * I.Δ_l.value
    detailed_soft_constraints["mean_examiner_day_length"] =
        Time(div(mean_day_length_min, 60), ceil(mean_day_length_min % 60))

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
