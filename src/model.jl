# --- Compact model --- #
function declare_CM(I::Instance, model::Model)

    # --- Main decision variables --- #
    @variable(
        model,
        x[i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m; I.γ[i, j]],
        binary = true
    )

    # --- Student related constraints --- #
    # Student availability
    let
        sum_ids = Set{Tuple{Int,Int,Int}}()
        for i = 1:I.n_i, s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
            RHS = prod(I.θ[i, l-I.μ[s]:l+I.ν[s]-1])
            if !RHS
                valid_j = [j for j in I.J[s] if I.γ[i, j]]
                fix.(x[i, valid_j, l, 1:I.n_m], 0; force = true)
            else
                push!(sum_ids, (i, s, l))
            end
        end

        @constraint(
            model,
            student_availability[(i, s, l) in sum_ids],
            sum(x[i, j, l, m] for j in I.J[s] if I.γ[i, j] for m = 1:I.n_m; init = 0) <= 1
        )
    end

    # Student one exam 1
    @constraint(
        model,
        student_one_exam_1[i = 1:I.n_i, l = 1:I.n_l],
        sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for m = 1:I.n_m; init = 0) <= 1
    )

    # Student one exam 2
    let
        μ_max_stu = [maximum(I.μ[s] for s in I.S_stu[i]) for i = 1:I.n_i]
        ν_min_stu = [minimum(I.ν[s] for s in I.S_stu[i]) for i = 1:I.n_i]
        M = [
            ceil((I.ν[s] - 1 + I.τ_stu + μ_max_stu[i]) / ν_min_stu[i]) for s = 1:I.n_s,
            i = 1:I.n_i
        ]

        @constraint(
            model,
            student_one_exam_2[i = 1:I.n_i, s = 1:I.n_s, d = 1:I.n_d, l in I.L[d]],
            sum(
                x[i, k, l+t, m] for k = 1:I.n_j if I.γ[i, k] for
                t = 1:min(I.ν[s] - 1 + I.τ_stu + I.μ[I.groups[k].s], I.L[d][end] - l),
                m = 1:I.n_m;
                init = 0,
            ) <=
            M[s, i] * (
                1 - sum(
                    x[i, j, l, m_tilde] for j in I.J[s] if I.γ[i, j] for m_tilde = 1:I.n_m;
                    init = 0,
                )
            )
        )
    end

    # Student max exams
    @constraint(
        model,
        student_max_exams[i = 1:I.n_i, d = 1:I.n_d],
        sum(
            x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.L[d], m = 1:I.n_m;
            init = 0,
        ) <= I.ξ
    )

    # Student harmonious exams
    @variable(model, y[i = 1:I.n_i] >= 0)
    @constraint(
        model,
        student_harmonious_exams[i = 1:I.n_i, w = 1:I.n_w],
        sum(
            x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.Z[w], m = 1:I.n_m;
            init = 0,
        ) * [1, -1] .<= [ceil(I.ε[i] / I.n_w) + y[i], -floor(I.ε[i] / I.n_w) + y[i]]
    )

    # Student same class together
    is_jc_valid = [
        sum(I.γ[i, j] && (I.dataset["students"][i]["class_id"] == c) for i = 1:I.n_i) > 0 for j = 1:I.n_j, c = 1:I.n_c
    ]
    is_j_multi_class = [sum(is_jc_valid[j, :]) >= 2 for j = 1:I.n_j]

    # Student same class together 1
    @variable(
        model,
        R_tilde[
            j = 1:I.n_j,
            c = 1:I.n_c,
            d = 1:I.n_d;
            is_j_multi_class[j] && is_jc_valid[j, c],
        ] <= I.L[d][end]
    )
    @constraint(
        model,
        student_same_class_together_1[
            j in (j for j = 1:I.n_j if is_j_multi_class[j]),
            i in (i for i = 1:I.n_i if I.γ[i, j]),
            d = 1:I.n_d,
            l in I.L[d],
        ],
        l + (I.L[d][1] - l) * (1 - sum(x[i, j, l, m] for m = 1:I.n_m)) <=
        R_tilde[j, I.dataset["students"][i]["class_id"], d]
    )

    # Student same class together 2
    @variable(
        model,
        r_tilde[
            j = 1:I.n_j,
            c = 1:I.n_c,
            d = 1:I.n_d;
            is_j_multi_class[j] && is_jc_valid[j, c],
        ] >= I.L[d][1]
    )
    @constraint(
        model,
        student_same_class_together_2[
            j in (j for j = 1:I.n_j if is_j_multi_class[j]),
            i in (i for i = 1:I.n_i if I.γ[i, j]),
            d = 1:I.n_d,
            l in I.L[d],
        ],
        r_tilde[j, I.dataset["students"][i]["class_id"], d] <=
        l + (I.L[d][end] - l) * (1 - sum(x[i, j, l, m] for m = 1:I.n_m))
    )

    # Student same class together 3
    @constraint(
        model,
        student_same_class_together_3[
            j in (j for j = 1:I.n_j if is_j_multi_class[j]),
            c in (c for c = 1:I.n_c if is_jc_valid[j, c]),
            d = 1:I.n_d,
        ],
        r_tilde[j, c, d] <= R_tilde[j, c, d]
    )

    # --- Examiner related constraints --- #
    # Group availability
    let
        sum_ids = Set{Tuple{Int,Int}}()
        for s = 1:I.n_s, j in I.J[s], d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]

            one_alpha_null = !prod(I.α[e, l+t] for e in I.groups[j].e, t = -I.μ[s]:I.ν[s]-1)
            if one_alpha_null
                valid_i = [i for i = 1:I.n_i if I.γ[i, j]]
                fix.(x[valid_i, j, l, 1:I.n_m], 0; force = true)
            else
                push!(sum_ids, (j, l))
            end
        end
        @constraint(
            model,
            group_availability[(j, l) in sum_ids],
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) <= 1
        )
    end

    # Examiner obligation cancelation
    @variable(model, q[e = 1:I.n_e, P in I.U[e]]; binary = true)
    let ν_min_e = [minimum(I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        M(e, P) =
            length(P) * ceil(
                sum(I.μ[I.groups[j].s] + I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) /
                ν_min_e[e],
            )

        days_begginings = [I.L[d][1] for d = 1:I.n_d]
        @assert issorted(days_begginings)
        get_t_range(l, s) = begin
            d = searchsortedlast(days_begginings, l)
            return max(-I.μ[s], l - I.L[d][end]):min(I.ν[s] - 1, l - I.L[d][1])
        end
        left_sum(e, P) = sum(
            x[i, j, l-t, m] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j] for
            i = 1:I.n_i if I.γ[i, j] for l in P for m = 1:I.n_m,
            t in get_t_range(l, I.groups[j].s);
            init = 0,
        )

        @constraint(
            model,
            examiner_obligation_cancelation[e = 1:I.n_e, P in I.U[e]],
            prod(I.α[e, P]) * left_sum(e, P) <= M(e, P) * q[e, P]
        )
    end

    # Group one exam
    @constraint(
        model,
        group_one_exam[
            s in (s for s = 1:I.n_s if I.ν[s] > 1),
            j in I.J[s],
            d = 1:I.n_d,
            l in I.L[d][1:end-(I.ν[s]-1)],
        ],
        sum(
            x[i, j, l+t, m] for i = 1:I.n_i if I.γ[i, j] for t = 1:I.ν[s]-1, m = 1:I.n_m;
            init = 0,
        ) / I.η[s] <=
        1 -
        sum(
            x[i, j, l, m_tilde] for i = 1:I.n_i if I.γ[i, j] for m_tilde = 1:I.n_m;
            init = 0,
        ) / I.η[s]
    )

    # Examiner lunch break 1
    @variable(model, b[e = 1:I.n_e, l in vcat(I.V...)], binary = true)
    let
        μ_max_e = [maximum(I.μ[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        ν_max_e = [maximum(I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        ν_min_e = [minimum(I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        M(e) = ceil((μ_max_e[e] + ν_max_e[e] + I.τ_lun - 1) / ν_min_e[e]) + I.τ_lun

        @constraint(
            model,
            examiner_lunch_break_1[e = 1:I.n_e, d = 1:I.n_d, l in I.V[d]],
            sum(
                x[i, j, l+t, m] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j] for
                i = 1:I.n_i if I.γ[i, j] for t =
                    max(I.L[d][1] - l, -I.ν[I.groups[j].s] + 1):min(
                        I.L[d][end] - l,
                        I.μ[I.groups[j].s] + I.τ_lun - 1,
                    ), m = 1:I.n_m;
                init = 0,
            ) + sum(
                (l <= l_tilde <= min(I.L[d][end], l + I.τ_lun - 1)) * (1 - q[e, P]) for
                P in I.U[e] for l_tilde in P;
                init = 0,
            ) <= M(e) * (1 - b[e, l])
        )
    end

    # Examiner lunch break 2
    @constraint(
        model,
        examiner_lunch_break_2[e = 1:I.n_e, d = 1:I.n_d],
        sum(b[e, l] for l in I.V[d]; init = 0) >= 1
    )

    # Group switch break
    let
        M = [
            sum(
                ceil(
                    (I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s] + 1) /
                    I.ν[I.groups[k].s],
                ) for k = 1:I.n_j if k != j && I.σ[j, k];
                init = 0,
            ) for j = 1:I.n_j
        ]

        @constraint(
            model,
            group_switch_break[j = 1:I.n_j, d = 1:I.n_d, l in I.L[d]],
            sum(
                x[i, k, l+t, m] / I.η[I.groups[k].s] for k = 1:I.n_j if k != j && I.σ[j, k]
                for i = 1:I.n_i if I.γ[i, k] for t =
                    0:min(
                        I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s],
                        I.L[d][end] - l,
                    ) for m = 1:I.n_m;
                init = 0,
            ) <=
            M[j] * (
                1 -
                sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, k] for m = 1:I.n_m) /
                I.η[I.groups[j].s]
            )
        )
    end

    # Examiner max days 1
    @variable(model, v[e = 1:I.n_e, d = 1:I.n_d], binary = true)
    @constraint(
        model,
        examiner_max_days_1_and_max_exams[e = 1:I.n_e, d = 1:I.n_d],
        sum(
            x[i, j, l, m] for j = 1:I.n_j if I.λ[e, j] for i = 1:I.n_i if I.γ[i, j] for
            l in I.L[d], m = 1:I.n_m;
            init = 0,
        ) <= I.ζ[e] * v[e, d]
    )

    # Examiner max days 2 and 3
    @variable(model, w[e = 1:I.n_e] >= 0)
    @constraint(
        model,
        examiner_max_days_2[e = 1:I.n_e],
        (1 + w[e]) .* [-1, 1] .<= [-sum(v[e, d] for d = 1:I.n_d), I.κ[e]]
    )

    # Room switch break
    let
        M(s) = ceil((I.μ[s] + I.τ_room) / I.ν[s])

        @constraint(
            model,
            room_switch_break[j in 1:I.n_j, d = 1:I.n_d, l in I.L[d], m = 1:I.n_m],
            sum(
                x[i, j, l+I.ν[I.groups[j].s]+t, m_tilde] for
                m_tilde = 1:I.n_m if m_tilde != m for i = 1:I.n_i if I.γ[i, j] for t =
                    0:min(
                        I.L[d][end] - l - I.ν[I.groups[j].s],
                        I.τ_room + I.μ[I.groups[j].s] - 1,
                    );
                init = 0,
            ) / I.η[I.groups[j].s] <=
            M(I.groups[j].s) * (
                1 -
                sum(
                    x[i_prime, j, l, m] for i_prime = 1:I.n_i if I.γ[i_prime, j];
                    init = 0,
                ) / I.η[I.groups[j].s]
            )
        )
    end

    # Exam grouped 1
    @variable(model, R[e = 1:I.n_e, d = 1:I.n_d])
    @constraint(
        model,
        exam_grouped_1[j = 1:I.n_j, e in I.groups[j].e, d = 1:I.n_d, l in I.L[d]],
        R[e, d] >=
        l +
        (I.L[d][1] - l) * (
            1 -
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) /
            I.η[I.groups[j].s]
        )
    )

    # Exam grouped 2
    @variable(model, r[e = 1:I.n_e, d = 1:I.n_d])
    @constraint(
        model,
        exam_grouped_2[j = 1:I.n_j, e in I.groups[j].e, d = 1:I.n_d, l in I.L[d]],
        r[e, d] <=
        l +
        (I.L[d][end] - l) * (
            1 -
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m; init = 0) /
            I.η[I.groups[j].s]
        )
    )

    # Exam grouped 3
    @constraint(model, exam_grouped_3[e = 1:I.n_e, d = 1:I.n_d], r[e, d] <= R[e, d])


    # --- Room related constraints --- #
    # Room availability
    let
        sum_ids = Set{Tuple{Int,Int,Int}}()
        for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)], m = 1:I.n_m
            RHS = I.ψ[m, s] * prod(I.δ[m, l-I.μ[s]:l+I.ν[s]-1])

            if !RHS
                fix.(
                    [x[i, j, l, m] for i = 1:I.n_i, j in I.J[s] if I.γ[i, j]],
                    0;
                    force = true,
                )
            else
                push!(sum_ids, (s, l, m))
            end
        end

        @constraint(
            model,
            room_availability[(s, l, m) in sum_ids],
            sum(x[i, j, l, m] for i = 1:I.n_i, j in I.J[s] if I.γ[i, j]; init = 0) <=
            I.η[s]
        )
    end

    # Room group occupation
    let
        a(s, u) = I.ν[s] - 1 + I.τ_room + I.μ[u]
        M(s, u) = ceil((a(s, u) + 1) / I.ν[u])

        @constraint(
            model,
            room_group_occupation[
                j = 1:I.n_j,
                k in setdiff(1:I.n_j, [j]),
                d = 1:I.n_d,
                l in I.L[d],
                m = 1:I.n_m,
            ],
            sum(
                x[i, k, l+t, m] for i = 1:I.n_i if I.γ[i, k] for
                t = 0:min(I.L[d][end] - l, a(I.groups[j].s, I.groups[k].s));
                init = 0,
            ) / I.η[I.groups[k].s] <=
            M(I.groups[j].s, I.groups[k].s) * (
                1 -
                sum(x[i_prime, j, l, m] for i_prime = 1:I.n_i if I.γ[i_prime, j]) /
                I.η[I.groups[j].s];
                init = 0
            )
        )
    end

    # --- Exam related constraints --- #
    # Exam needed
    @constraint(
        model,
        exam_needed[j = 1:I.n_j, i in (i for i = 1:I.n_i if I.γ[i, j])],
        sum(x[i, j, l, m] for l = 1:I.n_l, m = 1:I.n_m; init = 0) == 1
    )

    # Exam student number
    @variable(model, p[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m], binary = true)
    @constraint(
        model,
        exam_student_number[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m],
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]; init = 0) ==
        I.η[I.groups[j].s] * p[j, l, m]
    )

    # Exam start and end
    fix.(
        [
            x[i, j, l, m] for i = 1:I.n_i, j = 1:I.n_j if I.γ[i, j] for d = 1:I.n_d for
            l in vcat(I.L[d][1:I.μ[I.groups[j].s]], I.L[d][end-I.ν[I.groups[j].s]-1:end]),
            m = 1:I.n_m
        ],
        0;
        force = true,
    )

    # Exam continuity 3
    @variable(model, z[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m] >= 0)

    # Exam continuity 1
    @variable(model, z_tilde[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m], binary = true)
    let M(j) = I.ρ[I.groups[j].s]
        @constraint(
            model,
            exam_continuity_1_1[
                j in 1:I.n_j,
                d = 1:I.n_d,
                l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
                m = 1:I.n_m,
            ],
            I.ρ[I.groups[j].s] - sum(
                x[i, j, l-t, m] for i = 1:I.n_i if I.γ[i, j] for
                t in I.ν[I.groups[j].s] * (1:I.ρ[I.groups[j].s]);
                init = 0,
            ) <= M(j) * (1 - z_tilde[j, l, m])
        )
    end
    @constraint(
        model,
        exam_continuity_1_2[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
            m = 1:I.n_m,
        ],
        sum(x[i, j, l-I.ν[I.groups[j].s], m] for i = 1:I.n_i if I.γ[i, j]; init = 0) /
        I.η[I.groups[j].s] <=
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]; init = 0) / I.η[I.groups[j].s] +
        z[j, l, m] +
        z_tilde[j, l, m]
    )

    # Exam continuity 2
    @constraint(
        model,
        exam_continuity_2[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ν[I.groups[j].s]:I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]],
            m = 1:I.n_m,
        ],
        sum(x[i, j, l-I.ν[I.groups[j].s], m] for i = 1:I.n_i if I.γ[i, j]; init = 0) <=
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]; init = 0) +
        I.η[I.groups[j].s] * z[j, l, m]
    )

    # Exam break min duration
    let
        M = [ceil(max(I.τ_seq, I.μ[s]) / I.ν[s]) for s = 1:I.n_s]

        @constraint(
            model,
            exam_break_min_duration[
                j = 1:I.n_j,
                d = 1:I.n_d,
                l in I.L[d][1+I.ν[I.groups[j].s]:end],
            ],
            sum(
                x[i, j, l+t, m] for i = 1:I.n_i if I.γ[i, j] for
                t = 0:min(I.L[d][end] - l, max(I.τ_seq, I.μ[I.groups[j].s]) - 1),
                m = 1:I.n_m;
                init = 0,
            ) / I.η[I.groups[j].s] <=
            M[I.groups[j].s] * (
                1 +
                sum(
                    x[i, j, l, m] - x[i, j, l-I.ν[I.groups[j].s], m] for
                    i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m
                ) / I.η[I.groups[j].s]
            )
        )
    end

    # Exam break series end
    @constraint(
        model,
        exam_break_series_end[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        sum(x[i, j, l, m] for i = 1:I.n_i, m = 1:I.n_m) / I.η[I.groups[j].s] <=
        I.ρ[I.groups[j].s] -
        sum(
            x[i, j, l-a*I.ν[I.groups[j].s], m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m,
            a = 1:I.ρ[I.groups[j].s];
            init = 0,
        ) / I.η[I.groups[j].s]
    )

    # --- Objective function --- #
    # Soft constraints penalty coefficients
    # Student harmonious exams
    y_coef = 30 * (I.n_w == 1 ? 0 : 1 / sum((1 - 1 / I.n_w) * I.ε))

    # Examiner availability
    q_coef = 80 / sum(length(P) for e = 1:I.n_e for P in I.U[e]; init = 0)
    !isfinite(q_coef) && (q_coef = 0)

    # Examiner max days
    is_expert(e) = (I.dataset["examiners"][e]["type"] == "expert")
    w_coef = 60 / sum(is_expert(e) * I.κ[e] for e = 1:I.n_e)

    # Exam continuity
    z_coef = 50 / sum(I.γ)

    # Exam early
    R_coef = 10 / (I.n_l / I.n_d * sum(I.κ))

    # Exam grouped
    Rr_coef = 50 / (I.n_l / I.n_d * sum(I.κ))

    # Student same class together
    group_κ = [minimum(I.κ[e] for e in I.groups[j].e) for j = 1:I.n_j]
    Rr_tilde_coef =
        30 / (
            I.n_l / I.n_d * sum(
                group_κ[j] * sum(is_jc_valid[j, :]) for j = 1:I.n_j if is_j_multi_class[j];
                init = 0,
            )
        )

    objective =
        y_coef * sum(y) +
        q_coef * sum(length(P) * q[e, P] for e = 1:I.n_e for P in I.U[e]; init = 0) +
        w_coef * sum(is_expert(e) * w[e] for e = 1:I.n_e) +
        z_coef * sum(z) +
        R_coef * sum(R[e, d] - I.L[d][1] for e = 1:I.n_e, d = 1:I.n_d) +
        Rr_coef * sum(R[e, d] - r[e, d] for e = 1:I.n_e, d = 1:I.n_d) +
        Rr_tilde_coef * sum(
            R_tilde[j, c, d] .- r_tilde[j, c, d] for j = 1:I.n_j if is_j_multi_class[j] for
            c = 1:I.n_c if is_jc_valid[j, c] for d = 1:I.n_d;
        )
    @objective(model, Min, objective)
end


# --- RSD models --- #
function declare_RSD_jl(I::Instance, model::Model)
    # --- Main decision variables --- #
    @variable(model, f[j = 1:I.n_j, l = 1:I.n_l], binary = true)


    # --- Examiner related constraints --- #
    # Group availability
    @variable(model, 0 <= q[e = 1:I.n_e, l = 1:I.n_l] <= 1)
    let
        M(j, s) = length(I.groups[j].e) * length(-I.μ[s]:I.ν[s]-1)

        sum_ids = Set{Tuple{Int,Int}}()
        for s = 1:I.n_s, j in I.J[s], d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]

            one_alpha_null = !prod(I.α[e, l+t] for e in I.groups[j].e, t = -I.μ[s]:I.ν[s]-1)
            if one_alpha_null
                fix(f[j, l], 0; force = true)
            else
                push!(sum_ids, (j, l))
            end
        end

        @constraint(model, group_availability[(j, l) in sum_ids], f[j, l] <= 1)
    end

    # Examiner obligation cancelation
    @variable(model, q[e = 1:I.n_e, P in I.U[e]]; binary = true)
    let ν_min_e = [minimum(I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        M(e, P) =
            length(P) * ceil(
                sum(I.μ[I.groups[j].s] + I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) /
                ν_min_e[e],
            )

        days_begginings = [I.L[d][1] for d = 1:I.n_d]
        @assert issorted(days_begginings)
        get_t_range(l, s) = begin
            d = searchsortedlast(days_begginings, l)
            return max(-I.μ[s], l - I.L[d][end]):min(I.ν[s] - 1, l - I.L[d][1])
        end
        left_sum(e, P) = sum(
            f[j, l-t] for j = 1:I.n_j if I.λ[e, j] for l in P for
            t in get_t_range(l, I.groups[j].s);
            init = 0,
        )

        @constraint(
            model,
            examiner_obligation_cancelation[e = 1:I.n_e, P in I.U[e]],
            prod(I.α[e, P]) * left_sum(e, P) <= M(e, P) * q[e, P]
        )
    end

    # Group one exam
    let
        M = 1
        @constraint(
            model,
            group_one_exam[
                s in (s for s = 1:I.n_s if I.ν[s] > 1),
                j in I.J[s],
                d = 1:I.n_d,
                l in I.L[d][1:end-(I.ν[s]-1)],
            ],
            sum(f[j, l+t] for t = 1:I.ν[s]-1) <= M * (1 - f[j, l])
        )
    end

    # Examiner lunch break 1
    @variable(model, b[e = 1:I.n_e, l in vcat(I.V...)], binary = true)
    let
        μ_max_e = [maximum(I.μ[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        ν_max_e = [maximum(I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        ν_min_e = [minimum(I.ν[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j]) for e = 1:I.n_e]
        M(e) = ceil((μ_max_e[e] + ν_max_e[e] + I.τ_lun - 1) / ν_min_e[e]) + I.τ_lun

        @constraint(
            model,
            examiner_lunch_break_1[e = 1:I.n_e, d = 1:I.n_d, l in I.V[d]],
            sum(
                f[j, l+t] for j = 1:I.n_e if I.λ[e, j] for t =
                    max(I.L[d][1] - l, -I.ν[I.groups[j].s] + 1):min(
                        I.L[d][end] - l,
                        I.μ[I.groups[j].s] + I.τ_lun - 1,
                    );
                init = 0,
            ) + sum(
                (l <= l_tilde <= min(I.L[d][end], l + I.τ_lun - 1)) * (1 - q[e, P]) for
                P in I.U[e] for l_tilde in P;
                init = 0,
            ) <= M(e) * (1 - b[e, l])
        )
    end

    # Examiner lunch break 2
    @constraint(
        model,
        examiner_lunch_break_2[e = 1:I.n_e, d = 1:I.n_d],
        sum(b[e, l] for l in I.V[d]; init = 0) >= 1
    )

    # Group switch break
    let
        M = [
            sum(
                ceil(
                    (I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s] + 1) /
                    I.ν[I.groups[k].s],
                ) for k = 1:I.n_j if k != j && I.σ[j, k];
                init = 0,
            ) for j = 1:I.n_j
        ]

        @constraint(
            model,
            group_switch_break[j = 1:I.n_j, d = 1:I.n_d, l in I.L[d]],
            sum(
                f[k, l+t] for k = 1:I.n_j if k != j && I.σ[j, k] for t =
                    0:min(
                        I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s],
                        I.L[d][end] - l,
                    );
                init = 0,
            ) <= M[j] * (1 - f[j, l])
        )
    end

    # Examiner max days 1 and max exams
    @variable(model, v[e = 1:I.n_e, d = 1:I.n_d], binary = true)
    let
        M(d) = length(I.L[d])
        @constraint(
            model,
            examiner_max_days_1_and_max_exams[d = 1:I.n_d, e = 1:I.n_e],
            sum(f[j, l] for j = 1:I.n_j if I.λ[e, j] for l in I.L[d]; init = 0) <=
            I.ζ[e] * v[e, d]
        )
    end

    # Examiner max days 2 and 3
    @variable(model, w[e = 1:I.n_e] >= 0)
    @constraint(
        model,
        examiner_max_days_2_1[e = 1:I.n_e],
        sum(v[e, d] for d = 1:I.n_d) <= 1 + w[e]
    )
    @constraint(model, examiner_max_days_2_2[e = 1:I.n_e], 1 + w[e] <= I.κ[e])

    # Exam grouped 1
    @variable(model, R[e = 1:I.n_e, d = 1:I.n_d])
    @constraint(
        model,
        exam_grouped_1[j = 1:I.n_j, e in I.groups[j].e, d = 1:I.n_d, l in I.L[d]],
        R[e, d] >= l + (I.L[d][1] - l) * (1 - f[j, l])
    )

    # Exam grouped 2
    @variable(model, r[e = 1:I.n_e, d = 1:I.n_d])
    @constraint(
        model,
        exam_grouped_2[j = 1:I.n_j, e in I.groups[j].e, d = 1:I.n_d, l in I.L[d]],
        r[e, d] <= l + (I.L[d][end] - l) * (1 - f[j, l])
    )

    # Exam grouped 3
    @constraint(model, exam_grouped_3[e = 1:I.n_e, d = 1:I.n_d], r[e, d] <= R[e, d])


    # --- Exam related constraints --- #
    # Exam start and end
    fix.(
        [
            f[j, l] for j = 1:I.n_j, d = 1:I.n_d for
            l in vcat(I.L[d][1:I.μ[I.groups[j].s]], I.L[d][end-I.ν[I.groups[j].s]-1:end])
        ],
        0;
        force = true,
    )

    # Exam continuity 3
    @variable(model, z[j = 1:I.n_j, l = 1:I.n_l] >= 0)

    # Exam continuity 1
    @variable(model, z_tilde[j = 1:I.n_j, l = 1:I.n_l], binary = true)
    @constraint(
        model,
        exam_continuity_1_1[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        sum(1 - f[j, l-t] for t in I.ν[I.groups[j].s] * (1:I.ρ[I.groups[j].s]); init = 0) <=
        I.ρ[I.groups[j].s] * (1 - z_tilde[j, l])
    )
    @constraint(
        model,
        exam_continuity_1_2[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        f[j, l-I.ν[I.groups[j].s]] <= f[j, l] + z[j, l] + z_tilde[j, l]
    )

    # Exam continuity 2
    @constraint(
        model,
        exam_continuity_2[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ν[I.groups[j].s]:I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]],
        ],
        f[j, l-I.ν[I.groups[j].s]] <= f[j, l] + z[j, l]
    )

    # Exam break min duration
    let
        M = [ceil(max(I.τ_seq, I.μ[s]) / I.ν[s]) for s = 1:I.n_s]

        @constraint(
            model,
            exam_break_min_duration[
                j = 1:I.n_j,
                d = 1:I.n_d,
                l in I.L[d][1+I.ν[I.groups[j].s]:end],
            ],
            sum(
                f[j, l+t] for
                t = 0:min(I.L[d][end] - l, max(I.τ_seq, I.μ[I.groups[j].s]) - 1);
                init = 0,
            ) <= M[I.groups[j].s] * (1 + f[j, l] - f[j, l-I.ν[I.groups[j].s]])
        )
    end

    # Exam break series end
    @constraint(
        model,
        exam_break_series_end[
            j = 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        f[j, l] <=
        I.ρ[I.groups[j].s] -
        sum(f[j, l-a*I.ν[I.groups[j].s]] for a = 1:I.ρ[I.groups[j].s]; init = 0)
    )


    # --- Room related constraints --- #
    # Room occupation 1
    @variable(model, h[j = 1:I.n_j, l = 1:I.n_l], binary = true)
    let
        M = [I.ν[s] + max(I.τ_seq, I.τ_room) - 1 + I.μ[s] + 1 for s = 1:I.n_s]

        @constraint(
            model,
            room_occupation_1[
                j = 1:I.n_j,
                d = 1:I.n_d,
                l in I.L[d][I.μ[I.groups[j].s]+1:end-I.ν[I.groups[j].s]],
            ],
            sum(
                1 - h[j, l+t] for t =
                    -I.μ[I.groups[j].s]:min(
                        I.L[d][end] - l,
                        I.ν[I.groups[j].s] + max(I.τ_seq, I.τ_room) - 1,
                    );
                init = 0,
            ) <= M[I.groups[j].s] * (1 - f[j, l])
        )
    end

    # Room occupation 2
    @constraint(
        model,
        room_occupation_2[(room_type, dict) in I.room_type_data, l = 1:I.n_l],
        sum(h[j, l] for s in dict["subjects"] for j in I.J[s]; init = 0) <=
        sum(I.δ[m, l] for m in dict["rooms"])
    )


    # --- Student related constraints --- #
    @variable(model, g[i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l; I.γ[i, j]], binary = true)

    # Subjects that student i has to take, classified by preparation and presentation time
    S_stu_ord = [Dict{Tuple{Int,Int},Vector{Int}}() for i = 1:I.n_i]
    for i = 1:I.n_i, j = 1:I.n_j
        if I.γ[i, j]
            s = I.groups[j].s
            if !haskey(S_stu_ord[i], (I.μ[s], I.ν[s]))
                S_stu_ord[i][(I.μ[s], I.ν[s])] = []
            end
            push!(S_stu_ord[i][(I.μ[s], I.ν[s])], s)
        end
    end

    # Student availability
    let
        sum_ids = Set{Tuple{Int,Int,Tuple{Int,Int}}}()
        for i = 1:I.n_i,
            ((mu, nu), value) in S_stu_ord[i],
            s in value,
            d = 1:I.n_d,
            l in I.L[d][1+mu:end-(nu-1)]

            RHS = prod(I.θ[i, l-mu:l+nu-1])
            if !RHS
                valid_j = [j for j in I.J[s] if I.γ[i, j]]
                fix.(g[i, valid_j, l], 0; force = true)
            else
                push!(sum_ids, (i, l, (mu, nu)))
            end
        end

        @constraint(
            model,
            student_availability[(i, l, key) in sum_ids],
            sum(
                g[i, j, l] for s in S_stu_ord[i][key] for j in I.J[s] if I.γ[i, j];
                init = 0,
            ) <= 1
        )
    end

    # Student one exam 1
    @constraint(
        model,
        student_one_exam_1[i = 1:I.n_i, l = 1:I.n_l],
        sum(g[i, j, l] for j = 1:I.n_j if I.γ[i, j]; init = 0) <= 1
    )


    # Student one exam 2
    let
        μ_max_stu =
            [maximum(I.μ[I.groups[j].s] for j = 1:I.n_j if I.γ[i, j]) for i = 1:I.n_i]
        ν_min_stu =
            [minimum(I.ν[I.groups[j].s] for j = 1:I.n_j if I.γ[i, j]) for i = 1:I.n_i]

        M(i, nu, d, l) =
            sum(I.γ[i, :]) *
            ceil((min(nu - 1 + I.τ_stu + μ_max_stu[i], I.L[d][end] - l)) / ν_min_stu[i])

        @constraint(
            model,
            student_one_exam_2[
                i = 1:I.n_i,
                ((mu, nu), valid_s) in S_stu_ord[i],
                d = 1:I.n_d,
                l in I.L[d],
            ],
            sum(
                g[i, k, l+t] for k = 1:I.n_j if I.γ[i, k] for
                t = 1:min(nu - 1 + I.τ_stu + I.μ[I.ν[I.groups[k].s]], I.L[d][end] - l);
                init = 0,
            ) <=
            M(i, nu, d, l) *
            (1 - sum(g[i, j, l] for s in valid_s for j in I.J[s] if I.γ[i, j]; init = 0))
        )
    end

    # Student max exams
    @constraint(
        model,
        student_max_exams[i = 1:I.n_i, d = 1:I.n_d],
        sum(g[i, j, l] for j = 1:I.n_j if I.γ[i, j] for l in I.L[d]; init = 0) <= I.ξ
    )

    # Exam needed
    @constraint(
        model,
        exam_needed[j = 1:I.n_j, i in (i for i = 1:I.n_i if I.γ[i, j])],
        sum(g[i, j, l] for l = 1:I.n_l) == 1
    )

    # Student hard constraints link
    @constraint(
        model,
        student_hard_constraints_link[j = 1:I.n_j, l = 1:I.n_l],
        sum(g[i, j, l] for i in (i for i = 1:I.n_i if I.γ[i, j]); init = 0) /
        I.η[I.groups[j].s] == f[j, l]
    )


    # --- Objective function --- #
    # Soft constraints penalty coefficients
    # Examiner availability
    q_coef = 80 / sum(length(P) for e = 1:I.n_e for P in I.U[e]; init = 0)
    !isfinite(q_coef) && (q_coef = 0)

    # Examiner max days
    is_expert(e) = (I.dataset["examiners"][e]["type"] == "expert")
    w_coef = 60 / sum(is_expert(e) * I.κ[e] for e = 1:I.n_e)

    # Exam continuity
    z_coef = 50 / sum(I.γ)

    # Exam early
    R_coef = 10 / (I.n_l / I.n_d * sum(I.κ))

    # Exam grouped
    Rr_coef = 50 / (I.n_l / I.n_d * sum(I.κ))

    objective =
        q_coef * sum(length(P) * q[e, P] for e = 1:I.n_e for P in I.U[e]; init = 0) +
        w_coef * sum(is_expert(e) * w[e] for e = 1:I.n_e) +
        z_coef * sum(z) +
        R_coef * sum(R[e, d] - I.L[d][1] for e = 1:I.n_e, d = 1:I.n_d) +
        Rr_coef * sum(R[e, d] - r[e, d] for e = 1:I.n_e, d = 1:I.n_d)
    @objective(model, Min, objective)
end

function declare_RSD_jl_split(SplitI::SplitInstance, model::Model)
    I = SplitI.I
    d_range = SplitI.day_range
    l_range = I.L[d_range[1]][1]:I.L[d_range[end]][end]
    valid_ij = SplitI.exams

    valid_i = Set{Int}()
    valid_j = Set{Int}()
    is_j_valid = zeros(Bool, I.n_j)
    is_ij_valid = zeros(Bool, I.n_i, I.n_j)
    valid_e = Set{Int}()
    for (i, j) in valid_ij
        push!(valid_i, i)

        push!(valid_j, j)
        is_j_valid[j] = true

        is_ij_valid[i, j] = true

        for e in I.groups[j].e
            push!(valid_e, e)
        end
    end
    is_P_valid(P) = (sum(l in l_range for l in P) > 0)

    # --- Main decision variables --- #
    @variable(model, f[j in valid_j, l = l_range], binary = true)


    # --- Examiner related constraints --- #
    # Group availability
    let
        M(j, s) = length(I.groups[j].e) * length(-I.μ[s]:I.ν[s]-1)

        sum_ids = Set{Tuple{Int,Int}}()
        for s = 1:I.n_s,
            j in (j for j in I.J[s] if is_j_valid[j]),
            d in d_range,
            l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]

            one_alpha_null = !prod(I.α[e, l+t] for e in I.groups[j].e, t = -I.μ[s]:I.ν[s]-1)
            if one_alpha_null
                fix(f[j, l], 0; force = true)
            else
                push!(sum_ids, (j, l))
            end
        end

        @constraint(model, group_availability[(j, l) in sum_ids], f[j, l] <= 1)
    end

    # Examiner obligation cancelation
    @variable(model, q[e in valid_e, P in I.U[e]; is_P_valid(P)], binary = true)
    let ν_min_e = [
            (e in valid_e ? minimum(I.ν[I.groups[j].s] for j in valid_j if I.λ[e, j]) : -1) for e = 1:I.n_e
        ]
        M(e, P) =
            length(P) * ceil(
                sum(I.μ[I.groups[j].s] + I.ν[I.groups[j].s] for j in valid_j if I.λ[e, j]) /
                ν_min_e[e],
            )

        days_begginings = [I.L[d][1] for d = 1:I.n_d]
        @assert issorted(days_begginings)
        get_t_range(l, s) = begin
            d = searchsortedlast(days_begginings, l)
            !(d in d_range) && return 0:-1
            return max(-I.μ[s], l - I.L[d][end]):min(I.ν[s] - 1, l - I.L[d][1])
        end
        left_sum(e, P) = sum(
            f[j, l-t] for j in valid_j if I.λ[e, j] for l in P for
            t in get_t_range(l, I.groups[j].s);
            init = 0,
        )

        @constraint(
            model,
            examiner_obligation_cancelation[
                e in valid_e,
                P in (P for P in I.U[e] if is_P_valid(P)),
            ],
            prod(I.α[e, P]) * left_sum(e, P) <= M(e, P) * q[e, P]
        )
    end

    # Group one exam
    let
        M = 1
        @constraint(
            model,
            group_one_exam[
                s in (s for s = 1:I.n_s if I.ν[s] > 1),
                j in (j for j in I.J[s] if is_j_valid[j]),
                d = d_range,
                l in I.L[d][1:end-(I.ν[s]-1)],
            ],
            sum(f[j, l+t] for t = 1:I.ν[s]-1) <= M * (1 - f[j, l])
        )
    end

    # Examiner lunch break 1
    @variable(model, b[e in valid_e, l in vcat(I.V[d_range]...)], binary = true)
    let
        μ_max_e = [
            (e in valid_e ? maximum(I.μ[I.groups[j].s] for j in valid_j if I.λ[e, j]) : -1) for e = 1:I.n_e
        ]
        ν_max_e = [
            (e in valid_e ? maximum(I.ν[I.groups[j].s] for j in valid_j if I.λ[e, j]) : -1) for e = 1:I.n_e
        ]
        ν_min_e = [
            (e in valid_e ? minimum(I.ν[I.groups[j].s] for j in valid_j if I.λ[e, j]) : -1) for e = 1:I.n_e
        ]
        M(e) = ceil((μ_max_e[e] + ν_max_e[e] + I.τ_lun - 1) / ν_min_e[e]) + I.τ_lun

        @constraint(
            model,
            examiner_lunch_break_1[e in valid_e, d = d_range, l in I.V[d]],
            sum(
                f[j, l+t] for j in valid_j if I.λ[e, j] for t =
                    max(I.L[d][1] - l, -I.ν[I.groups[j].s] + 1):min(
                        I.L[d][end] - l,
                        I.μ[I.groups[j].s] + I.τ_lun - 1,
                    );
                init = 0,
            ) + sum(
                (l <= l_tilde <= min(I.L[d][end], l + I.τ_lun - 1)) * (1 - q[e, P]) for
                P in I.U[e] if is_P_valid(P) for l_tilde in P;
                init = 0,
            ) <= M(e) * (1 - b[e, l])
        )
    end

    # Examiner lunch break 2
    @constraint(
        model,
        examiner_lunch_break_2[e in valid_e, d = d_range],
        sum(b[e, l] for l in I.V[d]; init = 0) >= 1
    )

    # Group switch break
    let
        M = [
            sum(
                ceil(
                    (I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s] + 1) /
                    I.ν[I.groups[k].s],
                ) for k in valid_j if k != j && I.σ[j, k];
                init = 0,
            ) for j = 1:I.n_j
        ]

        @constraint(
            model,
            group_switch_break[j in valid_j, d = d_range, l in I.L[d]],
            sum(
                f[k, l+t] for k in valid_j if k != j && I.σ[j, k] for t =
                    0:min(
                        I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s],
                        I.L[d][end] - l,
                    );
                init = 0,
            ) <= M[j] * (1 - f[j, l])
        )
    end

    # Examiner max days 1 and max exams
    @variable(model, v[e in valid_e, d = d_range], binary = true)
    let
        M(d) = length(I.L[d])
        @constraint(
            model,
            examiner_max_days_1_and_max_exams[d = d_range, e in valid_e],
            sum(f[j, l] for j in valid_j if I.λ[e, j] for l in I.L[d]; init = 0) <=
            I.ζ[e] * v[e, d]
        )
    end

    # Examiner max days 2 and 3
    @variable(model, w[e in valid_e] >= 0)
    @constraint(
        model,
        examiner_max_days_2_1[e in valid_e],
        sum(v[e, d] for d in d_range) <= 1 + w[e]
    )
    @constraint(model, examiner_max_days_2_2[e in valid_e], 1 + w[e] <= SplitI.κ[e])

    # Exam grouped 1
    @variable(model, R[e in valid_e, d = d_range])
    @constraint(
        model,
        exam_grouped_1[j in valid_j, e in I.groups[j].e, d = d_range, l in I.L[d]],
        R[e, d] >= l + (I.L[d][1] - l) * (1 - f[j, l])
    )

    # Exam grouped 2
    @variable(model, r[e in valid_e, d = d_range])
    @constraint(
        model,
        exam_grouped_2[j in valid_j, e in I.groups[j].e, d = d_range, l in I.L[d]],
        r[e, d] <= l + (I.L[d][end] - l) * (1 - f[j, l])
    )

    # Exam grouped 3
    @constraint(model, exam_grouped_3[e in valid_e, d in d_range], r[e, d] <= R[e, d])


    # --- Exam related constraints --- #
    # Exam start and end
    fix.(
        [
            f[j, l] for j in valid_j, d in d_range for
            l in vcat(I.L[d][1:I.μ[I.groups[j].s]], I.L[d][end-I.ν[I.groups[j].s]-1:end])
        ],
        0;
        force = true,
    )

    # Exam continuity 3
    @variable(model, z[j in valid_j, l = l_range] >= 0)

    # Exam continuity 1
    @variable(model, z_tilde[j in valid_j, l = l_range], binary = true)
    @constraint(
        model,
        exam_continuity_1_1[
            j in valid_j,
            d = d_range,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        sum(1 - f[j, l-t] for t in I.ν[I.groups[j].s] * (1:I.ρ[I.groups[j].s]); init = 0) <=
        I.ρ[I.groups[j].s] * (1 - z_tilde[j, l])
    )
    @constraint(
        model,
        exam_continuity_1_2[
            j in valid_j,
            d = d_range,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        f[j, l-I.ν[I.groups[j].s]] <= f[j, l] + z[j, l] + z_tilde[j, l]
    )

    # Exam continuity 2
    @constraint(
        model,
        exam_continuity_2[
            j in valid_j,
            d = d_range,
            l in I.L[d][1+I.ν[I.groups[j].s]:I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]],
        ],
        f[j, l-I.ν[I.groups[j].s]] <= f[j, l] + z[j, l]
    )

    # Exam break min duration
    let
        M = [ceil(max(I.τ_seq, I.μ[s]) / I.ν[s]) for s = 1:I.n_s]

        @constraint(
            model,
            exam_break_min_duration[
                j in valid_j,
                d in d_range,
                l in I.L[d][1+I.ν[I.groups[j].s]:end],
            ],
            sum(
                f[j, l+t] for
                t = 0:min(I.L[d][end] - l, max(I.τ_seq, I.μ[I.groups[j].s]) - 1);
                init = 0,
            ) <= M[I.groups[j].s] * (1 + f[j, l] - f[j, l-I.ν[I.groups[j].s]])
        )
    end

    # Exam break series end
    @constraint(
        model,
        exam_break_series_end[
            j in valid_j,
            d in d_range,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        f[j, l] <=
        I.ρ[I.groups[j].s] -
        sum(f[j, l-a*I.ν[I.groups[j].s]] for a = 1:I.ρ[I.groups[j].s]; init = 0)
    )


    # --- Room related constraints --- #
    # Room occupation 1
    @variable(model, h[j in valid_j, l = l_range], binary = true)
    let
        M = [I.ν[s] + max(I.τ_seq, I.τ_room) - 1 + I.μ[s] + 1 for s = 1:I.n_s]

        @constraint(
            model,
            room_occupation_1[
                j in valid_j,
                d = d_range,
                l in I.L[d][I.μ[I.groups[j].s]+1:end-I.ν[I.groups[j].s]],
            ],
            sum(
                1 - h[j, l+t] for t =
                    -I.μ[I.groups[j].s]:min(
                        I.L[d][end] - l,
                        I.ν[I.groups[j].s] + max(I.τ_seq, I.τ_room) - 1,
                    );
                init = 0,
            ) <= M[I.groups[j].s] * (1 - f[j, l])
        )
    end

    # Room occupation 2
    @constraint(
        model,
        room_occupation_2[(room_type, dict) in I.room_type_data, l = l_range],
        sum(h[j, l] for s in dict["subjects"] for j in I.J[s] if is_j_valid[j]; init = 0) <=
        sum(I.δ[m, l] for m in dict["rooms"])
    )


    # --- Student related constraints --- #
    @variable(
        model,
        g[i = 1:I.n_i, j = 1:I.n_j, l = l_range; is_ij_valid[i, j]],
        binary = true
    )

    # Subjects that student i has to take, classified by preparation and presentation time
    S_stu_ord = [Dict{Tuple{Int,Int},Vector{Int}}() for i = 1:I.n_i]
    for (i, j) in valid_ij
        s = I.groups[j].s
        if !haskey(S_stu_ord[i], (I.μ[s], I.ν[s]))
            S_stu_ord[i][(I.μ[s], I.ν[s])] = []
        end
        push!(S_stu_ord[i][(I.μ[s], I.ν[s])], s)
    end

    # Student availability
    let
        sum_ids = Set{Tuple{Int,Int,Tuple{Int,Int}}}()
        for i in valid_i,
            ((mu, nu), value) in S_stu_ord[i],
            s in value,
            d in d_range,
            l in I.L[d][1+mu:end-(nu-1)]

            RHS = prod(I.θ[i, l-mu:l+nu-1])
            if !RHS
                valid_j = [j for j in I.J[s] if is_ij_valid[i, j]]
                fix.(g[i, valid_j, l], 0; force = true)
            else
                push!(sum_ids, (i, l, (mu, nu)))
            end
        end

        @constraint(
            model,
            student_availability[(i, l, key) in sum_ids],
            sum(
                g[i, j, l] for s in S_stu_ord[i][key] for j in I.J[s] if is_ij_valid[i, j];
                init = 0,
            ) <= 1
        )
    end

    # Student one exam 1
    @constraint(
        model,
        student_one_exam_1[i in valid_i, l = l_range],
        sum(g[i, j, l] for j in valid_j if is_ij_valid[i, j]; init = 0) <= 1
    )


    # Student one exam 2
    let
        μ_max_stu = [
            maximum(
                vcat([I.μ[I.groups[j].s] for j in valid_j if is_ij_valid[i, j]], [-Inf]),
            ) for i = 1:I.n_i
        ]
        ν_min_stu = [
            minimum(
                vcat([I.ν[I.groups[j].s] for j in valid_j if is_ij_valid[i, j]], [Inf]),
            ) for i = 1:I.n_i
        ]

        M(i, nu, d, l) =
            sum(is_ij_valid[i, :]) *
            ceil((min(nu - 1 + I.τ_stu + μ_max_stu[i], I.L[d][end] - l)) / ν_min_stu[i])

        @constraint(
            model,
            student_one_exam_2[
                i in valid_i,
                ((mu, nu), valid_s) in S_stu_ord[i],
                d = d_range,
                l in I.L[d],
            ],
            sum(
                g[i, k, l+t] for k in valid_j if is_ij_valid[i, k] for
                t = 1:min(nu - 1 + I.τ_stu + I.μ[I.ν[I.groups[k].s]], I.L[d][end] - l);
                init = 0,
            ) <=
            M(i, nu, d, l) * (
                1 - sum(
                    g[i, j, l] for s in valid_s for j in I.J[s] if is_ij_valid[i, j];
                    init = 0,
                )
            )
        )
    end

    # Student max exams
    @constraint(
        model,
        student_max_exams[i in valid_i, d = d_range],
        sum(g[i, j, l] for j in valid_j if is_ij_valid[i, j] for l in I.L[d]; init = 0) <=
        I.ξ
    )

    # Exam needed
    @constraint(
        model,
        exam_needed[(i, j) in valid_ij],
        sum(g[i, j, l] for l in l_range) == 1
    )

    # Student hard constraints link
    @constraint(
        model,
        student_hard_constraints_link[j in valid_j, l = l_range],
        sum(g[i, j, l] for i in valid_i if is_ij_valid[i, j]; init = 0) /
        I.η[I.groups[j].s] == f[j, l]
    )


    # --- Objective function --- #
    # Soft constraints penalty coefficients
    # Examiner availability
    q_coef = 80 / sum(length(P) for e in valid_e for P in I.U[e] if is_P_valid(P); init = 0)
    !isfinite(q_coef) && (q_coef = 0)

    # Examiner max days
    is_expert(e) = (SplitI.I.dataset["examiners"][e]["type"] == "expert")
    w_coef = 60 / sum(is_expert(e) * SplitI.κ[e] for e in valid_e)

    # Exam continuity
    z_coef = 50 / length(valid_ij)

    # Exam early
    R_coef = 10 / (length(l_range) / length(d_range) * sum(SplitI.κ[e] for e in valid_e))

    # Exam grouped
    Rr_coef = 50 / (length(l_range) / length(d_range) * sum(SplitI.κ[e] for e in valid_e))

    objective =
        q_coef * sum(
            length(P) * q[e, P] for e in valid_e for P in I.U[e] if is_P_valid(P);
            init = 0,
        ) +
        w_coef * sum(is_expert(e) * w[e] for e in valid_e) +
        z_coef * sum(z) +
        R_coef * sum(R[e, d] - I.L[d][1] for e in valid_e, d in d_range) +
        Rr_coef * sum(R[e, d] - r[e, d] for e in valid_e, d in d_range)
    @objective(model, Min, objective)
end

function declare_RSD_jlm(I::Instance, f_values::Matrix{Bool}, model::Model)
    #=
    [input] I: instance
    [input] f_values: values of the variable f of a solved RSD_jl submodel
    [output] model: RSD_jlm submodel that has not been solved
    =#

    is_jl_valid = zeros(Bool, I.n_j, I.n_l)
    for j in axes(f_values)[1], l in axes(f_values)[2]
        if f_values[j, l]
            is_jl_valid[j, l] = true
        end
    end


    # --- Main decision variables --- #
    @variable(
        model,
        b[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m; is_jl_valid[j, l]],
        binary = true
    )


    # --- Constraints --- #
    # Group inside room
    @constraint(
        model,
        group_inside_room[l = 1:I.n_l, j in (j for j = 1:I.n_j if is_jl_valid[j, l])],
        sum(b[j, l, m] for m = 1:I.n_m) == 1
    )

    # Room availability
    let
        sum_ids = Set{Tuple{Int,Int,Int}}()
        for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)], m = 1:I.n_m
            RHS = I.ψ[m, s] * prod(I.δ[m, l-I.μ[s]:l+I.ν[s]-1])

            if !RHS
                valid_j = [j for j in I.J[s] if is_jl_valid[j, l]]
                fix.(b[valid_j, l, m], 0; force = true)
            else
                push!(sum_ids, (s, l, m))
            end
        end

        @constraint(
            model,
            room_availability[(s, l, m) in sum_ids],
            sum(b[j, l, m] for j in I.J[s] if is_jl_valid[j, l]; init = 0) <= 1
        )
    end

    # Room group occupation
    let
        a(s, u) = I.ν[s] - 1 + I.τ_room + I.μ[u]
        M(s, u) = ceil((a(s, u) + 1) / I.ν[u])

        @constraint(
            model,
            room_group_occupation[
                j = 1:I.n_j,
                d = 1:I.n_d,
                l in (l for l in I.L[d] if is_jl_valid[j, l]),
                k in (k for k = 1:I.n_j if k != j &&
                      sum(
                    is_jl_valid[k, l+t] for
                    t = 0:min(I.L[d][end] - l, a(I.groups[j].s, I.groups[k].s))
                ) > 0),
                m = 1:I.n_m,
            ],
            sum(
                b[k, l+t, m] for
                t = 0:min(I.L[d][end] - l, a(I.groups[j].s, I.groups[k].s)) if
                is_jl_valid[k, l+t];
                init = 0,
            ) <= M(I.groups[j].s, I.groups[k].s) * (1 - b[j, l, m])
        )
    end

    # Room switch break
    let
        M(s) = ceil(I.μ[s] + I.τ_room) / I.ν[s]

        @constraint(
            model,
            room_switch_break[
                j in 1:I.n_j,
                d = 1:I.n_d,
                l in (l for l in I.L[d] if is_jl_valid[j, l]),
                m = 1:I.n_m,
            ],
            sum(
                b[j, l+I.ν[I.groups[j].s]+t, m_tilde] for m_tilde = 1:I.n_m if m_tilde != m
                for t =
                    0:min(
                        I.L[d][end] - l - I.ν[I.groups[j].s],
                        I.τ_room + I.μ[I.groups[j].s] - 1,
                    ) if is_jl_valid[j, l+I.ν[I.groups[j].s]+t];
                init = 0,
            ) <= M(I.groups[j].s) * (1 - b[j, l, m])
        )
    end
end

function declare_RSD_ijlm(I::Instance, b_values::Array{Bool,3}, model::Model)
    #=
    [input] I: instance
    [input] b_values: values of the variable b in a solved RSD_jlm submodel
    [output] model: RSD_ijlm submodel that has not been solved
    =#

    # Valid indexes identification
    is_jlm_valid = zeros(Bool, I.n_j, I.n_l, I.n_m)
    for j in axes(b_values)[1], l in axes(b_values)[2], m in axes(b_values)[3]
        if b_values[j, l, m]
            is_jlm_valid[j, l, m] = true
        end
    end
    is_jl_valid = convert.(Bool, sum(is_jlm_valid, dims = 3))
    is_jd_valid = [sum(is_jl_valid[j, l] for l in I.L[d]) > 0 for j = 1:I.n_j, d = 1:I.n_d]

    is_ijlm_valid = zeros(Bool, I.n_i, I.n_j, I.n_l, I.n_m)
    for i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m
        is_ijlm_valid[i, j, l, m] = I.γ[i, j] && is_jlm_valid[j, l, m]
    end

    valid_jlm = Set{Tuple{Int,Int,Int}}([
        (j, l, m) for j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m if is_jlm_valid[j, l, m]
    ])


    # --- Main decision variables --- #
    @variable(
        model,
        x[i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m; is_ijlm_valid[i, j, l, m]],
        binary = true
    )

    # --- Constraints --- #
    # Students with groups
    @constraint(
        model,
        students_with_groups[(j, l, m) in valid_jlm],
        sum(x[i, j, l, m] for i = 1:I.n_i if is_ijlm_valid[i, j, l, m]; init = 0) ==
        I.η[I.groups[j].s]
    )

    # Subjects that student i has to take, classified by preparation and presentation time
    S_stu_ord = [Dict{Tuple{Int,Int},Vector{Int}}() for i = 1:I.n_i]
    for i = 1:I.n_i, j = 1:I.n_j
        if I.γ[i, j]
            s = I.groups[j].s
            if !haskey(S_stu_ord[i], (I.μ[s], I.ν[s]))
                S_stu_ord[i][(I.μ[s], I.ν[s])] = []
            end
            push!(S_stu_ord[i][(I.μ[s], I.ν[s])], s)
        end
    end

    # Student availability
    let
        sum_ids = Set{Tuple{Int,Int,Tuple{Int,Int}}}()
        for i = 1:I.n_i,
            ((mu, nu), value) in S_stu_ord[i],
            s in value,
            d = 1:I.n_d,
            l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]

            RHS = prod(I.θ[i, l-mu:l+nu-1])
            if !RHS
                valid_jm =
                    [(j, m) for j in I.J[s], m = 1:I.n_m if is_ijlm_valid[i, j, l, m]]
                fix.([x[i, j, l, m] for (j, m) in valid_jm], 0; force = true)
            else
                push!(sum_ids, (i, l, (mu, nu)))
            end
        end

        @constraint(
            model,
            student_availability[(i, l, key) in sum_ids],
            sum(
                x[i, j, l, m] for s in S_stu_ord[i][key] for
                j in I.J[s], m = 1:I.n_m if is_ijlm_valid[i, j, l, m];
                init = 0,
            ) <= 1
        )
    end

    # Student one exam 1
    @constraint(
        model,
        student_one_exam_1[i = 1:I.n_i, l = 1:I.n_l],
        sum(
            x[i, j, l, m] for j = 1:I.n_j, m = 1:I.n_m if is_ijlm_valid[i, j, l, m];
            init = 0,
        ) <= 1
    )

    # Student one exam 2
    let
        μ_max_stu = [
            maximum(vcat([I.μ[I.groups[j].s] for j = 1:I.n_j if I.γ[i, j]], [-Inf])) for
            i = 1:I.n_i
        ]
        ν_min_stu = [
            minimum(vcat([I.ν[I.groups[j].s] for j = 1:I.n_j if I.γ[i, j]], [Inf])) for
            i = 1:I.n_i
        ]

        M(i, nu, d, l) =
            sum(I.γ[i, :]) *
            ceil((min(nu - 1 + I.τ_stu + μ_max_stu[i], I.L[d][end] - l)) / ν_min_stu[i])

        @constraint(
            model,
            student_one_exam_2[
                i = 1:I.n_i,
                ((mu, nu), valid_s) in S_stu_ord[i],
                d = 1:I.n_d,
                l in I.L[d],
            ],
            sum(
                x[i, k, l+t, m] for k = 1:I.n_j if I.γ[i, k] for
                t = 1:min(nu - 1 + I.τ_stu + I.μ[I.ν[I.groups[k].s]], I.L[d][end] - l),
                m = 1:I.n_m if is_ijlm_valid[i, k, l+t, m];
                init = 0,
            ) <=
            M(i, nu, d, l) * (
                1 - sum(
                    x[i, j, l, m] for s in valid_s for j in I.J[s] if I.γ[i, j] for
                    m = 1:I.n_m if is_ijlm_valid[i, j, l, m];
                    init = 0,
                )
            )
        )
    end

    # Student max exams
    @constraint(
        model,
        student_max_exams[i = 1:I.n_i, d = 1:I.n_d],
        sum(
            x[i, j, l, m] for
            j = 1:I.n_j, l in I.L[d], m = 1:I.n_m if is_ijlm_valid[i, j, l, m];
            init = 0,
        ) <= I.ξ
    )

    # Student harmonious exams
    @variable(model, y[i = 1:I.n_i] >= 0)
    @constraint(
        model,
        student_harmonious_exams[i = 1:I.n_i, w = 1:I.n_w],
        sum(
            x[i, j, l, m] for
            j = 1:I.n_j, l in I.Z[w], m = 1:I.n_m if is_ijlm_valid[i, j, l, m];
            init = 0,
        ) * [1, -1] .<= [ceil(I.ε[i] / I.n_w) + y[i], -floor(I.ε[i] / I.n_w) + y[i]]
    )

    # Student same class together
    is_jc_valid = [
        sum(I.γ[i, j] && (I.dataset["students"][i]["class_id"] == c) for i = 1:I.n_i) > 0 for j = 1:I.n_j, c = 1:I.n_c
    ]
    is_j_multi_class = [sum(is_jc_valid[j, :]) >= 2 for j = 1:I.n_j]

    # Student same class together 1
    @variable(
        model,
        R_tilde[
            j = 1:I.n_j,
            c = 1:I.n_c,
            d = 1:I.n_d;
            is_jd_valid[j, d] && is_j_multi_class[j] && is_jc_valid[j, c],
        ] <= I.L[d][end]
    )
    @constraint(
        model,
        student_same_class_together_1[
            j in (j for j = 1:I.n_j if is_j_multi_class[j]),
            i in (i for i = 1:I.n_i if I.γ[i, j]),
            d in (d for d = 1:I.n_d if is_jd_valid[j, d]),
            l in (l for l in I.L[d] if is_jl_valid[j, l]),
        ],
        l +
        (I.L[d][1] - l) *
        (1 - sum(x[i, j, l, m] for m = 1:I.n_m if is_ijlm_valid[i, j, l, m]; init = 0)) <=
        R_tilde[j, I.dataset["students"][i]["class_id"], d]
    )

    # Student same class together 2
    @variable(
        model,
        r_tilde[
            j = 1:I.n_j,
            c = 1:I.n_c,
            d = 1:I.n_d;
            is_jd_valid[j, d] && is_j_multi_class[j] && is_jc_valid[j, c],
        ] >= I.L[d][1]
    )
    @constraint(
        model,
        student_same_class_together_2[
            j in (j for j = 1:I.n_j if is_j_multi_class[j]),
            i in (i for i = 1:I.n_i if I.γ[i, j]),
            d in (d for d = 1:I.n_d if is_jd_valid[j, d]),
            l in (l for l in I.L[d] if is_jl_valid[j, l]),
        ],
        r_tilde[j, I.dataset["students"][i]["class_id"], d] <=
        l +
        (I.L[d][end] - l) *
        (1 - sum(x[i, j, l, m] for m = 1:I.n_m if is_ijlm_valid[i, j, l, m]; init = 0))
    )

    # Student same class together 3
    @constraint(
        model,
        student_same_class_together_3[
            j in (j for j = 1:I.n_j if is_j_multi_class[j]),
            c in (c for c = 1:I.n_c if is_jc_valid[j, c]),
            d in (d for d = 1:I.n_d if is_jd_valid[j, d]),
        ],
        r_tilde[j, c, d] <= R_tilde[j, c, d]
    )


    # --- Exam related constraints --- #
    # Exam needed
    @constraint(
        model,
        exam_needed[j = 1:I.n_j, i in (i for i = 1:I.n_i if I.γ[i, j])],
        sum(
            x[i, j, l, m] for l = 1:I.n_l, m = 1:I.n_m if is_ijlm_valid[i, j, l, m];
            init = 0,
        ) == 1
    )


    # --- Objective function --- #
    # Soft constraints penalty coefficients
    y_coef = 30 * (I.n_w == 1 ? 0 : 1 / sum((1 - 1 / I.n_w) * I.ε)) # student availability

    # Student same class together
    group_κ = [minimum(I.κ[e] for e in I.groups[j].e) for j = 1:I.n_j]
    Rr_tilde_coef =
        30 / (
            I.n_l / I.n_d * sum(
                group_κ[j] * sum(is_jc_valid[j, :]) for j = 1:I.n_j if is_j_multi_class[j];
                init = 0,
            )
        )

    objective =
        y_coef * sum(y) +
        Rr_tilde_coef * sum(
            R_tilde[j, c, d] .- r_tilde[j, c, d] for j = 1:I.n_j if is_j_multi_class[j] for
            c = 1:I.n_c if is_jc_valid[j, c] for d = 1:I.n_d if is_jd_valid[j, d];
            init = 0,
        )
    @objective(model, Min, objective)
end

# --- SPLIT model --- #
function declare_splitting_MILP(
    I::Instance,
    n_splits::Int,
    fill_rate::Float64,
    exams::Vector{Tuple{Int,Int}},
    days_split::Vector{UnitRange{Int}},
    model::Model,
)
    # --- Main decision variables --- #
    @variable(model, y[exam in exams, d = 1:I.n_d], binary = true)

    # --- Constraints --- #
    # Exam needed
    @constraint(model, exam_needed[exam in exams], sum(y[exam, d] for d = 1:I.n_d) == 1)

    # Group enough time
    let exam_length(s) = (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]

        function helper_group_available_time(j, d)
            # Count the timeslots were exams can be scheduled
            s = I.groups[j].s
            group_alpha = [prod(I.α[e, l] for e in I.groups[j].e) for l in I.L[d]]
            group_nb_timeslots_avail = 0
            prev_l_loc = 0
            for (l_loc, val) in enumerate(group_alpha)
                val && continue
                time_in_bloc = l_loc - prev_l_loc - 1 + I.τ_seq
                group_nb_timeslots_avail +=
                    time_in_bloc - (time_in_bloc % (exam_length(s) * I.η[s]))
                prev_l_loc = l_loc

            end
            time_in_bloc = length(I.L[d]) - prev_l_loc + I.τ_seq
            group_nb_timeslots_avail +=
                time_in_bloc - (time_in_bloc % (exam_length(s) * I.η[s]))

            return fill_rate * group_nb_timeslots_avail
        end

        @constraint(
            model,
            group_enough_time[j = 1:I.n_j, d = 1:I.n_d],
            sum(
                y[exam, d] * exam_length(I.groups[exam[2]].s) for
                exam in exams if j == exam[2];
                init = 0,
            ) <= helper_group_available_time(j, d)
        )
    end

    # Examiner enough time
    @variable(model, v[j = 1:I.n_j, d = 1:I.n_d], binary = true) # j has an exam on d implies v[j, d] == 1
    @constraint(
        model,
        group_has_exam[j = 1:I.n_j, d = 1:I.n_d],
        sum(y[exam, d] for exam in exams if exam[2] == j; init = 0) <=
        sum(I.γ[:, j]) * v[j, d]
    )
    @variable(model, t[e = 1:I.n_e, P in I.U[e]], binary = true)
    let exam_length(s) = (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]
        @constraint(
            model,
            examiner_enough_time[e = 1:I.n_e, d = 1:I.n_d],
            sum(
                y[exam, d] * exam_length(I.groups[exam[2]].s) for
                exam in exams if I.λ[e, exam[2]];
                init = 0,
            ) + I.τ_swi * (sum(v[j, d] for j = 1:I.n_j if I.λ[e, j]) - 1) <=
            fill_rate * (
                sum(I.α[e, l] for l in I.L[d]) + sum(
                    prod(I.α[e, l] for l in P) *
                    sum(I.L[d][1] <= l <= I.L[d][end] for l in P) *
                    (t[e, P] - 1) for P in I.U[e];
                    init = 0,
                )
            )
        )
    end

    # Examiner max exams
    @variable(model, z[e = 1:I.n_e, d = 1:I.n_d], binary = true)
    @constraint(
        model,
        examiner_max_exams[e = 1:I.n_e, d = 1:I.n_d],
        sum(
            y[exam, d] / I.η[I.groups[exam[2]].s] for
            exam in exams if e in I.groups[exam[2]].e;
            init = 0,
        ) <= I.ζ[e] * z[e, d]
    )

    # Examiner max days
    @constraint(
        model,
        examiner_max_days[e = 1:I.n_e],
        sum(z[e, d] for d = 1:I.n_d) <= I.κ[e]
    )

    # Rooms enough time
    let exam_length(s) = (I.ν[s] + (I.τ_seq + I.μ[s]) / I.ρ[s]) / I.η[s]
        @constraint(
            model,
            rooms_enough_time[(room_type, dict) in I.room_type_data, d = 1:I.n_d],
            sum(
                y[exam, d] * exam_length(I.groups[exam[2]].s) for
                exam in exams if I.groups[exam[2]].s in dict["subjects"];
                init = 0,
            ) <= fill_rate * sum(I.δ[m, l] for l in I.L[d], m in dict["rooms"])
        )
    end

    # Feasible amount of students each day for exams with multiple simultaneous students
    @variable(model, r[j = 1:I.n_j, d = 1:I.n_d] >= 0, integer = true)
    @constraint(
        model,
        group_feasible_amount_students[j = 1:I.n_j, d = 1:I.n_d],
        sum(y[exam, d] for exam in exams if exam[2] == j; init = 0) ==
        r[j, d] * I.η[I.groups[j].s]
    )

    # Student enough time
    let exam_length(s) = I.ν[s] + I.μ[s] + I.τ_stu
        @constraint(
            model,
            student_enough_time[i = 1:I.n_i, d = 1:I.n_d],
            sum(
                y[exam, d] * exam_length(I.groups[exam[2]].s) for
                exam in exams if i == exam[1];
                init = 0,
            ) <= fill_rate * sum(I.θ[i, l] for l in I.L[d])
        )
    end

    # Student max exams
    @constraint(
        model,
        student_max_exams[i = 1:I.n_i, d = 1:I.n_d],
        sum(y[exam, d] for exam in exams if exam[1] == i; init = 0) <= I.ξ
    )

    # Harmonious exam distribution between splits
    @variable(model, p[split in 1:n_splits] >= 0)
    @constraint(
        model,
        split_harmonious_exams_1[split = 1:n_splits],
        p[split] >=
        sum(y[exam, d] for exam in exams, d in days_split[split]) -
        length(exams) * length(days_split[split]) / I.n_d
    )
    @constraint(
        model,
        split_harmonious_exams_2[split = 1:n_splits],
        p[split] >=
        length(exams) * length(days_split[split]) / I.n_d -
        sum(y[exam, d] for exam in exams, d in days_split[split])
    )

    # Student harmonious exams
    @variable(model, q[i = 1:I.n_i, split = 1:n_splits])
    @constraint(
        model,
        student_harmonious_exams_1[i = 1:I.n_i, split = 1:n_splits],
        q[i, split] >=
        sum(
            y[exam, d] for exam in exams if exam[1] == i for d in days_split[split];
            init = 0,
        ) - ceil(I.ε[i] * length(days_split[split]) / I.n_d)
    )
    @constraint(
        model,
        student_harmonious_exams_2[i = 1:I.n_i, split = 1:n_splits],
        q[i, split] >=
        floor(I.ε[i] * length(days_split[split]) / I.n_d) - sum(
            y[exam, d] for exam in exams if exam[1] == i for d in days_split[split];
            init = 0,
        )
    )


    # --- Objective --- #
    is_expert(e) = (I.dataset["examiners"][e]["type"] == "expert")
    z_coef = 60 / sum(is_expert(e) * I.κ[e] for e = 1:I.n_e) # examiner max days
    p_coef = 30 / length(exams)
    q_coef = 30 / sum(I.ε)
    t_coef = 80 / sum(length(P) for e = 1:I.n_e for P in I.U[e]; init = 0)
    !isfinite(t_coef) && (t_coef = 0)

    objective =
        z_coef * sum(is_expert(e) * sum(z[e, :]) for e = 1:I.n_e) +
        p_coef * sum(p) +
        q_coef * sum(q) +
        t_coef * sum(t)
    @objective(model, Min, objective)
end