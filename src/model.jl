# Compact model
function declare_CM(model::Model, I::Instance)

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
            sum(x[i, j, l, m] for j in I.J[s] if I.γ[i, j] for m = 1:I.n_m) <= 1
        )
    end

    # Student one exam 1
    @constraint(
        model,
        student_one_exam_1[i = 1:I.n_i, l = 1:I.n_l],
        sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for m = 1:I.n_m) <= 1
    )

    # Student one exam 2
    @constraint(
        model,
        student_one_exam_2[
            u = 1:I.n_s,
            i = 1:I.n_i,
            k in (k for k in I.J[u] if I.γ[i, k]),
            s = 1:I.n_s,
            d = 1:I.n_d,
            l in I.L[d],
            t = 1:min(I.ν[s] - 1 + I.τ_stu + I.μ[u], I.L[d][end] - l),
            m = 1:I.n_m,
        ],
        x[i, k, l+t, m] <=
        1 - sum(x[i, j, l, m_tilde] for j in I.J[s] if I.γ[i, j] for m_tilde = 1:I.n_m)
    )

    # Student max exams
    @constraint(
        model,
        student_max_exams[i = 1:I.n_i, d = 1:I.n_d],
        sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.L[d], m = 1:I.n_m) <= I.ξ
    )

    # Student harmonious exams
    @variable(model, y[i = 1:I.n_i] >= 0)
    @constraint(
        model,
        student_harmonious_exams[i = 1:I.n_i, w = 1:I.n_w],
        sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.Z[w], m = 1:I.n_m) *
        [1, -1] .<= [ceil(I.ε[i] / I.n_w) + y[i], -floor(I.ε[i] / I.n_w) + y[i]]
    )


    # --- Group related constraints --- #
    # Group availability 1 and 2
    @variable(model, 0 <= q[e = 1:I.n_e, l = 1:I.n_l] <= 1)
    let
        sum_ids = Set{Tuple{Int,Int}}()
        for s = 1:I.n_s,
            j in I.J[s],
            e in I.groups[j].e,
            d = 1:I.n_d,
            l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]

            one_alpha_null = !prod(I.α[e, l-I.μ[s]:l+I.ν[s]-1])
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
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m) .<=
            I.η[I.groups[j].s] * [I.β[e, l] ? 1 : q[e, l] for e in I.groups[j].e]
        )
    end

    # Remove useless q
    fix.(q[.!I.α.||I.β], 0; force = true)

    # Group one block cancelation
    @constraint(
        model,
        group_one_block_cancelation[e = 1:I.n_e, P in I.U[e], a = 1:lastindex(P)-1],
        q[e, P[a]] == q[e, P[a+1]],
    )

    # Group one exam
    @constraint(
        model,
        group_one_exam[
            s in (s for s = 1:I.n_s if I.ν[s] > 1),
            j in I.J[s],
            t = 1:I.ν[s]-1,
            d = 1:I.n_d,
            l in I.L[d][1:end-(I.ν[s]-1)],
            i = 1:I.n_i,
            m = 1:I.n_m,
        ],
        x[i, j, l+t, m] <=
        1 -
        sum(x[i, j, l, m_tilde] for i = 1:I.n_i if I.γ[i, j] for m_tilde = 1:I.n_m) /
        I.η[s]
    )

    # Examiner lunch break 1
    @variable(model, b[e = 1:I.n_e, l in vcat(I.V...)], binary = true)
    @constraint(
        model,
        examiner_lunch_break_1[
            j in 1:I.n_j,
            i in (i for i = 1:I.n_i if I.γ[i, j]),
            d = 1:I.n_d,
            l in I.V[d],
            t = max(I.L[d][1] - l, -I.ν[I.groups[j].s] + 1):min(
                I.L[d][end] - l,
                I.μ[I.groups[j].s] + I.τ_lun - 1,
            ),
            m = 1:I.n_m,
        ],
        x[i, j, l+t, m] .<= 1 .- b[I.groups[j].e, l]
    )

    # Examiner lunch break 2
    @constraint(
        model,
        examiner_lunch_break_2[e = 1:I.n_e, d = 1:I.n_d],
        sum(b[e, l] for l in I.V[d]) >= 1
    )

    # Group switch break
    @constraint(
        model,
        group_switch_break[
            j = 1:I.n_j,
            k in (k for k = 1:I.n_j if k != j && I.σ[j, k]),
            d = 1:I.n_d,
            l in I.L[d][1:end-a],
            t = 0:min(
                I.ν[I.groups[j].s] - 1 + I.τ_swi + I.μ[I.groups[k].s],
                I.L[d][end] - l,
            ),
        ],
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m) /
        I.η[I.groups[j].s] +
        sum(x[i, k, l+t, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m) /
        I.η[I.groups[k].u] <= 1
    )

    # Examiner max exams
    @constraint(
        model,
        examiner_max_exams[e = 1:I.n_e, d = 1:I.n_d],
        sum(
            x[i, j, l, m] / I.η[I.groups[j].s] for j = 1:I.n_j if I.λ[e, j] for
            i = 1:I.n_i if I.γ[i, j] for l in I.L[d], m = 1:I.n_m
        ) <= I.ζ[e]
    )

    # Group max days 1
    @variable(model, v[j = 1:I.n_j, d = 1:I.n_d], binary = true)
    @constraint(
        model,
        group_max_days_1[
            i = 1:I.n_i,
            j in (j for j = 1:I.n_j if I.γ[i, j]),
            d = 1:I.n_d,
            l in I.L[d],
            m = 1:I.n_m,
        ],
        x[i, j, l, m] <= v[j, d]
    )

    # Group max days 2 and 3
    @variable(model, w[j = 1:I.n_j] >= 0)
    @constraint(
        model,
        group_max_days_2[j = 1:I.n_j],
        (1 + w[j]) .* [-1, 1] .<= [-sum(v[j, d] for d = 1:I.n_d), I.κ[j]]
    )

    # Room switch break
    @constraint(
        model,
        room_switch_break[
            j in 1:I.n_j,
            i = (i for i = 1:I.n_i if I.γ[i, j]),
            d = 1:I.n_d,
            l in I.L[d],
            t = 0:min(I.L[d][end] - l - I.ν[I.groups[j].s], I.τ_room + I.μ[I.groups[j].s]),
            m = 1:I.n_m,
            m_tilde in setdiff(1:I.n_m, [m]),
        ],
        x[i, j, l+I.ν[I.groups[j].s]+t, m_tilde] <=
        1 -
        sum(x[i_prime, j, l, m] for i_prime = 1:I.n_i if I.γ[i_prime, j]) /
        I.η[I.groups[j].s]
    )

    # Exam grouped
    @variable(model, r[j = 1:I.n_j, d = 1:I.n_d] >= I.L[d][1])
    @variable(model, R[j = 1:I.n_j, d = 1:I.n_d] <= I.L[d][end])
    @constraint(
        model,
        exam_grouped_1_and_2[j = 1:I.n_j, d = 1:I.n_d, l in I.L[d]],
        [r[j, d], -R[j, d]] .<=
        [l, -l] .+
        [I.L[d][end] - l, -I.L[d][1] + l] * (
            1 -
            sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j] for m = 1:I.n_m) /
            I.η[I.groups[j].s]
        )
    )
    @constraint(model, exam_grouped_1[j = 1:I.n_j, d = 1:I.n_d], r[j, d] <= R[j, d])


    # --- Room related constraints --- #
    let
        sum_ids = Set{Tuple{Int,Int,Int}}()
        for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)], m = 1:I.n_m
            RHS = prod(I.δ[m, l-I.μ[s]:l+I.ν[s]-1, s])

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
            sum(x[i, j, l, m] for i = 1:I.n_i, j in I.J[s] if I.γ[i, j]) <= I.η[s]
        )
    end

    # Room group occupation
    @constraint(
        model,
        room_group_occupation[
            j = 1:I.n_j,
            k in setdiff(1:I.n_j, [j]),
            i in (i for i = 1:I.n_i if I.γ[i, k]),
            d = 1:I.n_d,
            l in I.L[d],
            t = 0:min(
                I.L[d][end] - l,
                I.ν[I.groups[j].s] - 1 + I.τ_room + I.μ[I.groups[k].s],
            ),
            m = 1:I.n_m,
        ],
        x[i, k, l+t, m] <=
        1 -
        sum(x[i_prime, j, l, m] for i_prime = 1:I.n_i if I.γ[i_prime, j]) /
        I.η[I.groups[j].s]
    )

    # --- Exam related constraints --- #
    # Exam needed
    let
        sum_ids = Set{Tuple{Int,Int}}()
        for i = 1:I.n_i, j = 1:I.n_j
            if !I.γ[i, j]
                fix.(x[i, j, 1:I.n_l, 1:I.n_m], 0; force = true)
            else
                push!(sum_ids, (i, j))
            end
        end
        @constraint(
            model,
            exam_needed[(i, j) in sum_ids],
            sum(x[i, j, l, m] for l = 1:I.n_l, m = 1:I.n_m) == 1
        )
    end

    # Exam student number
    @variable(model, p[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m], binary = true)
    @constraint(
        model,
        exam_student_number[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m],
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]) == I.η[I.groups[j].s] * p[j, l, m]
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
    @constraint(
        model,
        exam_continuity_1[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
            m = 1:I.n_m,
        ],
        sum(x[i, j, l-I.ν[I.groups[j].s], m] for i = 1:I.n_i if I.γ[i, j]) .<=
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]) .+
        I.η[I.groups[j].s] * z[j, l, m] .+ [
            sum(x[i, j, l-t, m] for i = 1:I.n_i if I.γ[i, j]) for
            t in I.ν[I.groups[j].s] * (1:I.ρ[I.groups[j].s])
        ]
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
        sum(x[i, j, l-I.ν[I.groups[j].s], m] for i = 1:I.n_i if I.γ[i, j]) <=
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]) + I.η[I.groups[j].s] * z[j, l, m]
    )

    # Exam break
    @constraint(
        model,
        exam_break[
            j in 1:I.n_j,
            i in (i for i = 1:I.n_i if I.γ[i, j]),
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
            t = 0:min(I.L[d][end] - l, I.τ_seq + I.μ[I.groups[j].s]),
            m = 1:I.n_m,
        ],
        x[i, j, l+t, m] <=
        I.ρ[I.groups[j].s] -
        sum(
            x[i_prime, j, l-a*I.ν[I.groups[j].s], m_tilde] for
            i_prime = 1:I.n_i if I.γ[i_prime, j] for m_tilde = 1:I.n_m,
            a = 1:I.ρ[I.groups[j].s]
        ) / I.η[I.groups[j].s]
    )

    # --- Objective function --- #
    y_coef = 30 / I.n_i
    y_sum = zero(AffExpr)
    for i = 1:I.n_i
        add_to_expression!(y_sum, y[i])
    end

    q_coef = 30 / (I.n_e * I.n_l)
    q_sum = zero(AffExpr)
    for e = 1:I.n_e, l = 1:I.n_l
        add_to_expression!(q_sum, q[e, l])
    end

    w_coef = 30 / I.n_j
    w_sum = zero(AffExpr)
    for j = 1:I.n_j
        add_to_expression!(w_sum, w[j])
    end

    z_coef = 30 / (I.n_j * I.n_l * I.n_m)
    z_sum = zero(AffExpr)
    for j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m
        add_to_expression!(z_sum, z[j, l, m])
    end

    Rr_coef = 30 / (I.n_j * I.n_d)
    Rr_sum = zero(AffExpr)
    for j = 1:I.n_j, d = 1:I.n_d
        add_to_expression!(Rr_sum, R[j, d] - r[j, d])
    end

    objective =
        y_coef * y_sum + q_coef * q_sum + w_coef * w_sum + z_coef * z_sum + Rr_coef * Rr_sum

    @objective(model, Min, objective)
end


# DSE
function declare_RSD_jl(model::Model, I::Instance)
    # --- Main decision variables --- #
    @variable(model, f[j = 1:I.n_j, l = 1:I.n_l], binary = true)


    # --- Group related constraints --- #
    # Group availability 1 and 2
    @variable(model, 0 <= q[e = 1:I.n_e, l = 1:I.n_l] <= 1)
    for s = 1:I.n_s,
        j in I.J[s],
        e in I.groups[j].e,
        d = 1:I.n_d,
        l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]

        one_alpha_null = !prod(I.α[e, l-I.μ[s]:l+I.ν[s]-1])

        if one_alpha_null
            fix(f[j, l], 0; force = true)
        else
            LHS = f[j, l]
            RHS = I.α[e, l] * (I.β[e, l] + (1 - I.β[e, l]) * q[e, l])

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "group_availability (s=$s, j=$j, e=$e, d=$d, l=$l)")
        end
    end

    # Remove useless q
    for e = 1:I.n_e, l = 1:I.n_l
        if !I.α[e, l] || I.β[e, l]
            fix(q[e, l], 0; force = true)
        end
    end

    # Group one block cancelation
    for e = 1:I.n_e, P in I.U[e]
        for a = 1:lastindex(P)-1
            cons = @constraint(model, q[e, P[a]] == q[e, P[a+1]])
            set_name(cons, "group_one_block_cancelation (e=$e, l=$P[a])")
        end
    end

    # Group one exam
    for s = 1:I.n_s
        if I.ν[s] == 1
            continue
        end

        for j in I.J[s], d = 1:I.n_d, l in I.L[d][1:end-(I.ν[s]-1)], t = 1:I.ν[s]-1
            cons = @constraint(model, f[j, l+t] <= 1 - f[j, l])
            set_name(cons, "group_one_exam (s=$s, j=$j, d=$d, l=$l, t=$t)")
        end
    end

    # Examiner lunch break 1
    @variable(model, b[e = 1:I.n_e, l = 1:I.n_l], binary = true)
    for d = 1:I.n_d,
        l in I.V[d],
        s = 1:I.n_s,
        j in I.J[s],
        e in I.groups[j].e,
        t = max(I.L[d][1] - l, -I.ν[s] + 1):min(I.L[d][end] - l, I.μ[s] + I.τ_lun - 1)

        cons = @constraint(model, f[j, l+t] <= 1 - b[e, l])
        set_name(cons, "examiner_lunch_break_1 (d=$d, l=$l, s=$s, j=$j, e=$e, t=$t)")
    end

    # Examiner lunch break 2
    for e = 1:I.n_e, d = 1:I.n_d
        LHS = zero(AffExpr)
        for l in I.V[d]
            add_to_expression!(LHS, b[e, l])
        end

        cons = @constraint(model, LHS >= 1)
        set_name(cons, "examiner_lunch_break_2 (e=$e, d=$d)")
    end

    # Remove useless b
    for d = 1:I.n_d, l in I.L[d]
        if !(l in I.V[d])
            for e = 1:I.n_e
                fix(b[e, l], 0; force = true)
            end
        end
    end

    # Group switch break
    for j = 1:I.n_j, k = 1:I.n_j
        if j == k || !I.σ[j, k]
            continue
        end

        s = I.groups[j].s
        u = I.groups[k].s
        a = I.ν[s] - 1 + I.τ_swi + I.μ[u]

        for d = 1:I.n_d, l in I.L[d][1:end-a], t = 0:min(a, I.L[d][end] - l)
            LHS = f[j, l] + f[k, l+t]

            cons = @constraint(model, LHS <= 1)
            set_name(cons, "group_switch_break (j=$j, k=$k, d=$d, l=$l, t=$t)")
        end
    end

    # Examiner max exams
    for e = 1:I.n_e, d = 1:I.n_d
        LHS = zero(AffExpr)
        for s = 1:I.n_s, j in I.J[s]
            expr = zero(AffExpr)
            for l in I.L[d]
                add_to_expression!(expr, f[j, l])
            end
            add_to_expression!(LHS, I.λ[e, j] * expr)
        end

        cons = @constraint(model, LHS <= I.ζ[e])
        set_name(cons, "examiner_max_exams (e=$e, d=$d)")
    end

    # Group max days 1
    @variable(model, v[j = 1:I.n_j, d = 1:I.n_d], binary = true)
    for s = 1:I.n_s, j in I.J[s], d = 1:I.n_d, l in I.L[d]
        cons = @constraint(model, f[j, l] <= v[j, d])
        set_name(cons, "group_max_days_1 (s=$s, j=$j, d=$d, l=$l)")
    end

    # Group max days 2 and 3
    @variable(model, w[j = 1:I.n_j] >= 0)
    for j = 1:I.n_j
        expr = zero(AffExpr)
        for d = 1:I.n_d
            add_to_expression!(expr, v[j, d])
        end

        cons = @constraint(model, expr <= 1 + w[j])
        set_name(cons, "group_max_days_2_1 (j=$j)")

        cons = @constraint(model, 1 + w[j] <= I.κ[j])
        set_name(cons, "group_max_days_2_2 (j=$j)")
    end

    # Exam grouped
    @variable(model, r[j = 1:I.n_j, d = 1:I.n_d])
    @variable(model, R[j = 1:I.n_j, d = 1:I.n_d])
    for s = 1:I.n_s, j in I.J[s], d = 1:I.n_d
        cons = @constraint(model, r[j, d] >= I.L[d][1])
        set_name(cons, "exam_grouped_3_1 (s=$s, j=$j, d=$d)")

        cons = @constraint(model, r[j, d] <= R[j, d])
        set_name(cons, "exam_grouped_3_2 (s=$s, j=$j, d=$d)")

        cons = @constraint(model, R[j, d] <= I.L[d][end])
        set_name(cons, "exam_grouped_3_3 (s=$s, j=$j, d=$d)")

        for l in I.L[d]
            RHS = l + (I.L[d][end] - l) * (1 - f[j, l])
            cons = @constraint(model, r[j, d] <= RHS)
            set_name(cons, "exam_grouped_1 (s=$s, j=$j, d=$d, l=$l")

            RHS = l + (I.L[d][1] - l) * (1 - f[j, l])
            cons = @constraint(model, R[j, d] >= RHS)
            set_name(cons, "exam_grouped_2 (s=$s, j=$j, d=$d, l=$l)")
        end
    end


    # --- Exam related constraints --- #
    # Exam start
    for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1:I.μ[s]], j in I.J[s]
        fix(f[j, l], 0; force = true)
    end

    # Exam end
    for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][end-I.ν[s]-1:end], j in I.J[s]
        fix(f[j, l], 0; force = true)
    end

    # Exam continuity 3
    @variable(model, z[j = 1:I.n_j, l = 1:I.n_l] >= 0)

    # Exam continuity 1
    for s = 1:I.n_s,
        j in I.J[s],
        d = 1:I.n_d,
        l in I.L[d][1+I.ρ[s]*I.ν[s]:end],
        t in I.ν[s] * (1:I.ρ[s])

        LHS = f[j, l-I.ν[s]]
        RHS = f[j, l] + z[j, l] + f[j, l-t]

        cons = @constraint(model, LHS <= RHS)
        set_name(cons, "exam_continuity_1 (s=$s, j=$j, d=$d, l=$l, t=$t)")
    end

    # Exam continuity 2
    for s = 1:I.n_s, j in I.J[s], d = 1:I.n_d, l in I.L[d][1+I.ν[s]:I.ρ[s]*I.ν[s]]
        LHS = f[j, l-I.ν[s]]
        RHS = f[j, l] + z[j, l]

        cons = @constraint(model, LHS <= RHS)
        set_name(cons, "exam_continuity_2 (s=$s, j=$j, d=$d, l=$l)")
    end

    # Exam break
    for s = 1:I.n_s,
        j in I.J[s],
        d = 1:I.n_d,
        l in I.L[d][1+I.ρ[s]*I.ν[s]:end],
        t = 0:min(I.L[d][end] - l, I.τ_seq + I.μ[s])

        RHS = zero(AffExpr)
        for a = 1:I.ρ[s]
            add_to_expression!(RHS, f[j, l-a*I.ν[s]])
        end
        RHS = I.ρ[s] - RHS

        cons = @constraint(model, f[j, l+t] <= RHS)
        set_name(cons, "exam_break (s=$s, j=$j, d=$d, l=$l, t=$t)")
    end


    # --- Room related constraints --- #
    # Room occupation 1
    @variable(model, h[j = 1:I.n_j, l = 1:I.n_l], binary = true)
    for s = 1:I.n_s,
        j in I.J[s],
        d = 1:I.n_d,
        l in I.L[d][I.μ[s]+1:end-I.ν[s]],
        t = -I.μ[s]:min(I.L[d][end] - l, I.ν[s] + max(I.τ_seq, I.τ_room) - 1)

        cons = @constraint(model, f[j, l] <= h[j, l+t])
        set_name(cons, "room_occupation_1 (s=$s, j=$j, d=$d, l=$l, t=$t)")
    end

    # Room occupation 2
    for s = 1:I.n_s, l = 1:I.n_l
        LHS = zero(AffExpr)
        for j in I.J[s]
            add_to_expression!(LHS, h[j, l])
        end

        RHS = sum(I.δ[:, l, s])

        cons = @constraint(model, LHS <= RHS)
        set_name(cons, "room_occupation_2 (s=$s, l=$l)")
    end

    # Remove useless h
    for s = 1:I.n_s, j in I.J[s], d = 1:I.n_d
        for l in vcat(I.L[d][1:I.μ[s]], I.L[d][end-I.ν[s]:end])
            fix(h[j, l], 0; force = true)
        end
    end


    # --- Student related constraints --- #
    @variable(model, g[i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l], binary = true)

    # Student availability
    for i = 1:I.n_i, s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
        RHS = prod(I.θ[i, l-I.μ[s]:l+I.ν[s]-1])

        if !RHS
            # All the individual variables are set to 0 so that the presolve routine easily removes those variables
            for j in I.J[s]
                fix(g[i, j, l], 0; force = true)
            end
        else
            LHS = zero(AffExpr)
            for j in I.J[s]
                add_to_expression!(LHS, g[i, j, l])
            end

            cons = @constraint(model, LHS <= 1)
            set_name(cons, "student_availability (i=$i, s=$s, d=$d, l=$l)")
        end
    end

    # Student one exam 1
    for i = 1:I.n_i, l = 1:I.n_l
        LHS = zero(AffExpr)
        for j = 1:I.n_j
            add_to_expression!(LHS, g[i, j, l])
        end
        cons = @constraint(model, LHS <= 1)
        set_name(cons, "student_one_exam_1 (i=$i, l=$l)")
    end

    # Student one exam 2
    for s = 1:I.n_s, u = 1:I.n_s
        a = I.ν[s] - 1 + I.τ_stu + I.μ[u]

        for i = 1:I.n_i,
            k in I.J[u],
            d = 1:I.n_d,
            l in I.L[d],
            t = 1:min(a, I.L[d][end] - l)

            RHS = zero(AffExpr)
            for j in I.J[s]
                add_to_expression!(RHS, g[i, j, l])
            end
            RHS = 1 - RHS

            cons = @constraint(model, g[i, k, l+t] <= RHS)
            set_name(cons, "student_one_exam_2 (s=$s, u=$u, i=$i, k=$k, d=$d, l=$l, t=$t)")
        end
    end

    # Student max exams
    for i = 1:I.n_i, d = 1:I.n_d
        LHS = zero(AffExpr)
        for j = 1:I.n_j, l in I.L[d]
            add_to_expression!(LHS, g[i, j, l])
        end

        cons = @constraint(model, LHS <= I.ξ)
        set_name(cons, "student_max_exams (i=$i, d=$d)")
    end

    # Exam needed
    for i = 1:I.n_i, j = 1:I.n_j
        if !I.γ[i, j]
            for l = 1:I.n_l
                fix(g[i, j, l], 0; force = true)
            end
        else
            LHS = zero(AffExpr)
            for l = 1:I.n_l
                add_to_expression!(LHS, g[i, j, l])
            end

            cons = @constraint(model, LHS == 1)
            set_name(cons, "exam_needed (i=$i, j=$j)")
        end
    end

    # Student hard constraints link
    for s = 1:I.n_s, j in I.J[s], l = 1:I.n_l
        LHS = zero(AffExpr)
        for i = 1:I.n_i
            add_to_expression!(LHS, g[i, j, l])
        end
        LHS /= I.η[s]

        cons = @constraint(model, LHS == f[j, l])
        set_name(cons, "student_hard_constraints_link (s=$s, j=$j, l=$l)")
    end


    # --- Objective function --- #
    q_coef = 30 / (I.n_e * I.n_l)
    q_sum = zero(AffExpr)
    for e = 1:I.n_e, l = 1:I.n_l
        add_to_expression!(q_sum, q[e, l])
    end

    w_coef = 30 / I.n_j
    w_sum = zero(AffExpr)
    for j = 1:I.n_j
        add_to_expression!(w_sum, w[j])
    end

    z_coef = 30 / (I.n_j * I.n_l)
    z_sum = zero(AffExpr)
    for j = 1:I.n_j, l = 1:I.n_l
        add_to_expression!(z_sum, z[j, l])
    end

    Rr_coef = 30 / (I.n_j * I.n_d)
    Rr_sum = zero(AffExpr)
    for j = 1:I.n_j, d = 1:I.n_d
        add_to_expression!(Rr_sum, R[j, d] - r[j, d])
    end

    objective = q_coef * q_sum + w_coef * w_sum + z_coef * z_sum + Rr_coef * Rr_sum

    @objective(model, Min, objective)
end