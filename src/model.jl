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
                valid_j = (j for j in I.J[s] if I.γ[i, j])
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
    # Room availability
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
    @constraint(
        model,
        exam_needed[j = 1:I.n_j, i in (i for i = 1:I.n_i if I.γ[i, j])],
        sum(x[i, j, l, m] for l = 1:I.n_l, m = 1:I.n_m) == 1
    )

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
    q_coef = 30 / (I.n_e * I.n_l)
    w_coef = 30 / I.n_j
    z_coef = 30 / (I.n_j * I.n_l * I.n_m)
    Rr_coef = 30 / (I.n_j * I.n_d)

    objective =
        y_coef * sum(y) +
        q_coef * sum(q) +
        w_coef * sum(w) +
        z_coef * sum(z) +
        Rr_coef * sum(R .- r)
    @objective(model, Min, objective)
end


# --- RSD models --- #
function declare_RSD_jl(I::Instance, model::Model)
    # --- Main decision variables --- #
    @variable(model, f[j = 1:I.n_j, l = 1:I.n_l], binary = true)


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
                fix(f[j, l], 0; force = true)
            else
                push!(sum_ids, (j, l))
            end
        end
        @constraint(
            model,
            group_availability[(j, l) in sum_ids],
            f[j, l] .<= [I.β[e, l] ? 1 : q[e, l] for e in I.groups[j].e]
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
        ],
        f[j, l+t] <= 1 - f[j, l]
    )

    # Examiner lunch break 1
    @variable(model, b[e = 1:I.n_e, l in vcat(I.V...)], binary = true)
    @constraint(
        model,
        examiner_lunch_break_1[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.V[d],
            t = max(I.L[d][1] - l, -I.ν[I.groups[j].s] + 1):min(
                I.L[d][end] - l,
                I.μ[I.groups[j].s] + I.τ_lun - 1,
            ),
        ],
        f[j, l+t] .<= 1 .- b[I.groups[j].e, l]
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
        f[j, l] + f[k, l+t] <= 1
    )

    # Examiner max exams
    @constraint(
        model,
        examiner_max_exams[e = 1:I.n_e, d = 1:I.n_d],
        sum(f[j, l] for j = 1:I.n_j if I.λ[e, j] for l in I.L[d]) <= I.ζ[e]
    )

    # Group max days 1
    @variable(model, v[j = 1:I.n_j, d = 1:I.n_d], binary = true)
    @constraint(
        model,
        group_max_days_1[d = 1:I.n_d, l in I.L[d], j = 1:I.n_j],
        f[j, l] <= v[j, d]
    )

    # Group max days 2 and 3
    @variable(model, w[j = 1:I.n_j] >= 0)
    @constraint(
        model,
        group_max_days_2[j = 1:I.n_j],
        (1 + w[j]) .* [-1, 1] .<= [-sum(v[j, d] for d = 1:I.n_d), I.κ[j]]
    )

    # Exam grouped
    @variable(model, r[j = 1:I.n_j, d = 1:I.n_d] >= I.L[d][1])
    @variable(model, R[j = 1:I.n_j, d = 1:I.n_d] <= I.L[d][end])
    @constraint(
        model,
        exam_grouped_1_and_2[j = 1:I.n_j, d = 1:I.n_d, l in I.L[d]],
        [r[j, d], -R[j, d]] .<=
        [l, -l] .+ [I.L[d][end] - l, -I.L[d][1] + l] * (1 - f[j, l])
    )
    @constraint(model, exam_grouped_1[j = 1:I.n_j, d = 1:I.n_d], r[j, d] <= R[j, d])


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
    @constraint(
        model,
        exam_continuity_1[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
        ],
        f[j, l-I.ν[I.groups[j].s]] .<=
        f[j, l] .+ z[j, l] .+
        [f[j, l-t] for t in I.ν[I.groups[j].s] * (1:I.ρ[I.groups[j].s])]
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

    # Exam break
    @constraint(
        model,
        exam_break[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d][1+I.ρ[I.groups[j].s]*I.ν[I.groups[j].s]:end],
            t = 0:min(I.L[d][end] - l, I.τ_seq + I.μ[I.groups[j].s]),
        ],
        f[j, l+t] <= sum(f[j, l-a*I.ν[I.groups[j].s]] for a = 1:I.ρ[I.groups[j].s])
    )


    # --- Room related constraints --- #
    # Room occupation 1
    @variable(model, h[j = 1:I.n_j, l = 1:I.n_l], binary = true)
    @constraint(
        model,
        room_occupation_1[
            s = 1:I.n_s,
            j in I.J[s],
            d = 1:I.n_d,
            l in I.L[d][I.μ[s]+1:end-I.ν[s]],
            t = -I.μ[s]:min(I.L[d][end] - l, I.ν[s] + max(I.τ_seq, I.τ_room) - 1),
        ],
        f[j, l] <= h[j, l+t]
    )

    # Room occupation 2
    @constraint(
        model,
        room_occupation_2[s = 1:I.n_s, l = 1:I.n_l],
        sum(h[j, l] for j in I.J[s]) <= sum(I.δ[:, l, s])
    )

    # Remove useless h
    fix.(
        [
            h[j, l] for j = 1:I.n_j, d = 1:I.n_d for
            l in vcat(I.L[d][1:I.μ[I.groups[j].s]], I.L[d][end-I.ν[I.groups[j].s]:end])
        ],
        0;
        force = true,
    )


    # --- Student related constraints --- #
    @variable(model, g[i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l; I.γ[i, j]], binary = true)

    # Student availability
    let
        sum_ids = Set{Tuple{Int,Int,Int}}()
        for i = 1:I.n_i, s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
            RHS = prod(I.θ[i, l-I.μ[s]:l+I.ν[s]-1])
            if !RHS
                valid_j = (j for j in I.J[s] if I.γ[i, j])
                fix.(g[i, valid_j, l], 0; force = true)
            else
                push!(sum_ids, (i, s, l))
            end
        end

        @constraint(
            model,
            student_availability[(i, s, l) in sum_ids],
            sum(g[i, j, l] for j in I.J[s] if I.γ[i, j]) <= 1
        )
    end

    # Student one exam 1
    @constraint(
        model,
        student_one_exam_1[i = 1:I.n_i, l = 1:I.n_l],
        sum(g[i, j, l] for j = 1:I.n_j if I.γ[i, j]) <= 1
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
        ],
        g[i, k, l+t] <= 1 - sum(g[i, j, l] for j in I.J[s] if I.γ[i, j])
    )

    # Student max exams
    @constraint(
        model,
        student_max_exams[i = 1:I.n_i, d = 1:I.n_d],
        sum(g[i, j, l] for j = 1:I.n_j if I.γ[i, j] for l in I.L[d]) <= I.ξ
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
        sum(g[i, j, l] for i in (i for i = 1:I.n_i if I.γ[i, j])) / I.η[I.groups[j].s] ==
        f[j, l]
    )


    # --- Objective function --- #
    q_coef = 30 / (I.n_e * I.n_l)
    w_coef = 30 / I.n_j
    z_coef = 30 / (I.n_j * I.n_l)
    Rr_coef = 30 / (I.n_j * I.n_d)

    objective = q_coef * sum(q) + w_coef * sum(w) + z_coef * sum(z) + Rr_coef * sum(R .- r)
    @objective(model, Min, objective)
end

function declare_RSD_jlm(I::Instance, model_jl::Model, model_jlm::Model)
    #=
    [input] I: instance
    [input] model_jl: RSD_jl submodel that has been solved
    [output] model_jlm: RSD_jlm submodel that has not been solved
    =#

    @assert has_values(model_jl) "The given RSD_jl submodel must have values"


    # --- Main decision variables --- #
    @variable(model_jlm, b[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m], binary = true)


    # --- Constraints --- #
    # Group inside room
    @constraint(
        model_jlm,
        group_inside_room[j = 1:I.n_j, l = 1:I.n_l],
        sum(b[j, l, m] for m = 1:I.n_m) == value(model_jl[:f][j, l])
    )

    # Room availability
    let
        sum_ids = Set{Tuple{Int,Int,Int}}()
        for s = 1:I.n_s, d = 1:I.n_d, l in I.L[d][1+I.μ[s]:end-(I.ν[s]-1)], m = 1:I.n_m
            RHS = prod(I.δ[m, l-I.μ[s]:l+I.ν[s]-1, s])

            if !RHS
                fix.(b[I.J[s], l, m], 0; force = true)
            else
                push!(sum_ids, (s, l, m))
            end
        end

        @constraint(
            model_jlm,
            room_availability[(s, l, m) in sum_ids],
            sum(b[j, l, m] for j in I.J[s]) <= 1
        )
    end

    # Room group occupation
    @constraint(
        model_jlm,
        room_group_occupation[
            j = 1:I.n_j,
            k in setdiff(1:I.n_j, [j]),
            d = 1:I.n_d,
            l in I.L[d],
            t = 0:min(
                I.L[d][end] - l,
                I.ν[I.groups[j].s] - 1 + I.τ_room + I.μ[I.groups[k].s],
            ),
            m = 1:I.n_m,
        ],
        b[k, l+t, m] <= 1 - b[j, l, m]
    )

    # Room switch break
    @constraint(
        model_jlm,
        room_switch_break[
            j in 1:I.n_j,
            d = 1:I.n_d,
            l in I.L[d],
            t = 0:min(I.L[d][end] - l - I.ν[I.groups[j].s], I.τ_room + I.μ[I.groups[j].s]),
            m = 1:I.n_m,
            m_tilde in setdiff(1:I.n_m, [m]),
        ],
        b[j, l+I.ν[I.groups[j].s]+t, m_tilde] <= 1 - b[j, l, m]
    )
end

function declare_RSD_ijlm(I::Instance, model_jlm::Model, model_ijlm::Model)
    #=
    [input] I: instance
    [input] model_jlm: RSD_jlm submodel that has been solved
    [output] model_ijlm: RSD_ijlm submodel that has not been solved
    =#

    @assert has_values(model_jlm) "The given RSD_jlm submodel must have values"


    # --- Main decision variables --- #
    @variable(
        model_ijlm,
        x[i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m; I.γ[i, j]],
        binary = true
    )


    # --- Constraints --- #
    # Students with groups
    @constraint(
        model_ijlm,
        students_with_groups[j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m],
        sum(x[i, j, l, m] for i = 1:I.n_i if I.γ[i, j]) ==
        I.η[I.groups[j].s] * value(model_jlm[:b][j, l, m])
    )

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
            model_ijlm,
            student_availability[(i, s, l) in sum_ids],
            sum(x[i, j, l, m] for j in I.J[s] if I.γ[i, j] for m = 1:I.n_m) <= 1
        )
    end

    # Student max exams
    @constraint(
        model_ijlm,
        student_max_exams[i = 1:I.n_i, d = 1:I.n_d],
        sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.L[d], m = 1:I.n_m) <= I.ξ
    )

    # Student harmonious exams
    @variable(model_ijlm, y[i = 1:I.n_i] >= 0)
    @constraint(
        model_ijlm,
        student_harmonious_exams[i = 1:I.n_i, w = 1:I.n_w],
        sum(x[i, j, l, m] for j = 1:I.n_j if I.γ[i, j] for l in I.Z[w], m = 1:I.n_m) *
        [1, -1] .<= [ceil(I.ε[i] / I.n_w) + y[i], -floor(I.ε[i] / I.n_w) + y[i]]
    )


    # --- Exam related constraints --- #
    # Exam needed
    @constraint(
        model_ijlm,
        exam_needed[j = 1:I.n_j, i in (i for i = 1:I.n_i if I.γ[i, j])],
        sum(x[i, j, l, m] for l = 1:I.n_l, m = 1:I.n_m) == 1
    )


    # Objective
    y_coef = 30 / I.n_i
    @objective(model_ijlm, Min, y_coef * sum(y))
end
