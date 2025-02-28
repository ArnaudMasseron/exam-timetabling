function declare_CM(model::Model, I::Instance)

    # --- Main decision variables --- #
    @variable(model, x[i = 1:I.n_i, j = 1:I.n_j, l = 1:I.n_l, m = 1:I.n_m], binary=true)

    # --- Student related constraints --- #
    # Student availability
    for i=1:I.n_i, s=1:I.n_s, d=1:I.n_d, l=I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
        RHS = prod(I.θ[i, l-I.μ[s]:l+I.ν[s]-1])

        if !RHS
            # All the individual variables are set to 0 so that the presolve routine easily removes those variables
            for j=I.J[s], m=1:I.n_m
                fix(x[i,j,l,m], 0; force=true)
            end
        else
            LHS = zero(AffExpr)
            for j=I.J[s], m=1:I.n_m
                add_to_expression!(LHS, x[i, j, l, m])
            end

            cons = @constraint(model, LHS <= 1)
            set_name(cons, "student_availability (i=$i, s=$s, d=$d, l=$l)")
        end
    end

    # Student one exam 1
    for i=1:I.n_i, l=1:I.n_l
        LHS = zero(AffExpr)
        for j=1:I.n_j, m=1:I.n_m
            add_to_expression!(LHS, x[i, j, l, m])
        end
        cons = @constraint(model, LHS <= 1)
        set_name(cons, "student_one_exam_1 (i=$i, l=$l)")
    end

    # Student one exam 2
    for s=1:I.n_s, i=1:I.n_i 
        M = I.ν[s]-1 + I.τ_stu + maximum([I.μ[s_tilde] for s_tilde=I.S_stu[i]])

        for d=1:I.n_d, l=I.L[d]
            LHS = zero(AffExpr)
            for u=1:I.n_s
                a = I.ν[s]-1 + I.τ_stu + I.μ[u]
                for k=I.J[u], m=1:I.n_m, t=1:min(a, I.L[d][end]-l)
                    add_to_expression!(LHS, x[i, k, l+t, m])
                end
            end

            RHS = zero(AffExpr)
            for j=I.J[s], m=1:I.n_m
                add_to_expression!(LHS, x[i, j, l, m])
            end
            RHS = M * (1 - RHS)

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "student_one_exam_2 (i=$i, s=$s, d=$d, l=$l)")
        end
    end

    # Student max exams
    for i=1:I.n_i, d=1:I.n_d
        LHS = zero(AffExpr)
        for j=1:I.n_j, l=I.L[d], m=1:I.n_m
            add_to_expression!(LHS, x[i, j, l, m])
        end

        cons = @constraint(model, LHS <= I.ξ)
        set_name(cons, "student_max_exams (i=$i, d=$d)")
    end

    # Student harmonious exams
    @variable(model, y[i = 1:I.n_i] >= 0)
    for i=1:I.n_i, w=1:I.n_w
        LHS = zero(AffExpr)
        for j=1:I.n_j, l=I.Z[w], m=1:I.n_m
            add_to_expression!(LHS, x[i, j, l, m])
        end

        RHS = ceil(I.ε[i]/I.n_w) + y[i]
        @constraint(model, LHS <= RHS)

        RHS = floor(I.ε[i]/I.n_w) - y[i]
        cons = @constraint(model, LHS >= RHS)
        set_name(cons, "student_harmonious_exams (i=$i, w=$w)")
    end


    # --- Group related constraints --- #
    # Group availability 1 and 2
    @variable(model, 0 <= q[e=1:I.n_e, l=1:I.n_l] <= 1)
    for s=1:I.n_s, j=I.J[s], e=I.groups[j].e, d=1:I.n_d, l=I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
        one_alpha_null = !prod(I.α[e, l-I.μ[s]:l+I.ν[s]-1])
        
        if one_alpha_null
            for i=1:I.n_i, m=1:I.n_m
                fix(x[i,j,l,m], 0; force=true)
            end
        else
            LHS = zero(AffExpr)
            for i=1:I.n_i, m=1:I.n_m
                add_to_expression!(LHS, x[i, j, l, m])
            end

            RHS = I.η[s] * I.α[e, l] * (I.β[e, l] + (1 - I.β[e, l]) * q[e, l])

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "group_availability (s=$s, j=$j, e=$e, d=$d, l=$l)")
        end
    end

    # Remove useless q
    for e=1:I.n_e, l=1:I.n_l
        if !I.α[e, l] || I.β[e, l]
            cons = @constraint(model, q[e, l] == 0)
            set_name(cons, "remove_useless_q (e=$e, l=$l)")
        end
    end

    # Group one block cancelation
    for e=1:I.n_e, P=I.U[e]
        for a in 1:lastindex(P)-1
            cons = @constraint(model, q[e, P[a]] == q[e, P[a+1]])
            set_name(cons, "group_one_block_cancelation (e=$e, l=$P[a])")
        end
    end

    # Group one exam
    for s=1:I.n_s
        if I.ν[s] == 1
            continue
        end

        M = I.ν[s]-1
        for j=I.J[s], d=1:I.n_d, l=I.L[d][1:end-(I.ν[s]-1)]
            LHS = zero(AffExpr)
            for i=1:I.n_i, t=1:I.ν[s]-1, m=1:I.n_m
                add_to_expression!(LHS, x[i, j, l+t, m])
            end
            LHS /= I.η[s]

            RHS = zero(AffExpr)
            for i=1:I.n_i, m=1:I.n_m
                add_to_expression!(RHS, x[i, j, l, m])
            end
            RHS = M * (1 - RHS / I.η[s])

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "group_one_exam (s=$s, j=$j, d=$d, l=$l)")
        end
    end

    # Examiner lunch break 1
    @variable(model, t[e=1:I.n_e, 1:I.n_l], binary=true)
    for e=1:I.n_e, 
        M = sum(I.λ[e, :]) * (maximum([I.μ[s] for s=I.S_ex[e]]) + maximum([I.ν[s] for s=I.S_ex[e]]) + I.τ_lun - 1)

        for d=1:I.n_d, l=I.V[d]
            LHS = zero(AffExpr)
            for s=1:I.n_s
                expr1 = zero(AffExpr)
                for j=I.J[s]
                    expr2 = zero(AffExpr)
                    for i=1:I.n_i, m=1:I.n_m, t=-I.ν[s]+1:I.μ[s]+I.τ_lun-1
                        add_to_expression!(expr2, x[i, j, l+t, m])
                    end
                    add_to_expression!(expr1, I.λ[e, j] * expr2)
                end
                add_to_expression!(LHS, 1/I.η[s] * expr1)
            end

            RHS = M * (1 - t[e, l])

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "examiner_lunch_break_1 (e=$e, d=$d, l=$l)")
        end
    end

    # Examiner lunch break 2
    for e=1:I.n_e, d=1:I.n_d
        LHS = zero(AffExpr)
        for l=I.V[d]
            add_to_expression!(LHS, t[e, l])
        end

        cons = @constraint(model, LHS >= 1)
        set_name(cons, "examiner_lunch_break_2 (e=$e, d=$d)")
    end

    # Remove useless t
    for d=1:I.n_d, l=I.L[d]
        if !(l in I.V[d])
            for e=1:I.n_e
                cons = @constraint(model, t[e, l] == 0)
                set_name(cons, "remove_useless_t (d=$d, l=$l, e=$e)")
            end
        end
    end

    # Group switch break
    for j=1:I.n_j, k=j+1:I.n_j
        if !I.σ[j, k]
            continue
        end

        s = I.groups[j].s
        u = I.groups[k].s
        a = I.ν[s]-1 + I.τ_swi + I.μ[u]

        for d=1:I.n_d, l=I.L[d][1:end-a], t=0:min(a, I.L[d][end]-l)
            expr1 = zero(AffExpr)
            expr2 = zero(AffExpr)
            for i=1:I.n_i, m=1:I.n_m
                add_to_expression!(expr1, x[i, j, l, m])
                add_to_expression!(expr2, x[i, j, l+t, m])
            end
            LHS = 1/I.η[s] * expr1 + 1/I.η[u] * expr2

            RHS = 2 - I.σ[j, k]

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "group_switch_break (j=$j, k=$k, d=$d, l=$l, t=$t)")
        end
    end

    # Examiner max exams
    for e=1:I.n_e, d=1:I.n_d
        LHS = zero(AffExpr)
        for s=1:I.n_s
            expr1 = zero(AffExpr)
            for j=I.J[s]
                expr2 = zero(AffExpr)
                for i=1:I.n_i, l=I.L[d], m=1:I.n_m
                    add_to_expression!(expr2, x[i, j, l, m])
                end
                add_to_expression!(expr1, I.λ[e, j] * expr2)
            end
            add_to_expression!(LHS, expr1 / I.η[s])
        end

        cons = @constraint(model, LHS <= I.ζ[e])
        set_name(cons, "examiner_max_exams (e=$e, d=$d)")
    end

    # Group max days 1
    @variable(model, v[j=1:I.n_j, d=1:I.n_d], binary=true)
    for s=1:I.n_s, d=1:I.n_d
        M = floor(length(I.L[d])/I.ν[s])
        for j=I.J[s]
            LHS = zero(AffExpr)
            for i=1:I.n_i, l=I.L[d], m=1:I.n_m
                add_to_expression!(LHS, x[i, j, l, m])
            end
            LHS /= I.η[s]

            RHS = M * v[j, d]

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "group_max_days_1 (s=$s, d=$d, j=$j)")
        end
    end

    # Group max days 2 and 3
    @variable(model, w[j=1:I.n_j] >= 0)
    for j=1:I.n_j
        expr = zero(AffExpr)
        for d=1:I.n_d
            add_to_expression!(expr, v[j, d])
        end

        cons = @constraint(model, expr <= 1 + w[j])
        set_name(cons, "group_max_days_2_1 (j=$j)")

        cons = @constraint(model, 1 + w[j] <= I.κ[j])
        set_name(cons, "group_max_days_2_2 (j=$j)")
    end

    # Room switch break
    for s=1:I.n_s
        M = ceil((I.μ[s] + I.τ_room + 1) / I.ν[s])

        for j=I.J[s], m=1:I.n_m, d=1:I.n_d, l=I.L[d]
            LHS = zero(AffExpr)
            for i=1:I.n_i, m_tilde=1:I.n_m
                if m_tilde != m
                    for t=0:min(I.τ_room + I.μ[s], I.L[d][end]-I.ν[s]-l)
                        add_to_expression!(LHS, x[i, j, l+t, m_tilde])
                    end
                end
            end
            LHS /= I.η[s]

            RHS = zero(AffExpr)
            for i=1:I.n_i
                add_to_expression!(RHS, x[i, j, l, m])
            end
            RHS = M * (1 - RHS / I.η[s])

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "room_switch_break (s=$s, j=$j, m=$m, d=$d, l=$l)")
        end
    end


    # --- Room related constraints --- #
    # Room availability
    for s=1:I.n_s, m=1:I.n_m, d=1:I.n_d, l=I.L[d][1+I.μ[s]:end-(I.ν[s]-1)]
        RHS = prod(I.δ[m, l-I.μ[s]:l+I.ν[s]-1])

        if !RHS
            # All the individual variables are set to 0 so that the presolve routine easily removes those variables
            for i=1:I.n_i, j=I.J[s]
                fix(x[i,j,l,m], 0; force=true)
            end
        else
            LHS = zero(AffExpr)
            for i=1:I.n_i, j=I.J[s]
                add_to_expression!(LHS, x[i, j, l, m])
            end
            LHS /= I.η[s]

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "room_availability (s=$s, m=$m, d=$d, l=$l)")
        end
    end

    # Room group occupation
    for j=1:I.n_j, k=j+1:I.n_j
        s = I.groups[j].s
        u = I.groups[k].s
        a = I.ν[s]-1 + I.τ_room + I.μ[u]
        M = a + 1

        for m=1:I.n_m, d=1:I.n_d, l=I.L[d]
            LHS = zero(AffExpr)
            for i=1:I.n_i, t=0:min(a, I.L[d][end]-l)
                add_to_expression!(LHS, x[i, k, l+t, m])
            end
            LHS /= I.η[u]

            RHS = zero(AffExpr)
            for i=1:I.n_i
                add_to_expression!(RHS, x[i, j, l, m])
            end
            RHS = M * (1 - RHS / I.η[s])

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "room_group_occupation (j=$j, k=$k, m=$m, d=$d, l=$l)")
        end
    end


    # --- Exam related constraints --- #
    # Exam needed
    for i=1:I.n_i, j=1:I.n_j
        if !I.γ[i, j]
            for l=1:I.n_l, m=1:I.n_m
                fix(x[i,j,l,m], 0; force=true)
            end
        else
            LHS = zero(AffExpr)
            for l=1:I.n_l, m=1:I.n_m
                add_to_expression!(LHS, x[i, j, l, m])
            end

            cons = @constraint(model, LHS == 1)
            set_name(cons, "exam_needed (i=$i, j=$j)")
        end
    end

    # Exam student number
    @variable(model, p[j=1:I.n_j, l=1:I.n_l, m=1:I.n_m], binary=true)
    for s=1:I.n_s, j=I.J[s], l=1:I.n_l, m=1:I.n_m
        LHS = zero(AffExpr)
        for i=1:I.n_i
            add_to_expression!(LHS, x[i, j, l, m])
        end

        cons = @constraint(model, LHS == I.η[s] * p[j, l, m])
        set_name(cons, "exam_student_number (s=$s, j=$j, l=$l, m=$m)")
    end

    # Exam start
    for s=1:I.n_s, d=1:I.n_d, l=I.L[d][1:I.μ[s]], i=1:I.n_i, j=I.J[s], m=1:I.n_m
        fix(x[i,j,l,m], 0; force=true)
    end

    # Exam end
    for s=1:I.n_s, d=1:I.n_d, l=I.L[d][end-I.ν[s]-1:end], i=1:I.n_i, j=I.J[s], m=1:I.n_m
        fix(x[i,j,l,m], 0; force=true)
    end

    # Exam continuity 3
    @variable(model, z[j=1:I.n_j, l=1:I.n_l, m=1:I.n_m] >= 0)

    # Exam continuity 1
    for s=1:I.n_s, 
        M = 1 / I.η[s]

        for j=I.J[s], m=1:I.n_m, d=1:I.n_d, l=I.L[d][1+I.ρ[s]*I.ν[s]:end], t=I.ν[s]*(1:I.ρ[s])
            LHS = zero(AffExpr)
            for i=1:I.n_i
                add_to_expression!(LHS, x[i, j, l-I.ν[s], m])
            end
            LHS /= I.η[s]

            expr1 = zero(AffExpr)
            for i=1:I.n_i
                add_to_expression!(expr1, x[i, j, l, m])
            end
            expr1 /= I.η[s]

            expr2 = zero(AffExpr)
            for i=1:I.n_i
                add_to_expression!(expr2, x[i, j, l-t, m])
            end

            RHS = expr1 + z[j, l, m] + M * expr2

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "exam_continuity_1 (s=$s, j=$j, m=$m, d=$d, l=$l, t=$t)")
        end
    end

    # Exam continuity 2
    for s=1:I.n_s, j=I.J[s], m=1:I.n_m, d=1:I.n_d, l=I.L[d][1+I.ν[s]:I.ρ[s]*I.ν[s]]
        LHS = zero(AffExpr)
        for i=1:I.n_i
            add_to_expression!(LHS, x[i, j, l-I.ν[s], m])
        end
        LHS /= I.η[s]

        expr = zero(AffExpr)
        for i=1:I.n_i
            add_to_expression!(expr, x[i, j, l, m])
        end
        expr /= I.η[s]

        RHS = expr + z[j, l, m]

        cons = @constraint(model, LHS <= RHS)
        set_name(cons, "exam_continuity_2 (s=$s, j=$j, m=$m, d=$d, l=$l)")
    end

    # Exam break
    for s=1:I.n_s
        M = 1 + ceil(I.τ_seq / I.μ[s])
        
        for j=I.J[s], d=1:I.n_d, l=I.L[d][1+I.ρ[s]*I.ν[s]:end]
            LHS = zero(AffExpr)
            for i=1:I.n_i, t=0:min(I.τ_seq+I.μ[s], I.L[d][end]-l), m=1:I.n_m
                add_to_expression!(LHS, x[i, j, l+t, m])
            end
            LHS /= I.η[s]

            RHS = zero(AffExpr)
            for i=1:I.n_i, m=1:I.n_m, a=1:I.ρ[s]
                add_to_expression!(RHS, x[i, j, l-a*I.ν[s], m])
            end
            RHS = M * (I.ρ[s] - RHS / I.η[s])

            cons = @constraint(model, LHS <= RHS)
            set_name(cons, "exam_break (s=$s, j=$j, d=$d, l=$l)")
        end
    end

    # Exam grouped
    @variable(model, r[j=1:I.n_j, d=1:I.n_d])
    @variable(model, R[j=1:I.n_j, d=1:I.n_d])
    for s=1:I.n_s, j=I.J[s], d=1:I.n_d
        cons = @constraint(model, r[j, d] >= I.L[d][1])
        set_name(cons, "exam_grouped_3_1 (s=$s, j=$j, d=$d)")

        cons = @constraint(model, r[j, d] <= R[j, d])
        set_name(cons, "exam_grouped_3_2 (s=$s, j=$j, d=$d)")
        
        cons = @constraint(model, R[j, d] <= I.L[d][end])
        set_name(cons, "exam_grouped_3_3 (s=$s, j=$j, d=$d)")
        
        for l=I.L[d]
            expr = zero(AffExpr)
            for i=1:I.n_i, m=1:I.n_m
                add_to_expression!(expr, x[i, j, l, m])
            end

            RHS = l + (I.L[d][end] - l) * (1 - expr / I.η[s])
            cons = @constraint(model, r[j, d] <= RHS)
            set_name(cons, "exam_grouped_1 (s=$s, j=$j, d=$d, l=$l")

            RHS = l + (I.L[d][1] - l) * (1 - expr / I.η[s])
            cons = @constraint(model, R[j, d] >= RHS)
            set_name(cons, "exam_grouped_2 (s=$s, j=$j, d=$d, l=$l)")
        end
    end


    # --- Objective function --- #
    y_coef = 30 / I.n_i
    y_sum = zero(AffExpr)
    for i=1:I.n_i
        add_to_expression!(y_sum, y[i])
    end

    q_coef = 30 / (I.n_e * I.n_l)
    q_sum = zero(AffExpr)
    for e=1:I.n_e, l=1:I.n_l
        add_to_expression!(q_sum, q[e, l])
    end

    w_coef = 30 / I.n_j
    w_sum = zero(AffExpr)
    for j=1:I.n_j
        add_to_expression!(w_sum, w[j])
    end

    z_coef = 30 / (I.n_j * I.n_l * I.n_m)
    z_sum = zero(AffExpr)
    for j=1:I.n_j, l=1:I.n_l, m=1:I.n_m
        add_to_expression!(z_sum, z[j, l, m])
    end

    Rr_coef = 30 / (I.n_j * I.n_d)
    Rr_sum = zero(AffExpr)
    for j=1:I.n_j, d=1:I.n_d
        add_to_expression!(Rr_sum, R[j, d] - r[j, d])
    end

    objective = y_coef * y_sum + q_coef * q_sum + w_coef * w_sum + z_coef * z_sum + Rr_coef * Rr_sum

    @objective(model, Min, 0)
end