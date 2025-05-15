function print_constraint_conflicts(model::Model, name_only::Bool = false)
    compute_conflict!(model)  # Compute IIS

    # Check all constraints (including variable bounds)
    for (F, S) in list_of_constraint_types(model)
        for cons in all_constraints(model, F, S)
            # Check if the constraint is in the conflict
            status = MOI.get(model, MOI.ConstraintConflictStatus(), cons)
            if status == MOI.IN_CONFLICT
                if name_only
                    println("Conflict in: ", name(cons))
                else
                    println("Conflict in: ", cons)
                end
            end
        end
    end
end


# --- Student groups related functions --- #

function find_student_equivalence_classes(I::Instance)
    stu_equiv = Dict{Dict{String,Any},Set{Int}}()

    for i = 1:I.n_i
        groups = findall(x -> x, I.γ[i, :])
        unavailabilities = findall(x -> !x, I.θ[i, :])
        key = Dict("groups" => groups, "unavailabilities" => unavailabilities)

        if !haskey(stu_equiv, key)
            stu_equiv[key] = Set()
        end
        push!(stu_equiv[key], i)
    end

    return stu_equiv
end

function find_student_groups(I::Instance)
    #=
    Returns an array containing ids of students that need to be grouped together.
    =#
    stu_equiv = find_student_equivalence_classes(I)

    student_groups = Vector{Vector{Int}}()
    for (key, value) in stu_equiv
        # Compute the number of students in one student group for the current equivalence class
        nb_stu_in_group = Inf
        examiner_groups = key["groups"]
        for j in examiner_groups
            s = I.groups[j].s
            nb_stu_in_group = min(nb_stu_in_group, I.ρ[s] * I.η[s])
        end
        @assert isfinite(nb_stu_in_group)

        # Group some students together
        stu_group = Vector{Int}()
        for i in value
            push!(stu_group, i)

            if length(stu_group) == nb_stu_in_group
                push!(student_groups, stu_group)
                stu_group = []
            end
        end
    end

    return student_groups
end