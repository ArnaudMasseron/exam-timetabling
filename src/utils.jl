function print_constraint_conflicts(model::Model, name_only::Bool=false)
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