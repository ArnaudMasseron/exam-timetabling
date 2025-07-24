# Save function that creates the folder if it doesnt exist
function save_with_dir(path::String, data)
    # If the directory doesnt exist then create it
    dir_path = dirname(path)
    isdir(dir_path) || mkpath(dir_path)

    @save path data
end

# Print the message by adding dashes before and after
function println_dash(mystring::String)
    println(repeat("-", 30) * " " * mystring * " " * repeat("-", 30))
    flush(stdout)
end

function print_constraint_conflicts(model::Model, name_only::Bool = false)
    #=
    Print a subset of constraints containing the constraints that 
    make the model infeasible.
    =#
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

function reorder_students_inside_series(I::Instance, x_values::Array{Bool,4})
    #= 
    Reorder students inside exams series (ie exams that are next to one another and 
    that have the same group) so that students from the same class are next to one another 
    =#

    for j = 1:I.n_j
        s = I.groups[j].s
        !I.dataset["subjects"][s]["group_students_by_class"] && continue

        l = 1
        d = 1
        while l <= I.n_l
            if sum(x_values[i, j, l, m] for i = 1:I.n_i, m = 1:I.n_m) <= 0
                l += 1
            else
                students_in_serie = []

                list_m = findall(identity, sum(x_values[i, j, l, :] for i = 1:I.n_i) .> 0)
                @assert length(list_m) == 1
                m = first(list_m)

                let curr_l = l
                    while true
                        curr_l > I.L[d][end] && break

                        students_l = findall(identity, view(x_values, :, j, curr_l, m))
                        isempty(students_l) && break
                        @assert length(students_l) == I.η[s]

                        for i in students_l
                            x_values[i, j, curr_l, m] = false
                        end
                        students_in_serie = vcat(students_in_serie, students_l)

                        curr_l += 1
                    end
                end

                #= 
                This array tells in which order the classes should be reordered
                The class id is not used directly so that its not always students from a
                specific class first
                =#
                student_to_class_position = Dict{Int,Int}()
                let class_id_to_position = Dict{Int,Int}()
                    for i in students_in_serie
                        c = I.dataset["students"][i]["class_id"]

                        if !haskey(class_id_to_position, c)
                            class_id_to_position[c] = length(class_id_to_position) + 1
                        end
                        student_to_class_position[i] = class_id_to_position[c]
                    end
                end

                # Reorder the students by their class position
                sort!(students_in_serie, by = (i -> student_to_class_position[i]))

                # Change x_values
                curr_l = l
                nb_stu_l = 0
                for i in students_in_serie
                    x_values[i, j, curr_l, m] = true
                    nb_stu_l += 1
                    if nb_stu_l == I.η[s]
                        nb_stu_l = 0
                        curr_l += 1
                    end
                end

                l = curr_l
            end

            (l > I.L[d][end]) && (d += 1)
        end
    end
end

function get_objective_value_callback(
    entry_id::Int,
    objective_evolution::Vector{Dict{String,Vector{Float64}}},
)
    f =
        (cb_data::Gurobi.CallbackData, cb_where::Cint) -> begin
            # only act on new integer solutions
            if cb_where == GRB_CB_MIPSOL
                # get the objective value
                obj_ref = Ref{Cdouble}()
                Gurobi.GRBcbget(cb_data, cb_where, GRB_CB_MIPSOL_OBJ, obj_ref)
                obj_val = obj_ref[]

                # get the current runtime (in seconds)
                time_ref = Ref{Cdouble}()
                Gurobi.GRBcbget(cb_data, cb_where, GRB_CB_RUNTIME, time_ref)
                run_time = time_ref[]

                push!(objective_evolution[entry_id]["time"], run_time)
                push!(objective_evolution[entry_id]["objective"], obj_val)
            end
        end

    return f
end

function get_instance_arguments(instance_path::String)
    @assert endswith(instance_path, ".json")
    instance_name = basename(instance_path)

    instance_arguments = split(instance_name, "_")
    year = instance_arguments[1]
    instance_type = instance_arguments[3]
    time_step_min = parse(Int, instance_arguments[4][1:end-8])

    return year, instance_type, time_step_min
end

function get_frozen_exams(I::Instance, modalities_reschedule, start_x_values::Array{Bool,4})
    #=
    Get the exams in starting_x_values that shouldn't be rescheduled
    Arguments:
    [input] I: instance
    [input] modalties_reschedule : modalities of the exams that need to be rescheduled
    [input] start_x_values : modalities of the exams that need to be rescheduled

    Return value: set of all (i,j) exams that need to be frozen
    i.e. not be rescheduled
    =#

    exams_reschedule = Set{Tuple{Int,Int}}()
    for modality in modalities_reschedule
        exam_id = findfirst(x -> x["modality"] == modality, I.dataset["exams"])
        i = I.dataset["exams"][exam_id]["student_id"]
        j = I.dataset["exams"][exam_id]["group_id"]
        push!(exams_reschedule, (i, j))
    end

    # Allow the exams of dummy students to be rescheduled
    dummy_exams = Set{Tuple{Int,Int}}()
    dummy_class_id = findfirst(x -> contain(x["acronym"], "dummy"), I.dataset["classes"])
    if !isnothing(dummy_class_id)
        dummy_students =
            findall(x -> x["class_id"] == dummy_class_id, I.dataset["students"])
        dummy_exams = Set([(i, j) for i in dummy_students, j = 1:I.n_j if I.γ[i, j]])
    end

    instance_exams = Set([(i, j) for i = 1:I.n_i, j = 1:I.n_j if I.γ[i, j]])
    frozen_exams = setdiff!(instance_exams, union(exams_reschedule, dummy_exams))

    # Get the ijlm indexes in start_x_values coreresponding to the frozen exams
    frozen_ijlm = Set{NTuple{4,Int}}()
    for (i, j) in frozen_exams
        cart_id = findfirst(identity, view(x_values, i, j, :, :))
        if !isnothing(cart_id)
            i, j = cart_id.I
            push!(frozen_ijlm, (i, j, l, m))
        end
    end

    return frozen_ijlm
end
