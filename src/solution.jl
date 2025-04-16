using JSON, XLSX

function write_solution_json(I::Instance, x_values::Array{Bool,4}, solution_path::String)
    @assert endswith(solution_path, ".json")

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

            subject_name = I.dataset["subjects"][s]["acronym"]
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

    # Save exams in a json file
    open(solution_path, "w") do file
        JSON.print(file, exams, 2)
    end
end

function reorder_students_inside_series(I::Instance, x_values::Array{Bool,4})
    #= 
    Reorder students inside exams series (ie exams that are next to one another and 
    that have the same group) so that students from the same class are next to one another 
    =#

    for j = 1:I.n_j, m = 1:I.n_m, l = 1:I.n_l
        if sum(x_values[i, j, l, m] for i = 1:I.n_i) > 0
            s = I.groups[j].s
            students_in_serie = []

            # Find the students in the current exam series
            let curr_l = l
                while true
                    @assert curr_l <= I.n_l

                    students_l = findall(identity, x_values[:, j, curr_l, m])
                    if isempty(students_l)
                        break
                    end
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

            # Reorder the students by theur class position
            sort(students_in_serie, by = (i -> student_to_class_position[i]))

            # Change x_values
            let curr_l = l
                nb_stu_l = 0
                for i in students_in_serie
                    x_values[i, j, curr_l, m] = true
                    nb_stu_l += 1
                    if nb_stu_l == I.η[s]
                        nb_stu_l = 0
                        curr_l += 1
                    end
                end
            end
        end
    end
end
