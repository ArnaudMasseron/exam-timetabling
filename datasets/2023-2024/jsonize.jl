using XLSX
using Dates

# Read the files provided by the school and fetch the useful data
data_dir = "/home/arnaud/Documents/UNIFR/travail/exam-timetabling/datasets/2023-2024/school_files/"
exam_list_file = data_dir * "2324_CSUD_Liste_oraux.xlsx"
teacher_schedule_file = data_dir * "2324_CSUD_Horaires_Juin.xlsx"
room_file = data_dir * "2324_CSUD_Salles-liste.xlsx"

student_data = Dict{Tuple{String,String},Dict{String,Any}}() # key = (student name, class acronym)
examiner_data = Dict{String,Dict{String,Any}}()
subject_data = Dict{String,Dict{String,Any}}()
room_data = Dict{String,Dict{String,Any}}()
group_set = Set{Dict{String,Any}}()
exam_set = Set{Dict{String,Any}}()
class_data = Dict{String,Any}()

time_step = Minute(15)

XLSX.openxlsx(exam_list_file) do workbook
    #@assert(XLSX.sheetcount(workbook) == 1)
    sheet_name = XLSX.sheetnames(workbook)[1]
    sheet = workbook[sheet_name]

    row_number = 2
    for row in XLSX.eachtablerow(sheet)
        group_examiner_acronyms = split(row[Symbol("Sigles expert et examinateur")], ", ")
        subject_acronym = split(row[Symbol("Nom de l'examen")], " ")[1]
        subject_duration =
            Minute.(
                sum(parse.(Int, (split(row[Symbol("Durée de l'examen")], "h"))) .* [60, 1])
            ) / time_step
        students = split.(split(row[Symbol("Nom de l'étudiant_classe")], ", "), "_") #students[i] = (class, student name)

        @assert(
            prod(isinteger.(subject_duration)),
            "BAD PARAMETER: The time must be discretizable into whole time_step long time slots"
        )
        subject_duration = Int.(subject_duration)

        @assert(
            prod([students[i][1] == students[i+1][1] for i = 1:length(students)-1]),
            "BAD EXCEL SHEET: some students belong to different classes in row $row_number"
        )
        class_acronym = students[1][1]

        for (student_class, student_name) in students
            student_data[(student_name, class_acronym)] = Dict{String,Any}()
            class_data[student_class] = Dict{String,Any}()
        end

        for e in group_examiner_acronyms
            push!(
                examiner_data,
                e => Dict{String,Any}(
                    "soft_obligations" => Vector{Tuple{DateTime,DateTime}}(),
                    "hard_obligations" => Vector{Tuple{DateTime,DateTime}}(),
                ),
            )
        end

        if haskey(subject_data, subject_acronym)
            @assert(
                subject_data[subject_acronym]["duration_time"] == subject_duration,
                "BAD EXCEL SHEET ERROR: subject $subject_acronym has varying durations"
            )
            @assert(
                subject_data[subject_acronym]["number_of_students"] == length(students),
                "BAD EXCEL SHEET ERROR: subject $subject_acronym has varying numbers of students"
            )
        else
            subject_data[subject_acronym] = Dict(
                "duration_time" => subject_duration,
                "number_of_students" => length(students),
            )
        end

        push!(
            group_set,
            Dict(
                "examiner_acronyms" => Set(group_examiner_acronyms),
                "subject_acronym" => subject_acronym,
                "class_acronym" => class_acronym,
            ),
        )

        for (_, student_name) in students
            push!(
                exam_set,
                Dict(
                    "student_name" => student_name,
                    "examiner_acronyms" => Set(group_examiner_acronyms),
                    "subject_acronym" => subject_acronym,
                    "class_acronym" => students[1][1],
                ),
            )
        end
        row_number += 1
    end
end

XLSX.openxlsx(teacher_schedule_file) do workbook
    #@assert(XLSX.sheetcount(workbook) == 1)
    sheet_name = XLSX.sheetnames(workbook)[1]
    sheet = workbook[sheet_name]

    for row in XLSX.eachtablerow(sheet)
        teacher_acronym = row[:sigle]
        date = row[:date]
        start_time = row[:heuredeb]
        end_time = row[:heurefin]

        if haskey(examiner_data, teacher_acronym)
            push!(
                examiner_data[teacher_acronym]["soft_obligations"],
                (DateTime(date, start_time), DateTime(date, end_time)),
            )
        end
    end
end

XLSX.openxlsx(room_file) do workbook
    #@assert(XLSX.sheetcount(workbook) == 1)
    sheet_name = XLSX.sheetnames(workbook)[1]
    sheet = workbook[sheet_name]

    for row in XLSX.eachtablerow(sheet)
        room_acronym = row[:Code]
        if room_acronym[1] != '3'
            continue
        end
        room_data[room_acronym] = Dict{String,Any}()
    end
end

# Add indexes to the students, the subjects, the groups, the examiners and the rooms
for (i, key) in enumerate(keys(student_data))
    student_data[key]["id"] = i
end
for (s, key) in enumerate(keys(subject_data))
    subject_data[key]["id"] = s
end
for (m, key) in enumerate(keys(room_data))
    room_data[key]["id"] = m
end
for (e, key) in enumerate(keys(examiner_data))
    examiner_data[key]["id"] = e
end
for (c, key) in enumerate(keys(class_data))
    class_data[key]["id"] = c
end

group_array = collect(group_set)
for j in eachindex(group_array)
    group_array[j]["id"] = j
end
group_set = Set{Dict{String,Any}}(group_array)


# Construct the dictionnary containing the whole dataset with the correct format
dataset = Dict{String,Any}()

dataset["general_parameters"] = Dict{String,Any}()
dataset["general_parameters"]["time_slot_length_minutes"] = time_step.value
dataset["general_parameters"]["max_number_exams_student"] = 1
dataset["general_parameters"]["lunch_break_duration"] = 4
dataset["general_parameters"]["room_break_duration"] = 2
dataset["general_parameters"]["exam_sequence_break_duration"] = 2
dataset["general_parameters"]["student_break_duration"] = 4
dataset["general_parameters"]["group_switch_break_duration"] = 2
dataset["general_parameters"]["exam_time_windows"] = Vector{Tuple{DateTime,DateTime}}([
    (DateTime(2024, 6, 17 + k, 8), DateTime(2024, 6, 17 + k, 20)) for k = 0:12 if k != 6
])
dataset["general_parameters"]["lunch_time_window"] =
    Tuple{Time,Time}((Time("11:30am", "HH:MMp"), Time("01pm", "HHp")))

dataset["students"] =
    Vector{Dict{String,Any}}([Dict{String,Any}() for i = 1:length(student_data)])
for ((student_name, class_acronym), value) in student_data
    dataset["students"][value["id"]] = Dict(
        "name" => student_name,
        "class_id" => class_data[class_acronym]["id"],
        "unavailabilities" => Vector{Tuple{DateTime,DateTime}}(),
    )
end

dataset["examiners"] =
    Vector{Dict{String,Any}}([Dict{String,Any}() for e = 1:length(examiner_data)])
for (key, value) in examiner_data
    dataset["examiners"][value["id"]] = Dict(
        "acronym" => key,
        "soft_unavailabilities" =>
            Vector{Tuple{DateTime,DateTime}}(value["soft_obligations"]),
        "hard_unavailabilities" => Vector{Tuple{DateTime,DateTime}}(),
        "max_number_exams_per_day" => 24,
    )
end

dataset["subjects"] =
    Vector{Dict{String,Any}}([Dict{String,Any}() for s = 1:length(subject_data)])
for (key, value) in subject_data
    dataset["subjects"][value["id"]] = Dict(
        "acronym" => key,
        "preparation_time" => 1,
        "duration_time" => value["duration_time"],
        "number_of_students" => value["number_of_students"],
        "max_number_exams_row" => 6,
    )
end

dataset["rooms"] =
    Vector{Dict{String,Any}}([Dict{String,Any}() for j = 1:length(room_data)])
for (key, value) in room_data
    dataset["rooms"][value["id"]] = Dict(
        "acronym" => key,
        "unavailabilities" => Vector{Tuple{DateTime,DateTime}}(),
        "unsuported_subjects" => Vector{Int}(),
    )
end

dataset["groups"] =
    Vector{Dict{String,Any}}([Dict{String,Any}() for j = 1:length(group_set)])
for item in group_set
    dataset["groups"][item["id"]] = Dict(
        "examiner_ids" => Set([
            examiner_data[acronym]["id"] for acronym in item["examiner_acronyms"]
        ]),
        "subject_id" => subject_data[item["subject_acronym"]]["id"],
        "class_id" => class_data[item["class_acronym"]]["id"],
        "max_number_days" => 5,
    )
end

dataset["classes"] =
    Vector{Dict{String,Any}}([Dict{String,Any}() for j = 1:length(class_data)])
for (key, value) in class_data
    dataset["classes"][value["id"]] = Dict("acronym" => key)
end

dataset["exams"] = Vector{Dict{String,Any}}()
for item in exam_set
    student_id = student_data[(item["student_name"], item["class_acronym"])]["id"]
    group_candidates = filter(
        x ->
            x["examiner_acronyms"] == item["examiner_acronyms"] &&
                x["subject_acronym"] == item["subject_acronym"] &&
                x["class_acronym"] == item["class_acronym"],
        group_set,
    )
    @assert(length(group_candidates) == 1, "One group has multiple ids in group_set")
    group_id = first(group_candidates)["id"]

    push!(dataset["exams"], Dict("student_id" => student_id, "group_id" => group_id))
end


# Save the dataset in a JSON file
using JSON
save_dir = "/home/arnaud/Documents/UNIFR/travail/exam-timetabling/datasets/2023-2024/"
open(save_dir * "2023-2024_dataset.json", "w") do file
    JSON.print(file, dataset, 2)
end
