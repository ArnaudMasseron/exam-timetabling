* **rooms** -> each entry contains the informations about one room
  * **unavailabilities** -> list containing the datetimes where the current room is unavailable; it is under the format *[start datetime, end datetime]*
  * **type** -> type of the room
  * **acronym** -> codename of the room
* **groups** -> each entry contains the onformations about one group
  * **subject_id** -> index of the subject, this references the position in the **subjects** list
  * **examiner_ids** -> index of the examiners, this references the position in the **examiners** list
* **classes** -> each entry contains the informations about one class
  * **name** -> name of the class
* **subjects** -> each entry contains the informations about one subject
  * **duration_time** -> number of timeslots needed for the presentation phase of one exam with the current subject
  * **preparation_time** -> number of timeslots needed for the preparation phase of one exam with the current subject
  * **name** -> name of the subject
  * **number_of_students** -> number of students that go take the exam simultaneously
  * **max_number_exams_row** -> maximum number of exams that can be scheduled before taking a break
  * **group_students_by_class** -> should the students from a same class be grouped together or not
  * **room_type** -> type of the rooms where exams with this subject can take place
* **examiners** -> each entry contains the informations about one examiner
  * **name** -> name of the examiner
  * **acronym** -> codename of the examiner
  * **type** -> type of the examiner, *teacher* or *expert*
  * **max_number__days** -> maximum number of days where the examiner can give exams
  * **max_number_exams_per_day** -> maximum number of exams per day for the examiner
  * **soft_unavailabilities** -> list containing the datetimes of the cancelable obligations of the current examiner; it is under the format *[start datetime, end datetime]*
  * **hard_unavailabilities** -> list containing the datetimes of the uncancelable obligations of the current examiner; it is under the format *[start datetime, end datetime]*
* **exams** -> list of *(student, group)* couples that need to have a exam scheduled together; each entry contains a single student since the student groups aren't known in advance for exams with multiple students simultaneously
  * **group_id** -> index of the group, this references the position in the **groups** list
  * **student_id** -> index of the student, this references the position in the **students** list
  * **modality** -> unique index associated to each couple *(student, group)*
* **general_parameters**
  * **time_slot_length_minutes** -> length of a time slot in minutes
  * **exam_sequence_break_duration** -> minimum number of time slots needed for each group for a break between series of exams scheduled next to one another
  * **student_break_duration** -> minimum number of time slots needed for each student for each break between two exams
  * **room_break_duration** -> minimum number of time slots needed for a break when a group switches rooms
  * **group_switch_break_duration** -> minimum number of time slots needed for a break when an examiner switches groups
  * **lunch_break_duration** -> minimum number of time slots needed for the a lunch break for each examiner
  * **max_number_exams_student** -> maximum number of exams per day for each student
  * **exam_time_window** -> list of all datetimes where exams can take place; it is under the format *[start datetime, end datetime]*
  * **lunch_time_window** -> time where a lunch break can take place for each examiner; it is under the format *(start time, end time)*
* **student** -> each entry contains the informations about a student
  * **name** -> name of the student
  * **class_id** -> index of the class of the student, this references the position in the **classes** list
  * **unavailabilities** -> list containing the datetimes where the current student is unavailable; it is under the format *[start datetime, end datetime]*
