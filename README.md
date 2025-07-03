## Exam timetabling

This repository contains the scripts developped during Arnaud Masseron's 2025 internship at the University of Fribourg , Switzerland. Their goal is solve the oral exam timetabling problem encountered by high schools in the canton of Fribourg, Switzerland.

The `./solvers` folder contains the high level scripts that solve the entire scheduling problem. In this folder, each one of those scripts corresponds to a different solving algorithm. The script `./solvers/solve_RSD_split.jl` is the one that was worked on the most.

The `./src` folder contains all the source code used by the scripts in `./solvers`.

The `./instances` folder contains a sample tiny instance. The high school instances aren't publicly available as they contain private information such as student and examiner names.
