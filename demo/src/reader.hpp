
#ifndef READER_HPP
#define READER_HPP

#include <string>

#include "definitions.hpp"

student_name_map read_student_names(const std::string& filename);
teacher_name_map read_teacher_names(const std::string& filename);
subject_name_map read_subject_names(const std::string& filename);

grade_map read_grade_map(const std::string& filename);
student_teacher_map read_teacher_map(const std::string& filename);

#endif

