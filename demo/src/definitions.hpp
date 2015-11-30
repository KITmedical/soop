
#ifndef DEFINITIONS_HPP
#define DEFINITIONS_HPP

#include <unordered_map>
#include <cstdint>
#include <vector>
#include <string>
#include <utility>
#include <map>

#include "soop/entity.hpp"
#include "onto.hpp"

// Use one datatype for everything to
// work around the static typesystem
// as a lot of bad programmers appear
// to do in real-life:

using student_id = soop::e<std::size_t>;
using teacher_id = soop::e<std::size_t>;
using subject_id = soop::e<std::size_t>;
using grade = soop::e<std::size_t>; // for consistency

using student_name_map = soop::e<std::unordered_map<student_id, soop::e<std::string>>>;
using teacher_name_map = soop::e<std::unordered_map<subject_id, soop::e<std::string>>>;
using subject_name_map = soop::e<std::unordered_map<subject_id, soop::e<std::string>>>;


using grade_map =           soop::e<std::map<std::pair<student_id, subject_id>, grade>>;
using student_teacher_map = soop::e<std::map<std::pair<student_id, subject_id>, teacher_id>>;

#endif
