
#ifndef STATS_HPP
#define STATS_HPP

#include <vector>
#include <utility>

#include "definitions.hpp"

std::vector<std::pair<teacher_id, double>> avg_success(const grade_map& grades,
                                                       const student_teacher_map& teachers);

#endif
