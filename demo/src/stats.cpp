
#include "stats.hpp"

#include <algorithm>
#include <iterator>
#include <unordered_map>

template<typename Int>
inline static double d_div(Int l, Int r) {
	return static_cast<double>(l) / static_cast<double>(r);
}

std::vector<std::pair<std::size_t, double>> avg_success(const grade_map& grades,
                                                       const student_teacher_map& teachers) {
	auto results = std::unordered_map<std::size_t, std::pair<std::size_t, std::size_t>>{};
	for (const auto& g : *grades) {
		const auto teacher_it = teachers->find(g.first);
		if (teacher_it == teachers->end()) {
			continue;
		}
		ONTO_ASSERT_SATISFACTION(preds::is_teacher(teacher_it->second));
		ONTO_ASSERT_SATISFACTION(preds::is_grade(g.second));
		// ONTO_ASSERT_SATISFACTION(preds::is_student(g.second)); // This should fire!
		auto& pair = results[*(teacher_it->second)];
		pair.first += *g.second;
		++pair.second;
	}
	auto ret = std::vector<std::pair<std::size_t, double>>{};
	std::transform(results.begin(), results.end(), std::back_inserter(ret), [](const auto& p) {
		return std::make_pair(p.first, d_div(p.second.first, p.second.second));
	});
	return ret;
}
