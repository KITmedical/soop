
#include "onto.hpp"

bool is_teacher(const soop::e<std::size_t>& e) { return e.problem()->request_satisfication(is_teacher, e); }
bool is_student(const soop::e<std::size_t>& e) { return e.problem()->request_satisfication(is_student, e); }
bool is_subject(const soop::e<std::size_t>& e) { return e.problem()->request_satisfication(is_subject, e); }
bool is_grade  (const soop::e<std::size_t>& e) { return e.problem()->request_satisfication(is_grade,   e); }

soop::basic_problem& get_onto() {
	using namespace soop;
	static auto p = []{
		problem<
			functions<
				make_function<std::size_t>,
				make_function<std::string>,
				make_function<std::unordered_map<std::size_t, std::string>>,
				make_function<std::map<std::pair<std::size_t, std::size_t>, std::size_t>>
			>,
			predicates<>,
			formulae<>
		> tmp;
		tmp.add_relation(is_teacher);
		tmp.add_relation(is_student);
		tmp.add_relation(is_subject);
		tmp.add_relation(is_grade);
		return tmp;
	}();
	return p;
}
