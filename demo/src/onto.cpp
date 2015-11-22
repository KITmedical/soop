
#include "onto.hpp"

bool is_teacher(const soop::e<std::size_t>& e) { return e.problem()->request_satisfaction(is_teacher, e); }
bool is_student(const soop::e<std::size_t>& e) { return e.problem()->request_satisfaction(is_student, e); }
bool is_subject(const soop::e<std::size_t>& e) { return e.problem()->request_satisfaction(is_subject, e); }
bool is_grade  (const soop::e<std::size_t>& e) { return e.problem()->request_satisfaction(is_grade,   e); }

soop::basic_problem& get_onto() {
	using namespace soop;
	static auto p = []{
		problem<
			functions<
				make_function<std::size_t>,
				make_function<std::string>,
				make_function<std::unordered_map<e<std::size_t>, e<std::string>>>,
				make_function<std::map<std::pair<e<std::size_t>, e<std::size_t>>, e<std::size_t>>>
			>,
			predicates<
				predicate<has_grade_t>,
				predicate<deserves_price_t>
			>,
			formulae<
				formula<
					forall<set<var<'S'>, x,y,z>,
						implies<and_<
							has_grade<var<'S'>, x>,
							has_grade<var<'S'>, y>,
							has_grade<var<'S'>, z>
							>,
							deserves_price<var<'S'>>
						>
					>
				>
			>
		> tmp;
		tmp.add_relation(is_teacher);
		tmp.add_relation(is_student);
		tmp.add_relation(is_subject);
		tmp.add_relation(is_grade);
		return tmp;
	}();
	return p;
}
