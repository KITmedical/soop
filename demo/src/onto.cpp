
#include "onto.hpp"

soop::ontology& get_onto() {
	static auto p = []{
		using soop::e;
		soop::ontology onto{
			soop::type_list<
				e<std::size_t>,
				e<std::string>,
				e<std::unordered_map<e<std::size_t>, e<std::string>>>,
				e<std::map<std::pair<e<std::size_t>, e<std::size_t>>, e<std::size_t>>>
			>,
			soop::pred_list<
				::preds::has_grade_t,
				::preds::deserves_price_t,
				::preds::is_teacher_t,
				::preds::is_student_t,
				::preds::is_subject_t,
				::preds::is_grade_t,
				::preds::passing_grade_t,
				::preds::good_grade_t,
				::preds::very_good_grade_t
			>()
		};
		using namespace soop::preds;
		using namespace ::preds;
		//onto.add_axiom(forall({"g"}, implies(very_good_grade("g"), good_grade("g"))));
		//onto.add_axiom(forall({"g"}, implies(good_grade("g"), passing_grade("g"))));
		//onto.add_axiom(forall({"g"}, implies(passing_grade("g"), is_grade("g"))));
		//onto.add_axiom(forall({"S"}, implies(
		//	exists({"x", "y", "z"},
		//		and_(
		//			and_(has_grade("S", "x"), very_good_grade("x")), and_(
		//			and_(has_grade("S", "y"), very_good_grade("y")),
		//			and_(has_grade("S", "z"),      good_grade("z"))))),
		//	deserves_price("S")
		//	)));
		return onto;
	}();
	return p;
}
