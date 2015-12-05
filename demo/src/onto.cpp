
#include "onto.hpp"

soop::ontology& get_onto() {
	static auto p = []{
		soop::ontology onto{
			::preds::has_grade,
			::preds::deserves_price,
			::preds::is_teacher,
			::preds::is_student,
			::preds::is_subject,
			::preds::is_grade,
			::preds::passing_grade,
			::preds::good_grade,
			::preds::very_good_grade
		};
		using soop::e;
		onto.add_type<e<std::size_t>>();
		onto.add_type<e<std::string>>();
		onto.add_type<e<std::unordered_map<e<std::size_t>, e<std::string>>>>();
		onto.add_type<e<std::map<std::pair<e<std::size_t>, e<std::size_t>>, e<std::size_t>>>>();
		using namespace soop::preds;
		using namespace ::preds;
		onto.add_axiom(forall({"g"}, implies(very_good_grade("g"), good_grade("g"))));
		onto.add_axiom(forall({"g"}, implies(good_grade("g"), passing_grade("g"))));
		onto.add_axiom(forall({"g"}, implies(passing_grade("g"), is_grade("g"))));
		onto.add_axiom(forall({"S"}, implies(
			exists({"x", "y", "z"},
				and_(
					and_(has_grade("S", "x"), very_good_grade("x")), and_(
					and_(has_grade("S", "y"), very_good_grade("y")),
					and_(has_grade("S", "z"),      good_grade("z"))))),
			deserves_price("S")
			)));
		return onto;
	}();
	return p;
}
