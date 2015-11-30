
#include "onto.hpp"

soop::ontology& get_onto() {
	static auto p = []{
		soop::ontology onto{
			::preds::has_grade,
			::preds::deserves_price,
			::preds::is_teacher,
			::preds::is_student,
			::preds::is_subject,
			::preds::is_grade
		};
		using soop::e;
		onto.add_type<e<std::size_t>>();
		onto.add_type<e<std::string>>();
		onto.add_type<e<std::unordered_map<e<std::size_t>, e<std::string>>>>();
		onto.add_type<e<std::map<std::pair<e<std::size_t>, e<std::size_t>>, e<std::size_t>>>>();
		using namespace soop::preds;
		using namespace ::preds;
		onto.add_axiom(forall({"S", "x", "y", "z"},implies(and_(has_grade("S", "x"), and_(has_grade("S", "y"), has_grade("S", "z"))), deserves_price("S"))));
		return onto;
	}();
	return p;
}
