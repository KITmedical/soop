

#include <iostream>
#include <string>

#include <soop/onto.hpp>

class person {
public:
	person(std::string name): name{std::move(name)} {}
	std::string name;
};
using person_e = soop::e<person>;

SOOP_MAKE_TYPECHECKED_PREDICATE(parent_of, 2, person_e, person_e)

int main() {
	using namespace preds;
	using namespace soop::preds;
	soop::ontology o{};
	o.add_type<person_e>();
	o.add_predicate<parent_of_t>();
	soop::variable<'p'> p;
	soop::variable<'c'> c;
	o.add_axiom(forall({p, c}, implies(parent_of(p, c), and_(
			instance_of(p, soop::type<person_e>),
			instance_of(c, soop::type<person_e>)))));
	o.add_axiom(forall({p, c}, implies(parent_of(p, c), not_(parent_of(c, p)))));
	
	person_e max{o, "Max Mustermann"};
	person_e erika{o, "Erika Mustermann"};
	o.add_axiom(preds::parent_of(max, erika));

	soop::variable<'s'> s;
	const auto& parent = std::get<0>(o.request_entities<person_e>(
		exists({c}, parent_of(s, c)), s));
	std::cout << parent->name << " is a parent.\n";
}
