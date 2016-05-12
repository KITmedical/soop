
SOOP - Semantic ObjectOriented Programming
==========================================

SOOP is a library that combines the worlds of traditional object-oriented
programming and semantic ontologies. Unlike every other library out there,
it does this not by mapping ontological data into the OOP-language, but by
mapping the OOP-data into the ontology.

By implementing this in C++ we had many tools at our hands that allowed the
creation of a great API, that is very close to normal predicate-logic
without feeling foreign in C++. To demonstrate this, consider the following
working code:


```cpp
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
```

This will print: “`Max Mustermann is a parent.`”

While some details, like the need to define semantic variables before using
them in quantors, are still not perfect, we believe that this is a great
step forward from existing approaches.

Publications
============

* A very detailed description of this project can be found in the
  original [Bachelors thesis](http://florianjw.de/ba/soop.pdf) (German) by Florian Weber.
* We are currently preparing a paper for a
  [workshop at the Informatik 2016-conference](http://informatik2016.de/1171.html)

License
-------

For now LGPLv2 or, at your option, any later version of the LGPL.

