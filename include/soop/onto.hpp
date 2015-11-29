#pragma once

#include <string>
#include <typeinfo>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "predicates.hpp"
#include "entity.hpp"

namespace soop {

SOOP_MAKE_PREDICATE(equal, 2)
SOOP_MAKE_PREDICATE(instance_of, 2)
SOOP_MAKE_PREDICATE(implies, 2)
SOOP_MAKE_RENAMED_PREDICATE(or_, "or", 2)
SOOP_MAKE_RENAMED_PREDICATE(and_, "and", 2)
SOOP_MAKE_RENAMED_PREDICATE(not_, "not", 1)

class ontology {
public:
	template <typename... Ps>
	ontology(const Ps&... predicates);

	std::size_t add_axiom(std::string axiom);
	void delete_axiom(std::size_t index);

	std::size_t add_entity(entity& e);

	template <typename T>
	void add_type();
	bool request(const std::string& conjecture) const;

private:
	std::string types() const;
	std::string entities() const;
	std::string predicates() const;
	std::string axioms() const;

	std::unordered_map<std::size_t, std::string> m_names;
	std::vector<std::string> m_axioms;
	std::vector<std::pair<const entity*, std::vector<std::size_t>>> m_entities;
	std::unordered_set<std::string> m_known_types;
};

/////////////////////////////////////////////////////////////
//             Implementation of templates
/////////////////////////////////////////////////////////////

template <typename... Ps>
ontology::ontology(const Ps&... predicates)
        : m_names{{preds::instance_of.id(), preds::instance_of.name()},
                  {predicates.id(), predicates.name()}...} {}

template <typename T>
void ontology::add_type() {
	auto name = std::string{typeid(T).name()};
	if (m_known_types.count(name)) {
		// TODO: customn exception:
		throw std::invalid_argument{"type already known"};
	}
	m_known_types.insert(std::move(name));
}

} // namespace soop
