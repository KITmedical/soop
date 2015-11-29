#pragma once

#include <unordered_map>
#include <algorithm>
#include <iterator>
#include <string>
#include <vector>

#include "predicates.hpp"


namespace soop {

SOOP_MAKE_PREDICATE(equal, 2);
SOOP_MAKE_PREDICATE(instance_of, 2);
SOOP_MAKE_RENAMED_PREDICATE(or_, "or", 2);
SOOP_MAKE_RENAMED_PREDICATE(and_, "and", 2);

class ontology {
public:
	template <typename... Ps>
	ontology(const Ps&... predicates);

	template <typename P, typename... Args>
	std::size_t add_axiom(P pred, const Args&... args);

	void delete_axiom(std::size_t index);
	std::size_t add_preprocessed_axiom(std::string axiom);
	void delete_preprocessed_axiom(std::size_t index);

	std::string axioms() const;

private:
	std::unordered_map<std::size_t, std::string> m_names;
	std::vector<std::vector<std::size_t>> m_axioms;
	std::vector<std::string> m_preprocessed_axioms;
};

/////////////////////////////////////////////////////////////
//             Implementation of templates
/////////////////////////////////////////////////////////////


template <typename... Ps>
ontology::ontology(const Ps&... predicates)
        : m_names{{preds::instance_of.id(), preds::instance_of.name()},
                  {predicates.id(), predicates.name()}...} {}

template <typename P, typename... Args>
std::size_t ontology::add_axiom(P pred, const Args&... args) {
	static_assert(pred.rank() == sizeof...(Args), "");
	m_axioms.push_back({pred.id(), args...});
	return m_axioms.size() - 1u;
}

} // namespace soop
