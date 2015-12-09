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

namespace preds {
std::string exists(std::initializer_list<const char*> vars, const std::string& p);
std::string forall(std::initializer_list<const char*> vars, const std::string& p);
}

template<typename... Types>
struct type_list{};

template<typename... Preds>
class pred_list_t{
public:
	pred_list_t(Preds... preds): values{std::move(preds)...} {}
	std::tuple<Preds...> values;
};
template<typename... Preds>
pred_list_t<Preds...> pred_list(Preds... preds) {
	return {std::move(preds)...};
}

using axiom_list = std::initializer_list<std::string>;

class ontology {
public:
	ontology();
	template <typename... Ts, typename... Ps>
	ontology(type_list<Ts...>, const pred_list_t<Ps...>& ps, axiom_list as = {});

	std::size_t add_axiom(std::string axiom);
	void delete_axiom(std::size_t index);

	std::size_t add_entity(entity& e);
	std::size_t add_entity(entity& e, const std::type_info&);

	void delete_entity(std::size_t id);

	template <typename T>
	void add_type();
	bool request(const std::string& conjecture) const;

	void reseat_entity(std::size_t id, const entity& e);

	template<typename P>
	std::size_t add_predicate(const P& p);
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

template <typename... Ts, typename... Ps>
ontology::ontology(type_list<Ts...>, const pred_list_t<Ps...>& ps, axiom_list as):
	m_axioms{as}
{
	using ignore = std::initializer_list<int>;
	(void) ignore{ (add_type<Ts>(),0)... };
	add_predicate(preds::instance_of);
	explode_tuple([&](const auto& p){add_predicate(p);}, ps.values);
}

template <typename T>
void ontology::add_type() {
	auto name = std::string{typeid(T).name()};
	if (m_known_types.count(name)) {
		// TODO: customn exception:
		throw std::invalid_argument{"type already known"};
	}
	m_known_types.insert(std::move(name));
}

template<typename P>
std::size_t ontology::add_predicate(const P& p) {
	m_names[p.id()] = p.name();
	return p.id();
}

} // namespace soop
