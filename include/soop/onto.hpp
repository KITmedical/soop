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
//////////////////////////// forall

template <typename Pred>
struct forall_t {
	forall_t(bound_vars vars, Pred pred) : vars{std::move(vars)}, pred{std::move(pred)} {}
	void collect_entities(std::vector<std::size_t>& ids, std::size_t& next_index) {
		collect_entity(ids, next_index, pred);
	}
	void stream(std::ostream& out, const std::vector<std::string>& names) const {
		out << "forall(" << vars.str() << ", ";
		pred.stream(out, names);
		out << ')';
	}
	bound_vars vars;
	Pred pred;
};

template <typename Pred>
auto forall(bound_vars vars, Pred p) {
	return forall_t<Pred>{std::move(vars), p};
}

//////////////////////////// exists

template <typename Pred>
struct exists_t {
	exists_t(bound_vars vars, Pred pred) : vars{std::move(vars)}, pred{std::move(pred)} {}
	void collect_entities(std::vector<std::size_t>& ids, std::size_t& next_index) {
		collect_entity(ids, next_index, pred);
	}
	void stream(std::ostream& out, const std::vector<std::string>& names) const {
		out << "exists(" << vars.str() << ", ";
		pred.stream(out, names);
		out << ')';
	}
	bound_vars vars;
	Pred pred;
};

template <typename Pred>
auto exists(bound_vars vars, Pred p) {
	return exists_t<Pred>{std::move(vars), p};
}

}

template<typename... Types>
struct type_list_t{};
template<typename... Types>
type_list_t<Types...> type_list;

template<template<typename...>class... Preds>
class pred_list{
};

using axiom_list = std::initializer_list<std::string>;

class ontology {
public:
	ontology();
	template <typename... Ts, template<typename...>class... Ps>
	ontology(type_list_t<Ts...>, pred_list<Ps...> ps, axiom_list as = {});

	std::size_t add_axiom(const formula& axiom);
	void delete_axiom(std::size_t index);

	std::size_t add_entity(entity& e);
	std::size_t add_entity(entity& e, const std::type_info&);

	void delete_entity(std::size_t id);

	template <typename T>
	void add_type();
	bool request(const formula& conjecture) const;

	void reseat_entity(std::size_t id, const entity& e);

	template<template<typename...>class P>
	std::size_t add_predicate();
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

template <typename... Ts, template<typename...>class ... Ps>
ontology::ontology(type_list_t<Ts...>, pred_list<Ps...>, axiom_list as):
	m_axioms{as}
{
	using ignore = std::initializer_list<int>;
	(void) ignore{ (add_type<Ts>(),0)... };
	(void) ignore{ (add_predicate<Ps>(),0)... };
	//add_predicate<preds::instance_of>();
	//explode_tuple([&](const auto& p){add_predicate(p);}, ps.values);
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

template<template<typename...>class P>
std::size_t ontology::add_predicate() {
	//m_names[p.id()] = p.name();
	//return p.id();
	return 0;
}

} // namespace soop
