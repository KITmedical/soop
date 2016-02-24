#ifndef SOOP_ONTO_HPP
#define SOOP_ONTO_HPP

#include <string>
#include <typeinfo>
#include <unordered_set>
#include <vector>

#include "predicates.hpp"
#include "entity.hpp"
#include "buildin_predicates.hpp"

namespace soop {

template<typename... Types>
struct type_list_t{};
template<typename... Types>
type_list_t<Types...> type_list;

template<template<typename...>class... Preds>
class pred_list{};

using axiom_list = std::vector<formula>;

struct not_found_error: std::runtime_error {
	using std::runtime_error::runtime_error;
};

class ontology {
public:
	ontology();
	template <typename... Ts, template<typename...>class... Ps>
	ontology(type_list_t<Ts...>, pred_list<Ps...> ps, axiom_list as = {});

	std::size_t add_axiom(formula axiom);
	void delete_axiom(std::size_t index);

	std::size_t add_entity(entity& e);
	std::size_t add_entity(entity& e, const std::type_info&);

	void delete_entity(std::size_t id);

	template <typename T>
	void add_type();
	bool request(const formula& conjecture) const;

	std::vector<const entity*> request_entities_ptr(const formula& description, const std::vector<std::string>& result_names) const;

	template<typename...Ts, typename... Vars>
	std::tuple<const Ts&...> request_entities(const formula& description, Vars...) const;

	bool check_sat() const;

	void reseat_entity(std::size_t id, const entity& e);

	template<template<typename...>class P>
	void add_predicate();
private:
	template<typename...Ts, typename... Vars, std::size_t...Is>
	std::tuple<const Ts&...> request_entities_impl(const formula& description, std::index_sequence<Is...>, Vars...) const;
	std::string types() const;
	std::string entities() const;
	std::string predicates() const;
	std::string axioms() const;
	std::string entity_ids() const;

	axiom_list m_axioms;
	std::vector<std::pair<const entity*, std::vector<std::size_t>>> m_entities;
	std::unordered_set<std::string> m_known_types;
	std::vector<std::pair<std::string, std::size_t>> m_predicates;
};

struct already_known_error: std::invalid_argument {
	using std::invalid_argument::invalid_argument;
};

/////////////////////////////////////////////////////////////
//             Implementation of templates
/////////////////////////////////////////////////////////////

template <typename... Ts, template<typename...>class ... Ps>
ontology::ontology(type_list_t<Ts...>, pred_list<Ps...>, axiom_list as):
	m_axioms(std::move(as))
{
	using ignore = std::initializer_list<int>;
	(void) ignore{ (add_type<Ts>(),0)... };
	add_predicate<preds::instance_of_t>();
	(void) ignore{ (add_predicate<Ps>(),0)... };
}

template <typename T>
void ontology::add_type() {
	auto name = std::string{typeid(T).name()};
	if (m_known_types.count(name)) {
		throw already_known_error{"type already known"};
	}
	m_known_types.insert(std::move(name));
}

template<typename...Ts, typename... Vars, std::size_t...Is>
std::tuple<const Ts&...> ontology::request_entities_impl(const formula& description, std::index_sequence<Is...>, Vars... vars) const {
	const auto ids = request_entities_ptr(description, {vars.str()...});
	if (std::any_of(ids.begin(), ids.end(), [](auto ptr){return not ptr;})) {
		throw not_found_error{"some or all of the subrequests did not have a solution"};
	}
	return std::tie((dynamic_cast<const Ts&>(*ids.at(Is)))...);
}
template<typename...Ts, typename... Vars>
std::tuple<const Ts&...> ontology::request_entities(const formula& description, Vars... vars) const {
	return request_entities_impl<Ts...>(description, std::make_index_sequence<sizeof...(Vars)>{}, vars...);
}



template<template<typename...>class P>
void ontology::add_predicate() {
	using Pred = P<get_meta_information>;
	m_predicates.emplace_back(Pred::name(), Pred::rank());
}

} // namespace soop

#endif // SOOP_ONTO_HPP
