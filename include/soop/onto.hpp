#pragma once

#include <string>
#include <typeinfo>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "predicates.hpp"
#include "entity.hpp"

namespace soop {

SOOP_MAKE_RENAMED_PREDICATE(equal, "=", 2)
SOOP_MAKE_PREDICATE(instance_of, 2)
SOOP_MAKE_PREDICATE(implies, 2)
SOOP_MAKE_PREDICATE(distinct, variadic_rank)
SOOP_MAKE_RENAMED_PREDICATE(or_, "or", variadic_rank)
SOOP_MAKE_RENAMED_PREDICATE(and_, "and", variadic_rank)
SOOP_MAKE_RENAMED_PREDICATE(not_, "not", 1)

namespace preds {
class distinct_range_t: public soop::is_predicate {
public:
	template<typename Iterator>
	distinct_range_t(Iterator begin, Iterator end) {
		for(auto it= begin; it != end; ++it) {
			m_entities.emplace_back(it->id());
		}
	}
	void collect_entities(std::vector<std::size_t>&);
	void stream(std::ostream& out, const std::vector<std::string>& names) const;
private:
	std::vector<std::size_t> m_entities;
};

template<typename Iterator>
distinct_range_t distinct_range(Iterator first, Iterator last) {
	return distinct_range_t{first, last};
}
} // namespace preds


namespace preds {
//////////////////////////// forall

template <typename Pred>
struct forall_t : is_predicate {
	forall_t(bound_vars vars, Pred pred) : vars{std::move(vars)}, pred{std::move(pred)} {}
	void collect_entities(std::vector<std::size_t>& ids) {
		collect_entity(ids, pred);
	}
	void stream(std::ostream& out, const std::vector<std::string>& names) const {
		out << "(forall " << vars.str() << " ";
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
struct exists_t : is_predicate{
	exists_t(bound_vars vars, Pred pred) : vars{std::move(vars)}, pred{std::move(pred)} {}
	void collect_entities(std::vector<std::size_t>& ids) {
		collect_entity(ids, pred);
	}
	void stream(std::ostream& out, const std::vector<std::string>& names) const {
		out << "(exists " << vars.str() << " ";
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

	struct hash_first {
		std::size_t operator()(const std::pair<std::string, std::size_t>& p) const {
			return std::hash<std::string>{}(p.first);
		}
	};

	std::vector<formula> m_axioms;
	std::vector<std::pair<const entity*, std::vector<std::size_t>>> m_entities;
	std::unordered_set<std::string> m_known_types;
	std::vector<std::pair<std::string, std::size_t>> m_predicate_names;
};

class already_known_error: public std::invalid_argument {
public:
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
	m_predicate_names.emplace_back(Pred::name(), Pred::rank());
}

} // namespace soop
