#ifndef PROBLEM_HPP
#define PROBLEM_HPP

#include <string>
#include <vector>
#include <unordered_map>
#include <utility>

#include "primitives.hpp"
#include "relation.hpp"

template<typename F>
using fun_ptr = F*;

using int_lst = std::initializer_list<int>;

template<typename...Args>
std::string rel_string_id(fun_ptr<bool(Args...)> f) {
	return "dynamic_relation_" + std::to_string(reinterpret_cast<std::size_t>(f));
}

template<typename Functions, typename Predicates, typename Axioms>
struct problem {
	template<typename...>
	static constexpr bool false_fun() {return false;}
	static_assert(false_fun<Functions, Predicates, Axioms>(),
			"problem must receive `functions`, `predicates` and `formulae` as "
			"template arguments.");
};

class basic_problem;

class entity {
public:
	entity(basic_problem& p);
	entity(entity&& other) noexcept;
	entity(const entity& other);
	entity& operator=(entity&& other) noexcept;
	entity& operator=(const entity& other) noexcept;
	virtual ~entity();
	virtual std::string instance_of() const = 0;
	std::string entity_id_name() const {
		return "dynamic_object_" + std::to_string(m_id);
	}
	std::size_t id() const {
		return m_id;
	}
	basic_problem* problem() const {return m_prob;}
private:
	std::size_t m_id = static_cast<std::size_t>(-1);
	basic_problem* m_prob = nullptr;
	friend class basic_problem;
};

class basic_problem {
public:

	void add(entity& e);
	void clone(entity& e, std::size_t orig_id);
	virtual bool request(const std::string&) const = 0;
	void reseat_entity(std::size_t id, const entity&);
	void remove_entity(std::size_t id);

	template<typename...Args>
	void add_relation(fun_ptr<bool(Args...)> p) {
		const auto id = reinterpret_cast<std::size_t>(p);
		m_dynamic_relations.emplace(std::make_pair(id, sizeof...(Args)));
		m_known_relations.emplace(std::make_pair(id, std::initializer_list<std::size_t>{}));
	}
	template<typename... FArgs, typename...Args>
	void declare_satifies(const fun_ptr<bool(FArgs...)> rel, Args&&... args) {
		static_assert(std::is_same<bool, decltype(rel(std::forward<Args>(args)...))>::value, "invalid arguments to relation");
		const auto axiom_id = m_dynamic_axioms.size();
		m_dynamic_axioms.push_back({reinterpret_cast<std::size_t>(rel), (args.id())...});
		(void) int_lst{ ((m_known_relations[args.id()].push_back(axiom_id)),0)... };
	}
	template<typename... FArgs, typename...Args>
	bool request_satisfication(const fun_ptr<bool(FArgs...)> rel, Args&&... args) {
		return request( "formula(" + rel_string_id(rel) + "(" + entity_join(args...) + ")).\n" );
	}
protected:
	std::string dyn_fun_list() const;
	std::string dyn_rel_list() const;
	std::string dyn_axiom_list() const;
private:
	std::unordered_map<std::size_t, std::size_t> m_dynamic_relations;
	std::vector<const entity*> m_entities;
	std::vector<std::vector<std::size_t>> m_dynamic_axioms;
	std::unordered_map<std::size_t, std::vector<std::size_t>> m_known_relations;
};

template<typename... Functions, typename... Predicates, typename... Axioms>
struct problem<
	functions<Functions...>,
	predicates<Predicates...>,
	formulae<Axioms...>>
	: basic_problem
{
	template<typename Conjecture>
	bool request(formula<Conjecture>) const {
		return request(formula<Conjecture>::to_string());
	}
	bool request(const std::string& conjecture) const override final {
		const auto p =
			"begin_problem(prob).\n"

			"list_of_descriptions.\n"
			"name({**}).\n"
			"author({**}).\n"
			"status(unsatisfiable).\n"
			"description({**}).\n"
			"end_of_list.\n"

			"list_of_symbols.\n"
			"functions["
			+ functions<Functions...>::to_string() + ",\n"
			+ dyn_fun_list() +
			"].\n"
			"predicates[\n"
			+ predicates<Predicates...>::to_string() + ",\n"
			+ dyn_rel_list() +
			"].\n"
			"end_of_list.\n"

			"list_of_formulae(axioms).\n"
			+ formulae<Axioms...>::to_string()
			+ dyn_axiom_list() +
			"end_of_list.\n"

			"list_of_formulae(conjectures).\n"
			+ conjecture +
			"end_of_list.\n"

			"end_problem.\n\n";
		//std::cout << p;
		return try_proof(p);
	}
};

template<typename T>
struct type_name_helper {
	static std::string get() {
		return T::name();
	}
};

template<typename T>
class e : public entity {
public:
	template<typename...Args>
	e(basic_problem& p, Args&&... args): entity{p}, m_value{std::forward<Args>(args)...} {}
	T& operator*() {return m_value;}
	const T& operator*() const {return m_value;}
	T* operator->() {return &m_value;}
	const T* operator->() const {return &m_value;}

	std::string instance_of() const override {
		return type_name_helper<T>::get();
	}
private:
	T m_value;
};

#endif

