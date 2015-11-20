#ifndef PROBLEM_HPP
#define PROBLEM_HPP

#include <string>
#include <vector>
#include <unordered_map>
#include <utility>
#include <typeindex>

#include "primitives.hpp"
#include "free_vars.hpp"

namespace soop {


template<typename Functions, typename Predicates, typename Axioms>
struct problem;

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
	template<typename Rel, typename...Args>
	void declare_satifies(const Rel rel, Args&&... args) {
		//static_assert(std::is_same<bool, decltype(rel(std::forward<Args>(args)...))>::value, "invalid arguments to relation");
		const auto axiom_id = m_dynamic_axioms.size();
		m_dynamic_axioms.push_back({rel_id(rel), (args.id())...});
		(void) ignore{ ((m_known_relations[args.id()].push_back(axiom_id)),0)... };
	}
	template<typename Rel, typename...Args>
	bool request_satisfication(const Rel rel, Args&&... args) {
		return request_satisfication_impl(std::integral_constant<bool, has_free_var<Args...>()>{},
			rel_string_id(rel), std::forward<Args>(args)...);
	}
	std::string get_name_of(std::type_index index) const { return m_type_names.at(index); }
protected:
	std::string dyn_fun_list() const;
	std::string dyn_rel_list() const;
	std::string dyn_axiom_list() const;

	std::unordered_map<std::type_index, std::string> m_type_names;
private:
	template<typename... FArgs, typename...Args>
	bool request_satisfication_impl(std::false_type, const std::string& rel, Args&&... args) {
		return request( "formula(" + rel + "(" + entity_join(args...) + ")).\n" );
	}
	template<typename... FArgs, typename...Args>
	bool request_satisfication_impl(std::true_type, const std::string& rel, Args&&... args) {
		return request( "formula(exists(" + get_var_list<Args...>::to_string() +", " + rel + "(" + entity_join(args...) + "))).\n" );
	}
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
	problem() {
		(void) ignore{
			(m_type_names.emplace(std::make_pair(Functions::type_index(), Functions::name())
			),0)...};
	}
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
			+ predicates<predicate<instance>, Predicates...>::to_string() + ",\n"
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
class e : public entity {
public:
	template<typename...Args>
	e(basic_problem& p, Args&&... args): entity{p}, m_value{std::forward<Args>(args)...} {}
	T& operator*() {return m_value;}
	const T& operator*() const {return m_value;}
	T* operator->() {return &m_value;}
	const T* operator->() const {return &m_value;}

	std::string instance_of() const override {
		if (not this->problem()) {
			throw std::logic_error{"instance_of can only be called on entities that are part of a relation"};
		}
		return this->problem()->get_name_of(std::type_index{typeid(T)});
	}
private:
	T m_value;
};


} // namespace soop

#endif

