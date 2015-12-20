
#ifndef SOOP_PREDICATES_HPP
#define SOOP_PREDICATES_HPP

#include <cstddef>
#include <string>
#include <memory>
#include <sstream>
#include <iterator>
#include <iostream>
#include <typeindex>

#include "entity.hpp"
#include "type_checking.hpp"
#include "util.hpp"

namespace soop {

class formula {
public:
	formula() = default;

	template <typename P>
	formula(P p);

	std::string to_string() const;

	explicit operator bool() const { return m_formula != nullptr; }

private:
	class basic_formula {
	public:
		virtual ~basic_formula() {}
		virtual void stream(std::ostream&, const std::vector<std::string>&) const = 0;
	};
	template <typename P>
	class concrete_formula : public basic_formula {
	public:
		concrete_formula(P p) : m_pred{std::move(p)} {}

		void stream(std::ostream& s,
		            const std::vector<std::string>& args) const final override;

	private:
		P m_pred;
	};

	std::unique_ptr<basic_formula> m_formula;
	std::vector<std::size_t> m_args;
};

struct bound_entity {
	bound_entity(const entity& e) : id{e.id()} {}
	void stream(std::ostream& out, const std::vector<std::string>& names) const;
	std::size_t id; // before collection: id of the entity, after: argument_index
};

template <typename T>
struct bound_type {
	void stream(std::ostream& out, const std::vector<std::string>&) const;
};
template <typename T>
static auto type = bound_type<T>{};

class dyn_type {
public:
	dyn_type(const std::type_info& info) : m_type{info} {}
	void stream(std::ostream& out, const std::vector<std::string>&) const;

private:
	std::type_index m_type;
};

template <char... Name>
struct variable {
	static std::string str() { return {Name...}; }
	static void stream(std::ostream& out, const std::vector<std::string>&) { out << str(); }
};

template <typename T>
using to_bound_type =
        std::conditional_t<std::is_base_of<entity, T>{}, bound_entity, std::remove_const_t<T>>;

///////////////// adding entities
void collect_entity(std::vector<std::size_t>& ids, std::size_t& next_index, bound_entity& v);

template <char... Name>
void collect_entity(std::vector<std::size_t>&, std::size_t&, variable<Name...>) {}

template <typename T>
void collect_entity(std::vector<std::size_t>&, std::size_t&, bound_type<T>) {}

inline void collect_entity(std::vector<std::size_t>&, std::size_t&, const dyn_type&) {}

struct is_predicate {};
constexpr void require_predicate(const is_predicate&) {}

template <typename T>
auto collect_entity(std::vector<std::size_t>& ids, std::size_t& next_index, T& pred)
        -> decltype(require_predicate(pred));

template <typename... Ts>
void collect_entities(std::vector<std::size_t>& ids, std::size_t& next_index,
                      std::tuple<Ts...>& args);

///////////////// streaming entities
template <typename... Args>
void stream(std::ostream& s, const std::vector<std::string>& args, const std::string& name,
            const std::tuple<Args...>& tuple);

template <template <typename...> class Self, typename... Args>
struct basic_predicate : is_predicate {
	basic_predicate(Args... args) : args{std::move(args)...} {}
	using self = Self<Args...>;
	void collect_entities(std::vector<std::size_t>& ids, std::size_t& next_index);
	void stream(std::ostream& out, const std::vector<std::string>& names) const;
	std::tuple<Args...> args;
};

template <template <typename...> class Pred, typename... Args>
auto make_pred(const Args&... args) {
	return Pred<to_bound_type<Args>...>{args...};
}

class bound_vars {
public:
	template <typename... Args>
	bound_vars(Args... args);
	const std::string& str() const { return m_str; }

private:
	std::string m_str;
};

namespace impl {

template <typename>
struct base_basic_predicate;

template <template <typename...> class Template, typename... Args>
struct base_basic_predicate<Template<Args...>> {
	using type = basic_predicate<Template, Args...>;
};

template <typename T>
using base_basic_predicate_t = typename base_basic_predicate<T>::type;
}

struct get_meta_information {};

#define SOOP_MAKE_RENAMED_TYPECHECKED_PREDICATE(Identifier, Name, Rank, ...)                       \
	namespace preds {                                                                          \
	template <typename... Args>                                                                \
	struct Identifier##_t : ::soop::basic_predicate<Identifier##_t, Args...> {                 \
		Identifier##_t(Args... args)                                                       \
		        : ::soop::impl::base_basic_predicate_t<Identifier##_t>{                    \
		                  std::move(args)...} {}                                           \
		static std::string name() { return Name; }                                         \
		constexpr static std::size_t rank() { return (Rank); }                             \
		static_assert(sizeof...(Args) == (Rank),                                           \
		              "Invalid number of arguments to predicate");                         \
	};                                                                                         \
	template <>                                                                                \
	struct Identifier##_t<::soop::get_meta_information> {                                      \
		static std::string name() { return Name; }                                         \
		constexpr static std::size_t rank() { return (Rank); }                             \
	};                                                                                         \
                                                                                                   \
	template <typename... Args>                                                                \
	auto Identifier(const Args&... args) {                                                     \
		::soop::impl::require_valid_types(::soop::impl::actual_types_list<Args...>{},      \
		                                  ::soop::allowed_types_list<__VA_ARGS__>{});      \
		return ::soop::make_pred<Identifier##_t>(args...);                                 \
	}                                                                                          \
	}

#define SOOP_MAKE_RENAMED_PREDICATE(Identifier, Name, Rank)                                        \
	SOOP_MAKE_RENAMED_TYPECHECKED_PREDICATE(Identifier, Name, Rank, void)
#define SOOP_MAKE_TYPECHECKED_PREDICATE(Identifier, Rank, ...)                                     \
	SOOP_MAKE_RENAMED_TYPECHECKED_PREDICATE(Identifier, #Identifier, Rank, __VA_ARGS__)
#define SOOP_MAKE_PREDICATE(Identifier, Rank)                                                      \
	SOOP_MAKE_RENAMED_TYPECHECKED_PREDICATE(Identifier, #Identifier, Rank, void)

/////////////////////////////////////////////////////////////
//             Implementation of templates
/////////////////////////////////////////////////////////////

template <typename P>
formula::formula(P p) {
	auto index = std::size_t{};
	p.collect_entities(m_args, index);
	m_formula = std::make_unique<concrete_formula<P>>(std::move(p));
}

template <typename P>
void formula::concrete_formula<P>::stream(std::ostream& s,
                                          const std::vector<std::string>& args) const {
	m_pred.stream(s, args);
}

template <typename T>
void bound_type<T>::stream(std::ostream& out, const std::vector<std::string>&) const {
	out << typeid(T).name();
}

template <typename T>
auto collect_entity(std::vector<std::size_t>& ids, std::size_t& next_index, T& pred)
        -> decltype(require_predicate(pred)) {
	pred.collect_entities(ids, next_index);
}

template <typename... Ts>
void collect_entities(std::vector<std::size_t>& ids, std::size_t& next_index,
                      std::tuple<Ts...>& args) {
	tuple_foreach(args, [&](auto& arg) { collect_entity(ids, next_index, arg); });
}

///////////////// streaming entities
template <typename... Args>
void stream(std::ostream& s, const std::vector<std::string>& args, const std::string& name,
            const std::tuple<Args...>& tuple) {
	s << name << '(';
	indexed_tuple_foreach(tuple, [&](const auto& arg, std::size_t index) {
		if (index) {
			s << ", ";
		}
		arg.stream(s, args);
	});
	s << ')';
}

template <template <typename...> class Self, typename... Args>
void basic_predicate<Self, Args...>::collect_entities(std::vector<std::size_t>& ids,
                                                      std::size_t& next_index) {
	soop::collect_entities(ids, next_index, args);
}
template <template <typename...> class Self, typename... Args>
void basic_predicate<Self, Args...>::stream(std::ostream& out,
                                            const std::vector<std::string>& names) const {
	soop::stream(out, names, self::name(), args);
}

template <typename... Args>
bound_vars::bound_vars(Args... args) {
	static_assert(sizeof...(Args) > 0, "");
	m_str = "[";
	indexed_tuple_foreach(std::tie(args...), [&](const auto& arg, std::size_t i) {
		if (i) {
			m_str += ", ";
		}
		m_str += arg.str();
	});
	m_str += ']';
}

} // namespace soop

#endif
