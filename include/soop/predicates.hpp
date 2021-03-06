
#ifndef SOOP_PREDICATES_HPP
#define SOOP_PREDICATES_HPP

#include <cstddef>
#include <string>
#include <memory>
#include <sstream>
#include <iterator>
#include <iostream>
#include <typeindex>
#include <limits>

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
	const std::vector<std::size_t> entity_ids() const {return m_args;}

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


///// Bound Entities

struct bound_entity {
	bound_entity(const entity& e) : id{e.id()} {}
	void stream(std::ostream& out, const std::vector<std::string>& names) const;
	std::size_t id; // before collection: id of the entity, after: argument_index
};

void collect_entity(std::vector<std::size_t>& ids, bound_entity& v);

///// Bound Types

class bound_type {
public:
	bound_type(const std::type_info& info) : m_type{info} {}
	void stream(std::ostream& out, const std::vector<std::string>&) const;

private:
	std::type_index m_type;
};

template <typename T>
static auto type = bound_type{typeid(T)};

inline void collect_entity(std::vector<std::size_t>&, const bound_type&) {}


///// Variables

namespace impl{
template<char...Str>
struct not_reserved: std::true_type{};
template<char...Tail>
struct not_reserved<'o', '_', Tail...>: std::false_type{};
} // namespace impl

template <char... Name>
struct variable {
	static_assert(impl::not_reserved<Name...>::value,
			"only unreserved names may be used for variables");
	static std::string str() { return {Name...}; }
	static void stream(std::ostream& out, const std::vector<std::string>&) { out << str(); }
};

template <char... Name>
void collect_entity(std::vector<std::size_t>&, variable<Name...>) {}

// bound variables (for quantors):

class bound_vars {
public:
	template <typename... Args>
	bound_vars(Args... args);
	const std::string& str() const { return m_str; }

private:
	std::string m_str;
};

///// Predicates

// Inheriting from is_predicate is a necessary bot not a sufficient
// thing for predicates to do.
struct is_predicate {};

namespace impl {
constexpr void require_predicate(const is_predicate&); // not defined
} // namespace impl

// this will call pred.collect_entities(ids), meaning
// that that function must be implemented
template <typename T>
auto collect_entity(std::vector<std::size_t>& ids, T& pred)
        -> decltype(impl::require_predicate(pred));

// not shown, but required nonetheless: pred.stream(out, names)


// tag-type: Every predicate that is instantiated with this, should provide it's name
// and it's rank via static methods without creating errors
//
// it is however acceptable to create a stand-in that provides the information,
// should it be impossible to do directly in a good way.
struct get_meta_information {};

///// Predicate Helpers:

template <template <typename...> class Self, typename... Args>
struct basic_predicate : is_predicate {
	basic_predicate(Args... args) : args{std::move(args)...} {}
	using self = Self<Args...>;
	void collect_entities(std::vector<std::size_t>& ids);
	void stream(std::ostream& out, const std::vector<std::string>& names) const;
	std::tuple<Args...> args;
};

template <typename T>
using to_bound_type =
        std::conditional_t<std::is_base_of<entity, T>{}, bound_entity, std::decay_t<T>>;

template <template <typename...> class Pred, typename... Args>
auto make_pred(const Args&... args) {
	return Pred<to_bound_type<Args>...>{args...};
}

namespace impl {

template <typename>
struct base_basic_predicate;

template <template <typename...> class Template, typename... Args>
struct base_basic_predicate<Template<Args...>> {
	using type = basic_predicate<Template, Args...>;
};

template <typename T>
using base_basic_predicate_t = typename base_basic_predicate<T>::type;

} // namespace impl

static constexpr auto variadic_rank = std::numeric_limits<std::size_t>::max();

#define SOOP_MAKE_RENAMED_TYPECHECKED_PREDICATE(Identifier, Name, Rank, ...)                       \
	namespace preds {                                                                          \
	template <typename... Args>                                                                \
	struct Identifier##_t : ::soop::basic_predicate<Identifier##_t, Args...> {                 \
		Identifier##_t(Args... args)                                                       \
		        : ::soop::impl::base_basic_predicate_t<Identifier##_t>{                    \
		                  std::move(args)...} {}                                           \
		static std::string name() { return Name; }                                         \
		constexpr static std::size_t rank() { return (Rank); }                             \
		static_assert((sizeof...(Args) == (Rank)) or ((Rank) == ::soop::variadic_rank),    \
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



///// Utility-functions for the implementation:
// these functions may be used by users of the library, which is why they are
// not part of the impl-namespace

// adding entities
template <typename... Ts>
void collect_entities(std::vector<std::size_t>& ids, std::tuple<Ts...>& args);

// streaming entities
template <typename... Args>
void stream(std::ostream& s, const std::vector<std::string>& args, const std::string& name,
            const std::tuple<Args...>& tuple);

/////////////////////////////////////////////////////////////
//             Implementation of templates
/////////////////////////////////////////////////////////////

template <typename P>
formula::formula(P p) {
	p.collect_entities(m_args);
	m_formula = std::make_unique<concrete_formula<P>>(std::move(p));
}

template <typename P>
void formula::concrete_formula<P>::stream(std::ostream& s,
                                          const std::vector<std::string>& args) const {
	m_pred.stream(s, args);
}

template <typename T>
auto collect_entity(std::vector<std::size_t>& ids, T& pred)
        -> decltype(impl::require_predicate(pred)) {
	pred.collect_entities(ids);
}

template <typename... Ts>
void collect_entities(std::vector<std::size_t>& ids, std::tuple<Ts...>& args) {
	tuple_foreach(args, [&](auto& arg) { collect_entity(ids, arg); });
}

///////////////// streaming entities
template <typename... Args>
void stream(std::ostream& s, const std::vector<std::string>& args, const std::string& name,
            const std::tuple<Args...>& tuple) {
	s << '(' << name << ' ';
	tuple_foreach(tuple, [&](const auto& arg) {
		arg.stream(s, args);
		s << ' ';
	});
	s << ')';
}

template <template <typename...> class Self, typename... Args>
void basic_predicate<Self, Args...>::collect_entities(std::vector<std::size_t>& ids) {
	soop::collect_entities(ids, args);
}
template <template <typename...> class Self, typename... Args>
void basic_predicate<Self, Args...>::stream(std::ostream& out,
                                            const std::vector<std::string>& names) const {
	soop::stream(out, names, self::name(), args);
}

template <typename... Args>
bound_vars::bound_vars(Args... args) {
	static_assert(sizeof...(Args) > 0, "");
	m_str = "(";
	tuple_foreach(std::tie(args...), [&](const auto& arg) {
		m_str += "(";
		m_str += arg.str();
		m_str += " Entity) ";
	});
	m_str += ')';
}

} // namespace soop

#endif
