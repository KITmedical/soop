
#ifndef SOOP_FREE_VARS_HPP
#define SOOP_FREE_VARS_HPP

#include <string>
#include <type_traits>

#include "primitives.hpp"

template <char... String>
struct var {
	static std::string to_string() { return std::string{String...}; }
	static std::string name() {return to_string();}
	static unsigned rank() {return 0;}

	static std::string entity_id_name() {return to_string(); }

	template<typename T>
	operator T() const; // declare but never define: This is intended to
	// be used by the type-checker, not by the programmer
};

using v = var<'v'>;
using w = var<'w'>;
using x = var<'x'>;
using y = var<'y'>;
using z = var<'z'>;

inline constexpr bool any_of(std::initializer_list<bool> lst) {
	for(bool b: lst) {
		if (b) return true;
	}
	return false;
}

template<typename T> struct is_var: std::false_type{};
template<char... Name> struct is_var<var<Name...>>: std::true_type{};


template<typename... Ts>
constexpr bool has_free_var() {
	return any_of({is_var<Ts>::value...});
};

template<typename...Vars>
struct var_list{
	static std::string to_string() {
		return "[" + join<Vars...>() + "]";
	}
};

namespace impl {

template<typename, typename> struct add_var{};

template<typename... Vars, typename T>
struct add_var<var_list<Vars...>, T> {
	using type = var_list<Vars...>;
};

template<typename... Vars, char... Name>
struct add_var<var_list<Vars...>, var<Name...>> {
	using type = var_list<Vars..., var<Name...>>;
};


template<typename, typename>
struct collect_var_list{};

template<typename... Vars, typename H, typename... Tail>
struct collect_var_list<var_list<Vars...>, var_list<H, Tail...>>{
	using type = typename collect_var_list<typename add_var<var_list<Vars...>, H>::type, var_list<Tail...>>::type;
};
template<typename... Vars>
struct collect_var_list<var_list<Vars...>, var_list<>>{
	using type = var_list<Vars...>;
};

} // namespace impl

template<typename... Ts>
using get_var_list = typename impl::collect_var_list<var_list<>, var_list<Ts...>>::type;

static_assert(std::is_same<get_var_list<int, x, double, y, z>, var_list<x,y,z>>::value, "");

#endif

