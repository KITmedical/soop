#ifndef PRIMITIVES_HPP
#define PRIMITIVES_HPP

#include <iostream>
#include <vector>
#include <initializer_list>
#include <string>

#include "spass.hpp"

using ignore = std::initializer_list<int>;

template <typename Head, typename... Tail>
std::string join(const std::string& delim = ", ") {
	auto ret = Head::to_string();
	(void)ignore{(ret += delim, ret += Tail::to_string(), 0)...};
	return ret;
}

template <typename Head, typename... Tail>
std::string entity_join(const Head& h, const Tail&...t) {
	auto ret = h.entity_id_name();
	(void)ignore{(ret += ", ", ret += t.entity_id_name(), 0)...};
	return ret;
}
template <typename... Values>
struct set {
	static std::string to_string() { return "[" + join<Values...>() + "]"; }
};

template <typename List, typename Statement>
struct forall {
	static std::string to_string() {
		return "forall(" + List::to_string() + ", " + Statement::to_string() + ")";
	}
};

template <typename Cond, typename Statement>
struct implies {
	static std::string to_string() {
		return "implies(" + Cond::to_string() + ", " + Statement::to_string() + ")";
	}
};

template <typename... Values>
struct and_ {
	static std::string to_string() { return "and(" + join<Values...>() + ")"; }
};


template <typename... Values>
struct or_ {
	static std::string to_string() { return "or(" + join<Values...>() + ")"; }
};

template <typename... Values>
struct equal {
	static std::string to_string() { return "equal(" + join<Values...>() + ")"; }
};

template <typename Value>
struct not_ {
	static std::string to_string() { return "not(" + Value::to_string() + ")"; }
};

template <typename L, typename R>
struct less {
	static std::string to_string() {
		return "less(" + L::to_string() + ", " + R::to_string() + ")";
	}
	static std::string name() {
		return "less";
	}
	static unsigned rank() {
		return 2;
	}
};

template <typename Statement>
struct formula {
	static std::string to_string() { return "formula(" + Statement::to_string() + ").\n"; }
};

template<typename...Formulae>
struct formulae {
	static std::string to_string() {
		return join<Formulae...>("");
	}
};

template<typename P>
struct predicate {
	static std::string to_string() {
		return "(" + P::name() + ", " + std::to_string(P::rank()) + ")";
	}
};

template<typename...Ps>
struct predicates {
	static std::string to_string() {
		return join<Ps...>(",\n");
	}
};


template<typename F>
struct function {
	static std::string to_string() {
		return "(" + F::name() + ", " + std::to_string(F::rank()) + ")";
	}
};

template<typename...Fs>
struct functions {
	static std::string to_string() {
		return join<Fs...>(",\n");
	}
};

#endif
