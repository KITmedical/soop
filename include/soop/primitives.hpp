#ifndef PRIMITIVES_HPP
#define PRIMITIVES_HPP

#include <iostream>
#include <vector>
#include <initializer_list>
#include <string>
#include <typeindex>

#include "spass.hpp"

namespace soop {


template<typename F>
using fun_ptr = F*;

template<typename T>
struct pred{};
template<typename T>
struct type {
	static std::string entity_id_name() { return T::name(); }
};

template<typename Rel>
std::size_t rel_id(pred<Rel>) {
	return Rel::id();
}

template<typename...Args>
std::size_t rel_id(fun_ptr<bool(Args...)> f) {
	return reinterpret_cast<std::size_t>(f);
}


inline std::string rel_string_id(std::size_t address) {
	return "relation_" + std::to_string(address);
}

template<typename...Args>
std::string rel_string_id(fun_ptr<bool(Args...)> f) {
	return rel_string_id(rel_id(f));
}

template<typename Rel>
std::string rel_string_id(pred<Rel> rel) {
	return rel_string_id(rel_id(rel));
}

using ignore = std::initializer_list<int>;

namespace impl {
template<typename...Ts>
struct type_list{};

template <typename Head, typename... Tail>
std::string join(type_list<Head, Tail...>, const std::string& delim) {
	auto ret = Head::to_string();
	(void)ignore{(ret += delim, ret += Tail::to_string(), 0)...};
	return ret;
}

inline std::string join(type_list<>, const std::string&) { return ""; }

} // namespace impl

template<typename...Args>
std::string join(const std::string& delim = ",") {
	return impl::join(impl::type_list<Args...>{}, delim);
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
	static std::type_index type_index() {
		return F::type_index();
	}
	static std::string name() {
		return F::name();
	}
	static std::size_t rank() {
		return F::rank();
	}
};

template<typename...Fs>
struct functions {
	static std::string to_string() {
		return join<Fs...>(",\n");
	}
};

template<typename Self, std::size_t Rank = 0>
struct make_function_impl {
	static std::string name() {
		return rel_string_id(pred<make_function_impl<Self>>{});
	}
	static std::size_t id() {
		return reinterpret_cast<std::size_t>(&id);
	}
	static std::size_t rank() {
		return Rank;
	}
	static std::type_index type_index() {
		return std::type_index{typeid(Self)};
	}
	template<typename...Args>
	static std::string to_string(const Args&... args) {
		auto str = name() + "(";
		if (sizeof...(Args)) {
			(void) ignore{(str += (args.name() + ','),0)...};
			str.pop_back();
		}
		str += ')';
		return str;
	}
};
template<typename Self, std::size_t Rank = 0>
using make_function = function<make_function_impl<Self, Rank>>;

template<typename Self, std::size_t Rank = 1>
using make_predicate = predicate<make_function_impl<Self, Rank>>;


struct instance : public make_function_impl<instance, 2> {
};

} // namespace soop

#endif
