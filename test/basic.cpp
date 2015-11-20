#include "problem.hpp"

#include <cassert>
#include <utility>

#include <catch.hpp>

template<char...Name>
struct util_type {
	static std::string name() { return std::string{Name...}; }
	static std::string to_string() { return name(); }
	static std::size_t rank() { return 0; }
	static std::type_index type_index() { return std::type_index{typeid(util_type<Name...>)}; }
};

using v1 = util_type<'v','1'>;
using v2 = util_type<'v','2'>;
using v3 = util_type<'v','3'>;
using v4 = util_type<'v','4'>;

bool test_pred1(const soop::e<v1>& l, const soop::e<v2>& r) {
	assert(l.problem() == r.problem() and l.problem() != nullptr);
	auto& p = *l.problem();
	return p.request_satisfication(test_pred1, l, r);
}

bool test_pred2(const soop::e<v1>&, const soop::e<v2>&) { throw std::logic_error{""}; }

// centralized definitions are simple:
template<template<typename, typename> class T>
struct transitive {
	static std::string to_string() {
		const auto name = T<soop::x,soop::y>::name();
		return "forall([x,y,z], implies(and("+name+"(x,y), "+name+"(y, z)),"+name+"(x,z)))";
	}
};


TEST_CASE("instances") {
	using namespace soop;
	problem<
		functions<
			function<v1>,
			function<v2>,
			function<v3>,
			function<v4>
		>,
		predicates<
			predicate<less<x,y>>
		>,
		formulae<
			formula<less<v1, v2>>,
			formula<less<v2, v3>>,
			formula<less<v3, v4>>,
			formula<transitive<less>>
		>
	> p;

	e<v1> i1{p};
	e<v2> i2{p};
	CHECK(p.request(formula<less<v1, v4>>{}));
	CHECK_FALSE(p.request(formula<less<v3, v2>>{}));

	CHECK(p.request_satisfication(pred<instance>{}, i1, type<v1>{}));
	CHECK(p.request_satisfication(pred<instance>{}, i2, type<v2>{}));

	CHECK_FALSE(p.request_satisfication(pred<instance>{}, i1, type<v2>{}));
	CHECK_FALSE(p.request_satisfication(pred<instance>{}, i2, type<v1>{}));

	auto i3 = std::move(i1);

	CHECK(p.request_satisfication(pred<instance>{}, i3, type<v1>{}));
	CHECK_FALSE(p.request_satisfication(pred<instance>{}, i3, type<v2>{}));

	p.add_relation(test_pred1);
	p.add_relation(test_pred2);

	CHECK_FALSE(p.request_satisfication(test_pred1, i3, i2));

	p.declare_satifies(test_pred1, i3, i2);

	CHECK(p.request_satisfication(test_pred1, i3, i2));

	auto i4 = i3;

	CHECK(p.request_satisfication(test_pred1, i4, i2));
	CHECK(test_pred1(i4, i2));
}

