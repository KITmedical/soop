#include "problem.hpp"

#include <cassert>
#include <utility>

#include <catch.hpp>

using v1 = soop::var<'v','1'>;
using v2 = soop::var<'v','2'>;
using v3 = soop::var<'v','3'>;
using v4 = soop::var<'v','4'>;

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
	REQUIRE(p.request(formula<less<v1, v4>>{}));
	REQUIRE(not p.request(formula<less<v3, v2>>{}));
	REQUIRE(p.request("formula(instance("+i1.entity_id_name()+", "+v1::name()+"))."));
	REQUIRE(not p.request("formula(instance("+i1.entity_id_name()+", "+v2::name()+"))."));
	REQUIRE(not p.request("formula(instance("+i2.entity_id_name()+", "+v1::name()+"))."));
	REQUIRE(p.request("formula(instance("+i2.entity_id_name()+", "+v2::name()+"))."));

	auto i3 = std::move(i1);

	REQUIRE(p.request("formula(instance("+i3.entity_id_name()+", "+v1::name()+"))."));
	REQUIRE(not p.request("formula(instance("+i3.entity_id_name()+", "+v2::name()+"))."));

	p.add_relation(test_pred1);
	p.add_relation(test_pred2);

	REQUIRE(not p.request_satisfication(test_pred1, i3, i2));

	p.declare_satifies(test_pred1, i3, i2);

	REQUIRE(p.request_satisfication(test_pred1, i3, i2));

	auto i4 = i3;

	REQUIRE(p.request_satisfication(test_pred1, i4, i2));
	REQUIRE(test_pred1(i4, i2));
}

