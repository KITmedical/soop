#include <cassert>
#include <iostream>
#include <algorithm>
#include <string>
#include <initializer_list>

#include "problem.hpp"

using v1 = var<'v','1'>;
using v2 = var<'v','2'>;
using v3 = var<'v','3'>;
using v4 = var<'v','4'>;

bool test_pred1(const e<v1>& l, const e<v2>& r) {
	assert(l.problem() == r.problem() and l.problem() != nullptr);
	auto& p = *l.problem();
	return p.request("formula(dynamic_relation_" + std::to_string(reinterpret_cast<std::size_t>(&test_pred1)) + "(" + l.entity_id_name() + ", " + r.entity_id_name() + ")).");
}
bool test_pred2(const e<v1>&, const e<v2>&) { throw std::logic_error{""}; }

// centralized definitions are simple:
template<template<typename, typename> class T>
struct transitive {
	static std::string to_string() {
		const auto name = T<x,y>::name();
		return "forall([x,y,z], implies(and("+name+"(x,y), "+name+"(y, z)),"+name+"(x,z)))";
	}
};

int test_main_1() try {
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
	
	std::cout << "Question  1: " << std::boolalpha << p.request(formula<less<v1, v4>>{})
		<< "\t[expected: true ]\n";
	std::cout << "Question  2: " << std::boolalpha << p.request(formula<less<v3, v2>>{})
		<< "\t[expected: false]\n";
	std::cout << "Question  3: " << std::boolalpha
		<< p.request("formula(instance("+i1.entity_id_name()+", "+v1::name()+")).")
		<< "\t[expected: true ]\n";
	std::cout << "Question  4: " << std::boolalpha
		<< p.request("formula(instance("+i1.entity_id_name()+", "+v2::name()+")).")
		<< "\t[expected: false]\n";
	std::cout << "Question  5: " << std::boolalpha
		<< p.request("formula(instance("+i2.entity_id_name()+", "+v1::name()+")).")
		<< "\t[expected: false]\n";
	std::cout << "Question  6: " << std::boolalpha
		<< p.request("formula(instance("+i2.entity_id_name()+", "+v2::name()+")).")
		<< "\t[expected: true ]\n";

	auto i3 = std::move(i1);
	std::cout << "Question  7: " << std::boolalpha
		<< p.request("formula(instance("+i3.entity_id_name()+", "+v1::name()+")).")
		<< "\t[expected: true ]\n";
	std::cout << "Question  8: " << std::boolalpha
		<< p.request("formula(instance("+i3.entity_id_name()+", "+v2::name()+")).")
		<< "\t[expected: false]\n";

	p.add_relation(test_pred1);
	const auto pred1_name = "dynamic_relation_" + std::to_string(reinterpret_cast<std::size_t>(test_pred1));
	p.add_relation(test_pred2);
	const auto pred2_name = "dynamic_relation_" + std::to_string(reinterpret_cast<std::size_t>(test_pred1));

	std::cout << "Question  9: " << std::boolalpha
		<< p.request("formula(" + pred1_name + "("+i3.entity_id_name()+", " + i2.entity_id_name() +")).")
		<< "\t[expected: false]\n";

	p.declare_satifies(test_pred1, i3, i2);

	std::cout << "Question 10: " << std::boolalpha
		<< p.request("formula(" + pred1_name + "("+i3.entity_id_name()+", " + i2.entity_id_name() +")).")
		<< "\t[expected: true ]\n";

	auto i4 = i3;

	std::cout << "Question 11: " << std::boolalpha
		<< p.request("formula(" + pred1_name + "("+i4.entity_id_name()+", " + i2.entity_id_name() +")).")
		<< "\t[expected: true ]\n";

	std::cout << "Question 12: " << std::boolalpha << test_pred1(i4, i2) << "\t[expected: true ]\n";
	std::cout << "Question 13: " << std::boolalpha << p.request_satisfication(test_pred1, i4, i2) << "\t[expected: true ]\n";
	
	return 0;
} catch (std::exception& e) {
	std::cerr << "Error: " << e.what() << '\n';
	return 1;
}
