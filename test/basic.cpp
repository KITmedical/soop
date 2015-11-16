#include "problem.hpp"

#include <catch.hpp>

struct test_type {
	static std::string name() {return "test_type";};
	static constexpr std::size_t rank() {return 0;}
};
template<typename T>
struct test_pred {
	static std::string name() {return "test_pred";}
	static std::string to_string() {return name() + "(" + T::to_string() + ")";}
	static constexpr std::size_t rank() {return 1;}
};


TEST_CASE("simple") {
	soop::problem<
		soop::functions<soop::function<test_type>>,
		soop::predicates<soop::predicate<test_pred<soop::x>>>,
		soop::formulae<soop::function<test_pred<test_type>>>
	> p;
}


