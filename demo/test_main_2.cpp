
#include "problem.hpp"

using namespace soop; // TODO

bool is_x_coord(e<int>) {throw std::logic_error{"not implmented"};}
bool is_y_coord(e<int>) {throw std::logic_error{"not implmented"};}

bool is_coordpair(e<int>, e<int>) {return false;}

template<>
struct type_name_helper<int> {
	static std::string get() {
		return "int";
	}
};

void require(bool b, const char what[] = "") {
	if (not b) {
		throw std::runtime_error{what};
	}
}

struct point {
	point(basic_problem& p, int x, int y): x{p, x}, y{p, y} {
		p.declare_satifies(is_x_coord, this->x);
		p.declare_satifies(is_y_coord, this->y);
	}
	point(basic_problem& p, const e<int>& xarg, e<int> yarg): x{xarg}, y{yarg} {
		require(p.request_satisfication(is_x_coord, xarg), "xarg is not a x-coordinate");
		require(p.request_satisfication(is_y_coord, yarg), "yarg is not a y-coordinate");
		require(p.request_satisfication(is_x_coord, x), "x is not a x-coordinate");
		require(p.request_satisfication(is_y_coord, y), "y is not a y-coordinate");
	}
	e<int> x;
	e<int> y;
};


struct int_ {
	static std::string name() {return "int";}
	static std::string to_string() {return "int";}
	static std::size_t rank() { return 0; }
};
template<typename T>
struct dummy_pred {
	static std::string name() {return "dummy_pred";}
	static std::string to_string() { return name() + "(" + T::to_string() + ")"; }
	static std::size_t rank() { return 1; }
};

int test_main_2() try {
	auto prob = problem<
		functions<function<int_>>,
		predicates<predicate<dummy_pred<x>>>,
		formulae<formula<dummy_pred<int_>>>
	>{};
	prob.add_relation(is_x_coord);
	prob.add_relation(is_y_coord);
	prob.add_relation(is_coordpair);
	point p1{prob, 23, 42};

	prob.declare_satifies(is_coordpair, p1.x, p1.y);
	auto x = p1.x;
	point p2{prob, x, p1.y};
	try {
		point p3{prob, p1.x, p1.x}; // oops
		std::cout << "We should never get here\n";
		return 1;
	} catch (std::runtime_error&) {
		std::cout << "Succesfully caught exception from bad argument\n";
	}
	require(prob.request_satisfication(is_coordpair, p1.x, p1.y), "x and y should be a pair");
	require(prob.request_satisfication(is_coordpair, p1.x, v{}), "There should exist a pair with p1.x as x-coord");
	require(!prob.request_satisfication(is_coordpair, p1.y, v{}), "There should not be a pair with p1.y as x-coord");
	require(!prob.request_satisfication(is_coordpair, v{}, v{}), "There should not be a pair with v being x and y");
	require(prob.request_satisfication(is_coordpair, v{}, w{}), "There should be a pair of v and w");
	return 0;
} catch (std::runtime_error& e) {
	std::cerr << "Error: " << e.what() << '\n';
	return 1;
}
