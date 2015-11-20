
#include "problem.hpp"

#include <catch.hpp>

using namespace soop; // TODO

bool is_x_coord(e<int>) {throw std::logic_error{"not implmented"};}
bool is_y_coord(e<int>) {throw std::logic_error{"not implmented"};}

bool is_coordpair(e<int>, e<int>) {throw std::logic_error{"not implemented"};}

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

TEST_CASE("point-checks") {
	auto prob = problem<
		functions<make_function<int>>,
		predicates<>,
		formulae<>
	>{};
	prob.add_relation(is_x_coord);
	prob.add_relation(is_y_coord);
	prob.add_relation(is_coordpair);
	point p1{prob, 23, 42};

	prob.declare_satifies(is_coordpair, p1.x, p1.y);
	auto x = p1.x;
	point p2{prob, x, p1.y};

	CHECK_THROWS_AS((point{prob, p1.x, p1.x}), std::runtime_error);
	CHECK(prob.request_satisfication(is_coordpair, p1.x, p1.y));
	CHECK(prob.request_satisfication(is_coordpair, p1.x, v{}));
	CHECK_FALSE(prob.request_satisfication(is_coordpair, p1.y, v{}));
	CHECK_FALSE(prob.request_satisfication(is_coordpair, v{}, v{}));
	CHECK(prob.request_satisfication(is_coordpair, v{}, w{}));
}
