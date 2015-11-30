
#include "soop/onto.hpp"

#include <catch.hpp>


SOOP_MAKE_PREDICATE(is_x_coord, 1)
SOOP_MAKE_PREDICATE(is_y_coord, 1)
SOOP_MAKE_PREDICATE(is_coordpair, 2)

void require(bool b, const char what[] = "") {
	if (not b) {
		throw std::runtime_error{what};
	}
}

struct point {
	point(soop::ontology& p, int x, int y): x{p, x}, y{p, y} {
		p.add_axiom(preds::is_x_coord(this->x));
		p.add_axiom(preds::is_y_coord(this->y));
	}
	point(soop::ontology& p, soop::e<int> xarg, soop::e<int> yarg): x{std::move(xarg)}, y{std::move(yarg)} {
		require(p.request(preds::is_x_coord(xarg)), "xarg is not a x-coordinate");
		require(p.request(preds::is_y_coord(yarg)), "yarg is not a y-coordinate");
		// disabled because copy-ctors are currently not working, because implications would be unclear
		//require(p.request(is_x_coord(x)), "x is not a x-coordinate");
		//require(p.request(is_y_coord(y)), "y is not a y-coordinate");
	}
	soop::e<int> x;
	soop::e<int> y;
};

TEST_CASE("point-checks") {
	soop::ontology onto{preds::is_x_coord, preds::is_y_coord, preds::is_coordpair};
	onto.add_type<soop::e<int>>();
	point p1{onto, 23, 42};

	onto.add_axiom(preds::is_coordpair(p1.x, p1.y));

	soop::e<int> x1{onto, 1};
	soop::e<int> x2{onto, 1};
	soop::e<int> x3{onto, 1};
	soop::e<int> y1{onto, 1};
	soop::e<int> y2{onto, 1};

	CHECK_THROWS_AS((point{onto, std::move(x1), std::move(x2)}), std::runtime_error);

	CHECK(onto.request(preds::is_coordpair(p1.x, p1.y)));
	CHECK(onto.request(soop::preds::exists({"y"}, preds::is_coordpair(p1.x, "y"))));
	CHECK_FALSE(onto.request(soop::preds::exists({"x"}, preds::is_coordpair("x", p1.x))));
	CHECK_FALSE(onto.request(soop::preds::exists({"x"}, preds::is_coordpair("x", "x"))));
	CHECK(onto.request(soop::preds::exists({"x", "y"}, preds::is_coordpair("x", "y"))));

	// disabled because copy-ctors are currently not working, because implications would be unclear
	//auto x = p1.x;
	//point p2{onto, x, p1.y};

	//CHECK_THROWS_AS((point{prob, p1.x, p1.x}), std::runtime_error);
}
