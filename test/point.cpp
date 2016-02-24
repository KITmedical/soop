
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
		require(not p.request(soop::preds::not_(preds::is_x_coord(xarg))), "xarg is not a x-coordinate");
		require(not p.request(soop::preds::not_(preds::is_y_coord(yarg))), "yarg is not a y-coordinate");
		// disabled because copy-ctors are currently not working, because implications would be unclear
		//require(p.request(is_x_coord(x)), "x is not a x-coordinate");
		//require(p.request(is_y_coord(y)), "y is not a y-coordinate");
	}
	soop::e<int> x;
	soop::e<int> y;
};

TEST_CASE("point-checks") {
	soop::ontology onto{
		soop::type_list<>,
		soop::pred_list<preds::is_x_coord_t, preds::is_y_coord_t, preds::is_coordpair_t>()
	};
	using soop::preds::exists;
	using soop::preds::forall;
	using soop::preds::not_;
	using soop::preds::and_;
	using preds::is_coordpair;
	using preds::is_x_coord;
	using preds::is_y_coord;

	soop::variable<'x'> x;
	soop::variable<'y'> y;

	onto.add_axiom(forall({x, y}, implies(not_(and_(is_x_coord(x), is_y_coord(y))), not_(is_coordpair(x, y)))));
	onto.add_axiom(forall({x}, implies(is_x_coord(x), not_(is_y_coord(x)))));
	onto.add_axiom(forall({y}, implies(is_y_coord(y), not_(is_x_coord(y)))));
	onto.add_type<soop::e<int>>();
	point p1{onto, 23, 42};

	onto.add_axiom(is_coordpair(p1.x, p1.y));

	soop::e<int> x1{onto, 1};
	soop::e<int> x2{onto, 1};
	soop::e<int> x3{onto, 1};
	soop::e<int> y1{onto, 1};
	soop::e<int> y2{onto, 1};

	CHECK_THROWS_AS((point{onto, std::move(x1), std::move(x2)}), std::runtime_error);

	CHECK(onto.request(is_coordpair(p1.x, p1.y)));
	CHECK(onto.request(exists({y}, is_coordpair(p1.x, y))));
	CHECK_FALSE(onto.request(exists({x}, is_coordpair(x, p1.x))));
	CHECK_FALSE(onto.request(exists({x}, is_coordpair(x, x))));
	CHECK(onto.request(exists({x, y}, is_coordpair(x, y))));

	// disabled because copy-ctors are currently not working, because implications would be unclear
	//auto x = p1.x;
	//point p2{onto, x, p1.y};

	//CHECK_THROWS_AS((point{prob, p1.x, p1.x}), std::runtime_error);
}
