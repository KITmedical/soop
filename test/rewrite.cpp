

#include <catch.hpp>

#include "soop/onto.hpp"

soop::variable<'x'> x;
soop::variable<'y'> y;
soop::variable<'z'> z;

TEST_CASE("creation") { soop::ontology o{soop::type_list<>, soop::pred_list<>()}; }

TEST_CASE("adding types") {
	soop::ontology o{soop::type_list<>, soop::pred_list<>()};
	REQUIRE_NOTHROW(o.add_type<soop::e<int>>());
}

TEST_CASE("adding values") {
	soop::ontology o{soop::type_list<>, soop::pred_list<>()};
	o.add_type<soop::e<int>>();
	soop::e<int> e{nullptr, 2};
	REQUIRE_NOTHROW(o.add_entity(e));
}

SOOP_MAKE_PREDICATE(testpred, 2)
namespace p = preds;

TEST_CASE("simple axioms") {
	soop::ontology o{soop::type_list<>, soop::pred_list<preds::testpred_t>()};
	o.add_type<soop::e<int>>();
	soop::e<int> e1{nullptr, 2};
	soop::e<int> e2{nullptr, 2};
	o.add_entity(e1);
	o.add_entity(e2);
	REQUIRE_NOTHROW(o.add_axiom(p::testpred(e1, e2)));
	REQUIRE(o.request(p::testpred(e1, e2)));
}

SOOP_MAKE_PREDICATE(transitive, 1)

TEST_CASE("complex axioms") {
	using namespace soop::preds;
	soop::ontology o{soop::type_list<>, soop::pred_list<preds::testpred_t>()};
	o.add_axiom(
	        forall({x, y, z}, implies(and_(preds::testpred(x, y), preds::testpred(y, z)), preds::testpred(x, z))));
	o.add_axiom(forall({x}, preds::testpred(x, x)));
	o.add_axiom(forall({x, y}, implies(and_(preds::testpred(x, y), preds::testpred(y, x)), equal(x, y))));
	o.add_type<soop::e<int>>();
	soop::e<int> e1{o, 1};
	soop::e<int> e2{o, 2};
	soop::e<int> e3{o, 2};
	soop::e<int> e4{o, 3};

	o.add_axiom(preds::testpred(e1, e2));
	o.add_axiom(preds::testpred(e2, e3));
	o.add_axiom(preds::testpred(e3, e2));
	o.add_axiom(preds::testpred(e3, e4));

	CHECK(o.request(equal(e2, e3)));
	CHECK(o.request(preds::testpred(e1, e4)));
	CHECK(o.request(exists({x}, and_(preds::testpred(e1, x), preds::testpred(x, e4)))));
	// Not yet working because we also need to narrow down y to e<int>'s:
	// CHECK(o.request(sp::exists({x}, sp::forall({y}, tp(x, y)))));
}

SOOP_MAKE_TYPECHECKED_PREDICATE(int_pred, 1, soop::e<int>)

TEST_CASE("typechecked predicate") {
	soop::ontology o{
		soop::type_list<soop::e<int>, soop::e<double>>,
		soop::pred_list<preds::int_pred_t>()
	};
	soop::e<int> i{o, 23};
	o.add_axiom(preds::int_pred(i));
	CHECK(o.request(preds::int_pred(i)));
	soop::e<double> d{o, 2.7};
	//o.add_axiom(int_pred(d)); // correctly fires static assert
}
