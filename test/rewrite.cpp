

#include <catch.hpp>

#include "soop/onto.hpp"

TEST_CASE("creation") { soop::ontology o{}; }

TEST_CASE("adding types") {
	soop::ontology o{};
	REQUIRE_NOTHROW(o.add_type<soop::e<int>>());
}

TEST_CASE("adding values") {
	soop::ontology o{};
	o.add_type<soop::e<int>>();
	soop::e<int> e{nullptr, 2};
	REQUIRE_NOTHROW(o.add_entity(e));
}

SOOP_MAKE_PREDICATE(testpred, 2)
namespace p = preds;

TEST_CASE("simple axioms") {
	soop::ontology o{p::testpred};
	o.add_type<soop::e<int>>();
	soop::e<int> e1{nullptr, 2};
	soop::e<int> e2{nullptr, 2};
	o.add_entity(e1);
	o.add_entity(e2);
	REQUIRE_NOTHROW(o.add_axiom(p::testpred(e1, e2)));
	REQUIRE(o.request(p::testpred(e1, e2)));
}

TEST_CASE("complex axioms") {
	namespace sp = soop::preds;
	soop::ontology o{p::testpred};
	o.add_axiom(sp::forall({"x", "y", "z"},
	                       sp::implies(sp::and_(p::testpred("x", "y"), p::testpred("y", "z")),
	                                   p::testpred("x", "z"))));
	o.add_axiom(sp::forall({"x"}, p::testpred("x", "x")));
	o.add_axiom(sp::forall({"x", "y"},
	                       sp::implies(sp::and_(p::testpred("x", "y"), p::testpred("y", "x")),
	                                   sp::equal("x", "y"))));
	o.add_type<soop::e<int>>();
	soop::e<int> e1{nullptr, 1};
	soop::e<int> e2{nullptr, 2};
	soop::e<int> e3{nullptr, 2};
	soop::e<int> e4{nullptr, 3};

	o.add_entity(e1);
	o.add_entity(e2);
	o.add_entity(e3);
	o.add_entity(e4);

	o.add_axiom(p::testpred(e1, e2));
	o.add_axiom(p::testpred(e2, e3));
	o.add_axiom(p::testpred(e3, e2));
	o.add_axiom(p::testpred(e3, e4));

	CHECK(o.request(sp::equal(e2, e3)));
	CHECK(o.request(p::testpred(e1, e4)));
	// Not yet working because we also need to narrow down y to e<int>'s:
	//CHECK(o.request(sp::exists({"x"}, sp::forall({"y"}, p::testpred("x", "y")))));
}
