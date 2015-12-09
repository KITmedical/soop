

#include <catch.hpp>

#include "soop/onto.hpp"

TEST_CASE("creation") { soop::ontology o{soop::type_list<>, soop::pred_list()}; }

TEST_CASE("adding types") {
	soop::ontology o{soop::type_list<>, soop::pred_list()};
	REQUIRE_NOTHROW(o.add_type<soop::e<int>>());
}

TEST_CASE("adding values") {
	soop::ontology o{soop::type_list<>, soop::pred_list()};
	o.add_type<soop::e<int>>();
	soop::e<int> e{nullptr, 2};
	REQUIRE_NOTHROW(o.add_entity(e));
}

SOOP_MAKE_PREDICATE(testpred, 2)
namespace p = preds;

TEST_CASE("simple axioms") {
	soop::ontology o{soop::type_list<>, soop::pred_list(p::testpred)};
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
	const auto tp = preds::testpred;
	soop::ontology o{soop::type_list<>, soop::pred_list(tp)};
	o.add_axiom(
	        forall({"x", "y", "z"}, implies(and_(tp("x", "y"), tp("y", "z")), tp("x", "z"))));
	o.add_axiom(forall({"x"}, tp("x", "x")));
	o.add_axiom(forall({"x", "y"}, implies(and_(tp("x", "y"), tp("y", "x")), equal("x", "y"))));
	o.add_type<soop::e<int>>();
	soop::e<int> e1{o, 1};
	soop::e<int> e2{o, 2};
	soop::e<int> e3{o, 2};
	soop::e<int> e4{o, 3};

	o.add_axiom(tp(e1, e2));
	o.add_axiom(tp(e2, e3));
	o.add_axiom(tp(e3, e2));
	o.add_axiom(tp(e3, e4));

	CHECK(o.request(equal(e2, e3)));
	CHECK(o.request(tp(e1, e4)));
	CHECK(o.request(exists({"x"}, and_(tp(e1, "x"), tp("x", e4)))));
	// Not yet working because we also need to narrow down y to e<int>'s:
	// CHECK(o.request(sp::exists({"x"}, sp::forall({"y"}, tp("x", "y")))));
}
