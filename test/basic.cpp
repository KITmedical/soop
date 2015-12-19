
#include <cassert>
#include <utility>

#include <catch.hpp>

#include "soop/onto.hpp"
#include "soop/predicates.hpp"

struct v1{};
struct v2{};
struct v3{};
struct v4{};

SOOP_MAKE_PREDICATE(test_pred1, 2)
SOOP_MAKE_PREDICATE(test_pred2, 2)
SOOP_MAKE_PREDICATE(less, 2)

TEST_CASE("instances") {
	soop::ontology o{
		soop::type_list<>,
		soop::pred_list<
		::preds::test_pred1_t,
		::preds::test_pred2_t,
		::preds::less_t
		>()
	};
	o.add_type<soop::e<v1>>();
	o.add_type<soop::e<v2>>();
	o.add_type<soop::e<v3>>();
	o.add_type<soop::e<v4>>();
	using soop::e;
	o.add_axiom(::preds::less(soop::type<e<v1>>, soop::type<e<v2>>));
	o.add_axiom(::preds::less(soop::type<e<v2>>, soop::type<e<v3>>));
	o.add_axiom(::preds::less(soop::type<e<v3>>, soop::type<e<v4>>));
	using namespace ::preds;
	using namespace ::soop::preds;

	soop::variable<'x'> x;
	soop::variable<'y'> y;
	soop::variable<'z'> z;
	o.add_axiom(forall({x,y,z}, implies(and_(less(x, y), less(y, z)), less(x, z))));

	soop::e<v1> i1{o};
	soop::e<v2> i2{o};
	CHECK(o.request(less(soop::type<e<v1>>, soop::type<e<v4>>)));
	CHECK_FALSE(o.request(less(soop::type<e<v3>>, soop::type<e<v2>>)));

	//TODO make instance_of work again:
#if 0
	CHECK(o.request(instance_of(i1, soop::type<e<v1>>)));
	CHECK(o.request(instance_of(i2, soop::type<e<v2>>)));

	CHECK_FALSE(o.request(instance_of(i1, soop::type<e<v2>>)));
	CHECK_FALSE(o.request(instance_of(i2, soop::type<e<v1>>)));

	auto i3 = std::move(i1);

	CHECK(o.request(instance_of(i3, soop::type<e<v1>>)));
	CHECK_FALSE(o.request(instance_of(i3, soop::type<e<v2>>)));

	CHECK_FALSE(o.request(test_pred1(i3, i2)));

	o.add_axiom(test_pred1(i3, i2));

	CHECK(o.request(test_pred1(i3, i2)));

	// auto i4 = i3;
	//CHECK(o.request(test_pred1(i4, i2)));
#endif
}



