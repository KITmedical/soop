
#include <cassert>
#include <utility>

#include <catch.hpp>

#include "soop/onto.hpp"
#include "soop/predicates.hpp"

template<char...Name>
struct util_type {
	static std::string name() { return std::string{Name...}; }
	static std::string to_string() { return name(); }
	static std::size_t rank() { return 0; }
};

using v1 = util_type<'v','1'>;
using v2 = util_type<'v','2'>;
using v3 = util_type<'v','3'>;
using v4 = util_type<'v','4'>;

SOOP_MAKE_PREDICATE(test_pred1, 2)
SOOP_MAKE_PREDICATE(test_pred2, 2)
SOOP_MAKE_PREDICATE(less, 2)

bool test_pred2(const soop::e<v1>&, const soop::e<v2>&) { throw std::logic_error{""}; }

inline std::string transitive(const std::string& name) {
	return "forall([x,y,z], implies(and("+name+"(x,y), "+name+"(y, z)),"+name+"(x,z)))";
}

// TODO: reimplement support for axioms over types
#if 0

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
	o.add_axiom(::preds::less(soop::t_name<e<v1>>(), soop::t_name<e<v2>>()));
	o.add_axiom(::preds::less(soop::t_name<e<v2>>(), soop::t_name<e<v3>>()));
	o.add_axiom(::preds::less(soop::t_name<e<v3>>(), soop::t_name<e<v4>>()));
	o.add_axiom(::transitive(preds::less.name()));

	using namespace ::preds;
	using namespace ::soop::preds;

	soop::e<v1> i1{o};
	soop::e<v2> i2{o};
	CHECK(o.request(less(soop::t_name<e<v1>>(), soop::t_name<e<v4>>())));
	CHECK_FALSE(o.request(less(soop::t_name<e<v3>>(), soop::t_name<e<v2>>())));

	CHECK(o.request(instance_of(i1, soop::t_name<e<v1>>())));
	CHECK(o.request(instance_of(i2, soop::t_name<e<v2>>())));

	CHECK_FALSE(o.request(instance_of(i1, soop::t_name<e<v2>>())));
	CHECK_FALSE(o.request(instance_of(i2, soop::t_name<e<v1>>())));

	auto i3 = std::move(i1);

	CHECK(o.request(instance_of(i3, soop::t_name<e<v1>>())));
	CHECK_FALSE(o.request(instance_of(i3, soop::t_name<e<v2>>())));

	CHECK_FALSE(o.request(test_pred1(i3, i2)));

	o.add_axiom(test_pred1(i3, i2));

	CHECK(o.request(test_pred1(i3, i2)));

	// auto i4 = i3;
	//CHECK(o.request(test_pred1(i4, i2)));
}

#endif


