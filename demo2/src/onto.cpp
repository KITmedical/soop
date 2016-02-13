
#include "onto.hpp"
#include "data.hpp"

namespace {
const soop::variable<'T', '1'> t1{};
const soop::variable<'T', '1'> t2{};
const soop::variable<'S', '1'> s1{};
const soop::variable<'S', '1'> s2{};
const soop::variable<'R', '1'> r1{};
const soop::variable<'R', '1'> r2{};
const soop::variable<'S', 'l', '1'> sl1{};
const soop::variable<'S', 'l', '2'> sl2{};

using namespace soop::preds;
using namespace preds;

soop::formula uniqueness_of_talks() {
	return forall({t1,t2,s1,s2,r1,r2,sl1,sl2},
		implies(
			and_(
				talk_assignment(t1,s1,r1,sl1),
				talk_assignment(t2,s2,r2,sl2)
			),
			and_(
				equal(
					equal(t1,t2),
					and_(equal(r1,r2), equal(sl1,sl2))
				),
				implies(
					equal(t1,t2),
					equal(s1,s2)
				)
			)
		)
	);
}

soop::formula talk_assignment_is_typed() {
	return forall({t1,s1,r1,sl1},
		implies(
			not_(
				and_(
					instance_of(t1, soop::type<talk>),
					instance_of(s1, soop::type<speaker>),
					instance_of(r1, soop::type<room>),
					instance_of(sl1, soop::type<slot>))),
			not_(talk_assignment(t1,s1,r1,sl1))
		)
	);
}

soop::formula one_speaker_per_talk() {
	return forall({t1,s1,s2,r1,sl1},
		implies(
			and_(
				talk_assignment(t1,s1,r1,sl1),
				talk_assignment(t1,s2,r1,sl1)),
			equal(s1,s2)
		)
	);
}

soop::formula only_speakers_hold_their_talk() {
	return forall({t1, s1}, equal(
		is_speaker_of(s1, t1),
		exists({r1, sl1},
			talk_assignment(t1, s1, r1, sl1))));
}

soop::formula types_are_no_instances() {
	const soop::variable<'d'> d{};
	const soop::variable<'b'> b{};
	const soop::variable<'i'> i{};
	return forall({d, i}, implies(instance_of(i, d), not_(exists({b}, (instance_of(d, b))))));
}

soop::formula entities_have_only_one_type() {
	const soop::variable<'T','1'> T1{};
	const soop::variable<'T','2'> T2{};
	const soop::variable<'i'> i{};
	return forall({T1,T2,i}, implies(and_(instance_of(i, T1), instance_of(i, T2)),equal(T1,T2)));
}

} // namespace

soop::ontology make_ontology() {
	soop::ontology onto{
		soop::type_list_t<
			talk,
			speaker,
			room,
			slot
		>{},
		soop::pred_list<
			preds::is_speaker_of_t,
			preds::talk_assignment_t
		>{}
	};
	onto.add_axiom(uniqueness_of_talks());
	onto.add_axiom(talk_assignment_is_typed());
	onto.add_axiom(one_speaker_per_talk());
	onto.add_axiom(only_speakers_hold_their_talk());
	onto.add_axiom(types_are_no_instances());
	onto.add_axiom(entities_have_only_one_type());
	return onto;
}

