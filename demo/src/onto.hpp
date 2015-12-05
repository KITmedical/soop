
#ifndef ONTO_HPP
#define ONTO_HPP

#include "soop/onto.hpp"
#include "soop/entity_utils.hpp"

#include <map>
#include <unordered_map>
#include <utility>
#include <ostream>

soop::ontology& get_onto();

SOOP_MAKE_PREDICATE(is_teacher, 1)
SOOP_MAKE_PREDICATE(is_student, 1)
SOOP_MAKE_PREDICATE(is_subject, 1)
SOOP_MAKE_PREDICATE(is_grade, 1)

SOOP_MAKE_PREDICATE(very_good_grade, 1)
SOOP_MAKE_PREDICATE(good_grade, 1)
SOOP_MAKE_PREDICATE(passing_grade, 1)


SOOP_MAKE_PREDICATE(deserves_price, 1)
SOOP_MAKE_PREDICATE(has_grade, 2)

#ifndef DO_NOT_ASSERT
#define ONTO_ASSERT_SATISFACTION(...)\
	do {if (not get_onto().request(__VA_ARGS__)) {\
		throw std::logic_error{"unsatisfied requirement"};\
	}} while(false)
#else
#define ONTO_ASSERT_SATISFACTION(...)\
	do {} while(false)
#endif
#endif
