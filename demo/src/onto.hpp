
#ifndef ONTO_HPP
#define ONTO_HPP

#include "soop/problem.hpp"
#include "soop/entity_utils.hpp"

#include <map>
#include <unordered_map>
#include <utility>
#include <ostream>

soop::basic_problem& get_onto();

bool is_teacher(const soop::e<std::size_t>&);
bool is_student(const soop::e<std::size_t>&);
bool is_subject(const soop::e<std::size_t>&);
bool is_grade(const soop::e<std::size_t>&);

template<typename T>
struct deserves_price: soop::make_predicate_impl<deserves_price, 1, T> {};
using deserves_price_t = deserves_price<void>;

template<typename Stud, typename Subject>
struct has_grade: soop::make_predicate_impl<has_grade, 2, Stud, Subject> {};
using has_grade_t = has_grade<void, void>;

#ifndef DO_NOT_ASSERT
#define ONTO_ASSERT_SATISFACTION(...)\
	do {if (not get_onto().request_satisfaction(__VA_ARGS__)) {\
		throw std::logic_error{"unsatisfied requirement"};\
	}} while(false)
#else
#define ONTO_ASSERT_SATISFACTION(...)\
	do {} while(false)
#endif
#endif
