#ifndef SOOP_BUILDIN_PREDICATES_HPP
#define SOOP_BUILDIN_PREDICATES_HPP

#include <string>
#include <vector>
#include "predicates.hpp"

namespace soop {

SOOP_MAKE_RENAMED_PREDICATE(equal, "=", 2)
SOOP_MAKE_PREDICATE(instance_of, 2)
SOOP_MAKE_PREDICATE(implies, 2)
SOOP_MAKE_PREDICATE(distinct, variadic_rank)

namespace preds {

// and, or and not are defined manually, because not only
// is it necessary to rename them (because they are keywords),
// but the desireable not_,… result in the reserved identifiers
// not__t for the classtemplate.

///// not

template<typename Arg>
struct not_t: basic_predicate<not_t, Arg> {
	using basic_predicate<::soop::preds::not_t, Arg>::basic_predicate;
	static std::string name() {return "not";}
};
template<typename Arg>
not_t<Arg> not_(Arg arg) {
	return {std::move(arg)};
}

///// and

template<typename...Args>
struct and_t: basic_predicate<and_t, Args...> {
	using basic_predicate<::soop::preds::and_t, Args...>::basic_predicate;
	static std::string name() {return "and";}
};
template<typename...Args>
and_t<Args...> and_(Args... args) {
	return {std::move(args)...};
}

///// or

template<typename...Args>
struct or_t: basic_predicate<or_t, Args...> {
	using basic_predicate<::soop::preds::and_t, Args...>::basic_predicate;
	static std::string name() {return "or";}
};
template<typename...Args>
or_t<Args...> or_(Args... args) {
	return {std::move(args)...};
}


///// distinct_range

class distinct_range_t: public soop::is_predicate {
public:
	template<typename Iterator>
	distinct_range_t(Iterator begin, Iterator end) {
		for(auto it= begin; it != end; ++it) {
			m_entities.emplace_back(it->id());
		}
	}
	void collect_entities(std::vector<std::size_t>&);
	void stream(std::ostream& out, const std::vector<std::string>& names) const;
private:
	std::vector<std::size_t> m_entities;
};

template<typename Iterator>
distinct_range_t distinct_range(Iterator first, Iterator last) {
	return distinct_range_t{first, last};
}

///// forall

template <typename Pred>
struct forall_t : is_predicate {
	forall_t(bound_vars vars, Pred pred) : vars{std::move(vars)}, pred{std::move(pred)} {}
	void collect_entities(std::vector<std::size_t>& ids) {
		collect_entity(ids, pred);
	}
	void stream(std::ostream& out, const std::vector<std::string>& names) const {
		out << "(forall " << vars.str() << " ";
		pred.stream(out, names);
		out << ')';
	}
	bound_vars vars;
	Pred pred;
};

template <typename Pred>
auto forall(bound_vars vars, Pred p) {
	return forall_t<Pred>{std::move(vars), p};
}

///// exists

template <typename Pred>
struct exists_t : is_predicate{
	exists_t(bound_vars vars, Pred pred) : vars{std::move(vars)}, pred{std::move(pred)} {}
	void collect_entities(std::vector<std::size_t>& ids) {
		collect_entity(ids, pred);
	}
	void stream(std::ostream& out, const std::vector<std::string>& names) const {
		out << "(exists " << vars.str() << " ";
		pred.stream(out, names);
		out << ')';
	}
	bound_vars vars;
	Pred pred;
};

template <typename Pred>
auto exists(bound_vars vars, Pred p) {
	return exists_t<Pred>{std::move(vars), p};
}

} // namespace preds

} // namespace soop

#endif // SOOP_BUILDIN_PREDICATES_HPP
