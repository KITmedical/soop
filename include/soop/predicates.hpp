
#ifndef SOOP_PREDICATES_HPP
#define SOOP_PREDICATES_HPP

#include <cstddef>
#include <string>

#include "entity.hpp"
#include "util.hpp"

namespace soop {

template <typename F>
auto id(F f) -> decltype(f.id()) {
	return f.id();
}
template <typename F>
auto name(F f) -> decltype(f.name()) {
	return f.name();
}

template<typename T>
std::string t_name() {
	return typeid(T).name();
}

template <std::size_t Rank>
class binder {
public:
	static_assert(Rank > 0, "");

	template <typename F>
	binder(F f);

	template <typename... Args>
	std::string operator()(const Args&... args) const;

	const std::string& name() const { return m_name; }
	std::size_t id() const { return m_id; }
	constexpr static std::size_t rank() { return Rank; }

private:
	static const std::string& to_string(const std::string& s) { return s; }
	static std::string to_string(const entity& e) { return e.name(); }
	std::size_t m_id;
	std::string m_name;
};

#define SOOP_MAKE_RENAMED_PREDICATE(Identifier, Name, Rank)                                        \
	namespace predicate_definitions {                                                          \
	struct Identifier {                                                                        \
		static auto name() { return Name; }                                                \
		static std::size_t id() { return reinterpret_cast<std::size_t>(&id); }             \
		constexpr static std::size_t rank() { return (Rank); }                             \
	};                                                                                         \
	}                                                                                          \
	namespace preds {                                                                          \
	const auto Identifier = ::soop::binder<(Rank)>{predicate_definitions::Identifier{}};       \
	}

#define SOOP_MAKE_PREDICATE(Identifier, Rank)                                                      \
	SOOP_MAKE_RENAMED_PREDICATE(Identifier, #Identifier, Rank)

/////////////////////////////////////////////////////////////
//             Implementation of templates
/////////////////////////////////////////////////////////////

template <std::size_t Rank>
template <typename F>
binder<Rank>::binder(F f)
        : m_id{soop::id(f)}, m_name{soop::name(f)} {}

template <std::size_t Rank>
template <typename... Args>
std::string binder<Rank>::operator()(const Args&... args) const {
	static_assert(sizeof...(Args) == Rank, "");
	return m_name + "(" + join(to_string(args)...) + ")";
}

} // namespace soop

#endif
