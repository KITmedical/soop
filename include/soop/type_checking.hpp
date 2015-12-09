#ifndef SOOP_TYPE_CHECKING_HPP
#define SOOP_TYPE_CHECKING_HPP

#include <string>
#include <type_traits>

namespace soop {


template<typename...Ts>
struct allowed_types_list{};

namespace impl {

template<typename...Ts>
struct actual_types_list{};

template<typename Actual, typename Expected>
constexpr void require_valid_type() {
	static_assert(
		std::is_convertible<Actual, Expected>::value
		or
		std::is_convertible<Actual, std::string>::value
		, "the actual argument to the predicate is not is_convertible to "
		"the required type");
}

template<typename...As, typename...Es>
constexpr void require_valid_types(actual_types_list<As...>, allowed_types_list<Es...>) {
	using ignore = int[];
	(void) ignore{ (require_valid_type<As, Es>(),0)...};
}
template<typename...As>
constexpr void require_valid_types(actual_types_list<As...>, allowed_types_list<void>) {
	// no requirements, so no checks
}

} // namespace impl

} // namespace soop;

#endif
