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
struct require_valid_type_t {
	static_assert(
		std::is_convertible<Actual, Expected>::value,
		"the actual argument to the predicate is not is_convertible to "
		"the required type");
	enum { value = 0 };
};

template<typename Actual>
struct require_valid_type_t<Actual, bool> {
	enum { value = 0 };
};

template<typename...As, typename...Es>
constexpr void require_valid_types(actual_types_list<As...>, allowed_types_list<Es...>) {
	using ignore = int[];
	(void) ignore{ (require_valid_type_t<As, Es>::value)...};
}
template<typename...As>
constexpr void require_valid_types(actual_types_list<As...>, allowed_types_list<void>) {
	// no requirements, so no checks
}

} // namespace impl

} // namespace soop;

#endif
