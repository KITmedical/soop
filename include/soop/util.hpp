
#ifndef SOOP_UTIL_HPP
#define SOOP_UTIL_HPP

#include <string>

namespace soop {

inline std::string join() { return ""; }
template <typename... Tail>
std::string join(std::string head, const Tail&... tail) {
	using ignore = std::initializer_list<int>;
	(void)ignore{[&](const auto& arg) {
		head += ", ";
		head += arg;
		return 0;
	}(tail)...};
	return head;
}

} // namespace soop

#endif

