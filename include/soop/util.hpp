
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

template <typename It, typename F>
std::string it_transform_join(It b, It e, F f, const std::string& del = ",\n") {
	if (b == e) {
		return "";
	}
	std::string ret = f(*b);
	++b;
	for (; b != e; ++b) {
		ret += del;
		ret += f(*b);
	}
	return ret;
}

} // namespace soop

#endif
