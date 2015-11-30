
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

template <typename It, typename F, typename T>
std::string it_transform_join(It it, It e, F f, T t, const std::string& del = ",\n") {
	while (it != e and not f(*it)) {
		++it;
	}
	if (it == e) {
		return "";
	}
	std::string ret = t(*it);
	++it;
	for (; it != e; ++it) {
		if (f(*it)) {
			ret += del;
			ret += t(*it);
		}
	}
	return ret;
}

} // namespace soop

#endif
