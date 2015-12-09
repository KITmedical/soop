
#ifndef SOOP_UTIL_HPP
#define SOOP_UTIL_HPP

#include <initializer_list>
#include <string>
#include <tuple>
#include <utility>

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

namespace impl {
template<typename Fun, typename...Ts, std::size_t...Is>
void explode_tuple(Fun f, const std::tuple<Ts...>& t, std::index_sequence<Is...>) {
	using ignore = std::initializer_list<int>;
	(void) ignore{ (f(std::get<Is>(t)), 0)... };
}
} // namespace impl

template<typename Fun, typename...Ts>
void explode_tuple(Fun f, const std::tuple<Ts...>& t) {
	return impl::explode_tuple(f, t, std::make_index_sequence<sizeof...(Ts)>{});
}

} // namespace soop

#endif
