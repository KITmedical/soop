
#ifndef SOOP_UTIL_HPP
#define SOOP_UTIL_HPP

#include <algorithm>
#include <initializer_list>
#include <string>
#include <tuple>
#include <utility>

namespace soop {

inline void ignore(std::initializer_list<int>) {}

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
std::string it_transform_join(It begin, It e, F f, T t, const std::string& del = ",\n") {
	auto it = std::find_if(begin, e, f);
	if (it == e) {
		return "";
	}
	auto ret = std::string{t(*it)};
	for (it = std::find_if(it, e, f); it != e; it = std::find_if(it, e, f)) {
		ret += del;
		ret += t(*it);
	}
	return ret;
}

template<typename Fun, typename...Ts, std::size_t...Is>
void explode_tuple(Fun f, const std::tuple<Ts...>& t, std::index_sequence<Is...>) {
	using ignore = std::initializer_list<int>;
	ignore({ (f(std::get<Is>(t)), 0)... });
}

template<typename Fun, typename...Ts>
void explode_tuple(Fun f, const std::tuple<Ts...>& t) {
	return explode_tuple(f, t, std::make_index_sequence<sizeof...(Ts)>{});
}

template <typename F, typename... Ts, std::size_t... Is>
void tuple_foreach(std::tuple<Ts...>& t, F f, std::index_sequence<Is...>) {
	ignore({(f(std::get<Is>(t)), 0)...});
}
template <typename F, typename... Ts>
void tuple_foreach(std::tuple<Ts...>& t, F f) {
	tuple_foreach(t, f, std::make_index_sequence<sizeof...(Ts)>{});
}
template <typename F, typename... Ts, std::size_t... Is>
void tuple_foreach(const std::tuple<Ts...>& t, F f, std::index_sequence<Is...>) {
	ignore({(f(std::get<Is>(t)), 0)...});
}
template <typename F, typename... Ts>
void tuple_foreach(const std::tuple<Ts...>& t, F f) {
	tuple_foreach(t, f, std::make_index_sequence<sizeof...(Ts)>{});
}
template <typename F, typename... Ts, std::size_t... Is>
void indexed_tuple_foreach(std::tuple<Ts...>& t, F f, std::index_sequence<Is...>) {
	ignore({(f(std::get<Is>(t), Is), 0)...});
}
template <typename F, typename... Ts>
void indexed_tuple_foreach(std::tuple<Ts...>& t, F f) {
	indexed_tuple_foreach(t, f, std::make_index_sequence<sizeof...(Ts)>{});
}
template <typename F, typename... Ts, std::size_t... Is>
void indexed_tuple_foreach(const std::tuple<Ts...>& t, F f, std::index_sequence<Is...>) {
	ignore({(f(std::get<Is>(t), Is), 0)...});
}
template <typename F, typename... Ts>
void indexed_tuple_foreach(const std::tuple<Ts...>& t, F f) {
	indexed_tuple_foreach(t, f, std::make_index_sequence<sizeof...(Ts)>{});
}


} // namespace soop

#endif
