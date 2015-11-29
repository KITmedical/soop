
#ifndef SOOP_ENTITY_UTILS_HPP
#define SOOP_ENTITY_UTILS_HPP

#include "entity.hpp"

namespace std {

template<typename T>
struct hash<soop::e<T>> {
	size_t operator()(const soop::e<T>& arg) const {
		return std::hash<T>{}(*arg);
	}
};

} // namespace std

namespace soop {
	template<typename L, typename R>
	bool operator==(const e<L>& l, const e<R>& r) {
		return *l == *r;
	}
	template<typename L, typename R>
	bool operator!=(const e<L>& l, const e<R>& r) {
		return *l != *r;
	}
	template<typename L, typename R>
	bool operator<(const e<L>& l, const e<R>& r) {
		return *l <  *r;
	}
	template<typename L, typename R>
	bool operator>(const e<L>& l, const e<R>& r) {
		return *l >  *r;
	}
	template<typename L, typename R>
	bool operator<=(const e<L>& l, const e<R>& r) {
		return *l <= *r;
	}
	template<typename L, typename R>
	bool operator>=(const e<L>& l, const e<R>& r) {
		return *l >= *r;
	}

	template<typename T>
	std::ostream& operator<<(std::ostream& s, const e<T>& v) {
		return s << *v;
	}
}


#endif

