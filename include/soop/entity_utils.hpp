
#ifndef SOOP_ENTITY_UTILS_HPP
#define SOOP_ENTITY_UTILS_HPP

#include "problem.hpp"

namespace std {

template<typename T>
struct hash<soop::e<T>> {
	size_t operator()(const soop::e<T>& arg) const {
		return std::hash<T>{}(*arg);
	}
};

} // namespace std

namespace soop {
	template<typename T>
	bool operator==(const e<T>& l, const e<T>& r) {
		return *l == *r;
	}
	template<typename T>
	bool operator!=(const e<T>& l, const e<T>& r) {
		return *l != *r;
	}
	template<typename T>
	bool operator<(const e<T>& l, const e<T>& r) {
		return *l <  *r;
	}
	template<typename T>
	bool operator>(const e<T>& l, const e<T>& r) {
		return *l >  *r;
	}
	template<typename T>
	bool operator<=(const e<T>& l, const e<T>& r) {
		return *l <= *r;
	}
	template<typename T>
	bool operator>=(const e<T>& l, const e<T>& r) {
		return *l >= *r;
	}

	template<typename T>
	std::ostream& operator<<(std::ostream& s, const e<T>& v) {
		return s << *v;
	}
}


#endif

