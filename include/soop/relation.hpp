
#ifndef RELATION_HPP
#define RELATION_HPP

#include <iostream>
#include <memory>
#include <string>

namespace soop {


template<typename T>
using fun_pointer = T*;




class basic_dynamic_relation {
public:
	virtual ~basic_dynamic_relation() = default;
	virtual std::size_t id() const = 0;
	virtual std::size_t rank() const = 0;
	virtual std::string name() const = 0;
private:

};

template<typename Ret, typename...Args>
class dynamic_relation_fun: public basic_dynamic_relation {
public:
	using fun_type = fun_pointer<Ret(Args...)>;
	dynamic_relation_fun(fun_type f): m_fun{f} {}
	std::size_t id() const final override {
		return reinterpret_cast<std::size_t>(m_fun);
	}
	std::size_t rank() const final override {
		return sizeof...(Args) + 1;
	}
	std::string name() const final override {
		return "dynamic_relation_fun_" + std::to_string(id());
	}
private:
	fun_type m_fun = nullptr;
};

template<typename...Args>
class dynamic_relation_pred: public basic_dynamic_relation {
public:
	using fun_type = fun_pointer<bool(Args...)>;
	dynamic_relation_pred(fun_type f): m_fun{f} {}
	std::size_t id() const final override {
		return reinterpret_cast<std::size_t>(m_fun);
	}
	std::size_t rank() const final override {
		return sizeof...(Args);
	}
	std::string name() const final override {
		return "dynamic_relation_pred_" + std::to_string(id());
	}
private:
	fun_type m_fun = nullptr;
};


template<typename Ret, typename...Args>
std::unique_ptr<basic_dynamic_relation> prepare_relation(fun_pointer<Ret(Args...)> f) {
	return std::make_unique<dynamic_relation_fun<Ret, Args...>>(f);
}

template<typename...Args>
std::unique_ptr<basic_dynamic_relation> prepare_relation(fun_pointer<bool(Args...)> f) {
	return std::make_unique<dynamic_relation_fun<bool, Args...>>(f);
}

} // namespace soop

#endif
