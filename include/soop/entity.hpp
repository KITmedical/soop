
#ifndef SOOP_ENTITY_HPP
#define SOOP_ENTITY_HPP

#include <cstddef>
#include <string>
#include <typeinfo>
#include <vector>

namespace soop {

class ontology;

class entity {
public:
	entity(ontology& o, const std::type_info& t);

	entity(std::nullptr_t);

	entity(entity&&) noexcept;
	entity& operator=(entity&&) noexcept;

	// These COULD be added in the current
	// model by adding the axuiom equal(o, *this),
	// but it is very unclear, whether this is desireable
	entity(const entity&) = delete;
	entity& operator=(const entity&) = delete;

	virtual ~entity();

	std::string name() const { return "o_" + std::to_string(m_id); }
	std::size_t id() const { return m_id; }

private:
	friend class ontology;
	mutable ontology* m_ontology = nullptr;
	std::size_t m_id = 0;
};

template <typename T>
class e : public entity {
public:
	template <typename... Args>
	e(ontology& o, Args&&... args)
	        : entity{o, typeid(*this)}, m_value{std::forward<Args>(args)...} {}
	template <typename... Args>
	e(std::nullptr_t, Args&&... args)
	        : entity{nullptr}, m_value{std::forward<Args>(args)...} {}
	T& operator*() { return m_value; }
	const T& operator*() const { return m_value; }
	T* operator->() { return &m_value; }
	const T* operator->() const { return &m_value; }

private:
	T m_value;
};

} // namespace soop

#endif
