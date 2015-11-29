
#ifndef SOOP_ENTITY_HPP
#define SOOP_ENTITY_HPP

#include <cstddef>
#include <string>

namespace soop {

class ontology;

class entity {
public:
	// At some point I want this to work:
	entity(ontology& o) = delete;

	entity(std::nullptr_t);

	entity(entity&&) noexcept;
	entity& operator=(entity&&) noexcept;

	entity(const entity&) = delete;
	entity& operator=(const entity&) = delete;

	virtual ~entity();

	std::string name() const { return "o_" + std::to_string(m_id); }
	std::size_t id() const { return m_id; }

private:
	friend class ontology;
	ontology* m_ontology = nullptr;
	std::size_t m_id = 0;
};

template <typename T>
class e : public entity {
public:
	template <typename... Args>
	e(ontology& o, Args&&... args) = delete;
	//        : entity{o}, m_value{std::forward<Args>(args)...} {}
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
