
#include "soop/entity.hpp"


namespace soop {

entity::entity(ontology& o):
	m_ontology{&o}
{
	// TODO
}
entity::entity(std::nullptr_t):
	m_ontology{nullptr},
	m_id{}
{
	// TODO
}

entity::entity(entity&& o) noexcept {
	// TODO
}

entity& entity::operator=(entity&& o) noexcept {
	// TODO
	return *this;
}

entity::~entity() {
	// TODO
}


} // namespace soop
