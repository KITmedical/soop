
#include "soop/entity.hpp"


namespace soop {

entity::entity(ontology& o):
	m_ontology{&o}
{
}
entity::entity(std::nullptr_t):
	m_ontology{nullptr},
	m_id{}
{
}

entity::entity(entity&& o) noexcept {
}

entity& entity::operator=(entity&& o) noexcept {
	return *this;
}

entity::~entity() {
}


} // namespace soop
