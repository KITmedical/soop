
#include "soop/entity.hpp"

#include "soop/onto.hpp"


namespace soop {

// The problem with implementing it that
// way is that we don't know the exact type
// yet because RTTI doesn't work till all
// ctors have run:
entity::entity(ontology& o, const std::type_info& t){
	o.add_entity(*this, t);
}
entity::entity(std::nullptr_t){}

entity::entity(entity&& o) noexcept:
	m_ontology{o.m_ontology},
	m_id{o.m_id}
{
	o.m_ontology = nullptr;
	if (m_ontology) {
		m_ontology->reseat_entity(m_id, *this);
	}
}

entity& entity::operator=(entity&& o) noexcept {
	if (m_ontology) {
		m_ontology->delete_entity(m_id);
	}
	m_ontology = o.m_ontology;
	o.m_ontology = nullptr;
	m_id = o.m_id;

	if (m_ontology) {
		m_ontology->reseat_entity(m_id, *this);
	}
	return *this;
}

entity::~entity() {
	if (m_ontology) {
		m_ontology->delete_entity(m_id);
	}
}


} // namespace soop
