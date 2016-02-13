#include "soop/onto.hpp"

#include <cassert>

#include "soop/z3.hpp"

namespace soop {

ontology::ontology() {
	add_predicate<preds::instance_of_t>();
}

std::size_t ontology::add_axiom(formula axiom) {
	m_axioms.emplace_back(std::move(axiom));
	return m_axioms.size() - 1u;
}

void ontology::delete_axiom(std::size_t index) {
	m_axioms.at(index) = {};
}

std::size_t ontology::add_entity(entity& e) {
	return add_entity(e, typeid(e));
}
std::size_t ontology::add_entity(entity& e, const std::type_info& type) {
	assert(e.m_ontology == nullptr);
	const auto type_name = std::string{type.name()};
	assert(m_known_types.count(type_name));
	// If increasing the vectors throws, we would like
	// this to happen before we changed state:
	m_entities.reserve(m_entities.size() + 1);
	m_axioms.reserve(m_axioms.size() + 1);

	const auto id = m_entities.size();

	e.m_ontology = this;
	e.m_id = id;
	m_entities.push_back({&e, {m_axioms.size()}});
	auto axiom = formula{preds::instance_of(e, dyn_type{type})};
	m_axioms.push_back(std::move(axiom));
	return id;
}

void ontology::delete_entity(std::size_t id) {
	auto& data = m_entities.at(id);
	for(auto& a: data.second) {
		m_axioms.at(a) = {};
	}
	data = {};
}

bool ontology::request(const formula& conjecture) const {
	const auto types = this->types();
	const auto entities = this->entities();
	const auto predicates = this->predicates();
	const auto axioms = this->axioms();

	const auto problem
		= "(declare-sort Entity)\n"
		+ types
		+ entities
		+ predicates
		+ axioms
		+ "(push)\n"
		  "\t(assert (not " + conjecture.to_string() + "))\n"
		  "\t(check-sat)\n"
		  "(pop)\n";
	return !try_proof(problem);
}

void ontology::reseat_entity(std::size_t id, const entity& e) {
	m_entities.at(id).first = &e;
}

std::string ontology::types() const {
	return transform_if(m_known_types.begin(), m_known_types.end(),
		[](const std::string& s) {return not s.empty();},
		[](const std::string& t) {
			return "(declare-const " + t +" Entity)\n";
		})+
		"(assert (distinct "+
		transform_if(m_known_types.begin(), m_known_types.end(),
		[](const std::string& s) {return not s.empty();},
		[](const std::string& t) {
			return " " + t +" \n";
		})+
		"))\n";
}

std::string ontology::entities() const {
	return transform_if(m_entities.begin(), m_entities.end(),
		[](const auto& e) {return e.first != nullptr;},
		[](const auto& e) {
			return "(declare-const " + e.first->name() +" Entity)\n";
		}) +
		"(assert (forall ((x Entity)) (or\n" +
		transform_if(m_entities.begin(), m_entities.end(),
		[](const auto& e) {return e.first != nullptr;},
		[](const auto& e) {
			return "(= x " + e.first->name() +")\n";
		})+
		transform_if(m_known_types.begin(), m_known_types.end(),
		[](const std::string& s) {return not s.empty();},
		[](const std::string& t) {
			return "(= x " + t +")\n";
		})+
		")))\n";
}

std::string ontology::predicates() const {
	// TODO: deleted predicates
	return transform_if(m_predicate_names.begin(), m_predicate_names.end(),
		[](const auto&){return true;},
		[](const auto& p) {
			return "(declare-fun " + p.first + " (" + repeat("Entity ",p.second) + ") Bool)\n";
		});
}

std::string ontology::axioms() const {
	auto ret = std::string{};
	for (const auto& axiom : m_axioms) {
		if (not axiom) {
			continue;
		}
		ret += "(assert ";
		ret += axiom.to_string();
		ret += ")\n";
	}
	return ret;
}


} // namespace soop
