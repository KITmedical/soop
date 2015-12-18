#include "soop/onto.hpp"

#include <cassert>

#include "soop/spass.hpp"

namespace soop {

ontology::ontology() {
	//add_predicate(preds::instance_of);
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
	const auto axiom_id = m_axioms.size();
	m_entities.push_back({&e, {axiom_id}});
	///auto axiom = formula{preds::instance_of(e, type_name)};
	//m_axioms.push_back(std::move(axiom));
	return id;
}

void ontology::delete_entity(std::size_t id) {
	for(auto& a: m_entities.at(id).second) {
		m_axioms.at(a) = {};
	}
	m_entities.at(id) = {};
}

bool ontology::request(const formula& conjecture) const {
	auto types = this->types();
	const auto entities = this->entities();
	const auto predicates = this->predicates();
	const auto axioms = this->axioms();

	if (not types.empty() and not entities.empty()) {
		types += ",\n";
	}

	const auto problem = 
		"begin_problem(prob).\n"

		"list_of_descriptions.\n"
		"name({**}).\n"
		"author({**}).\n"
		"status(unsatisfiable).\n"
		"description({**}).\n"
		"end_of_list.\n"

		"list_of_symbols.\n"
		"functions["
		+ types + entities +
		"].\n"
		"predicates[\n"
		+ predicates +
		"].\n"
		"end_of_list.\n"

		"list_of_formulae(axioms).\n"
		+ axioms +
		"end_of_list.\n"

		"list_of_formulae(conjectures).\n"
		"formula(" + conjecture.to_string() + ").\n"
		"end_of_list.\n"

		"end_problem.\n\n";
	return try_proof(problem);
}

void ontology::reseat_entity(std::size_t id, const entity& e) {
	m_entities.at(id).first = &e;
}

std::string ontology::types() const {
	return it_transform_join(m_known_types.begin(), m_known_types.end(),
			[](const std::string& s) {return not s.empty();},
			[](const std::string& t) {
			return "(" + t +", 0)";
			});
}

std::string ontology::entities() const {
	return it_transform_join(m_entities.begin(), m_entities.end(),
			[](const auto& e) {return e.first != nullptr;},
			[](const auto& e) {
			return "(" + e.first->name() +", 0)";
			});
}

std::string ontology::predicates() const {
	// TODO: deleted predicates
	return it_transform_join(m_predicate_names.begin(), m_predicate_names.end(),
			[](const auto&){return true;},
			[](const auto& p) {
			return "(" + p.first + ", " + std::to_string(p.second) + ")";
			});
}

std::string ontology::axioms() const {
	auto ret = std::string{};
	for (const auto& axiom : m_axioms) {
		if (not axiom) {
			continue;
		}
		ret += "formula(";
		ret += axiom.to_string();
		ret += ").\n";
	}
	return ret;
}


} // namespace soop
