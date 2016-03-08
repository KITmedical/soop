#include "soop/onto.hpp"

#include <cassert>

#include "soop/z3.hpp"

namespace soop {

ontology::ontology() {
	add_predicate<preds::instance_of_t>();
}

std::size_t ontology::add_axiom(formula axiom) {
	const auto axiom_id = m_axioms.size();
	// an axiom might refer to an entity more then
	// once so get a list of the acutally used
	// ids first:
	auto used_ids = std::unordered_set<std::size_t>{};
	for (const auto& id: axiom.entity_ids()) {
		used_ids.insert(id);
	}
	for(auto id: used_ids) {
		m_entities.at(id).second.reserve(m_entities.at(id).second.size() + 1u);
	}
	// At this point, the next statement is the last that may throw
	// an exception and the first to do actual semantic changes
	// to the data, which ensures transactional behavior
	m_axioms.emplace_back(std::move(axiom));
	for (auto i: used_ids) {
		m_entities.at(i).second.push_back(axiom_id);
	}
	return axiom_id;
}

ontology::ontology(ontology&& o) noexcept:
	m_axioms(std::move(o.m_axioms)),
	m_entities(std::move(o.m_entities)),
	m_known_types(std::move(o.m_known_types)),
	m_predicates(std::move(o.m_predicates))
{
	o.m_axioms.clear();
	o.add_predicate<preds::instance_of_t>();
	reseat_ontology(this);
}

ontology& ontology::operator=(ontology&& o) noexcept {
	m_axioms = std::move(o.m_axioms);
	m_entities = std::move(o.m_entities);
	m_known_types = std::move(o.m_known_types);
	m_predicates = std::move(o.m_predicates);
	o.m_axioms.clear();
	o.add_predicate<preds::instance_of_t>();
	reseat_ontology(this);
	return *this;
}

ontology::~ontology() {
	reseat_ontology(nullptr);
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
	auto axiom = formula{preds::instance_of(e, bound_type{type})};
	m_axioms.push_back(std::move(axiom));
	return id;
}

void ontology::delete_entity(std::size_t id) {
	auto& data = m_entities.at(id);
	for(auto& a: data.second) {
		delete_axiom(a);
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
		+ "\t(assert " + conjecture.to_string() + ")\n";
	return try_proof(problem);
}

bool ontology::check_sat() const {
	const auto types = this->types();
	const auto entities = this->entities();
	const auto predicates = this->predicates();
	const auto axioms = this->axioms();

	const auto problem
		= "(declare-sort Entity)\n"
		+ types
		+ entities
		+ predicates
		+ axioms;
	return try_proof(problem);
}

std::vector<const entity*> ontology::request_entities_ptr(
		const formula& description,
		const std::vector<std::string>& result_names
) const {
	const auto types = this->types();
	const auto entities = this->entities();
	const auto predicates = this->predicates();
	const auto axioms = this->axioms();
	const auto entity_ids = this->entity_ids();

	auto result_vars = std::string{};
	for (const auto& var: result_names) {
		result_vars += "(declare-const " + var + " Entity)\n";
	}

	const auto problem
		= "(declare-sort Entity)\n"
		+ types
		+ entities
		+ predicates
		+ axioms
		+ entity_ids
		+ result_vars
		+ "(assert " + description.to_string() + ")\n";
	auto res_ids = ::soop::request_entities(problem, result_names);
	auto retval = std::vector<const entity*>(result_names.size());
	std::transform(res_ids.begin(), res_ids.end(), retval.begin(),
			[&](auto id) {return id > m_entities.size()? nullptr : m_entities.at(id).first;});
	return retval;
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
	return transform_if(m_predicates.begin(), m_predicates.end(),
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

std::string ontology::entity_ids() const {
	std::ostringstream ret;
	ret << "(define-fun to-entity-id ((e Entity)) Int\n";
	auto depth = std::size_t{1};
	for(const auto& e: m_entities) {
		if (e.first != nullptr) {
			++depth;
			ret << "(ite (= e " << e.first->name() << ") " << e.first->id() << '\n';
		}
	}
	ret << std::numeric_limits<std::size_t>::max() << std::string(depth, ')') << '\n';
	return ret.str();
}

void ontology::reseat_ontology(ontology* new_location) {
	for(auto& entity: m_entities) {
		if (entity.first) {
			entity.first->m_ontology = new_location;
		}
	}
}

} // namespace soop
