
#include <algorithm>
#include <cassert>
#include <iostream>
#include <utility>

#include "problem.hpp"

namespace soop {

void basic_problem::add(entity& e) {
	e.m_id = m_entities.size();
	m_entities.push_back(&e);
}

void basic_problem::clone(entity& e, std::size_t orig_id) {
	add(e);
	const auto new_id = e.m_id;
	for(auto rel: m_known_relations.at(orig_id)) {
		auto rels = m_dynamic_axioms.at(rel);
		std::transform(rels.begin(), rels.end(), rels.begin(),
				[&](std::size_t i) { return i == orig_id ? new_id : i;});
		const auto axiom_id = m_dynamic_axioms.size();
		m_dynamic_axioms.push_back(std::move(rels));
		m_known_relations[new_id].push_back(axiom_id);
	}
}

std::string basic_problem::dyn_fun_list() const {
	auto ret = std::string{};
	for (const auto e : m_entities) {
		if (e) {
			ret += ("(" + (*e).entity_id_name() + ", 0),\n");
		}
	}
	if (!ret.empty()) {
		ret.pop_back();
		ret.pop_back();
	}
	return ret;
}

std::string basic_problem::dyn_rel_list() const {
	auto ret = std::string{"(instance, 2),\n"};
	for (const auto& a: m_dynamic_relations) {
		ret += ("(dynamic_relation_" + std::to_string(a.first) + ", " + std::to_string(a.second)+"),\n");
	}
	ret.pop_back();
	ret.pop_back();
	return ret;
}

std::string basic_problem::dyn_axiom_list() const {
	auto ret = std::string{};
	for (const auto e : m_entities) {
		if (e) {
			ret += ("formula(instance(" + (*e).entity_id_name() + ", " + (*e).instance_of() +
				")).\n");
		}
	}
	for (const auto& a : m_dynamic_axioms) {
		if (a.empty()) {
			continue;
		}
		ret += ("formula(dynamic_relation_" + std::to_string(a.front()) + "(");
		assert(a.size() >= 2);
		ret += ("dynamic_object_" + std::to_string(a[1]));
		for(auto i = std::size_t{2}; i < a.size(); ++i) {
			ret += (", dynamic_object_" + std::to_string(a[i]));
		}

		ret += ")).\n";
	}
	return ret;
}

entity::entity(basic_problem& p): m_prob{&p} { m_prob->add(*this); }

entity::entity(entity&& other) noexcept {
	m_id = std::exchange(other.m_id, static_cast<std::size_t>(-1));
	m_prob = std::exchange(other.m_prob, nullptr);
	if (m_prob) {
		assert(m_id != static_cast<std::size_t>(-1));
		m_prob->reseat_entity(m_id,*this);
	}
}

entity& entity::operator=(entity&& other) noexcept {
	if (m_prob) {
		m_prob->remove_entity(m_id);
	}
	m_id = other.m_id;
	m_prob = other.m_prob;
	other.m_id = static_cast<std::size_t>(-1);
	other.m_prob = nullptr;
	if (m_prob) {
		m_prob->reseat_entity(m_id, *this);
	}
	return *this;
}

entity::entity(const entity& other): m_prob{other.m_prob} {
	if (m_prob) {
		m_prob->clone(*this, other.m_id);
		//m_prob->reseat_entity(m_id,*this);
	}
}

entity& entity::operator=(const entity& other) noexcept {
	if (m_prob) {
		m_prob->remove_entity(m_id);
	}
	m_prob = other.m_prob;
	if (m_prob) {
		m_prob->clone(*this, other.m_id);
	}
	return *this;
}

entity::~entity() {
	if (m_prob) {
		m_prob->remove_entity(m_id);
	}
}

void basic_problem::reseat_entity(std::size_t id, const entity& e) {
	assert(id < m_entities.size() and m_entities[id] != nullptr);
	m_entities[id] = &e;
}
void basic_problem::remove_entity(std::size_t id) {
	assert(id < m_entities.size() and m_entities[id] != nullptr);
	for (auto i: m_known_relations.at(id)) {
		m_dynamic_axioms[i] = {};
	}
	m_entities[id] = nullptr;
	m_known_relations.erase(id);
}


} //namespace soop

