#include "soop/onto.hpp"

namespace soop {

std::string ontology::axioms() const {
	auto ret = std::string{};
	for (const auto& axiom : m_axioms) {
		if (axiom.empty()) {
			continue;
		}
		ret += "formula(";
		ret += m_names.at(axiom.front());
		ret += "(";
		ret += std::to_string(axiom.at(1));
		for (auto i = 2u; i < axiom.size(); ++i) {
			ret += ", ";
			ret += std::to_string(axiom.at(i));
		}
		ret += ")).\n";
	}
	for (const auto& axiom : m_preprocessed_axioms) {
		if (axiom.empty()) {
			continue;
		}
		ret += "formula(";
		ret += axiom;
		ret += ").\n";
	}
	return ret;
}

void ontology::delete_axiom(std::size_t index) { m_axioms.at(index) = {}; }

std::size_t ontology::add_preprocessed_axiom(std::string axiom) {
	m_preprocessed_axioms.emplace_back(axiom);
	return m_preprocessed_axioms.size() - 1u;
}

void ontology::delete_preprocessed_axiom(std::size_t index) {
	m_preprocessed_axioms.at(index) = {};
}

} // namespace soop
