
#ifndef ONTO_HPP
#define ONTO_HPP

#include <vector>
#include <cstdint>

#include "../../include/soop/onto.hpp"
soop::ontology make_ontology();

SOOP_MAKE_PREDICATE(is_speaker_of, 2);
SOOP_MAKE_PREDICATE(talk_assignment, 4);

namespace preds {
class distinct_t: public soop::is_predicate {
public:
	template<typename Iterator>
	distinct_t(Iterator begin, Iterator end) {
		for(auto it= begin; it != end; ++it) {
			m_entities.emplace_back(it->id());
		}
	}
	void collect_entities(std::vector<std::size_t>&, std::size_t&);
	void stream(std::ostream& out, const std::vector<std::string>& names) const;
private:
	std::vector<std::size_t> m_entities;
};

template<typename Iterator>
distinct_t distinct(Iterator first, Iterator last) {
	return distinct_t{first, last};
}

} // namespace preds

#endif
