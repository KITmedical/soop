
#include <soop/buildin_predicates.hpp>

namespace soop {
namespace preds {
void distinct_range_t::collect_entities(std::vector<std::size_t>& ids) {
	for(auto& id: m_entities) {
		const auto index = ids.size();
		ids.push_back(id);
		id = index;
	}
}

void distinct_range_t::stream(std::ostream& out, const std::vector<std::string>& args) const {
	out << "(distinct ";
	for(auto i: m_entities) {
		out << args.at(i) << ' ';
	}
	out << ')';
}
} // namespace preds
} // namespace soop
