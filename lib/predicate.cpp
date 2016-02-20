
#include "soop/predicates.hpp"

namespace soop {

std::string formula::to_string() const {
	std::ostringstream stream;
	std::vector<std::string> args;
	std::transform(m_args.begin(), m_args.end(), std::back_inserter(args),
	               [](auto id) { return "o_" + std::to_string(id); });
	m_formula->stream(stream, args);
	return stream.str();
}

void bound_entity::stream(std::ostream& out, const std::vector<std::string>& names) const {
	out << names.at(id);
}

void bound_type::stream(std::ostream& out, const std::vector<std::string>&) const {
	out << m_type.name();
}

void collect_entity(std::vector<std::size_t>& ids, bound_entity& v) {
	const auto index = ids.size();
	ids.push_back(v.id);
	v.id = index;
}

} // namespace soop
