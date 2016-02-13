
#include "../../include/soop/onto.hpp"

#include <iostream>
#include <iomanip>
#include <stdexcept>
#include <fstream>

#include "data.hpp"
#include "onto.hpp"

int main(int argc, char** argv) try {
	if (argc != 2) {
		std::cerr << "Usage: " << argv[0] << " <datafile>\n";
		return 1;
	}

	std::ifstream file{argv[1]};
	if (!file.is_open()) {
		std::cerr << "Error: Couldn't open file \"" << argv[1] << "\"\n";
		return 2;
	}
	auto o = make_ontology();
	auto data = read_dataset(file, o);

	for (const auto& talk : data.talks) {
		o.add_axiom(preds::is_speaker_of(data.speakers.at(talk->speaker_id()), talk));
	}

	std::cout << std::boolalpha;

	const soop::variable<'T'> t{};
	const soop::variable<'S'> s{};
	const soop::variable<'R'> r{};
	const soop::variable<'S', 'l'> sl{};

	using namespace preds;
	using namespace soop::preds;
	std::cout << o.request(
	                     forall({t}, implies(instance_of(t, soop::type<talk>),
	                                         exists({s, r, sl}, talk_assignment(t, s, r, sl)))))
	          << '\n';

} catch (std::runtime_error& e) {
	std::cerr << "Error: " << e.what() << '\n';
	return 11;
}
