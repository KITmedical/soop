
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

	o.add_axiom(preds::distinct(data.talks.begin(), data.talks.end()));

	std::cout << std::boolalpha;

	const soop::variable<'S'> s{};
	const soop::variable<'S', 'l'> sl{};

	using namespace preds;
	using namespace soop::preds;

	if(!o.check_sat()) {
		std::cout << "No solution exits.\n";
		return 0;
	}

	for(const auto& talk: data.talks) {
		std::cout
			<< talk->title() << "(" << talk.id() << "): "
			<< "in room #";
		const auto& used_room =  o.request_entity<room>(exists({s, sl}, talk_assignment(talk, s, soop::result, sl)));
		std::cout
			<< used_room->number()
			<<", in slot #";
		const auto& used_slot = o.request_entity<slot>(exists({s}, talk_assignment(talk, s, used_room, soop::result)));
		o.add_axiom(talk_assignment(talk, data.speakers.at(talk->speaker_id()), used_room, used_slot));
		std::cout
			<< used_slot->time()
			<< '\n';
	}

} catch (std::runtime_error& e) {
	std::cerr << "Error: " << e.what() << '\n';
	return 11;
}
