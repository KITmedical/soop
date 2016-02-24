
#include "../../include/soop/onto.hpp"

#include <iostream>
#include <iomanip>
#include <stdexcept>
#include <fstream>

#include "data.hpp"
#include "onto.hpp"

int main(int argc, char** argv) try {
	if (argc < 2 or argc > 3) {
		std::cerr << "Usage: " << argv[0] << " <datafile> [checkonly]\n";
		return 1;
	}
	const auto quit_early = (argc == 3 and argv[2] == std::string{"checkonly"});

	std::ifstream file{argv[1]};
	if (!file.is_open()) {
		std::cerr << "Error: Couldn't open file \"" << argv[1] << "\"\n";
		return 2;
	}
	auto o = make_ontology();
	auto data = read_dataset(file, o);

	for (const auto& talk : data.talks) {
		for (const auto speaker_id: talk->speaker_ids()) {
			o.add_axiom(preds::is_speaker_of(data.speakers.at(speaker_id), talk));
		}
	}

	o.add_axiom(soop::preds::distinct_range(data.talks.begin(), data.talks.end()));

	const soop::variable<'r'> r{};
	const soop::variable<'S', 'l'> sl{};

	using preds::talk_assignment;
	using soop::preds::exists;

	if (!o.check_sat()) {
		std::cout << "No solution exits.\n";
		return 0;
	}
	if (quit_early) {
		return 0;
	}

	for (const auto& talk : data.talks) {
		const auto& speaker = data.speakers.at(talk->speaker_ids().front());

		auto solution = o.request_entities<room, slot>(talk_assignment(talk, speaker, r, sl), r, sl);
		const auto& used_room = std::get<0>(solution);
		const auto& used_slot = std::get<1>(solution);

		std::cout
			<< talk->title()
			<< ": in room #" << used_room->number()
			<< ", in slot #" << used_slot->time() << '\n';

		o.add_axiom(talk_assignment(talk, speaker, used_room, used_slot));
	}

} catch (std::runtime_error& e) {
	std::cerr << "Error: " << e.what() << '\n';
	return 11;
}
