#include "data.hpp"

#include <istream>
#include <iomanip>
#include <stdexcept>

namespace {
void add_speaker(std::istream& stream, std::vector<speaker>& speakers, soop::ontology& o);
void add_talk(std::istream& stream, std::vector<talk>& talks, std::size_t speakers,
              soop::ontology& o);
void add_slot(std::istream& stream, std::vector<slot>& slots, soop::ontology& o);
void add_room(std::istream& stream, std::vector<room>& rooms, soop::ontology& o);
}

dataset read_dataset(std::istream& stream, soop::ontology& o) {
	dataset data;
	std::string datum_type;
	while (stream >> datum_type) {
		if (datum_type == "speaker") {
			add_speaker(stream, data.speakers, o);
		} else if (datum_type == "talk") {
			add_talk(stream, data.talks, data.speakers.size(), o);
		} else if (datum_type == "room") {
			add_room(stream, data.rooms, o);
		} else if (datum_type == "slot") {
			add_slot(stream, data.slots, o);
		}
	}
	return data;
}

namespace {
void add_speaker(std::istream& stream, std::vector<speaker>& speakers, soop::ontology& o) {
	auto id = std::size_t{};
	auto name = std::string{};
	stream >> id >> std::quoted(name);
	if (id != speakers.size()) {
		throw std::invalid_argument{"bad speaker-id"};
	}
	if (name.empty()) {
		throw std::invalid_argument{"bad speaker-name"};
	}
	speakers.emplace_back(o, name, id);
}

void add_talk(std::istream& stream, std::vector<talk>& talks, std::size_t max_speaker_id,
              soop::ontology& o) {
	auto title = std::string{};
	auto desc = std::string{};
	auto speaker_count = std::size_t{};
	stream >> std::quoted(title) >> std::quoted(desc) >> speaker_count;
	auto speakers = std::vector<std::size_t>{};
	std::copy_n(std::istream_iterator<std::size_t>{stream}, speaker_count,
	            std::back_inserter(speakers));
	if (speakers.empty() or std::any_of(speakers.begin(), speakers.end(),
	                                    [=](auto i) { return i >= max_speaker_id; })) {
		throw std::invalid_argument{"bad speaker-id"};
	}
	if (title.empty()) {
		throw std::invalid_argument{"bad talk-title"};
	}
	talks.emplace_back(o, title, desc, std::move(speakers));
}

void add_slot(std::istream& stream, std::vector<slot>& slots, soop::ontology& o) {
	auto time = unsigned{};
	stream >> time;
	slots.emplace_back(o, time);
}

void add_room(std::istream& stream, std::vector<room>& rooms, soop::ontology& o) {
	auto number = unsigned{};
	stream >> number;
	rooms.emplace_back(o, number);
}
}
