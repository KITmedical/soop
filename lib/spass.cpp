
#include <iostream>
#include <fstream>
#include <iterator>
#include <procxx.hpp>

#include "spass.hpp"

namespace soop {

struct line : std::string {
	using std::string::basic_string;
};

bool begins_with(const std::string& larger, const std::string& prefix) {
	return larger.size() >= prefix.size() and
	       std::equal(prefix.begin(), prefix.end(), larger.begin());
}

std::string create_tempfile(const std::string& text = {}) {
	const auto filename = std::string{std::tmpnam(nullptr)};
	std::ofstream file{filename};
	if (!file.is_open()) {
		throw std::runtime_error{"could not open tempfile"};
	}
	file << text;
	return filename;
}

bool try_proof(const std::string& problem) {
	auto input = create_tempfile(problem);
	procxx::process spass{"SPASS", input};
	spass.exec();
	using line_it = std::istream_iterator<line>;
	for (std::string line; std::getline(spass.output(), line);) {
		if (begins_with(line, "SPASS beiseite:")) {
			// TODO: use RAII
			std::remove(input.c_str());
			return line == "SPASS beiseite: Proof found.";
		}
	}
	std::remove(input.c_str());
	std::cerr << problem;
	throw std::runtime_error{"Didn't find an answer"};
}


} // namespace soop
