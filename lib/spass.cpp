
#include <iostream>
#include <fstream>
#include <iterator>
#include <procxx.hpp>

#include "soop/spass.hpp"

namespace soop {

bool begins_with(const std::string& larger, const std::string& prefix) {
	return larger.size() >= prefix.size() and
	       std::equal(prefix.begin(), prefix.end(), larger.begin());
}

bool try_proof(const std::string& problem) {
	procxx::process spass{"SPASS", "/dev/stdin"};
	spass.exec();
	spass << problem;
	spass.close(procxx::pipe_t::write_end());
	for (std::string line; std::getline(spass.output(), line);) {
		if (begins_with(line, "SPASS beiseite:")) {
			return line == "SPASS beiseite: Proof found.";
		}
	}
	std::cerr << problem;
	throw std::runtime_error{"Didn't find an answer"};
}


} // namespace soop
