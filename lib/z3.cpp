
#include <iostream>
#include <fstream>
#include <iterator>
#include <procxx.hpp>

#include "soop/z3.hpp"

namespace soop {

bool begins_with(const std::string& larger, const std::string& prefix) {
	return larger.size() >= prefix.size() and
	       std::equal(prefix.begin(), prefix.end(), larger.begin());
}

bool try_proof(const std::string& problem) {
	procxx::process z3{"z3", "-in", "-nw"};
	z3.exec();
	z3 << problem;
	z3.close(procxx::pipe_t::write_end());
	std::string line;
	std::getline(z3.output(), line);
	if (line == "sat") {
		return true;
	} else if (line == "unsat") {
		return false;
	} else {
		std::cerr << problem;
		throw std::runtime_error{"Didn't find an answer"};
	}
}


} // namespace soop
