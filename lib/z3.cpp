
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
	static procxx::process z3{"z3", "-in", "-nw"};
	static int dummy = [&]{
		z3.exec();
		return 0;
	}();
	(void) dummy;

	z3 << "(push)\n";
	z3 << problem;
	z3 << "(pop)\n";

	z3.output().sync();
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
