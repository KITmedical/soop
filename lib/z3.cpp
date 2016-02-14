
#include <iostream>
#include <fstream>
#include <iterator>
#include <procxx.hpp>

#include "soop/z3.hpp"

namespace soop {

namespace {

procxx::process& get_z3() {
	static procxx::process z3{"z3", "-in", "-nw"};
	static int dummy = [&]{
		z3.exec();
		return 0;
	}();
	(void) dummy;
	return z3;
}

struct z3_transaction {
	z3_transaction() {
		get_z3() << "(push)\n";
	}
	~z3_transaction() {
		get_z3() << "(pop)\n";
		get_z3().output().sync();
	}
};

} // namespace

bool try_proof(const std::string& problem) {
	z3_transaction transaction;
	auto& z3 = get_z3();

	z3 << problem;

	z3.output().sync();
	std::string line;
	std::getline(z3.output(), line);
	if (line == "sat") {
		return true;
	} else if (line == "unsat") {
		return false;
	} else {
		std::cerr << problem;
		throw no_answer_found_error{"Didn't find an answer: " + line};
	}
}

std::size_t request_entity(const std::string& problem) {
	z3_transaction transaction;
	auto& z3 = get_z3();
	z3 << problem << "(check-sat)\n";
	z3.output().sync();
	std::string line;
		
	std::getline(z3.output(), line);
	if (line != "sat") {
		return std::numeric_limits<std::size_t>::max();
	}
	z3 << "(get-value ((to-entity-id result)))\n";
	z3.output().sync();
	std::getline(z3.output(), line);
	// it's fragile, but who cares: ;)
	line.erase(0, sizeof("(((to-entity-id result) ")-1u);

	return std::stoul(line);

}

} // namespace soop
