
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <iterator>
#include <algorithm>

#include <procxx.hpp>

#include "soop/z3.hpp"

namespace soop {

namespace {

procxx::process& get_z3() {
	thread_local static procxx::process z3{"z3", "-in", "-nw"};
	thread_local static int dummy = [&]{
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

std::size_t result_id_from_line(const std::string& line) {
	auto it = std::find_if(line.begin(), line.end(), [](char c){return std::isdigit(c);});
	return std::stoul(std::string{it, line.end()}); // performance, robustnes what's that?
}

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

std::vector<std::size_t> request_entities(const std::string& problem, const std::vector<std::string>& results) {
	z3_transaction transaction;
	auto& z3 = get_z3();
	z3 << problem << "(check-sat)\n";
	z3.output().sync();
	std::string line;
		
	std::getline(z3.output(), line);
	if (line != "sat") {
		return {};
	}
	auto ret = std::vector<std::size_t>(results.size(), std::numeric_limits<std::size_t>::max());
	for (const auto& res: results) {
		z3 << "(get-value ((to-entity-id " << res << ")))\n";
	}
	z3.output().sync();
	for (auto& r: ret) {
		std::getline(z3.output(), line);
		r = result_id_from_line(line);
	}
	// it's fragile, but who cares: ;)
	return ret;
}

} // namespace soop
