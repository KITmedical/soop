#ifndef SOOP_Z3_HPP
#define SOOP_Z3_HPP

#include <string>
#include <stdexcept>

namespace soop {

class proofer_error: public std::runtime_error {
public:
	using std::runtime_error::runtime_error;
};

class no_answer_found_error: public proofer_error {
public:
	using proofer_error::proofer_error;
};

bool try_proof(const std::string& request);

} // namespace soop

#endif
