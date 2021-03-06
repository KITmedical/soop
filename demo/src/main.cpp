
#include <iostream>
#include <stdexcept>

#include "definitions.hpp"
#include "reader.hpp"
#include "stats.hpp"
#include "onto.hpp"


int main(int argc, char** argv) try {
	if (argc != 6) {
		std::cerr << "Error: invalid number of arguments\n";
		return 1;
	}
	auto student_names = read_student_names(argv[1]);
	auto teacher_names = read_teacher_names(argv[2]);
	auto subject_names = read_subject_names(argv[3]);
	auto grades   = read_grade_map(argv[4]);
	auto teachers = read_teacher_map(argv[5]);
	for (auto& g: *grades) {
		get_onto().add_axiom(soop::preds::equal(g.first.first, student_names->find(g.first.first)->first));
	}

	const auto teacher_success = avg_success(grades, teachers);
	for (const auto& t: teacher_success) {
		std::cout << teacher_names->at({nullptr, t.first}) << ": " << t.second << '\n';
	}
	soop::variable<'x'> x;
	std::cout << "There exists a student that deserves a price: " << std::boolalpha
		<< get_onto().request(soop::preds::exists({x}, preds::deserves_price(x))) << '\n';
	for(auto& stud: *student_names) {
		std::cout << *stud.second << ": " << get_onto().request(preds::deserves_price(stud.first)) << '\n';
	}
} catch (std::runtime_error& e) {
	std::cerr << "Error: " << e.what() << '\n';
	return 2;
} catch (std::exception& e) {
	std::cerr << "Bad Error: " << e.what() << '\n';
	return 3;
}
