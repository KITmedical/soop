
#include "reader.hpp"

#include <fstream>
#include <stdexcept>
#include <iomanip>

#include "definitions.hpp"
#include "onto.hpp"

class file_open_error: public std::runtime_error {
	using std::runtime_error::runtime_error;
};

static std::ifstream open_file(const std::string& filename) {
	std::ifstream file{filename};
	if (!file.is_open()) {
		throw file_open_error{"Could not open " + filename};
	}
	return file;
}

static std::unordered_map<soop::e<std::size_t>, soop::e<std::string>> read_name_map(const std::string& filename) {
	std::unordered_map<soop::e<std::size_t>, soop::e<std::string>> map;
	auto file = open_file(filename);
	auto id = std::size_t{};
	auto name = std::string{};
	while (file >> id >> std::quoted(name)) {
		map.emplace(soop::e<std::size_t>{get_onto(), id},  soop::e<std::string>{get_onto(), name});
	}
	return map;
}

static std::map<std::pair<soop::e<std::size_t>, soop::e<std::size_t>>, soop::e<std::size_t>> read_tuple_map(const std::string& filename) {
	std::map<std::pair<soop::e<std::size_t>, soop::e<std::size_t>>, soop::e<std::size_t>> map;
	using size = soop::e<std::size_t>;
	auto file = open_file(filename);
	auto key1 = std::size_t{};
	auto key2 = std::size_t{};
	auto val  = std::size_t{};
	while (file >> key1 >> key2 >> val) {
		map.emplace(std::make_pair(size{get_onto(), key1}, size{get_onto(), key2}), size{get_onto(), val});
	}
	return map;
}


student_name_map read_student_names(const std::string& filename) {
	auto map = read_name_map(filename);
	for(auto& p: map) {
		get_onto().declare_satifies(is_student, p.first);
	}
	return {get_onto(), map};
}

teacher_name_map read_teacher_names(const std::string& filename) {
	auto map = read_name_map(filename);
	for(auto& p: map) {
		get_onto().declare_satifies(is_teacher, p.first);
	}
	return {get_onto(), map};
}

subject_name_map read_subject_names(const std::string& filename) {
	auto map = read_name_map(filename);
	for(auto& p: map) {
		get_onto().declare_satifies(is_subject, p.first);
	}
	return {get_onto(), map};
}

grade_map read_grade_map(const std::string& filename) {
	auto map = read_tuple_map(filename);
	for(auto& p: map) {
		get_onto().declare_satifies(is_student, p.first.first);
		get_onto().declare_satifies(is_subject, p.first.second);
		get_onto().declare_satifies(is_grade, p.second);
	}
	return {get_onto(), map};
}

student_teacher_map read_teacher_map(const std::string& filename) {
	auto map = read_tuple_map(filename);
	for(auto& p: map) {
		get_onto().declare_satifies(is_student, p.first.first);
		get_onto().declare_satifies(is_subject, p.first.second);
		get_onto().declare_satifies(is_teacher, p.second);
	}
	return {get_onto(), map};
}
