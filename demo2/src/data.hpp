#ifndef DATA_HPP
#define DATA_HPP

#include <string>
#include <iosfwd>
#include <cstdint>
#include <vector>

#include "../../include/soop/onto.hpp"

class speaker_t {
public:
	speaker_t(const std::string& name, std::size_t id) : m_name{name}, m_id{id} {}
	std::size_t id() const {return m_id;}

private:
	std::string m_name;
	std::size_t m_id;
};
using speaker = soop::e<speaker_t>;



class talk_t {
public:
	talk_t(const std::string& title, const std::string& desc, std::size_t s)
	        : m_title{title}, m_desc{desc}, m_speaker_id{s} {}
	std::size_t speaker_id() const { return m_speaker_id; }

private:
	std::string m_title;
	std::string m_desc;
	std::size_t m_speaker_id;
};
using talk = soop::e<talk_t>;




class slot_t {
public:
	slot_t(unsigned time) : m_time{time} {}
	unsigned time() const { return m_time; }

private:
	unsigned m_time;
};
using slot = soop::e<slot_t>;




class room_t {
public:
	room_t(unsigned number) : m_number{number} {}
	unsigned number() const { return m_number; }

private:
	unsigned m_number;
};
using room = soop::e<room_t>;


struct dataset {
	std::vector<speaker> speakers;
	std::vector<talk> talks;
	std::vector<slot> slots;
	std::vector<room> rooms;
};

dataset read_dataset(std::istream& stream, soop::ontology& o);

#endif
