
#ifndef ONTO_HPP
#define ONTO_HPP

#include <vector>
#include <cstdint>

#include "../../include/soop/onto.hpp"

#include "data.hpp"

soop::ontology make_ontology();

SOOP_MAKE_TYPECHECKED_PREDICATE(is_speaker_of, 2, speaker, talk);
SOOP_MAKE_TYPECHECKED_PREDICATE(talk_assignment, 4, talk, speaker, room, slot);

#endif
