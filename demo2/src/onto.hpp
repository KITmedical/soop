
#ifndef ONTO_HPP
#define ONTO_HPP

#include "../../include/soop/onto.hpp"

soop::ontology make_ontology();

SOOP_MAKE_PREDICATE(is_speaker_of, 2);
SOOP_MAKE_PREDICATE(talk_assignment, 4);

#endif
