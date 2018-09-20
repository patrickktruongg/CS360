#ifndef CLUE_REASONER_H
#define CLUE_REASONER_H

#include "SatSolver.h"
#include <string>
#include <vector>

// 'players' array contains all the players, sorted wrt the order that the players play. 
// The order is important for the 'suggest' function. 
// For instance, if "mu" is the suggester, "wh" is the first player to get a chance to refute the suggestion. If "wh" does not refute, then "gr" gets a turn, and so on (after pl, the order loops back to sc).
const std::string players[6] = {"sc", "mu", "wh", "gr", "pe", "pl"};

// case_file is treated as the 7th player, as a possible place for a card.
const std::string case_file = "cf";	

// suspects, weapons, and rooms array contains the names of the corresponding cards. 
// cards array is a concatanation of these three arrays.
const std::string suspects[6] = {"mu", "pl", "gr", "pe", "sc", "wh"};
const std::string weapons[6] = {"kn", "ca", "re", "ro", "pi", "wr"};
const std::string rooms[9] = {"ha", "lo", "di", "ki", "ba", "co", "bi", "li", "st"};
const std::string cards[21] = {"mu", "pl", "gr", "pe", "sc", "wh", "kn", "ca", "re", "ro", "pi", "wr", "ha", "lo", "di", "ki", "ba", "co", "bi", "li", "st"};

// The variables below specify the number of elements in each array. 
// You can iterate over all possible places, including the case_file, with a for loop: 
// for (int i = 0; i <= num_players; i++). 
// If you only want to iterate over the players, but not the case_file, you should use:
// for (int i = 0; i < num_players; i++)
const int num_players = 6;
const int num_suspects = 6;
const int num_weapons = 6;
const int num_rooms = 9;
const int num_cards = 21;
	
class ClueReasoner
{
public:
	ClueReasoner(){solver = new SatSolver();	player_num = -1;	AddInitialClauses();}
	~ClueReasoner(){delete solver;	solver = NULL;}
	
	// Convert from name to id.
	int GetPlayerNum(std::string player);
	int GetCardNum(std::string card);
	
	// Create the (positive) id for the literal that states 'player P has the card C'.
	int GetPairNum(int player, int card);
	int GetPairNum(std::string player, std::string card);
		
	int Query(std::string player, std::string card);
	std::string QueryString(int return_code);
	void PrintNotepad();
		
	void AddInitialClauses();
	void Hand(std::string player, std::string cards[3]);
	void Suggest(std::string suggester, std::string card1, std::string card2, std::string card3, std::string refuter, std::string card_shown);
	void Accuse(std::string suggester, std::string card1, std::string card2, std::string card3, bool is_correct);
    
    //Helper Methods
    std::vector<Clause> MoveDisjunctionsToConjunctions(std::vector<Clause> disjunctionOne, std::vector<Clause> disjunctionTwo);
    
    std::vector<Clause> DistributeLiteralsToConjunction(Literal literal, std::vector<Clause> conjunctions);
	
private:
	int player_num;	// Id of the current player (determined after Hand(..) is called).
	SatSolver* solver;
};

#endif
