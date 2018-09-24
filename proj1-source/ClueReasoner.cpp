#include "ClueReasoner.h"
using namespace std;

int ClueReasoner::GetPlayerNum(string player)
{
	if (player == case_file)
		return num_players;
	
	for (int i = 0; i < num_players; i++)
		if (player == players[i])
			return i;
			
	cout<<"Illegal player: "<<player<<endl;
	return -1;
}

int ClueReasoner::GetCardNum(string card)
{
	for (int i = 0; i < num_cards; i++)
		if (card == cards[i])
			return i;
			
	cout<<"Illegal card: "<<card<<endl;
	return -1;
}

int ClueReasoner::GetPairNum(int player, int card) 
{
	return player * num_cards + card + 1;
}

int ClueReasoner::GetPairNum(string player, string card) 
{
	return GetPairNum(GetPlayerNum(player), GetCardNum(card));
}

int ClueReasoner::Query(string player, string card) 
{
	return solver->TestLiteral(GetPairNum(player,card));
}

string ClueReasoner::QueryString(int return_code)
{
	if (return_code == kFalse)
		return "n";
	else if (return_code == kTrue)
		return "Y";
	else if (return_code == kUnknown)
		return "-";
	else
		return "X";
}

void ClueReasoner::PrintNotepad()
{
	for (int i = 0; i < num_players; i++)
		cout<<"\t"<<players[i];
	cout<<"\t"<<case_file<<endl;
	
	for (int i = 0; i < num_cards; i++)
	{
		cout<<cards[i]<<"\t";
		for (int j = 0; j < num_players; j++)
			cout<<QueryString(Query(players[j], cards[i]))<<"\t";
		
		cout<<QueryString(Query(case_file, cards[i]))<<endl;
	}
}
	
void ClueReasoner::AddInitialClauses()
{
	/* The following code is given as an example to show how to create Clauses and post them to the solver. SatSolver.h uses the following typedefs:
		typedef int Literal;
		typedef std::vector<Literal> Clause;
		
	That is, a Literal (a propositional variable or its negation) is defined as a positive or a negative (meaning that it is in negated form, as in -p or -q) integer, and a Clause is defined as a vector of Literals.
	
	The function GetPairNum(p, c) returns the literal that corresponds to card c being at location p (either a player's hand or the case_file). 
	See ClueReasoner.h, lines 7-31 for a definition of the arrays and variables that you can use in your implementation. 
	*/

	// Each card is in at least one place (including the case file).
	for (int c = 0; c < num_cards; c++)	// Iterate over all cards.
	{
		Clause clause;
		for (int p = 0; p <= num_players; p++)	// Iterate over all players, including the case file (as a possible place for a card).
			clause.push_back(GetPairNum(p, c)); // Add to the clause the literal that states 'p has c'.
		
		solver->AddClause(clause);
	}
	
	// If a card is in one place, it cannot be in another place.
    for(int c = 0; c < num_cards; c++) { //Iterate over all cards
        vector<Clause> oneCardDisjunction; //A disjunction of a card being in one place
        for(int p = 0; p <= num_players; p++) { //Iterate over all players
            int playerIndex = p;
            int nextPlayerIndex = (p == num_players) ? 0 : p + 1;
            while(nextPlayerIndex != playerIndex) {
                Clause clause;
                clause.push_back(GetPairNum(playerIndex, c) * -1);
                clause.push_back(GetPairNum(nextPlayerIndex, c) * -1);
                solver->AddClause(clause);
                nextPlayerIndex = (nextPlayerIndex == num_players) ? 0 : nextPlayerIndex + 1;
            }
        }
    }
	
	// At least one card of each category is in the case file.
	/*
        For this to happen, the case file must have one of the suspects, weapons, rooms, and cards. Can use a simple conjunction of disjunctions
     */
    Clause caseFileClause;
    for(int i = 0; i < num_suspects; i++) {
        caseFileClause.push_back(GetPairNum("cf", suspects[i]));
    }
    solver->AddClause(caseFileClause);
    caseFileClause.clear();
    
    for(int i = 0; i < num_weapons; i++) {
        caseFileClause.push_back(GetPairNum("cf", weapons[i]));
    }
    solver->AddClause(caseFileClause);
    caseFileClause.clear();
    
    for(int i = 0; i < num_rooms; i++) {
        caseFileClause.push_back(GetPairNum("cf", rooms[i]));
    }
    solver->AddClause(caseFileClause);
    caseFileClause.clear();

	// No two cards in each category can both be in the case file.
	//Similar logic to no cards should be in two places, except if there's one card of a category in the case file, then every other card cannot be assigned to the case file
    // If a card is in one place, it cannot be in another place.
    for(int s = 0; s < num_suspects; s++) { //Iterate over suspect cards
        int suspectIndex = s;
        int nextSuspectIndex = (suspectIndex == num_suspects) ? 0 : s + 1;
        while(nextSuspectIndex != suspectIndex) {
            Clause clause;
            clause.push_back(GetPairNum("cf", suspects[suspectIndex]) * -1);
            clause.push_back(GetPairNum("cf", suspects[nextSuspectIndex]) * -1);
            solver->AddClause(clause);
            nextSuspectIndex = (nextSuspectIndex == num_suspects) ? 0 : nextSuspectIndex + 1;
        }
    }
    
    for(int w = 0; w < num_weapons; w++) { //Iterate over suspect cards
        int weaponIndex = w;
        int nextWeaponIndex = (weaponIndex == num_weapons) ? 0 : w + 1;
        while(nextWeaponIndex != weaponIndex) {
            Clause clause;
            clause.push_back(GetPairNum("cf", weapons[weaponIndex]) * -1);
            clause.push_back(GetPairNum("cf", weapons[nextWeaponIndex]) * -1);
            solver->AddClause(clause);
            nextWeaponIndex = (nextWeaponIndex == num_weapons) ? 0 : nextWeaponIndex + 1;
        }
    }
    
    for(int r = 0; r < num_rooms; r++) { //Iterate over suspect cards
        int roomIndex = r;
        int nextRoomIndex = (roomIndex == num_rooms) ? 0 : r + 1;
        while(nextRoomIndex != roomIndex) {
            Clause clause;
            clause.push_back(GetPairNum("cf", weapons[roomIndex]) * -1);
            clause.push_back(GetPairNum("cf", weapons[nextRoomIndex]) * -1);
            solver->AddClause(clause);
            nextRoomIndex = (nextRoomIndex == num_rooms) ? 0 : nextRoomIndex + 1;
        }
    }
}


void ClueReasoner::Hand(string player, string cards[3])
{
	// GetPlayerNum returns the index of the player in the players array (not the suspects array). Remember that the players array is sorted wrt the order that the players play. Also note that, player_num (not to be confused with num_players) is a private variable of the ClueReasoner class that is initialized when this function is called.
	player_num = GetPlayerNum(player);
    for(int i = 0; i < 3; i++) {
        Clause clause;
        clause.push_back(GetPairNum(player, cards[i]));
        solver->AddClause(clause);
    }
}

void ClueReasoner::Suggest(string suggester, string card1, string card2, string card3, string refuter, string card_shown)
{
	// Note that in the Java implementation, the refuter and the card_shown can be NULL. 
	// In this C++ implementation, NULL is translated to be the empty string "".
	// To check if refuter is NULL or card_shown is NULL, you should use if(refuter == "") or if(card_shown == ""), respectively.
	
    if(refuter == "") {
        //no refuter at all --> all players except suggester do not have suggested cards
        for(int i = 0; i < num_players; i++) {
            if(players[i] != suggester) {
                Clause clause1;
                clause1.push_back(GetPairNum(players[i], card1) * -1);
                solver->AddClause(clause1);
                Clause clause2;
                clause2.push_back(GetPairNum(players[i], card2) * -1);
                solver->AddClause(clause2);
                Clause clause3;
                clause3.push_back(GetPairNum(players[i], card3) * -1);
                solver->AddClause(clause3);
            }
        }
    }
    else {
        int refuterIndex = (GetPlayerNum(suggester) == (num_players - 1)) ? 0 : GetPlayerNum(suggester) + 1;
        int lastRefuterIndex = GetPlayerNum(refuter);
        while(refuterIndex != lastRefuterIndex) {
            //The players in between do not have the cards
            Clause clause1;
            clause1.push_back(GetPairNum(players[refuterIndex], card1) * -1);
            solver->AddClause(clause1);
            Clause clause2;
            clause2.push_back(GetPairNum(players[refuterIndex], card2) * -1);
            solver->AddClause(clause2);
            Clause clause3;
            clause3.push_back(GetPairNum(players[refuterIndex], card3) * -1);
            solver->AddClause(clause3);
            refuterIndex = (refuterIndex == (num_players - 1)) ? 0 : refuterIndex + 1;
        }
        
        //we reach the refuter. In this case, we either can see the card shown or not
        if(card_shown == "") {
            //player does not get to see which card was shown upon refute
            Clause clause1;
            clause1.push_back(GetPairNum(players[refuterIndex], card1));
            clause1.push_back(GetPairNum(players[refuterIndex], card2));
            clause1.push_back(GetPairNum(players[refuterIndex], card3));
            solver->AddClause(clause1);
        } else {
            //player gets to see which card was shown
            Clause clause1;
            clause1.push_back(GetPairNum(players[refuterIndex], card_shown));
            solver->AddClause(clause1);
        }
    }
}

void ClueReasoner::Accuse(string suggester, string card1, string card2, string card3, bool is_correct)
{
	// TO BE IMPLEMENTED AS AN EXERCISE (you don't need to implement this)
}

















