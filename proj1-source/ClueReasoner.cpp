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
    
    /*
     The statement for a card only being in one place can be written as:
     (P1 has C0, and no one else does) OR (P2 has C0, and no one else does) OR (etc...)
     (C1p1 AND !C1p2 ... AND !C1p7) OR (!C1p1 AND C2p2 ... AND !C1p7) ...
     If we represent each conjunction as a symbol, we would have
     S1 OR S2 OR S3 OR ... S7
     We can solve this by expanding each statement one at a time
     S1 OR S2 OR ... S6 OR (!C1p1 AND !C1p2 AND ... C1P7)
     Using distributive property, it can be written as:
     S1 OR ... S5 OR [(S6 OR !C1p1) AND (S6 OR !C1p2)....]
     Expand S6
     S1 OR ... S5 OR [((!C1p1 AND ... C1p6 AND !C1p7) OR !C1p1) AND ...]
     S1 OR ... S5 OR [(!C1p1 OR !C1p7) AND (!C1p2 OR !C1p7) AND ...]
     Distribute S5
     S1 OR ... S4 OR [(S4 OR !C1p1 OR !C1p7) AND (S4 OR !C1p2 OR !C1p7) AND ...]
     And the pattern goes on --> slowly distribute over and over again until we get our clauses
     Because we are iteratively going, we can continuously add create our conjunction for one player, then combine it with the next, and so on.
     
     We will utilize MoveDisjunctionToConjunctions to implement this.
     */
    
    for(int c = 0; c < num_cards; c++) { //Iterate over all cards
        vector<Clause> oneCardDisjunction; //A disjunction of a card being in one place
        for(int p = 0; p <= num_players; p++) { //Iterate over all players
            vector<Clause> playerHasCardConjunction;
            Clause playerHasCardClause;
            playerHasCardClause.push_back(GetPairNum(p, c));
            playerHasCardConjunction.push_back(playerHasCardClause);
            for(int otherPlayer = 0; otherPlayer <= num_players; otherPlayer++) {
                if(otherPlayer != p) {
                    Clause playerDoesntHaveCard;
                    playerDoesntHaveCard.push_back(GetPairNum(otherPlayer, c) * -1);
                }
            }
            if(oneCardDisjunction.empty()) {
                oneCardDisjunction = playerHasCardConjunction;
            } else {
                vector<Clause> temp = oneCardDisjunction;
                oneCardDisjunction = MoveDisjunctionsToConjunctions(temp, playerHasCardConjunction);
            }
        }
        for(Clause clause : oneCardDisjunction) {
            solver->AddClause(clause);
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
    caseFileClause.empty();
    
    for(int i = 0; i < num_weapons; i++) {
        caseFileClause.push_back(GetPairNum("cf", weapons[i]));
    }
    solver->AddClause(caseFileClause);
    caseFileClause.empty();
    
    for(int i = 0; i < num_rooms; i++) {
        caseFileClause.push_back(GetPairNum("cf", rooms[i]));
    }
    solver->AddClause(caseFileClause);
    caseFileClause.empty();

	// No two cards in each category can both be in the case file.
	// TO BE IMPLEMENTED AS AN EXERCISE
}

void ClueReasoner::Hand(string player, string cards[3])
{
	// GetPlayerNum returns the index of the player in the players array (not the suspects array). Remember that the players array is sorted wrt the order that the players play. Also note that, player_num (not to be confused with num_players) is a private variable of the ClueReasoner class that is initialized when this function is called.
	player_num = GetPlayerNum(player);
	
	// TO BE IMPLEMENTED AS AN EXERCISE
}

void ClueReasoner::Suggest(string suggester, string card1, string card2, string card3, string refuter, string card_shown)
{
	// Note that in the Java implementation, the refuter and the card_shown can be NULL. 
	// In this C++ implementation, NULL is translated to be the empty string "".
	// To check if refuter is NULL or card_shown is NULL, you should use if(refuter == "") or if(card_shown == ""), respectively.
	
	// TO BE IMPLEMENTED AS AN EXERCISE
}

void ClueReasoner::Accuse(string suggester, string card1, string card2, string card3, bool is_correct)
{
	// TO BE IMPLEMENTED AS AN EXERCISE (you don't need to implement this)
}

vector<Clause> ClueReasoner::MoveDisjunctionsToConjunctions(vector<Clause> disjunctionOne, vector<Clause> disjunctionTwo)
{
    /*
        We will treat disjunctionOne as the literals we will distribute. If we have (s1 ^ s2) v (s3 ^ s4), we will treat (s3 ^ s4) as just S2. When we then have (s1 v S2) ^ (s2 v S2), we will use DistributeLiteralsToConjunction and treat each s1 and s2 as the one literal with S2 as our right conjunction previously.
     */
    vector<Clause> result;
    for(Clause disjunctionOneClause : disjunctionOne) {
        for(Literal literal : disjunctionOneClause) {
            //Distribute literal, and then add to result
            vector<Clause> literalsDistributed = DistributeLiteralsToConjunction(literal, disjunctionTwo);
            result.insert(result.end(), literalsDistributed.begin(), literalsDistributed.end());
        }
    }
    
    return result;
}

vector<Clause> ClueReasoner::DistributeLiteralsToConjunction(Literal literal, vector<Clause> conjunctions)
{
    /*
        Given a disjunction of a literal and a conjunction, use distributive property to make a conjunction of disjunctions
        Using distributive property: s1 v (s2 ^ s3) = (s1 v s2) ^ (s1 v s3)
     */
    vector<Clause> result;
    for(Clause clauseFromConjunction : conjunctions) {
        for(Literal conjunctionLiteral : clauseFromConjunction) {
            Clause clause;
            clause.push_back(literal);
            clause.push_back(conjunctionLiteral);
            result.push_back(clause);
        }
    }
    return result;
}

















