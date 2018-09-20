#include <iostream>
#include "SatSolver.h"
#include "ClueReasoner.h"

using namespace std;

void TestSatSolver()
{
	// Liar and truth-teller example test code:
	SatSolver solver;
	
	Clause c;
	
	c.push_back(-1);	c.push_back(-2);
	solver.AddClause(c);	c.clear();
	
	c.push_back(2);	c.push_back(1);
	solver.AddClause(c);	c.clear();
	
	c.push_back(-2);	c.push_back(-3);
	solver.AddClause(c);	c.clear();
	
	c.push_back(3);	c.push_back(2);
	solver.AddClause(c);	c.clear();
	
	c.push_back(-3);	c.push_back(-1);
	solver.AddClause(c);	c.clear();
	
	c.push_back(-3);	c.push_back(-2);
	solver.AddClause(c);	c.clear();
	
	c.push_back(1);	c.push_back(2);	c.push_back(3);
	solver.AddClause(c);	c.clear();

	bool result = solver.TestLiteral(3);
	
	if (result == kFalse)
		cout<<"No."<<endl;
	else if (result == kTrue)
		cout<<"Yes."<<endl;
	else
		cout<<"Unknown."<<endl;
}

void TestClueReasoner()
{
	ClueReasoner cr;
	string hand[3] = {"wh", "li", "st"};
	cr.Hand("sc", hand);
	cr.Suggest("sc", "sc", "ro", "lo", "mu", "sc");
	cr.Suggest("mu", "pe", "pi", "di", "pe", "");
	cr.Suggest("wh", "mu", "re", "ba", "pe", "");
	cr.Suggest("gr", "wh", "kn", "ba", "pl", "");
	cr.Suggest("pe", "gr", "ca", "di", "wh", "");
	cr.Suggest("pl", "wh", "wr", "st", "sc", "wh");
	cr.Suggest("sc", "pl", "ro", "co", "mu", "pl");
	cr.Suggest("mu", "pe", "ro", "ba", "wh", "");
	cr.Suggest("wh", "mu", "ca", "st", "gr", "");
	cr.Suggest("gr", "pe", "kn", "di", "pe", "");
	cr.Suggest("pe", "mu", "pi", "di", "pl", "");
	cr.Suggest("pl", "gr", "kn", "co", "wh", "");
	cr.Suggest("sc", "pe", "kn", "lo", "mu", "lo");
	cr.Suggest("mu", "pe", "kn", "di", "wh", "");
	cr.Suggest("wh", "pe", "wr", "ha", "gr", "");
	cr.Suggest("gr", "wh", "pi", "co", "pl", "");
	cr.Suggest("pe", "sc", "pi", "ha", "mu", "");
	cr.Suggest("pl", "pe", "pi", "ba", "", "");
	cr.Suggest("sc", "wh", "pi", "ha", "pe", "ha");
	cr.Suggest("wh", "pe", "pi", "ha", "pe", "");
	cr.Suggest("pe", "pe", "pi", "ha", "", "");
	cr.Suggest("sc", "gr", "pi", "st", "wh", "gr");
	cr.Suggest("mu", "pe", "pi", "ba", "pl", "");
	cr.Suggest("wh", "pe", "pi", "st", "sc", "st");
	cr.Suggest("gr", "wh", "pi", "st", "sc", "wh");
	cr.Suggest("pe", "wh", "pi", "st", "sc", "wh");
	cr.Suggest("pl", "pe", "pi", "ki", "gr", "");

	cr.PrintNotepad();
}

int main()
{
	//TestSatSolver();
	TestClueReasoner();	
	return 0;
}
