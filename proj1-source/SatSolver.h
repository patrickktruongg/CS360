#ifndef SAT_SOLVER_H
#define SAT_SOLVER_H

#include <stdio.h>
#include <iostream>
#include <fstream>
#include <string>
#include <vector>

typedef int Literal;
typedef std::vector<Literal> Clause;

const int kContradiction = -2;
const int kFalse = -1;
const int kUnknown = 0;
const int kTrue = 1;

class SatSolver
{
public:
	SatSolver(){}
	~SatSolver(){}
	
	void AddClause(Clause c)		{clauses.push_back(c);}
	void ClearClauses() 			{clauses.clear();}
	void AddQueryClause(Clause c) 	{query_clauses.push_back(c);}
	void ClearQueryClauses()	{query_clauses.clear();}
	
	bool MakeQuery();
	int TestLiteral(Literal l);
	
private:
	std::vector<Clause> clauses;
	std::vector<Clause> query_clauses;
};
#endif
