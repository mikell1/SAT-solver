#ifndef SAT_SOLVER_H
#define SAT_SOLVER_H

#include <iostream>
#include <vector>
#include <string>
#include <cstring>
#include <cmath>
#include <queue>
#include <fstream>
#include <sstream>
#include <map>
using namespace std;

struct literal {
    uint32_t var;
    bool positive;
};

class Clause;
class Sequent;

void free_clause(Clause *cl);
void free_sequent(Sequent *seq);
void free_remaining_sequents(vector<Sequent*> *stack);

void print_clause_set(Clause** clause_set, int n);

Clause* deep_cp_clause(Clause* cl, uint32_t ignore_var);

uint32_t choose_cut_var(Sequent *seq);
Sequent *atomic_cut_create_sequent(Clause **clause_set, int n, uint32_t var, bool val);
void apply_atomic_cut(Sequent *seq, Sequent **left, Sequent **right, uint32_t var);

Clause** build_full_clause_set(int num_vars);

Clause** read_cnf_file(string filename, int *n);

void test(int num_variables);

bool prove(Sequent *seq);
void solve(Clause **clause_set, int n);

#endif