#ifndef SAT_SOLVER_H
#define SAT_SOLVER_H

#include <iostream>
#include <tuple>
#include <vector>
#include <string>
#include <cstring>
#include <cmath>
#include <ctime>
#include <queue>
#include <fstream>
#include <sstream>
#include <map>
using namespace std;

map<int, string> variable_map;

struct atom {
    uint32_t var_hash;
    bool not_negated;
};

class Clause;
class Sequent;

void free_clause(Clause *cl);
void free_sequent(Sequent *seq);

void print_clause_set(Clause** clause_set, int n);

Clause* deep_cp_clause(Clause* cl);
tuple<Sequent*, Sequent*> apply_atomic_cut(Sequent *seq);

void prove_it(Clause** clause_set, int n);

string increment_string(string str);
vector<string> build_var_set(int n);
uint32_t hash_str_uint32(string& str);
Clause** build_full_clause_set(vector<string> vars);

tuple<Clause**, int> read_clause_set_from_file(string &filename);

void test(int num_variables);


#endif