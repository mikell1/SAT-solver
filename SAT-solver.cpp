#include "SAT-solver.hpp"
#include "cnf_io.hpp"

class Clause {
    public:
        literal *literals;
        int n;
        Clause(literal *literals, int n);
        int can_be_simplified_with(literal lit, literal *lit_out);
        void print();
};

Clause::Clause(literal *literals, int n) {
    this->literals = literals;
    this->n = n;
}

/**
 * Determines whether the clause can be simplified with a given literal.
 * Returns true if the given literal's variable is contained in its array of literals.
*/
int Clause::can_be_simplified_with(literal lit, literal *lit_out) {
    for (int i = 1; i < n; i++) {
        if (lit.var == this->literals[i].var) {
            // Clause contains given literal's variable, thus can be simplified with given literal
            *lit_out = {this->literals[i].var, this->literals[i].positive};
            return 1;
        }
    }

    return 0;
}

void Clause::print() {
    for (int i = 0; i < n; i++) {
        if (!literals[i].positive) cout << "-";
        cout << literals[i].var << " ";
    }
}

class Sequent {
    public:
        Clause **clause_set;
        int n;
        queue<int> single_clause_indexes;
        map<uint32_t, int> var_count;
        Sequent(Clause **clause_set, int n);
        bool is_axiom();
        bool propagate();
};

Sequent::Sequent(Clause **clause_set, int n) {
    this->clause_set = clause_set;
    this->n = n;
}

/**
 * Determining whether the sequent is an axiom or not.
 * A sequent is an axiom if the sequent is true for all possible interpretations.
*/
bool Sequent::is_axiom() {
    for (int i = 0; i < n; i++) {
        if (clause_set[i]->n == 0)
            // Axiom by empty clause
            return true;
        // skips if clause' length is not 1
        if (clause_set[i]->n != 1) continue;

        literal this_lit = clause_set[i]->literals[0];

        for (int j = 0; j < n; j++) {
            if (i == j) continue;
            if (clause_set[j]->n != 1) continue;
            literal other_lit = clause_set[j]->literals[0];
            // Checks if first literal's variable is equal to second literal's variable,
            // and if respective literal's negation is different.
            if (this_lit.var == other_lit.var && this_lit.positive != other_lit.positive)
                // Axiom
                return true;
        }
    }
    return false;
}

/**
 * Applies unit propagation on a sequent.
 * I.e. for all single literal clauses in it's clause set,
 * remove all clauses containing the single literal from the clause set,
 * and remove the negated literal from any clause' literals array where the negated
 * literal of the single literal is included.
*/
bool Sequent::propagate() {
    while (!single_clause_indexes.empty()) {
        int i = single_clause_indexes.front();
        if (i > n || clause_set[i]->n != 1) {
            // Clause contains more than one literal or clause index is out of bounds.
            single_clause_indexes.pop();
            continue;
        }
        
        literal lit = clause_set[i]->literals[0];
        for (int j = 0; j < n; j++) {
            literal simplify_with;
            if (clause_set[j]->can_be_simplified_with(lit, &simplify_with)) {
                if (lit.positive != simplify_with.positive) {
                    // Unit resolution
                    // Remove the atom from the clause' literals array
                    for (int k = 0; k < clause_set[j]->n; k++) {
                        if (clause_set[j]->literals[k].var == simplify_with.var && clause_set[j]->literals[k].positive == simplify_with.positive) {
                            clause_set[j]->literals[k] = clause_set[j]->literals[--clause_set[j]->n];
                            if (clause_set[j]->n == 1) single_clause_indexes.push(j);
                            break;
                        }
                    }
                } else {
                    // Unit subsumption
                    // Remove the whole clause
                    if (clause_set[--n]->n == 1) single_clause_indexes.push(j);
                    free_clause(clause_set[j]);
                    clause_set[j] = clause_set[n];
                }

                return true;
            }
        }
        single_clause_indexes.pop();
    }

    return false;
}

/**
 * Chooses the variable with the most occurences regardless of negation.
*/
uint32_t choose_cut_var(Sequent *seq) {
    int max = 0;
    uint32_t var = 0;

    for (auto const& [key, count] : seq->var_count) {
        if (count > max) {
            max = count;
            var = key;
        }
    }

    if (max == 1) return 0;
    return var;
}

/**
 * Creates a new sequent with atomic cut applied based on chosen variable.
*/
Sequent *atomic_cut_create_sequent(Clause **clause_set, int n, uint32_t var, bool val) {
    // Creates a new sequent
    literal this_lit = {var, val};
    literal *literals = new literal[1];
    literals[0] = this_lit;

    Clause *cl = new Clause(literals, 1);
    Clause **cl_set = new Clause*[n+1];
    int c_num = 0;

    queue<int> single_clause_indexes;
    map<uint32_t, int> var_count;

    for (int i = 0; i < n; i++) {
        bool keep = true;
        for (int j = 0; j < clause_set[i]->n; j++) {
            literal other_lit = clause_set[i]->literals[j];
            if (other_lit.var == this_lit.var && other_lit.positive == this_lit.positive) {
                // Unit resolution, ignores clause
                keep = false;
                break;
            }
        }
        if (keep) {
            for (int j = 0; j < clause_set[i]->n; j++) {
                literal l = clause_set[i]->literals[j];
                if (l.var != var) {
                    if (var_count.find(l.var) != var_count.end()) {
                        // Increment count by 1
                        var_count[l.var]++;
                    } else {
                        var_count[l.var] = 1;
                    }
                }
            }
            cl_set[c_num] = deep_cp_clause(clause_set[i], this_lit.var);
            if (cl_set[c_num]->n == 1) {
                // Save single clause index
                single_clause_indexes.push(c_num);
            }
            c_num++;
        }
    }

    cl_set[c_num] = cl;
    Sequent *seq = new Sequent(cl_set, c_num+1);
    seq->single_clause_indexes = single_clause_indexes;
    seq->var_count = var_count;

    return seq;
}

uint32_t atomic_cut_is_possible(Sequent *seq) {
    return choose_cut_var(seq);
}

/**
 * Applies atomic cut to a sequent to achieve atomic cut elimination.
 * Returns a left- and right sequent each with an additional clause
 * containing a single negated- and non-negated variable respectively.
 * The chosen variable is chosen strategically.
 * Returns 0 if atomic cut cannot be applied.
*/
void apply_atomic_cut(Sequent *seq, Sequent **left, Sequent **right, uint32_t var) {
    Clause **clause_set = seq->clause_set;
    int n = seq->n;

    // Sets the left Sequent
    *left = atomic_cut_create_sequent(clause_set, n, var, true);
    // Sets the right Sequent
    *right = atomic_cut_create_sequent(clause_set, n, var, false);
}

/**
 * Deep copies a clause.
*/
Clause* deep_cp_clause(Clause* cl, uint32_t ignore_var) {
    int n = cl->n;
    literal *literals = new literal[n];
    int c_i = 0;

    for (int i = 0; i < n; i++) {
        if (cl->literals[i].var == ignore_var) continue; // Unit resolution
        literal lit = {cl->literals[i].var, cl->literals[i].positive};
        literals[c_i] = lit;
        c_i++;
    }

    Clause *clause = new Clause(literals, c_i);
    return clause;
}

void free_clause(Clause *cl) {
    delete []cl->literals;
    delete cl;
}

void free_sequent(Sequent *seq) {
    for (int i = 0; i < seq->n; i++)
        free_clause(seq->clause_set[i]);
    delete [](seq->clause_set);
    delete seq;
}

void free_remaining_sequents(vector<Sequent*> *stack) {
    while ((*stack).size() > 0) {
        Sequent *seq = (*stack).back();
        free_sequent(seq);
        (*stack).pop_back();
    }
}

void print_clause_set(Clause** clause_set, int n) {
    for (int i = 0; i < n; i++) {
        clause_set[i]->print();
        cout << endl;
    }
}

bool prove(Sequent *seq) {
    // Simplifies the sequent as much as possible
    while (seq->propagate());

    // Abandons branch if the now-simplified sequent is an axiom
    if (seq->is_axiom()) {
        free_sequent(seq);
        return 0;
    }

    uint32_t var = atomic_cut_is_possible(seq);

    // Sequent is satisfiable if atomic cut is impossible and sequent is not an axiom
    if (var == 0) {
        cout << "s SATISFIABLE" << endl;
        cout << "v ";
        for (int i = 0; i < seq->n; i++) {
            literal lit = seq->clause_set[i]->literals[0];
            if (!lit.positive) cout << "-";
            cout << lit.var << " ";
        }
        cout << "0" << endl;
        free_sequent(seq);
        return 1;
    }

    // Applies atomic cut, abandoning current sequent
    Sequent *left;
    Sequent *right;
    apply_atomic_cut(seq, &left, &right, var);
    free_sequent(seq);

    if (prove(left) == 1) {
        // Satisfiable
        free_sequent(right);
        return 0;
    }

    if (prove(right) == 1) {
        // Satisfiable
        return 1;
    }

    return 0;
}

/**
 * Determines the satisfiability of a clause set.
 * Writes 's SATISIFABLE' followed by solution, or 's UNSATISFIABLE' to stdout.
*/
void solve(Clause **clause_set, int n) {
    Sequent *seq = new Sequent(clause_set, n);
    map<uint32_t, int> var_count;

    // Find indexes of all one-literal clauses
    for (int i = 0; i < n; i++) {
        if (seq->clause_set[i]->n == 1) seq->single_clause_indexes.push(i);
        for (int j = 0; j < seq->clause_set[i]->n; j++) {
            literal lit = seq->clause_set[i]->literals[j];
            if (var_count.find(lit.var) != var_count.end()) {
                // Increment count by 1
                var_count[lit.var]++;
            } else {
                var_count[lit.var] = 1;
            }
        }
    }
    seq->var_count = var_count;

    bool res = prove(seq);
    if (res == 0) {
        // Unsatisfiable
        cout << "s UNSATISFIABLE" << endl;
    }
}

/*
void solve(Clause** clause_set, int n) {
    Sequent *seq = new Sequent(clause_set, n);
    map<uint32_t, int> var_count;

    // Find indexes of all one-literal clauses
    for (int i = 0; i < n; i++) {
        if (seq->clause_set[i]->n == 1) seq->single_clause_indexes.push(i);
        for (int j = 0; j < seq->clause_set[i]->n; j++) {
            literal lit = seq->clause_set[i]->literals[j];
            if (var_count.find(lit.var) != var_count.end()) {
                // Increment count by 1
                var_count[lit.var]++;
            } else {
                var_count[lit.var] = 1;
            }
        }
    }

    seq->var_count = var_count;
    vector<Sequent*> stack;
    stack.push_back(seq);

    while (stack.size() > 0) {
        seq = stack.back();
        stack.pop_back();
    
        // Simplifies the sequent as much as possible
        while (seq->propagate());

        // Abandons branch if the now-simplified sequent is an axiom
        if (seq->is_axiom()) {
            free_sequent(seq);
            continue;
        }

        // Applies atomic cut, abandoning current sequent
        Sequent *left;
        Sequent *right;
        int res = apply_atomic_cut(seq, &left, &right);

        // Sequent is satisfiable if atomic cut is impossible and sequent is not an axiom
        if (!res) {
            cout << "s SATISFIABLE" << endl;
            cout << "v ";
            for (int i = 0; i < seq->n; i++) {
                literal lit = seq->clause_set[i]->literals[0];
                if (!lit.positive) cout << "-";
                cout << lit.var << " ";
            }
            cout << "0" << endl;
            free_sequent(seq);
            free_remaining_sequents(&stack);
            return;
        }
        
        // Push the left- and right sequent to the stack
        stack.reserve(2);
        stack.push_back(left);
        stack.push_back(right);

        free_sequent(seq);
    }

    cout << "s UNSATISFIABLE" << endl;
}
*/

/**
 * Reads a formula in CNF from file.
 * Functions for parsing of cnf files authored by John Burkardt.
 * Returns formula as a clause set.
*/
Clause** read_cnf_file(string filename, int *n) {
    int v_num, c_num, l_num;
    cnf_header_read(filename, &v_num, &c_num, &l_num);

    int *l_c_num = new int[c_num+1];
    int *l_val = new int[l_num];
    cnf_data_read(filename, v_num, c_num, l_num, l_c_num, l_val);

    Clause **clause_set = new Clause*[c_num];
    int c_num2 = 0;
    int l_num2 = 0;

    while (1) {
        if (c_num2 == c_num) break;

        int num_literals = l_c_num[c_num2];
        literal* literals = new literal[num_literals];

        for (int i = 0; i < num_literals; i++) {
            int var = l_val[l_num2];
            bool positive = var > 0;
            literal lit = {(uint32_t) abs(var), positive};
            literals[i] = lit;
            l_num2++;
        }

        Clause *cl = new Clause(literals, num_literals);
        clause_set[c_num2] = cl;
        c_num2++;
    }

    *n = c_num;
    delete []l_c_num;
    delete []l_val;

    return clause_set;
}

/**
 * Builds a full clause set from the given variables.
 * The full clause set will be unsatisfiable.
 * n variables -> 2^n clauses.
*/
Clause** build_full_clause_set(int num_vars) {
    Clause **clause_set = new Clause*[(int)pow(2, num_vars)];

    for (int i = 0; i < pow(2, num_vars); i++) {
        literal* literals = new literal[num_vars];
        for (uint32_t j = 0; j < (uint32_t) num_vars; j++) {
            // Determines negation with this formula
            bool positive = int(i / (pow(2, num_vars) / pow(2, j + 1))) % 2 == 0;
            literal lit = {j+1, positive};
            literals[j] = lit;
        }
        Clause *cl = new Clause(literals, num_vars);
        clause_set[i] = cl;
    }

    return clause_set;
}

/** 20sek
 * Tests two formulae in CNF with n variables.
 * The first formula proven is a full clause set of 2^n clauses (unsatisfiable).
 * The second formula is an almost full clause set of 2^n-1 clauses (satisfiable).
*/
void test(int num_variables) {
    cout << "c Testing sequent with " << num_variables << " variables (" << pow(2, num_variables) << " clauses)" << endl;

    cout << "c Unsatisfiable test:" << endl;
    Clause** cl1 = build_full_clause_set(num_variables);
    solve(cl1, pow(2, num_variables));
    
    cout << "c Satisfiable test:" << endl;
    Clause** cl2 = build_full_clause_set(num_variables);
    free_clause(cl2[int(pow(2, num_variables))-1]);
    solve(cl2, int(pow(2, num_variables))-1);
}

int main(int argc, char** argv) {
    // Parse command line arguments
    int test_val = 0;
    string file_name;

    for (int i = 1; i < argc; ++i) {
        string arg(argv[i]);
        if (arg == "-test") {
            // Test flag
            if (++i >= argc) {
                cerr << "Error: please provide the value of the test flag (int)" << endl;
                return 1;
            }
            test_val = stoi(argv[i]);
        } else {
            // File name
            file_name = arg;
        }
    }

    // Check that only one of test flag or file name was specified
    if ((test_val == 0 && file_name.empty()) || (test_val != 0 && !file_name.empty())) {
        cerr << "Error: please specify either a test flag or a file name, but not both." << endl;
        return 1;
    }

    if (test_val != 0) {
        if (test_val < 0) {
            cerr << "Error: test flag must be higher than 0" << endl;
            return 1;
        }
        // run test
        test(test_val);
    } else {
        // prove CNF formula from file
        int n;
        Clause **clause_set = read_cnf_file(file_name, &n);

        cout << "c Solving " << file_name << endl;
        solve(clause_set, n);
    }

    return 0;
}