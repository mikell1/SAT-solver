#include "SAT-solver.hpp"
#include "cnf_io.hpp"

class Clause {
    public:
        atom *formulae;
        int n;
        Clause(atom *formulae, int n);
        atom can_be_simplified_with(atom);
        void print();
};

Clause::Clause(atom *formulae, int n) {
    this->formulae = formulae;
    this->n = n;
}

/**
 * Determines whether the clause can be simplified with a given atom.
 * Returns true if the given atom's variable is contained in its array of formulae.
*/
atom Clause::can_be_simplified_with(atom at) {
    for (int i = 1; i < n; i++) {
        if (at.var_hash == this->formulae[i].var_hash) {
            // Clause contains given atom's variable, thus can be simplified with given atom
            atom at = {this->formulae[i].var_hash, this->formulae[i].not_negated};
            return at;
        }
    }

    return {0, 0};
}

void Clause::print() {
    for (int i = 0; i < n; i++) {
        if (!formulae[i].not_negated) cout << "-";
        cout << formulae[i].var_hash << " ";
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
        // skips if clause' length is not 1
        if (clause_set[i]->n == 0)
            // Axiom by empty clause
            return true;
        
        if (clause_set[i]->n != 1) continue;
        atom this_at = clause_set[i]->formulae[0];

        for (int j = 0; j < n; j++) {
            if (clause_set[j]->n != 1) continue;
            atom other_at = clause_set[j]->formulae[0];
            // Checks if first atom's variable is equal to second atom's variable,
            // and if respective atom's negation is different.
            if (this_at.var_hash == other_at.var_hash && this_at.not_negated != other_at.not_negated && i != j)
                // Axiom
                return true;
        }
    }
    return false;
}

/**
 * Applies unit propagation on a sequent.
 * I.e. for all single formulae clauses in it's clause set,
 * remove all clauses containing the single formula from the clause set,
 * and remove the negated formula from any clause' formulae array where the negated
 * formula of the single formula is included.
*/
bool Sequent::propagate() {
    while (!single_clause_indexes.empty()) {
        int i = single_clause_indexes.front();
        if (i > n || clause_set[i]->n != 1) {
            // Clause contains more than one formulae or clause index is out of bounds.
            single_clause_indexes.pop();
            continue;
        }
        
        atom at = clause_set[i]->formulae[0];
        for (int j = 0; j < n; j++) {
            atom simplify_with = clause_set[j]->can_be_simplified_with(at);
            if (simplify_with.var_hash) {
                if (at.not_negated != simplify_with.not_negated) {
                    // Unit resolution
                    // Remove the atom from the clause' formulae array
                    for (int k = 0; k < clause_set[j]->n; k++) {
                        if (clause_set[j]->formulae[k].var_hash == simplify_with.var_hash && clause_set[j]->formulae[k].not_negated == simplify_with.not_negated) {
                            clause_set[j]->formulae[k] = clause_set[j]->formulae[--clause_set[j]->n];
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
Sequent *atomic_cut_create_sequent(Clause **clause_set, int n, uint32_t var_hash, bool val) {
    // Creates a new sequent
    atom at = {var_hash, val};
    atom *formulae = new atom[1];
    formulae[0] = at;

    Clause *cl = new Clause(formulae, 1);
    Clause **cl_set = new Clause*[n+1];
    int c_num = 0;

    queue<int> single_clause_indexes;
    map<uint32_t, int> var_count;

    for (int i = 0; i < n; i++) {
        bool keep = true;
        for (int j = 0; j < clause_set[i]->n; j++) {
            atom a = clause_set[i]->formulae[j];
            if (a.var_hash == at.var_hash && a.not_negated == at.not_negated) {
                // Unit resolution, ignores clause
                keep = false;
                break;
            }
        }
        if (keep) {
            for (int j = 0; j < clause_set[i]->n; j++) {
                atom a = clause_set[i]->formulae[j];
                if (a.var_hash != var_hash) {
                    if (var_count.find(a.var_hash) != var_count.end()) {
                        // Increment count by 1
                        var_count[a.var_hash]++;
                    } else {
                        var_count[a.var_hash] = 1;
                    }
                }
            }
            cl_set[c_num] = deep_cp_clause(clause_set[i], at.var_hash);
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

/**
 * Applies atomic cut to a sequent to achieve atomic cut elimination.
 * Returns a left- and right sequent each with an additional clause
 * containing a single negated- and non-negated variable respectively.
 * The chosen variable is chosen strategically.
 * Returns 0 if atomic cut cannot be applied.
*/
int apply_atomic_cut(Sequent *seq, Sequent **left, Sequent **right) {
    uint32_t var_hash = choose_cut_var(seq);
    if (!var_hash) return 0;

    Clause **clause_set = seq->clause_set;
    int n = seq->n;

    // Sets the left Sequent
    *left = atomic_cut_create_sequent(clause_set, n, var_hash, true);
    // Sets the right Sequent
    *right = atomic_cut_create_sequent(clause_set, n, var_hash, false);

    return 1;
}

/**
 * Deep copies a clause.
*/
Clause* deep_cp_clause(Clause* cl, uint32_t ignore_var) {
    int n = cl->n;
    atom *formulae = new atom[n];
    int c_i = 0;

    for (int i = 0; i < n; i++) {
        if (cl->formulae[i].var_hash == ignore_var) continue; // Unit resolution
        atom at = {cl->formulae[i].var_hash, cl->formulae[i].not_negated};
        formulae[c_i] = at;
        c_i++;
    }

    Clause *clause = new Clause(formulae, c_i);
    return clause;
}

void free_clause(Clause *cl) {
    delete []cl->formulae;
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

/**
 * Determines the satisfiability of a clause set.
 * Prints 'satisfiable' or 'unsatisfiable' to the terminal.
*/
void prove_it(Clause** clause_set, int n) {
    Sequent *seq = new Sequent(clause_set, n);
    map<uint32_t, int> var_count;

    // Find indexes of all one-formula clauses
    for (int i = 0; i < n; i++) {
        if (seq->clause_set[i]->n == 1) seq->single_clause_indexes.push(i);
        for (int j = 0; j < seq->clause_set[i]->n; j++) {
            atom a = seq->clause_set[i]->formulae[j];
            if (var_count.find(a.var_hash) != var_count.end()) {
                // Increment count by 1
                var_count[a.var_hash]++;
            } else {
                var_count[a.var_hash] = 1;
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
            cout << "satisfiable" << endl;
            cout << "Satisfying interpretation: ";
            //print_clause_set(seq->clause_set, seq->n);
            for (int i = 0; i < seq->n; i++) {
                atom at = seq->clause_set[i]->formulae[0];
                if (!at.not_negated) cout << "-";
                cout << at.var_hash << " ";
            }
            cout << endl;
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

    cout << "unsatisfiable" << endl;
}

/**
 * Reads a formula in CNF from file.
 * Functions for parsing of cnf files authored by John Burkardt.
 * Returns formula as a clause set.
*/
Clause** read_cnf_file(string filename, int *n) {
    int v_num, c_num, l_num;
    cnf_header_read(filename, &v_num, &c_num, &l_num);

    int *l_c_num = new int[c_num];
    int *l_val = new int[l_num];
    cnf_data_read(filename, v_num, c_num, l_num, l_c_num, l_val);

    Clause **clause_set = new Clause*[c_num];
    int c_num2 = 0;
    int l_num2 = 0;

    while (1) {
        if (c_num2 == c_num) break;

        int num_formulae = l_c_num[c_num2];
        atom* formulae = new atom[num_formulae];

        for (int i = 0; i < num_formulae; i++) {
            int var = l_val[l_num2];
            bool not_negated = var > 0;
            atom at = {(uint32_t) abs(var), not_negated};
            formulae[i] = at;
            l_num2++;
        }

        Clause *cl = new Clause(formulae, num_formulae);
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
        atom* formulae = new atom[num_vars];
        for (uint32_t j = 0; j < (uint32_t) num_vars; j++) {
            // Determines negation with this formula
            bool not_negated = int(i / (pow(2, num_vars) / pow(2, j + 1))) % 2 == 0;
            atom at = {j+1, not_negated};
            formulae[j] = at;
        }
        Clause *cl = new Clause(formulae, num_vars);
        clause_set[i] = cl;
    }

    return clause_set;
}

/**
 * Tests two formulae in CNF with n variables.
 * The first formula proven is a full clause set of 2^n clauses (unsatisfiable).
 * The second formula is an almost full clause set of 2^n-1 clauses (satisfiable).
*/
void test(int num_variables) {
    cout << "Testing sequent with " << num_variables << " variables" << endl;

    cout << "Unsatisfiable test: ";
    Clause** cl1 = build_full_clause_set(num_variables);
    prove_it(cl1, pow(2, num_variables));

    cout << "Satisfiable test: ";
    Clause** cl2 = build_full_clause_set(num_variables);
    free_clause(cl2[int(pow(2, num_variables))-1]);
    prove_it(cl2, int(pow(2, num_variables))-1);
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
        
        cout << "Determining the satisfiability of the following CNF formula: " << file_name << endl;
        //print_clause_set(clause_set, n);
        cout << endl << "Conclusion: ";
        prove_it(clause_set, n);
    }

    return 0;
}