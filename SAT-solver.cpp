#include "SAT-solver.h"

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
    cout << "  {";
    for (int i = 0; i < n; i++) {
        string pre = "";
        if (!formulae[i].not_negated) pre = "~";
        string post = ", ";
        if (i == n-1) post = "";
        cout << pre << variable_map[formulae[i].var_hash] << post;
    }
    cout << "}";
}

class Sequent {
    public:
        Clause **clause_set;
        int n;
        queue<int> single_clause_indexes;
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
        if (clause_set[i]->n != 1) continue;
        atom this_at = clause_set[i]->formulae[0];
        for (int j = 0; j < n; j++) {
            if (clause_set[j]->n != 1) continue;
            atom other_at = clause_set[j]->formulae[0];
            // Checks if first atom's variable is equal to second atom's variable,
            // and if respective atom's negation is different.
            if (this_at.var_hash == other_at.var_hash && this_at.not_negated != other_at.not_negated && i != j)
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
                    // Remove the atom from the clause' formulae array
                    for (int k = 0; k < clause_set[j]->n; k++) {
                        if (clause_set[j]->formulae[k].var_hash == simplify_with.var_hash && clause_set[j]->formulae[k].not_negated == simplify_with.not_negated) {
                            clause_set[j]->formulae[k] = clause_set[j]->formulae[--clause_set[j]->n];
                            if (clause_set[j]->n == 1) single_clause_indexes.push(j);
                            break;
                        }
                    }
                } else {
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
 * Applies atomic cut to a sequent to achieve atomic cut elimination.
 * Returns a left- and right sequent each with an additional clause
 * containing a single negated- and non-negated atom respectively.
 * The chosen atom is a random atom occuring in the sequent, but not
 * occuring in a one-formulae clause.
*/
tuple<Sequent*, Sequent*> apply_atomic_cut(Sequent *seq) {
    Clause **clause_set = seq->clause_set;
    int n = seq->n;
    for (int i = 0; i < n; i++) {
        // Skips all clauses with only one formula, as
        // atomic cut on such clauses are meaningless
        if (clause_set[i]->n == 1) continue;
        for (int j = 0; j < clause_set[i]->n; j++) {
            // Trying atom clause_set[i]->formulae[j]
            atom chosen_at = clause_set[i]->formulae[j];
            bool cut = true;
            for (int k = 0; k < n; k++) {
                if (i == k) continue;
                if (clause_set[k]->n != 1) continue;
                // Checks if the chosen atom occurs in a one-formulae clause,
                // abort and try next atom if so.
                if (chosen_at.var_hash == clause_set[k]->formulae[0].var_hash) {
                    cut = false;
                    break;
                }
            }
            if (cut) {
                // Applies atomic cut
                // Creates the left Sequent
                atom at_l = {chosen_at.var_hash, true};
                atom *formulae_l = new atom[1];
                formulae_l[0] = at_l;
                Clause *cl_l = new Clause(formulae_l, 1);
                Clause **cl_set_l = new Clause*[n+1];
                for (int i = 0; i < n; i++) cl_set_l[i] = deep_cp_clause(clause_set[i]);
                cl_set_l[n] = cl_l;
                Sequent *seq_l = new Sequent(cl_set_l, n+1);
                seq_l->single_clause_indexes = seq->single_clause_indexes;
                seq_l->single_clause_indexes.push(n);

                // Creates the right Sequent
                atom at_r = {chosen_at.var_hash, false};
                atom *formulae_r = new atom[1];
                formulae_r[0] = at_r;
                Clause *cl_r = new Clause(formulae_r, 1);
                Clause **cl_set_r = new Clause*[n+1];
                for (int i = 0; i < n; i++) cl_set_r[i] = deep_cp_clause(clause_set[i]);
                cl_set_r[n] = cl_r;
                Sequent *seq_r = new Sequent(cl_set_r, n+1);
                seq_r->single_clause_indexes = seq->single_clause_indexes;
                seq_r->single_clause_indexes.push(n);

                return {seq_l, seq_r};
            }
        }
    }
    // Atomic cut impossible
    return {NULL, NULL};
}

/**
 * Deep copies a clause.
*/
Clause* deep_cp_clause(Clause* cl) {
    int n = cl->n;
    atom *formulae = new atom[n];
    for (int i = 0; i < n; i++) {
        atom at = {cl->formulae[i].var_hash, cl->formulae[i].not_negated};
        formulae[i] = at;
    }
    Clause *clause = new Clause(formulae, n);
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

void print_clause_set(Clause** clause_set, int n) {
    cout << "{" << endl;
    for (int i = 0; i < n; i++) {
        clause_set[i]->print();
        if (i != n-1) cout << ",";
        cout << endl;
    }
    cout << "}" << endl;
}

uint32_t hash_str_uint32(string& str) {
    uint32_t hash = 0x811c9dc5;
    uint32_t prime = 0x1000193;
    for (int i = 0; i < (int)str.size(); ++i) {
        uint8_t value = str[i];
        hash = hash ^ value;
        hash *= prime;
    }
    return hash;
}

/**
 * Builds a full clause set from the given variables.
 * The full clause set will be unsatisfiable.
 * n variables -> 2^n clauses.
*/
Clause** build_full_clause_set(vector<string> vars) {
    int n = vars.size();
    Clause **clause_set = new Clause*[(int)pow(2, n)];
    for (int i = 0; i < pow(2, n); i++) {
        atom* formulae = new atom[n];
        for (int j = 0; j < n; j++) {
            // Determines negation with this formula
            bool not_negated = int(i / (pow(2, n) / pow(2, j + 1))) % 2 == 0;
            atom at = {hash_str_uint32(vars[j]), not_negated};
            formulae[j] = at;
        }
        Clause *cl = new Clause(formulae, n);
        clause_set[i] = cl;
    }
    return clause_set;
}

/**
 * Determines the satisfiability of a clause set.
 * Prints 'satisfiable' or 'unsatisfiable' to the terminal.
*/
void prove_it(Clause** clause_set, int n) {
    Sequent *seq = new Sequent(clause_set, n);
    // Find indexes of all one-formula clauses
    for (int i = 0; i < n; i++)
        if (seq->clause_set[i]->n == 1) seq->single_clause_indexes.push(i);
    vector<Sequent*> stack;
    stack.push_back(seq);

    while (stack.size() > 0) {
        seq = stack.back();
        stack.pop_back();
        // Simplifies the sequent as much as possible
        while (seq->propagate());
        // Continues if the now-simplified sequent is an axiom
        if (seq->is_axiom()) {
            free_sequent(seq);
            continue;
        }
        // Applies atomic cut, abandoning current sequent
        tuple<Sequent*, Sequent*> res = apply_atomic_cut(seq);
        free_sequent(seq);
        // Sequent is satisfiable if atomic cut is impossible and sequent is not an axiom
        if (get<0>(res) == NULL) {
            cout << "satisfiable" << endl;
            return;
        }
        // Push the left- and right sequent to the stack
        Sequent *left = get<0>(res);
        Sequent *right = get<1>(res);
        stack.reserve(2);
        stack.push_back(left);
        stack.push_back(right);
    }
    cout << "unsatisfiable" << endl;
}

/**
 * Increments string
 * a -> b
 * z -> aa
 * aa -> ab
*/
string increment_string(string str) {
    bool carry = 0;
    for (int i = str.length() - 1; i >= 0; i--) {
    char c = str[i];
        if (c == 'z') {
            str[i] = 'a';
            carry = true;
        } else {
            str[i] = c + 1;
            carry = false;
            break;
        }
    }
    if (carry) str = "a" + str;
    return str;
}

/**
 * Builds a vector of n unequal strings
 * E.g.: ['a', 'b', 'c', ..., 'z', 'aa', 'ab', ...]
*/
vector<string> build_var_set(int n) {
    string current_string = "a";
    vector<string> vars;
    for (int i = 0; i < n; i++) {
        vars.push_back(current_string);
        variable_map[hash_str_uint32(current_string)] = current_string;
        current_string = increment_string(current_string);
    }
    return vars;
}

/**
 * Reads a formula in CNF from file.
 * Returns formula as a clause set.
*/
tuple<Clause**, int> read_clause_set_from_file(string &filename) {
    // Opens file
    ifstream file(filename);
    vector<vector<string>> lines;
    string line;
    while (getline(file, line)) {
        // Reads line in file one by one
        istringstream stream(line);
        vector<string> data;
        string cell;
        while (getline(stream, cell, ' ')) {
            if ((int)cell[cell.length()-1] == 13) cell = cell.substr(0, cell.length()-1);
            data.push_back(cell);
        }
        lines.push_back(data);
    }
    // Closes file
    file.close();

    int n = lines.size();
    Clause **clause_set = new Clause*[n];
    for (int i = 0; i < n; i++) {
        int num_formulae = (int) lines[i].size();
        atom* formulae = new atom[num_formulae];

        for (int j = 0; j < num_formulae; j++) {
            bool not_negated = lines[i][j][0] != '-';
            atom at = {0, not_negated};
            string str = lines[i][j];
            if (!not_negated) str = str.substr(1);
            at.var_hash = hash_str_uint32(str);
            variable_map[at.var_hash] = str;
            formulae[j] = at;
        }
        Clause *cl = new Clause(formulae, num_formulae);
        clause_set[i] = cl;
    }
    return {clause_set, n};
}

/**
 * Tests two formulae in CNF with n variables.
 * The first formula proven is a full clause set of 2^n clauses (unsatisfiable).
 * The second formula is an almost full clause set of 2^n-1 clauses (satisfiable).
*/
void test(int num_variables) {
    vector<string> vars = build_var_set(num_variables);
    cout << "Testing sequent with " << num_variables << " variables" << endl;

    cout << "Unsatisfiable test: ";
    Clause** cl1 = build_full_clause_set(vars);
    prove_it(cl1, pow(2, num_variables));

    cout << "Satisfiable test: ";
    Clause** cl2 = build_full_clause_set(vars);
    free_clause(cl2[int(pow(2, num_variables))-1]);
    prove_it(cl2, int(pow(2, num_variables))-1);
}

int main(int argc, char** argv) {
    // Parse command line arguments
    int test_flag = 0;
    string file_name;
    for (int i = 1; i < argc; ++i) {
        string arg(argv[i]);
        if (arg == "-test") {
            // Test flag
            if (++i >= argc) {
                cerr << "Error: please provide the value of the test flag (int)" << endl;
                return 1;
            }
            test_flag = stoi(argv[i]);
        } else {
            // File name
            file_name = arg;
        }
    }

    // Check that only one of test flag or file name was specified
    if ((test_flag == 0 && file_name.empty()) || (test_flag != 0 && !file_name.empty())) {
        cerr << "Error: please specify either a test flag or a file name, but not both." << endl;
        return 1;
    }

    if (test_flag != 0) {
        if (test_flag < 0) {
            cerr << "Error: test flag must be higher than 0" << endl;
            return 1;
        }
        // run test
        test(test_flag);
    } else {
        // prove CNF formula from file
        tuple<Clause**, int> data = read_clause_set_from_file(file_name);
        Clause **clause_set = get<0>(data);
        int n = get<1>(data);
        cout << "Determining the satisfiability of the following CNF formula:" << endl;
        print_clause_set(clause_set, n);
        cout << endl << "Conclusion: ";
        prove_it(clause_set, n);
    }
    return 0;
}