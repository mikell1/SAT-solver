# SAT-solver

Welcome to the SAT-solver! This program is a command line tool for solving the [Boolean Satisfiability Problem (SAT)](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem). Given a formula in [Conjuncture Normal Form (CNF)](https://en.wikipedia.org/wiki/Conjunctive_normal_form), the SAT-solver will determine whether or not there exists a truth assignment to the variables in the formula that makes it true.

### Prerequisites

In order to use the SAT-solver, you will need to have C++ and make installed on your system. 

### Usage

1. Clone this repository: `git clone https://github.com/mikell1/SAT-solver.git`
2. Enter the directory: `cd SAT-solver`
3. Compile the program: `make`
4. Run the program: `./SAT-solver filename.cnf`

The `filename.cnf` should be a path to a file containing a formula in CNF. An example of such a file is:
```
p cnf 4 3
1 2 0
-2 3 0
1 -3 4 0
```

Each line in the file represents a clause of literals, and all the lines together represents the clause set. The - in front of a variable represents a negation. 
This file has 4 variables and 3 clauses as reflected in the header `p cnf 4 3`. The 0's at the end of each clause represents the end of the clause, and is not to be treated as a literal. 
This formula should be interpreted as `(1 ∨ 2) ∧ (¬2 ∨ 3) ∧ (1 ∨ ¬3 ∨ 4)`. 

Click [here](https://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html) to learn more about the DIMACS CNF file format. 

More examples of .cnf files can be found [here](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).

You can also test the program with the -test flag:
```
./SAT-solver -test 10
```
This will run the SAT-solver on a full clause set with 10 variables.

### Example

Here is an example of running the SAT-solver on a CNF formula:
```
$ ./SAT-solver example_CNF_formula.cnf
Determining the satisfiability of the following CNF formula: example_CNF_formula.cnf

Conclusion: satisfiable
Satisfying interpretation: 15 -19 -8 -4 13 6 -5 -7 -12 -16 -10 1 -11 -2 -9 20 -3 14 17 -18
```
