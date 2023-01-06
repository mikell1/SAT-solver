# SAT-solver

Welcome to the SAT-solver! This program is a command line tool for solving the [Boolean Satisfiability Problem (SAT)](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) in C++. Given a formula in [Conjuncture Normal Form (CNF)](https://en.wikipedia.org/wiki/Conjunctive_normal_form), the SAT-solver will determine whether or not there exists a truth assignment to the variables in the formula that makes it true.

### Prerequisites

In order to use the SAT-solver, you will need to have C++ and make installed on your system. 

### Usage

1. Clone this repository: `git clone https://github.com/mikell1/SAT-solver.git`
2. Enter the directory: `cd SAT-solver`
3. Compile the program: `make`
4. Run the program: `./SAT-solver filename.txt`

The `filename.txt` should be a path to a file containing a formula in CNF. An example of such a file is:
```
p q -r s
-p q r s
p -q r s
p q r -s
p -q -r -s
```

Each line in the file represents a clause, and all the lines together represents the clause set. The - in front of a variable represents a negation. 

You can also test the program with the -test flag:
```
./SAT-solver -test 10
```
This will run the SAT-solver on a full clause set with 10 variables.

### Example

Here is an example of running the SAT-solver on a CNF formula:
```
$ ./SAT-solver example_CNF_formula.txt
Determining the satisfiability of the following CNF formula:
{
  {p, q, ~r, ~s},
  {r, ~s},
  {p, r, s},
  {p, ~r, ~s},
  {~p, ~q, r, s},
  {r}
}

Conclusion: satisfiable
```

---
Note: This README file was created with the help of ChatGPT.