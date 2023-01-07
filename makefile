D_FLAGS := -pedantic-errors -Wall -Wextra -ggdb3 -std=gnu++17
O_FLAGS := -O3 -std=gnu++17

# valgrind --track-origins=yes --leak-check=full ./SAT-solver cnf/uf20-91.cnf

all:
	g++ $(O_FLAGS) -o SAT-solver SAT-solver.cpp cnf_io.cpp

debug:
	g++ $(D_FLAGS) -o SAT-solver SAT-solver.cpp cnf_io.cpp

expl:
	g++ $(E_FLAGS) -o cnf-read-test cnf_read_test.cpp cnf_io.cpp