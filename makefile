D_FLAGS := -pedantic-errors -Wall -Wextra -Werror -ggdb3
O_FLAGS := -O3

all:
	g++ $(O_FLAGS) -o SAT-solver SAT-solver.cpp

debug:
	g++ $(D_FLAGS) -o SAT-solver SAT-solver.cpp