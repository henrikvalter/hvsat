
import sys
import random
import subprocess
import TerminalGraphics
from Globals import *

class Loops:
    def __init__(self):
        self.var_dict = dict()
        self.clauses = []
        self.assignments = []

    def literals(self):
        return self.var_dict.keys()

    def add_clause(self, clause):
        for lit in clause:
            assert lit != 0
            literal = abs(lit)
            if literal in self.var_dict:
                self.var_dict[literal] += 1
            else:
                self.var_dict[literal] = 1
        self.clauses.append(clause)

    def parse_cnf_file(self, filename):
        with open(filename, "r") as f:
            for line in f:
                stripped = line.strip()
                if len(stripped) == 0:
                    continue
                words = stripped.split()
                if words[0] == "c":
                    continue
                if words[0] == "p":
                    continue
                # Parse clause
                intwords = list(map(int, words))
                assert intwords[-1] == 0
                clause = intwords[:-1]
                self.add_clause(clause)

    def assign(self, assigment):
        self.assignments.append(assigment)

    def literal_satisfied(self, literal):
        for assignment in self.assignments:
            if abs(literal) == abs(assignment):
                if literal == assignment:
                    return True
                else:
                    return False
            else:
                continue
        return None

    def clause_satisfied(self, clause):
        has_unassigned = False
        for literal in clause:
            sat = self.literal_satisfied(literal)
            if sat is None:
                has_unassigned = True
                continue
            if not sat:
                continue
            return True
        if has_unassigned:
            return None
        else:
            return False

    def formula_satisfied(self):
        for clause in self.clauses:
            sat = self.clause_satisfied(clause)
            if sat is None:
                return None
            if sat:
                continue
            if not sat:
                return False
        return True

    def solve(self):

        assert len(self.literals()) == 8

        ft = [-1, 1]

        models_checked = 0
        total_models = 2**8

        for x1 in ft:
            for x2 in ft:
                for x3 in ft:
                    for x4 in ft:
                        for x5 in ft:
                            for x6 in ft:
                                for x7 in ft:
                                    for x8 in ft:
                                        models_checked += 1
                                        self.assignments = []
                                        self.assignments.append(1*x1)
                                        self.assignments.append(2*x2)
                                        self.assignments.append(3*x3)
                                        self.assignments.append(4*x4)
                                        self.assignments.append(5*x5)
                                        self.assignments.append(6*x6)
                                        self.assignments.append(7*x7)
                                        self.assignments.append(8*x8)
                                        TerminalGraphics.print_string_and_clauses(
                                            f"Trying model {self.assignments} \n({models_checked} / {total_models}) ",
                                            self.clauses,
                                            self.assignments,
                                            False,
                                            GLOBAL_DELAY)
                                        sat = self.formula_satisfied()
                                        assert sat is not None
                                        if sat:
                                            return True
        return False

def main():
    assert len(sys.argv) == 2
    random.seed(1337)
    solver = Loops()
    cnf_filename = sys.argv[1]
    solver.parse_cnf_file(cnf_filename)
    result = solver.solve()
    print(f"Answer: {res2str(result)}")

if __name__ == "__main__":
    main()