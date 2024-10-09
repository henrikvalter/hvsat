
import sys
import random
import time
import TerminalGraphics
from Globals import *

class NaiveLocalSearch:
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

    def random_assignment(self, literal):
        pos = abs(literal)
        return random.choice([pos, -pos])

    def flip_random_assignment(self):
        index = random.randint(0, len(self.assignments)-1)
        self.assignments[index] *= -1
        return index

    def solve(self, assignment_timeout, termprint=False, termprint_delay_seconds=1):
        # Assign all variables randomly
        TerminalGraphics.flush_terminal()
        TerminalGraphics.print_clauses(self.clauses, self.assignments)
        time.sleep(termprint_delay_seconds)

        for literal in self.literals():
            assignment = self.random_assignment(literal)
            self.assign(assignment)
        for _ in range(assignment_timeout):
            if self.formula_satisfied():
                TerminalGraphics.flush_terminal()
                print(f"Final model: {self.assignments}")
                TerminalGraphics.print_clauses(self.clauses, self.assignments)
                time.sleep(termprint_delay_seconds)
                return True
            else:
                flipped_index = self.flip_random_assignment()
                if termprint:
                    TerminalGraphics.flush_terminal()
                    TerminalGraphics.print_clauses(self.clauses, self.assignments)
                    print(f"flipped x{abs(self.assignments[flipped_index])}")
                    time.sleep(termprint_delay_seconds)
        else:
            # timeout
            return None

def main():
    assert len(sys.argv) == 2
    random.seed(1337)
    solver = NaiveLocalSearch()
    cnf_filename = sys.argv[1]
    solver.parse_cnf_file(cnf_filename)
    result = solver.solve(1000, termprint=True, termprint_delay_seconds=GLOBAL_DELAY)
    print(f"Answer: {res2str(result)}")

if __name__ == "__main__":
    main()