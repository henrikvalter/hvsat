
import sys
import TerminalGraphics
from Globals import *

class DPLL:
    def __init__(self, termprint=False, waitforinput=False, termprint_delay_seconds=0.1):
        self.var_dict = dict()
        self.clauses = []
        self.termprint = termprint
        self.termprint_delay_seconds = termprint_delay_seconds
        self.waitforinput = waitforinput

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

    def assign(self, model, assignment):

        if self.termprint:
            varname = f"x{abs(assignment)}"
            value = 1 if assignment > 0 else 0
            string = f"assigning {varname}={value}. Current model: {model}"
            TerminalGraphics.print_string_and_clauses(\
                string, self.clauses, model, self.waitforinput, self.termprint_delay_seconds)

        # sanity check
        assigned_vars = list(map(abs, model))
        assert abs(assignment) not in assigned_vars
        # always return a copy of the model
        new_model = model.copy()
        new_model.append(assignment)

        return new_model

    def literal_satisfied(self, model, literal):
        for assignment in model:
            if abs(literal) == abs(assignment):
                return literal == assignment
        return None

    def partition_clause_literals(self, model, clause):
        """
        Partitions the literals in a clause into three lists:
            those satisfied, those unsatisfied, and those unassigned
        """
        satisfied_literals = []
        unsatisfied_literals = []
        unassigned_literals = []
        for literal in clause:
            satisfied = self.literal_satisfied(model, literal)
            if satisfied is None:
                unassigned_literals.append(literal)
            elif satisfied:
                satisfied_literals.append(literal)
            else:
                unsatisfied_literals.append(literal)
        return satisfied_literals, unsatisfied_literals, unassigned_literals

    def unit_propagation(self, model):
        all_clauses_satisfied = True
        for clause in self.clauses:
            nr_literals = len(clause)
            sat, unsat, unassigned = self.partition_clause_literals(model, clause)
            assert nr_literals == len(sat) + len(unsat) + len(unassigned)
            if len(sat) != 0:
                # clause is satisfied already
                continue
            else:
                all_clauses_satisfied = False
            if len(unsat) == nr_literals:
                # conflict
                return False, model
            if len(unassigned) == 1:
                assert len(unsat) == nr_literals-1
                # clause is unit: one assignment is forced
                required_assignment = unassigned[0]
                new_model = self.assign(model, required_assignment)
                return self.unit_propagation(new_model)
        if all_clauses_satisfied:
            return True, model
        return None, model

    """
        DPLL(f):
            Apply unit propagation
            if conflict, return UNSAT
            apply pure literal rule
            if f is satisfied, return SAT
            select some variable x
            if DPLL(f where x=1) return SAT
            return DPLL(f where x=0)
    """
    def DPLL(self, model0):
        sat, model1 = self.unit_propagation(model0)
        if sat is not None:
            return sat, model1
        # Pick an unassigned literal
        assigned_literals = list(map(abs, model1))
        unassigned_literals = [lit for lit in self.literals()
                               if lit not in assigned_literals]
        picked_literal = unassigned_literals[0]

        # Set it to True and recurse
        modelTrue0 = self.assign(model1, picked_literal)
        sat, modelTrue1 = self.DPLL(modelTrue0)
        if sat:
            return sat, modelTrue1

        # Set it to False and recurse
        modelFalse0 = self.assign(model1, -picked_literal)
        return self.DPLL(modelFalse0)

    def solve(self):
        sat, model = self.DPLL([])
        TerminalGraphics.print_string_and_clauses(\
            f"Final model: {model}", self.clauses, model, False, 0)
        return sat, model

def main():
    assert len(sys.argv) == 2
    solver = DPLL(termprint=True,
                  waitforinput=False,
                  termprint_delay_seconds=GLOBAL_DELAY)
    cnf_filename = sys.argv[1]
    solver.parse_cnf_file(cnf_filename)
    result, _ = solver.solve()
    print(f"Answer: {res2str(result)}")

if __name__ == "__main__":
    main()