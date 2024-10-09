
import sys
import TerminalGraphics
from ImplicationGraph import *
import random
from Globals import *

class CDCL:
    def __init__(self, termprint=False, waitforinput=False, termprint_delay_seconds=0.1):
        self.var_dict = dict()
        self.clauses = []
        self.termprint = termprint
        self.termprint_delay_seconds = termprint_delay_seconds
        self.waitforinput = waitforinput
        self.igraph = ImplicationGraph()

    def literals(self):
        return self.var_dict.keys()

    def model(self):
        return self.igraph.model()

    def add_clause(self, clause):
        for lit in clause:
            assert lit != 0
            literal = abs(lit)
            if literal in self.var_dict:
                self.var_dict[literal] += 1
            else:
                self.var_dict[literal] = 1
        self.clauses.append(clause)

    def get_literal_assignment(self, literal):
        for (assignment, decision_level) in self.igraph.assignments():
            if abs(literal) == abs(assignment):
                return assignment, decision_level
        assert False

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

    def literal_satisfied(self, literal):
        model = self.model()
        for assignment in model:
            if abs(literal) == abs(assignment):
                return literal == assignment
        return None

    def partition_clause_literals(self, clause):
        """
        Partitions the literals in a clause into three lists:
            those satisfied, those unsatisfied, and those unassigned
        """
        satisfied_literals = []
        unsatisfied_literals = []
        unassigned_literals = []
        for literal in clause:
            satisfied = self.literal_satisfied(literal)
            if satisfied is None:
                unassigned_literals.append(literal)
            elif satisfied:
                satisfied_literals.append(literal)
            else:
                unsatisfied_literals.append(literal)
        return satisfied_literals, unsatisfied_literals, unassigned_literals

    def unit_propagation(self, decision_level):
        all_formulas_satisfied = True
        for clause in self.clauses:
            nr_literals = len(clause)
            sat, unsat, unassigned = self.partition_clause_literals(clause)
            assert nr_literals == len(sat) + len(unsat) + len(unassigned)
            if len(sat) != 0:
                # clause is satisfied already
                continue
            else:
                all_formulas_satisfied = False
            if len(unsat) == nr_literals:
                # conflict
                return False
            if len(unassigned) == 1:
                assert len(unsat) == nr_literals-1
                # one variable is unassigned and the rest are
                # unsatisfied => we must make it satisfied
                required_assignment = unassigned[0]
                dst = (required_assignment,decision_level)

                # find the incoming edges
                assignments = self.igraph.assignments()
                srcs = []
                for unsat_literal in unsat:
                    inverted = unsat_literal * -1
                    # The inverted literal should be in the assignments
                    for lit,dl in assignments:
                        if lit == inverted:
                            break
                    else:
                        assert False
                    srcs.append((lit, dl))

                self.igraph.add(dst,srcs)
                return self.unit_propagation(decision_level)

        if all_formulas_satisfied:
            return True
        return None

    def pick_unassigned_literal(self):
        for clause in self.clauses:
            sat, unsat, unassigned = self.partition_clause_literals(clause)
            nr_literals = len(clause)
            # There should be no conflicts at this stage
            assert len(unsat) < nr_literals
            if len(sat) != 0:
                # clause is satisfied already
                continue
            return unassigned[0]
        assert False

    def backjump(self, decision_level):
        # Locate the variable that was chosen at will
        for ((assignment, dlevel),srcs) in self.igraph.graph:
            if dlevel == decision_level and srcs == []:
                break
        else:
            assert False
        old_assignment = assignment

        # Purge the igraph of everything at this decision level and higher
        new_igraph = ImplicationGraph()
        for ((assignment, dlevel),srcs) in self.igraph.graph:
            if dlevel < decision_level:
                new_igraph.add(dst=(assignment,dlevel),srcs=srcs)
        new_igraph.add(dst=(-old_assignment, decision_level), srcs=[])

        self.igraph = new_igraph
        return decision_level

    def CDCL(self):
        """
            1. Select a variable and assign True or False. This is called decision state. Remember the assignment.
            2. Apply Boolean constraint propagation (unit propagation).
            3. Build the implication graph. If there is any conflict
                Find the cut in the implication graph that led to the conflict
                Derive a new clause which is the negation of the assignments that led to the conflict
                Non-chronologically backtrack ("back jump") to the appropriate decision level, where the first-assigned variable involved in the conflict was assigned
            4. Otherwise continue from step 1 until all variable values are assigned.
        """
        decision_level = 0

        restart_likelihood = 0.05

        while True:

            sat = self.unit_propagation(decision_level)

            if self.termprint:
                TerminalGraphics.print_string_and_clauses(
                    f"before unit propagation\nDecision level: {decision_level}\nAssignments: {self.igraph.assignments()}",
                    self.clauses, self.model(), self.waitforinput, self.termprint_delay_seconds)

            if sat is not None:
                if sat:
                    # Done
                    return True

                # Conflict
                if decision_level == 0:
                    return False
                # Find the conflict
                for clause in self.clauses:
                    sat_lits, unsat_lits, unassigned_lits =\
                        self.partition_clause_literals(clause)
                    nr_literals = len(sat_lits) + len(unsat_lits) + len(unassigned_lits)
                    if len(unsat_lits) == nr_literals:
                        conflicting_clause = clause
                        break
                else:
                    assert False
                # Find the variables contributing to the conflict

                # Which variable is the problem?
                # I THINK it is the final one assigned
                clause_assignments = list(map(self.get_literal_assignment, conflicting_clause))
                max_dlevel = 0
                for (assignment, dlevel) in clause_assignments:
                    if dlevel >= max_dlevel:
                        problem_assignment = (assignment, dlevel)

                # Make a list of the other assignments in the conflict clause
                other_assignments_in_conflict_clause = [
                    assignment for assignment in clause_assignments if assignment != problem_assignment
                ]

                # What are the incoming edges?
                for (dst, incoming_edges) in self.igraph.graph:
                    if dst == problem_assignment:
                        break
                else:
                    assert False

                # Combine the other variables in the clause with the incoming edges
                # into one list of assigned literals
                # Duplicates must be removed
                inverted_learned_clause =\
                    list(dict.fromkeys(other_assignments_in_conflict_clause + incoming_edges))
                learned_clause = list(map(lambda pair:-pair[0], inverted_learned_clause))

                # Put the learned clause at the front of the clause list
                self.clauses.insert(0, learned_clause)

                # Roll back to the decision level of the first-assigned variable
                # in the conflict

                if inverted_learned_clause == []:
                    return False

                backjump_dlevel = min(map(lambda a:a[1], inverted_learned_clause))

                decision_level = self.backjump(backjump_dlevel)

                if decision_level > 0 and random.uniform(0.0, 1.0) < restart_likelihood:
                    decision_level = 0
                    self.igraph = ImplicationGraph()

            else:
                # Unknown.
                # Assign some literal.
                decision_level += 1
                assignment = self.pick_unassigned_literal()
                self.igraph.add(dst=(-assignment, decision_level),srcs=[])

    def solve(self):
        result = self.CDCL()
        model = self.model()

        if self.termprint:
            TerminalGraphics.print_string_and_clauses(
                f"Final model: {model}",
                self.clauses, model, False, 0)

        return result, model

def main():
    assert len(sys.argv) == 2
    random.seed(1337)
    solver = CDCL(termprint=True, waitforinput=False, termprint_delay_seconds=GLOBAL_DELAY)
    # When you gotta go fast
    # solver = CDCL()
    cnf_filename = sys.argv[1]
    solver.parse_cnf_file(cnf_filename)
    result, _ = solver.solve()
    print(f"Answer: {res2str(result)}")

if __name__ == "__main__":
    main()
