
import DPLL
from functools import cmp_to_key

GLOBAL_VERBOSE = False

# Implementation of a simple Congruence Closure algorithm,
# demonstrating an example of using SAT in a more expressive logic.

################################################################################

def cmp_primitives(a, b):
    if a > b:
        return 1
    elif a == b:
        return 0
    return -1

################################################################################

class Term:
    def __init__(self, termtype, var=None, function=None, argument=None):
        self.termtype = termtype
        match self.termtype:
            case "VAR":
                assert isinstance(var, str)
                self.var = var
            case "FUNCTION":
                assert isinstance(function, str)
                assert isinstance(argument, Term)
                self.function = function
                self.argument = argument
            case _:
                assert False

    def __hash__(self):
        match self.termtype:
            case "VAR":
                return self.var.__hash__()
            case "FUNCTION":
                return self.function.__hash__() + self.argument.__hash__()
            case _:
                assert False

    def variable(self):
        match self.termtype:
            case "VAR":
                return self.var
            case "FUNCTION":
                return self.argument.variable()
            case _:
                assert False

    def __eq__(self, other):
        return cmp_terms(self, other) == 0

    def __str__(self):
        match self.termtype:
            case "VAR":
                return f"{str(self.var)}"
            case "FUNCTION":
                return f"{self.function}({self.argument})"
            case _:
                assert False
    def __repr__(self):
        return self.__str__()

def cmp_terms(t1, t2):
    assert isinstance(t1, Term)
    assert isinstance(t2, Term)
    match t1.termtype:
        # vars
        case "VAR":
            if t2.termtype == "VAR":
                return cmp_primitives(t1.var, t2.var)
            return 1
        # then functions
        case "FUNCTION":
            if t2.termtype  == "VAR":
                return -1
            assert t2.termtype == "FUNCTION"
            f1 = t1.function
            a1 = t1.argument
            f2 = t2.function
            a2 = t2.argument
            # sort on function names first
            fun_cmp = cmp_primitives(f1, f2)
            if fun_cmp != 0:
                return fun_cmp
            # then arguments
            return cmp_terms(a1, a2)
        case _:
            assert False
cmp_terms_fn = cmp_to_key(cmp_terms)

################################################################################

class Atom:
    def __init__(self, left, right):
        assert isinstance(left, Term)
        assert isinstance(right, Term)
        [left2, right2] = sorted([left, right], key=cmp_terms_fn)
        self.left = left2
        self.right = right2

    def __eq__(self, other):
        return cmp_atoms(self, other) == 0

    def __str__(self):
        return f"{self.left}={self.right}"
    def __repr__(self):
        return self.__str__()

def cmp_atoms(a1, a2):
    assert isinstance(a1, Atom)
    assert isinstance(a2, Atom)
    l1 = a1.left
    r1 = a1.right
    l2 = a2.left
    r2 = a2.right
    left_cmp = cmp_terms(l1, l2)
    if left_cmp != 0:
        return left_cmp
    return cmp_terms(r1, r2)
cmp_atoms_fn = cmp_to_key(cmp_atoms)

################################################################################

class Formula:
    def __init__(self, formulatype, atom=None, neg_formula=None, left=None, right=None):
        self.formulatype = formulatype
        match self.formulatype:
            case "ATOM":
                assert isinstance(atom, Atom)
                self.atom = atom
            case "NOT":
                assert isinstance(neg_formula, Formula)
                self.neg_formula = neg_formula
            case "AND":
                assert isinstance(left, Formula)
                assert isinstance(right, Formula)
                [left2, right2] = sorted([left, right], key=cmp_formulas_fn)
                self.left = left2
                self.right = right2
            case "OR":
                assert isinstance(left, Formula)
                assert isinstance(right, Formula)
                [left2, right2] = sorted([left, right], key=cmp_formulas_fn)
                self.left = left2
                self.right = right2
            case _:
                assert False

    def __eq__(self, other):
        return cmp_formulas(self, other) == 0

    def __str__(self):
        match self.formulatype:
            case "ATOM":
                return f"{str(self.atom)}"
            case "NOT":
                return f"NOT({str(self.neg_formula)})"
            case "AND":
                return f"AND({str(self.left)}, {str(self.right)})"
            case "OR":
                return f"OR({str(self.left)},{str(self.right)})"
            case _:
                assert False
    def __repr__(self):
        return self.__str__()

def cmp_formulas(f1, f2):
    assert isinstance(f1, Formula)
    assert isinstance(f2, Formula)
    match f1.formulatype:
        case "ATOM":
            if f2.formulatype == "ATOM":
                return cmp_atoms(f1.atom, f2.atom)
            return 1
        case "NOT":
            if f2.formulatype == "ATOM":
                return -1
            if f2.formulatype == "NOT":
                return cmp_formulas(f1.neg_formula, f2.neg_formula)
            return 1
        case "AND":
            if f2.formulatype in ["ATOM", "NOT"]:
                return -1
            if f2.formulatype == "AND":
                l1 = f1.left
                r1 = f1.right
                l2 = f2.left
                r2 = f2.right
                left_cmp = cmp_formulas(l1, l2)
                if left_cmp != 0:
                    return left_cmp
                return cmp_formulas(r1, r2)
        case "OR":
            if f2.formulatype in ["ATOM", "NOT", "AND"]:
                return -1
            l1 = f1.left
            r1 = f1.right
            l2 = f2.left
            r2 = f2.right
            left_cmp = cmp_formulas(l1, l2)
            if left_cmp != 0:
                return left_cmp
            return cmp_formulas(r1, r2)
        case _:
            assert False
cmp_formulas_fn = cmp_to_key(cmp_formulas)

def formula_AND_list(formula_list):
    length = len(formula_list)
    assert length != 0
    if len(formula_list) == 1:
        return formula_list[0]
    return Formula("AND",
                   left=formula_list[0],
                   right=formula_AND_list(formula_list[1:]))

################################################################################

class ConjunctionTuple:
    def __init__(self, lhs, rhs, equ):
        assert isinstance(lhs, Term)
        assert isinstance(rhs, Term)
        assert isinstance(equ, bool)
        [lhs2, rhs2] = sorted([lhs,rhs], key=cmp_terms_fn)
        self.lhs = lhs2
        self.rhs = rhs2
        self.equ = equ

    def negated(self):
        return ConjunctionTuple(self.lhs, self.rhs, not self.equ)

    def __eq__(self, other):
        return cmp_ctups(self, other) == 0

    def __str__(self):
        return f"{self.lhs} {'=' if self.equ else '!='} {self.rhs}"

    def __repr__(self):
        return self.__str__()

def cmp_ctups(c1, c2):
    assert isinstance(c1, ConjunctionTuple)
    assert isinstance(c2, ConjunctionTuple)
    lhs1 = c1.lhs
    rhs1 = c1.rhs
    equ1 = c1.equ
    lhs2 = c2.lhs
    rhs2 = c2.rhs
    equ2 = c2.equ

    equ_cmp = cmp_primitives(equ1, equ2)
    if equ_cmp != 0:
        return equ_cmp

    lhs_cmp = cmp_terms(lhs1, lhs2)
    if lhs_cmp != 0:
        return lhs_cmp

    return cmp_terms(rhs1, rhs2)
cmp_ctups_fn = cmp_to_key(cmp_ctups)

################################################################################

class SimpleCongruenceClosure:
    """
    1. Consider all subterms t of ϕ.
    2. If (t1 = t2) is a predicate in ϕ, put t1,t2 in the same
    equivalence class. All other terms in their own singleton
    equivalence classes.
    3. If two classes share a term, merge them.
    4. Apply congruence closure: If t1 and t2 are in the same
    equivalence class, then merge the equivalence classes of F(t1)
    and F(t2).
    5. If there is a disequality t1 != t2 in ϕ, with t1 and t2 in the
    same equivalence class, return UNSAT. Else return SAT.
    """
    def __init__(self, verbose=False):
        self.conjunction_list = []
        self.unique_terms = []
        self.equivalence_classes = []
        self.disequalities = []
        self.verbose = verbose

    def variables(self):
        vars = []
        for term in self.unique_terms:
            if term.variable() not in vars:
                vars.append(term.variable())
        return vars

    def terms_bottom(self, t1, t2):
        if self.verbose:
            print(f"testing if {t1} == {t2} bottom")

        disequality_form = sorted([t1, t2], key=cmp_terms_fn)

        def inner(diseq_lhs, diseq_rhs):
            if self.verbose:
                print(f"    against requirement: {diseq_lhs} != {diseq_rhs}")

            if disequality_form == [diseq_lhs, diseq_rhs]:
                if self.verbose:
                    print(f"Bottom!")
                return True

            if  diseq_lhs.termtype == "FUNCTION" and \
                diseq_rhs.termtype == "FUNCTION" and \
                diseq_lhs.function == diseq_rhs.function:
                if inner(diseq_lhs.argument, diseq_rhs.argument):
                    if self.verbose:
                        print(f"Bottom!")
                    return True

            return False

        for [diseq_lhs, diseq_rhs] in self.disequalities:
            # if t1 = x1 and t2 = x2, meaning we are testing feasibility of x1=x2
            # this will test x1 = x2 against all disequalities
            if inner(diseq_lhs, diseq_rhs):
                return True

            # F(x1) == F(x2) ==> x1 == x2
            # This is incorrect.
            # if  t1.termtype == "FUNCTION" and \
            #     t2.termtype == "FUNCTION" and \
            #     t1.function == t2.function:
            #     if self.terms_bottom(t1.argument, t2.argument):
            #         return True

        return False

    def check(self):
        # check the disequalities internally
        for [lhs, rhs] in self.disequalities:
            if self.verbose:
                print(f"Checking if disequality {lhs} != {rhs} bottom by itself")
            if lhs == rhs:
                if self.verbose:
                    print(f"Bottom!")
                return False

        for ec in self.equivalence_classes:
            for idx1 in range(len(ec)):
                for idx2 in range(idx1+1, len(ec)):
                    t1 = ec[idx1]
                    t2 = ec[idx2]
                    if self.terms_bottom(t1, t2):
                        return False
        return True

    def functions_with_term_args(self, t1):
        has_argument = []
        for unique_term in self.unique_terms:
            if unique_term.termtype == "FUNCTION":
                if unique_term.argument == t1:
                    has_argument.append(unique_term.function)
        return has_argument

    def equivalence_classes_with_function(self, functionname, argument):
        idxs = []
        for idx, ec in enumerate(self.equivalence_classes):
            for term in ec:
                if term.termtype != "FUNCTION":
                    continue
                if term.function == functionname and term.argument == argument:
                    idxs.append(idx)
                    break
        return idxs

    def merge_equivalence_classes(self):
        def merge_loop_body():
            # Term equality: if a term exists in two
            # eclasses, merge those two eclasses
            for idx1 in range(len(self.equivalence_classes)):
                for idx2 in range(idx1+1, len(self.equivalence_classes)):
                    ec1 = self.equivalence_classes[idx1]
                    ec2 = self.equivalence_classes[idx2]
                    for t in ec1:
                        if t in ec2:
                            # Terms equal?
                            merge(ec1, ec2)
                            return True
            # Congruence closure: if t1 == t2, then
            # F(t1) == F(t2) for any F
            for ec in self.equivalence_classes:
                for idx1 in range(len(ec)):
                    for idx2 in range(idx1+1, len(ec)):
                        # t1 and t2 are in the same eclass
                        t1 = ec[idx1]
                        t2 = ec[idx2]

                        if self.verbose:
                            print(f"attempting CC with {t1} and {t2}")

                        has_t1_arg = self.functions_with_term_args(t1)
                        if has_t1_arg == []:
                            continue
                        if self.verbose:
                            print(f"functions {has_t1_arg} has {str(t1)} as input")

                        has_t2_arg = self.functions_with_term_args(t2)
                        if has_t2_arg == []:
                            continue
                        if self.verbose:
                            print(f"functions {has_t2_arg} has {str(t2)} as input")

                        has_both = [f for f in has_t1_arg if f in has_t2_arg]
                        if has_both == []:
                            continue
                        if self.verbose:
                            print(f"functions {has_both} has both as input")

                        for functionname in has_both:
                            # Find all equivalence class indexes with this function
                            ecidx_with_t1 = self.equivalence_classes_with_function(
                                functionname, t1
                            )
                            ecidx_with_t2 = self.equivalence_classes_with_function(
                                functionname, t2
                            )
                            no_dups = list(dict.fromkeys(ecidx_with_t1 + ecidx_with_t2))
                            if len(no_dups) >= 2:
                                merge(self.equivalence_classes[no_dups[0]], self.equivalence_classes[no_dups[1]])

            return False

        def merge(ec1, ec2):
            if self.verbose:
                print(f"merging {ec1} and {ec2}")
            # new_ec = list(dict.fromkeys(ec1 + ec2))
            new_ec = []
            for term in ec1:
                if term not in new_ec:
                    new_ec.append(term)
            for term in ec2:
                if term not in new_ec:
                    new_ec.append(term)

            self.equivalence_classes.remove(ec1)
            self.equivalence_classes.remove(ec2)
            self.equivalence_classes.append(new_ec)

        for _ in range(1000):
            merged_something = merge_loop_body()
            if not merged_something:
                break
        else:
            # Timeout
            assert False

    def add_conjunction_term(self, conj):
        assert isinstance(conj, ConjunctionTuple)
        lhs = conj.lhs
        rhs = conj.rhs
        equ = conj.equ

        self.conjunction_list.append(conj)
        self.conjunction_list.sort(key=cmp_ctups_fn)

        lhsrhs = sorted([lhs, rhs], key=cmp_terms_fn)

        # (Possibly) Add new unique terms
        for term in lhsrhs:
            if term not in self.unique_terms:
                if self.verbose:
                    print(f"Appending {term} to unique terms")
                self.unique_terms.append(term)

        # Check that functions only use existing variables
        for term in lhsrhs:
            if term.termtype == "FUNCTION":
                assert term.variable() in self.variables()

        # If this is an equality, make it an equivalence class
        # Otherwise add to the disequalities
        if equ:
            self.equivalence_classes.append(lhsrhs)
        else:
            self.disequalities.append(lhsrhs)

        # (Recursively) Merge equivalence classes
        self.merge_equivalence_classes()

        return True

    def __str__(self):
        string = ""
        string += "<CC solver>\n"
        string += "All (dis)equalities:\n"
        for idx, item in enumerate(self.conjunction_list):
            if idx != 0:
                string += "\n"
            string += f"    {str(item)}"
        string += "\n"

        string += "Unique terms:\n"
        for ut in self.unique_terms:
            string += f"    {ut}\n"

        string += "Disequalities\n"
        for (lhs,rhs) in self.disequalities:
            string += f"    {lhs} != {rhs}\n"

        for idx, ec in enumerate(self.equivalence_classes):
            string += f"Equivalence class {idx}:\n"
            for term in ec:
                string += f"    {str(term)}\n"
        string += "</CC solver>"
        return string
    def __repr__(self):
        return self.__str__()

################################################################################

class CNF:
    def __init__(self):
        self.disjunctions = []

    def add_disjunction(self, disjunction):
        assert isinstance(disjunction, list)
        assert all(isinstance(item, ConjunctionTuple) for item in disjunction)
        self.disjunctions.append(disjunction)

    def __str__(self):
        string = ""
        for didx, disjunction in enumerate(self.disjunctions):
            string += "["
            for idx, ctup in enumerate(disjunction):
                string += f"({ctup})"
                if idx != len(disjunction)-1:
                    string += " v "
            string += "]"
            if didx != len(self.disjunctions)-1:
                string += " & "
        return string
    def __repr__(self):
        return self.__str__()

def cnf_and(cnf1, cnf2):
    assert isinstance(cnf1, CNF)
    assert isinstance(cnf2, CNF)
    new_cnf = CNF()
    for disjunction in cnf1.disjunctions:
        new_cnf.add_disjunction(disjunction)
    for disjunction in cnf2.disjunctions:
        new_cnf.add_disjunction(disjunction)
    return new_cnf

def cnf_and_list(cnfs):
    assert isinstance(cnfs, list)
    assert all(isinstance(item, CNF) for item in cnfs)
    length = len(cnfs)
    if length == 0:
        return CNF()
    if length == 1:
        return cnfs[0]
    return cnf_and(cnfs[0], cnf_and_list(cnfs[1:]))

def cnf_not(cnf):
    assert isinstance(cnf, CNF)
    length = len(cnf.disjunctions)
    if length == 0:
        return cnf
    else:
        # not(a or b) = (not a) and (not b)
        new_cnf = CNF()
        for ctup in cnf.disjunctions[0]:
            assert isinstance(ctup, ConjunctionTuple)
            neg_ctup = ctup.negated()
            new_cnf.add_disjunction([neg_ctup])

        cnf_remaining = CNF()
        cnf_remaining.disjunctions = cnf.disjunctions[1:]
        not_rest = cnf_not(cnf_remaining)

        return cnf_or(new_cnf, not_rest)

def cnf_or(cnf1, cnf2):
    assert isinstance(cnf1, CNF)
    assert isinstance(cnf2, CNF)
    length1 = len(cnf1.disjunctions)
    length2 = len(cnf2.disjunctions)
    if length2 > length1:
        return cnf_or(cnf2, cnf1)
    if length1 == 0:
        return cnf2
    if length2 == 0:
        return cnf1
    # Base case
    new_cnf = CNF()
    if length2 == 1:
        cnf2_disjunction = cnf2.disjunctions[0]
        for disjunction in cnf1.disjunctions:
            new_disjunction = disjunction.copy()
            for literal in cnf2_disjunction:
                new_disjunction.append(literal)
            new_cnf.add_disjunction(new_disjunction)
        return new_cnf
    # Recursive case: distribute cnf2
    else:
        new_disjunctions = []
        for disjunction1 in cnf1.disjunctions:
            single_cnf1 = CNF()
            single_cnf1.add_disjunction(disjunction1)
            assert len(single_cnf1.disjunctions) == 1
            distributed_cnf = cnf_or(single_cnf1, cnf2)
            new_disjunctions.append(distributed_cnf)
        return cnf_and_list(new_disjunctions)


def formula2cnf(formula):
    assert isinstance(formula, Formula)
    unique_ctups = []

    def maybe_append_to_unique_list(left, right):
        [left2, right2] = sorted([left, right], key=cmp_terms_fn)
        for l, r in unique_ctups:
            if l == left2 and r == right2:
                break
        else:
            unique_ctups.append((left, right))

    def inner(formula):
        assert isinstance(formula, Formula)
        match formula.formulatype:
            case "ATOM":
                atom = formula.atom
                left = atom.left
                right = atom.right
                ctup = ConjunctionTuple(left, right, True)
                maybe_append_to_unique_list(left, right)
                cnf = CNF()
                cnf.add_disjunction([ctup])
                return cnf
            case "NOT":
                nf = formula.neg_formula
                match nf.formulatype:
                    case "ATOM":
                        atom = nf.atom
                        left = atom.left
                        right = atom.right
                        ctup = ConjunctionTuple(left, right, False)
                        maybe_append_to_unique_list(left, right)
                        cnf = CNF()
                        cnf.add_disjunction([ctup])
                        return cnf
                    case "AND":
                        l = nf.left
                        r = nf.right
                        conj = cnf_and(inner(l), inner(r))
                        return cnf_not(conj)
                    case "OR":
                        l = nf.left
                        r = nf.right
                        disj = cnf_or(inner(l), inner(r))
                        return cnf_not(disj)
                    case _:
                        assert False
            case "AND":
                l = formula.left
                r = formula.right
                return cnf_and(inner(l), inner(r))
            case "OR":
                l = formula.left
                r = formula.right
                return cnf_or(inner(l), inner(r))
            case _:
                assert False
    return inner(formula), unique_ctups

################################################################################

def formulaCC(formula, verbose=GLOBAL_VERBOSE):
    assert isinstance(formula, Formula)
    SAT_solver = DPLL.DPLL(termprint=False,
                           waitforinput=False,
                           termprint_delay_seconds=0)

    # uniquelist is a list of pairs of Terms
    cnf, uniquelist = formula2cnf(formula)
    if verbose:
        print(f"cnf: {cnf}")

    # dictionary mapping equations to their SAT solver representation
    # vardict[x1,x2] = 1 would mean that x1=x2 maps to 1 and x1 != x2 maps to -1
    vardict = dict()
    for idx, (lhs,rhs) in enumerate(uniquelist):
        vardict[(lhs,rhs)] = idx+1
        vardict[idx+1] = (lhs,rhs)
    if verbose:
        print(f"vardict: {vardict}")


    # turn cnf into clauses and add them to the SAT solver
    for disjunction in cnf.disjunctions:
        clause = []
        for ctup in disjunction:
            assert isinstance(ctup, ConjunctionTuple)
            lhs = ctup.lhs
            rhs = ctup.rhs
            # print(f"lhs: {lhs}")
            # print(f"rhs: {rhs}")
            sat_repr = vardict[(lhs,rhs)]
            if not ctup.equ:
                sat_repr *= -1
            clause.append(sat_repr)
        if verbose:
            print(f"adding clause {clause}")
        SAT_solver.add_clause(clause)

    timeout_value = 1000

    for i in range(timeout_value):
        if verbose:
            print(f"formulaCC starting loop iteration {i}")

        # get a model (conjunction) from the SAT solver
        sat_or_unsat, sat_model = SAT_solver.solve()
        if not sat_or_unsat:
            if verbose:
                print(f"SAT solver returned UNSAT.")
            return False
        if verbose:
            print(f"model: {sat_model}")

        # translate back to a list of conjunctions
        conj_list = []
        for literal in sat_model:
            abslit = abs(literal)
            (lhs,rhs) = vardict[abslit]
            ctup = ConjunctionTuple(lhs, rhs, literal > 0)
            conj_list.append(ctup)
        if verbose:
            print(f"conj_list: {conj_list}")

        # give to CC solver
        CC_solver = SimpleCongruenceClosure(verbose=verbose)
        for conj in conj_list:
            CC_solver.add_conjunction_term(conj)
        if verbose:
            print(f"CC_solver: {CC_solver}")
        if CC_solver.check():
            return True

        # The SAT model is invalid.
        # Negate it and add it as a clause to the SAT solver.
        neg_model_clause = []
        for literal in sat_model:
            neg_model_clause.append(literal * -1)
        if verbose:
            print(f"neg_model_clause: {neg_model_clause}")
        SAT_solver.add_clause(neg_model_clause)
    else:
        print("formulaCC timeout")
        assert False


################################################################################

def example1():
    print("Example 1: shows that (x1 = x2) and (x2 = x3) and (x1 != x3) is UNSAT")
    cc = SimpleCongruenceClosure(verbose=GLOBAL_VERBOSE)

    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    x3 = Term("VAR", var="x3")

    eq1 = ConjunctionTuple(x1, x2, True)
    eq2 = ConjunctionTuple(x2, x3, True)
    cc.add_conjunction_term(eq1)
    cc.add_conjunction_term(eq2)
    print(cc)
    print("SAT" if cc.check() else "UNSAT")
    print("Should be SAT")

    eq3 = ConjunctionTuple(x1, x3, False)
    cc.add_conjunction_term(eq3)
    print(cc)
    print("SAT" if cc.check() else "UNSAT")
    print("Should be UNSAT")

def example2():
    print("Example 2: shows merging of equivalence classes in the presence of functions")
    print("x1=x2 will create an equivalence class due to F(x1)=F(x2)")
    cc = SimpleCongruenceClosure(verbose=GLOBAL_VERBOSE)

    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    x3 = Term("VAR", var="x3")
    x4 = Term("VAR", var="x4")

    f_x1 = Term("FUNCTION", function="F", argument=x1)
    f_x2 = Term("FUNCTION", function="F", argument=x2)

    eq1 = ConjunctionTuple(x1, x2, True)
    eq2 = ConjunctionTuple(f_x1, x3, True)
    eq3 = ConjunctionTuple(f_x2, x4, True)

    cc.add_conjunction_term(eq1)
    cc.add_conjunction_term(eq2)
    cc.add_conjunction_term(eq3)
    print(cc)

def example3():
    print("Example 3: ")
    print("bottom due to (x1 = x3) and (F(x1) != F(x3))")
    cc = SimpleCongruenceClosure(verbose=GLOBAL_VERBOSE)

    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    x3 = Term("VAR", var="x3")
    x4 = Term("VAR", var="x4")
    x5 = Term("VAR", var="x5")

    f_x1 = Term("FUNCTION", function="F", argument=x1)
    f_x3 = Term("FUNCTION", function="F", argument=x3)

    eq1 = ConjunctionTuple(x1, x2, True)
    eq2 = ConjunctionTuple(x2, x3, True)
    eq3 = ConjunctionTuple(x4, x5, True)
    eq4 = ConjunctionTuple(x1, x5, False)
    eq5 = ConjunctionTuple(f_x1, f_x3, False)

    for e in [eq1, eq2, eq3, eq4, eq5]:
        cc.add_conjunction_term(e)

    print(cc)
    print("SAT" if cc.check() else "UNSAT")
    print("Should be UNSAT")

def example4():
    print("Example 4: shows that congruence causes an UNSAT result")
    print("x1 = x2 causes F(x1) != F(x2) to bottom out")
    cc = SimpleCongruenceClosure(verbose=GLOBAL_VERBOSE)

    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")

    f1 = Term("FUNCTION", function="F", argument=x1)
    f2 = Term("FUNCTION", function="F", argument=x2)

    cc.add_conjunction_term(ConjunctionTuple(x1, x2, True))
    cc.add_conjunction_term(ConjunctionTuple(f1, f2, False))

    print(cc)
    print("SAT" if cc.check() else "UNSAT")
    print("Should be UNSAT")

def example5():
    print("Example 5: x1 == x2 and F(x1) == F(x2) is SAT")
    cc = SimpleCongruenceClosure(verbose=GLOBAL_VERBOSE)

    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")

    f1 = Term("FUNCTION", function="F", argument=x1)
    f2 = Term("FUNCTION", function="F", argument=x2)

    cc.add_conjunction_term(ConjunctionTuple(x1, x2, False))
    cc.add_conjunction_term(ConjunctionTuple(f1, f2, True))

    print(cc)
    print("SAT" if cc.check() else "UNSAT")
    print("Should be SAT")

def example6():
    print("Example 6: bigger example")
    print("wrong result...")
    cc = SimpleCongruenceClosure(verbose=GLOBAL_VERBOSE)

    x = Term("VAR", var="x")

    gx = Term("FUNCTION", function="g", argument=x)
    ggx = Term("FUNCTION", function="g", argument=gx)
    gggx = Term("FUNCTION", function="g", argument=ggx)
    ggggx = Term("FUNCTION", function="g", argument=gggx)
    gggggx = Term("FUNCTION", function="g", argument=ggggx)

    cc.add_conjunction_term(ConjunctionTuple(gggx, x, True))
    cc.add_conjunction_term(ConjunctionTuple(gggggx, x, True))
    cc.add_conjunction_term(ConjunctionTuple(gx, x, False))

    print(cc)
    print("SAT" if cc.check() else "UNSAT")
    print("Should be UNSAT")

def example7():
    print("Example 7: constructing CNFs with the CNF data structure")
    a = Term("VAR", var="a")
    b = Term("VAR", var="b")
    c = Term("VAR", var="c")
    d = Term("VAR", var="d")
    e = Term("VAR", var="e")
    f = Term("VAR", var="f")
    g = Term("VAR", var="g")
    h = Term("VAR", var="h")

    c1 = CNF()
    c1.add_disjunction([
        ConjunctionTuple(a, a, True),
        ConjunctionTuple(b, b, True),
    ])
    c1.add_disjunction([
        ConjunctionTuple(c, c, True),
        ConjunctionTuple(d, d, True),
    ])

    c2 = CNF()
    c2.add_disjunction([
        ConjunctionTuple(e, e, True),
        ConjunctionTuple(f, f, True),
    ])
    c2.add_disjunction([
        ConjunctionTuple(g, g, True),
        ConjunctionTuple(h, h, True),
    ])
    c3 = CNF()
    c3 = cnf_or(c1, c2)

    print(f"c1: {c1}")
    print(f"c2: {c2}")
    print(f"c1 or c2: {c3}")

def example8():
    print("Example 8: constructing CNFs with the CNF data structure")
    a = Term("VAR", var="a")
    b = Term("VAR", var="b")

    c1 = CNF()
    c1.add_disjunction([
        ConjunctionTuple(a, a, True),
        ConjunctionTuple(b, b, True),
    ])
    print(c1)
    print(cnf_not(c1))
    print(cnf_not(cnf_not(c1)))
    print()

    c2 = CNF()
    c2.add_disjunction([
        ConjunctionTuple(a, a, True)
    ])
    c2.add_disjunction([
        ConjunctionTuple(b, b, True)
    ])
    print(c2)
    print("negate:", cnf_not(c2))
    print("negate back:", cnf_not(cnf_not(c2)))
    print()

    c3 = cnf_and(c1, c2)
    print(c3)
    print("negate:", cnf_not(c3))
    print("negate back:", cnf_not(cnf_not(c3)))

def example9():
    print("Example 9: build a formula and translate to CNF")
    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    F_x1 = Term("FUNCTION", function="F", argument=x1)

    formula1 = Formula("ATOM", atom=Atom(F_x1, x1))
    formula2 = Formula("NOT", neg_formula=formula1)
    cnf, uniquelist = formula2cnf(formula2)
    print(f"formula: {formula2}")
    print(f"cnf: {cnf}")

    sat = formulaCC(formula2)
    print("SAT" if sat else "UNSAT")
    print("Should be SAT")

def example10():
    print("Example 10: run congruence closure on a formula")
    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    formula = Formula("ATOM", atom=Atom(x1, x2))
    print(f"formula: {formula}")
    sat = formulaCC(formula)
    print("SAT" if sat else "UNSAT")
    print("Should be SAT")

def example11():
    print("Example 11: run congruence closure on a formula")
    x = Term("VAR", var="x")
    formula1 = Formula("ATOM", atom=Atom(x, x))
    formula2 = Formula("NOT", neg_formula=formula1)
    print(f"formula: {formula2}")
    sat = formulaCC(formula2)
    print("SAT" if sat else "UNSAT")
    print("should be UNSAT")

def example12():
    print("Example 12: run congruence closure on a formula")
    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    x3 = Term("VAR", var="x3")
    x4 = Term("VAR", var="x4")

    f1 = Formula("ATOM", atom=Atom(x1, x2))
    f2 = Formula("ATOM", atom=Atom(x2, x4))
    f12 = Formula("AND", left=f1, right=f2)

    f3 = Formula("ATOM", atom=Atom(x1, x3))
    f4 = Formula("ATOM", atom=Atom(x3, x4))
    f34 = Formula("AND", left=f3, right=f4)

    f12_or_34 = Formula("OR", left=f12, right=f34)

    f5 = Formula("NOT", neg_formula=Formula("ATOM", atom=Atom(x1, x4)))

    formula = Formula("AND", left=f12_or_34, right=f5)
    print(f"formula: {formula}")

    sat = formulaCC(formula)
    print("SAT" if sat else "UNSAT")
    print("should be UNSAT")

def example13():
    print("Example 13: run congruence closure on a formula")
    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    x3 = Term("VAR", var="x3")
    x4 = Term("VAR", var="x4")
    F_x1 = Term("FUNCTION", function="F", argument=x1)
    F_x2 = Term("FUNCTION", function="F", argument=x2)
    G_x3 = Term("FUNCTION", function="G", argument=x3)
    G_x4 = Term("FUNCTION", function="G", argument=x4)

    f1 = Formula("ATOM", atom=Atom(x1, x2))
    f2 = Formula("ATOM", atom=Atom(x3, x4))
    f1or2 = Formula("OR", left=f1, right=f2)

    f3 = Formula("ATOM", atom=Atom(F_x1, F_x2))
    f4 = Formula("ATOM", atom=Atom(G_x3, G_x4))
    f3or4 = Formula("OR", left=f3, right=f4)

    print()

    formula1 = Formula("AND", left=f1or2, right=f3or4)
    print(f"formula: {formula1}")
    sat = formulaCC(formula1)
    print("SAT" if sat else "UNSAT")
    print("should be SAT")

    print()

    not_f3or4 = Formula("NOT", neg_formula=f3or4)
    formula2 = Formula("AND", left=f1or2, right=not_f3or4)

    print(f"formula: {formula2}")
    sat = formulaCC(formula2)
    print("SAT" if sat else "UNSAT")
    print("should be UNSAT")

def example14():
    print("Example 14: disequalities makes CC UNSAT")
    print("i.e. F(x1) != F(x2) ==> x1 != x2")
    x1 = Term("VAR", var="x1")
    x2 = Term("VAR", var="x2")
    F_x1 = Term("FUNCTION", function="F", argument=x1)
    F_x2 = Term("FUNCTION", function="F", argument=x2)
    Fx1_eq_Fx2 = Formula("ATOM", atom=Atom(F_x1, F_x2))
    Fx1_neq_Fx2 = Formula("NOT", neg_formula=Fx1_eq_Fx2)
    x1_eq_x2 = Formula("ATOM", atom=Atom(x1, x2))
    formula = Formula("AND", left=Fx1_neq_Fx2, right=x1_eq_x2)
    print(f"formula: {formula}")
    sat = formulaCC(formula)
    print("SAT" if sat else "UNSAT")
    print("should be UNSAT")

def example15():
    print("Example 15: running example from slides")
    print("i.e. (x=y)&(x!=z) OR (x=z)&(x!=y) AND (y=z) ")
    x = Term("VAR", var="x")
    y = Term("VAR", var="y")
    z = Term("VAR", var="z")
    xy = Formula("ATOM", atom=Atom(x, y))
    xz = Formula("ATOM", atom=Atom(x, z))
    yz = Formula("ATOM", atom=Atom(y, z))
    n_xz = Formula("NOT", neg_formula=xz)
    n_xy = Formula("NOT", neg_formula=xy)

    and0 = Formula("AND", left=xy, right=n_xz)
    and1 = Formula("AND", left=xz, right=n_xy)

    or0 = Formula("OR", left=and0, right=and1)

    formula = Formula("AND", left=or0, right=yz)
    print(f"formula: {formula}")
    sat = formulaCC(formula, verbose=True)
    print("SAT" if sat else "UNSAT")
    print("should be UNSAT")



def all_examples():
    print("________________________________________________________________________________")
    example1()
    print("________________________________________________________________________________")
    example2()
    print("________________________________________________________________________________")
    example3()
    print("________________________________________________________________________________")
    example4()
    print("________________________________________________________________________________")
    example5()
    print("________________________________________________________________________________")
    example6()
    print("________________________________________________________________________________")
    example7()
    print("________________________________________________________________________________")
    example8()
    print("________________________________________________________________________________")
    example9()
    print("________________________________________________________________________________")
    example10()
    print("________________________________________________________________________________")
    example11()
    print("________________________________________________________________________________")
    example12()
    print("________________________________________________________________________________")
    example13()
    print("________________________________________________________________________________")
    example14()
    print("________________________________________________________________________________")
    example15()
    print("________________________________________________________________________________")


def main():
    all_examples()


if __name__ == "__main__":
    main()

