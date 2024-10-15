
# hvsat

![hvsat](https://github.com/henrikvalter/hvsat/blob/master/hvsat.gif)

hvsat is a collection of SAT solvers with visual elements.
During processing, they can print their current solver state
to the terminal, making them a good tool for learning about SAT solving.

This project originated as a follow-up project after a summer school
in SAT/SMT/AR (SAT/SMT/AR Summer School 2024, in Nancy, France).

See slides.pdf for a presentation about the project.

## Solvers

The functionality for printing to the terminal is in
TerminalGraphics.py.

### Loops

Possibly the simplest and most straightforward solution,
this solver loops over each variable (True or False) and
tries every model. The implementation here is hard-coded
for 8 variables.

### NaiveLocalSearch

Assigns all variables randomly, and then, in an infinite loop,
negates assignments. If the instance is SAT it will eventually
terminate, and if UNSAT it will loop forever.

### BetterLocalSearch

Like NaiveLocalSearch, but uses a better metric (that being, any at all)
for picking the next variable. Often surprisingly good.

### DPLL

Implements a DPLL algorithm; see the slides.

### CDCL

Implements a CDCL algorithm; see the slides.

## CongruenceClosure

CongruenceClosure is an implementation of a simple Congruence Closure algorithm,
demonstrating an example of using SAT in a more expressive logic.

## Examples

Use the Loops solver to solve a (unsatisfiable) instance
$ python3 src/Loops.py input/nordstrom2.cnf

Use the DPLL solver to solve a simple (satisfiable) instance
$ python3 src/DPLL.py input/simple.cnf

Use the CDCL solver to solve a more complex instance
$ python3 src/DPLL.py input/aim-50-1_6-yes1-4.cnf

Use the CDCL solver to prove the pidgeonhole principle
for 5 pidgeons and 4 holes.
SAT is infamously bad at PHP, so this is pretty slow.
$ python3 src/CDCL.py input/php_5_4.cnf

Use the CDCL solver to solve a big instance
$ python3 src/DPLL.py input/aim-50-1_6-yes1-4.cnf

If you don't want CDCL (or any other solver) to
print to the terminal, just instantiate the solver with CDCL().
The main function in CDCL.py demonstrates this.


