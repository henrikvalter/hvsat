
from termcolor import colored
import os
import time

def print_clauses(clauses, assignments):
    for clause in clauses:
        print("[", end="")
        for cnt, lit in enumerate(clause):
            for assignment in assignments:
                if lit == assignment:
                    color = "green"
                    break
                elif lit == -assignment:
                    color = "red"
                    break
            else:
                color = "white"
            # print the literal
            abslit = abs(lit)
            sign = " " if lit > 0 else "-"
            print(colored(f"{sign}x{abslit}", color), end="")
            if cnt < len(clause)-1:
                print(", ", end="")
        print("]\n", end="")

def flush_terminal():
    os.system("clear")
    # for windows it's probably cls

def print_string_and_clauses(string, clauses, assignments, waitforinput, delay):
    flush_terminal()
    print(string)
    print_clauses(clauses, assignments)
    if waitforinput:
        input("press enter to continue")
    else:
        time.sleep(delay)

def main():
    ex_clauses = [
        [1, 2, -3],
        [-2, 3]
    ]
    ex_assignments = [1, 3]

if __name__ == "__main__":
    main()
