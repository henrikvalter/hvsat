
GLOBAL_DELAY = 0.1

# This is definitely the correct place to put this function.
def res2str(res):
    if res is None:
        return "UNKNOWN"
    if res:
        return "SATISFIABLE"
    return "UNSATISFIABLE"