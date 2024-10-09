
from graphviz import Digraph

class ImplicationGraph:
    def __init__(self):
        self.graph = []

    def __repr__(self):
        return self.graph.__repr__()

    def assignments(self):
        return [dst for (dst, _) in self.graph]

    def model(self):
        return [lit_assignment for (lit_assignment, _) in self.assignments()]

    def model_literals(self):
        return list(map(abs,self.model()))

    def add(self, dst, srcs):
        # Checks
        old_assigned_vars = self.assignments()
        assert isinstance(dst, tuple)
        assert isinstance(srcs, list)
        for src in srcs:
            assert src in old_assigned_vars
        assignment, _ = dst
        assert abs(assignment) not in self.model_literals()

        # Logic
        self.graph.append((dst, srcs))

    def nodes(self):
        return self.assignments()

    def node_dict(self):
        nodes = self.nodes()
        dictionary = dict()
        for cnt, node in enumerate(nodes):
            dictionary[node] = cnt
        return dictionary

    def edges(self):
        edges = []
        for dst, srcs in self.graph:
            for src in srcs:
                edges.append((src, dst))
        return edges

    def visualize(self):
        dot = Digraph()

        node_dict = self.node_dict()
        print(node_dict)

        print(self.edges())

        for node, nodeidx in node_dict.items():
            var, dlevel = node
            dot.node(str(nodeidx), f"{var}@{dlevel}")

        for src, dst in self.edges():

            src_idx = str(node_dict[src])
            dst_idx = str(node_dict[dst])

            dot.edge(src_idx, dst_idx)

        dot.render(view=True)

def main():
    igraph = ImplicationGraph()
    igraph.add(dst=(-1, 1), srcs=[])
    igraph.add(dst=(4, 1), srcs=[(-1,1)])

    igraph.add(dst=(3, 2), srcs=[])
    igraph.add(dst=(-8, 2), srcs=[(-1,1), (3,2)])

    igraph.add(dst=(-2, 3), srcs=[])
    igraph.add(dst=(11, 3), srcs=[(-2, 3)])

    igraph.add(dst=(7, 4), srcs=[])
    igraph.add(dst=(9, 4), srcs=[(3, 2), (7, 4)])

    print(igraph)

    igraph.visualize()

if __name__ == "__main__":
    main()