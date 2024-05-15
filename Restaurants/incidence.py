import csv
from itertools import chain, combinations
import networkx as nx
import xml.etree.ElementTree as ET


def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))


def csv_to_I(csv_file, incidence_symbols=['x'], sep=';'):
    with open(csv_file, 'r', encoding="utf-8-sig", errors='ignore') as file:
        table = list(csv.reader(file, delimiter=sep))

    table[0].pop(0)
    B = table.pop(0)
    I = set()

    # Create a tuple of the object/attribute for each cell containing the specified truth value
    for row in table:
        for count, cell in enumerate(row):
            if cell in incidence_symbols:
                I.add((row[0], B[count - 1]))

    return Graph(I)


class Graph:
    _instances = dict()

    def __new__(cls, edges):

        # Check if instance already exists; if so, return it
        for instance in cls._instances.values():
            if instance.edges == edges:
                return instance

        instance = super().__new__(cls)
        cls._instances['g' + str(len(cls._instances))] = instance
        return instance

    def __init__(self, edges):
        self.id = len(self._instances)
        self.edges = edges
        self.nodes = {node for edge in edges for node in edge}
        self._episteme = None

    # Generate episteme if called from graph.
    @property
    def episteme(self):
        if self._episteme is None:
            self._episteme = Episteme(self.__construct_lattice())
        return self._episteme

    @episteme.setter
    def episteme(self, value):
        self._episteme = value

    # Generates the reflexive closure of the graph as a new Graph instance.
    def refl_closure(self):
        closure = set(self.edges)
        while True:
            new_relations = set((x, x) for x, y in closure for q, w in closure if True)

            closure_until_now = closure | new_relations

            if closure_until_now == closure:
                break

            closure = closure_until_now

        return Graph(closure)

    # Generates the transitive closure of the graph as a new Graph instance.
    def trans_closure(self):
        closure = set(self.edges)
        while True:
            new_relations = set((x, w) for x, y in closure for q, w in closure if q == y)

            closure_until_now = closure | new_relations

            if closure_until_now == closure:
                break

            closure = closure_until_now

        return Graph(closure)

    # Generates the transitive reduction of the graph as a new Graph instance.
    def trans_reduction(self):
        reduction = set(self.edges)

        for x in self.nodes:
            for y in self.nodes:
                for z in self.nodes:
                    if not (x == y or y == z):
                        if (x, z) in reduction:
                            if {(x, y),(y, z)}.issubset(self.edges):
                                reduction.remove((x,z))
        return Graph(reduction)

    # Generates the reflexive reduction of the graph as a new Graph instance
    def refl_reduction(self):
        return Graph({edge for edge in self.edges if edge[0] != edge[1]})

    # Gets the codomain elements that share tuples with elements of A in the graph
    def up(self, A):
        return {b for b in self.nodes if all((a, b) in self.edges for a in A)}

    # Gets the domain elements that share tuples with elements of B in the graph
    def down(self, B):
        return {a for a in self.nodes if all((a, b) in self.edges for b in B)}


    # Construct concepts from sub-structures in the graph
    def __construct_lattice(self):
        concepts = set()

        # CbO algorithm; found in Konecny & Krajca (2021)
        def GenerateFrom(A1, B1, seen):
            # Input: A - Extent
            #        B - Intent
            #        i - Last added attribute

            # Instantiate new concept from the passed extent and intent and add it to the output set
            concepts.add(Concept(A1, B1, self))

            # For all the unvisited attributes in I
            for b in self.nodes.difference(seen):
                # if the attribute is not in the intent
                if b not in B1:
                    # Derive an extent from the attribute, and from the extent another intent
                    A2 = A1.intersection(self.down({b}))
                    B2 = self.up(A2)

                    # Check whether all seen attributes are in the new intent. This avoids needless repetition
                    if B1.intersection(seen) == B2.intersection(seen):
                        seen.add(b)
                        GenerateFrom(A2, B2, seen.copy())

        GenerateFrom(self.nodes, self.up(self.nodes), set())
        return concepts

    def to_graphml(self, file):
        g = nx.DiGraph()

        # Add sub-concept nodes
        for node in self.nodes:
            if node not in g.nodes:
                if isinstance(node, Concept):
                    g.add_node(node, objects=str(set(node.A)), attributes=str(set(node.B)),
                               incidences=node.__str__(auxiliary_info=False))
                else:
                    g.add_node(node, label=str(node))

        g.add_edges_from(self.edges)

        nx.write_graphml(g, path=file)



# A specification of the graph class which carries the lattice axioms. Join and meet operators are defined here
class Lattice(Graph):
    def __init__(self, edges):
        super().__init__(edges)

        # Check if the graph is a lattice
        for n1 in self.nodes:
            if not (n1, n1) in self.edges:
                raise ValueError('Passed edges do not form a reflexive graph')
            for n2 in self.nodes:
                for n3 in self.nodes:
                    # Check for transitivity
                    if (n1, n2) in self.edges and (n2, n3) in self.edges and not (n1, n3) in self.edges:
                        raise ValueError('Passed edges do not form a transitive graph')

                # Check for joins and meets (Can be much more efficient)
                self.join(n1, n2)
                self.meet(n1, n2)

    def join(self, *nodes):

        # Get candidates
        candidates = []
        for right_node in self.nodes:
            if all((node, right_node) in self.edges for node in nodes):
                candidates.append(right_node)

        # Limit to least upper nodes
        candidates[:] = [c1 for c1 in candidates if not any(c1 != c2 and (c2, c1) in self.edges for c2 in candidates)]

        # Check if there is only one join (Requirement of lattice structure)
        if len(candidates) > 1:
            raise ValueError('Too many candidates in join operation')
        elif len(candidates) == 0:
            raise ValueError('Too few candidates in join operation')
        else:
            return candidates[0]

    def meet(self, *nodes):

        # Get lower-ordered nodes as candidates (Requirement of lattice structure)
        candidates = []
        for left_node in self.nodes:
            if all((left_node, node) in self.edges for node in nodes):
                candidates.append(left_node)

        # Limit to greatest lower nodes
        candidates[:] = [c1 for c1 in candidates if not any(c1 != c2 and (c1, c2) in self.edges for c2 in candidates)]

        # Check if there is only one meet
        if len(candidates) > 1:
            raise ValueError('Too many candidates in meet operation')
        elif len(candidates) == 0:
            raise ValueError('Too few candidates in meet operation')
        else:
            return candidates[0]

    def assign_depths(self):

        # Get root
        root = list(self.nodes)[0]
        for node in self.nodes:
            root = self.join(root, node)
        root.lvl = 1

        # Transitively reduce edges
        reduction = self.edges.copy()
        for x in self.nodes:
            for y in self.nodes:
                for z in self.nodes:
                    if not (x == y or y == z):
                        if (x, z) in reduction:
                            if {(x, y), (y, z)}.issubset(self.edges):
                                reduction.remove((x, z))

        # Assign depths
        stack = [root]
        while stack:
            node = stack.pop()
            for edge in reduction:
                if edge[0] != edge[1] and edge[1] == node and edge[0].lvl <= node.lvl:
                    edge[0].lvl = node.lvl + 1
                    stack.insert(0, edge[0])

    def assign_heights(self):

        # Get root
        root = list(self.nodes)[0]
        for node in self.nodes:
            root = self.meet(root, node)
        root.height = 1

        # Transitively reduce edges
        reduction = self.edges.copy()
        for x in self.nodes:
            for y in self.nodes:
                for z in self.nodes:
                    if not (x == y or y == z):
                        if (x, z) in reduction:
                            if {(x, y), (y, z)}.issubset(self.edges):
                                reduction.remove((x, z))

        # Assign heights
        stack = [root]
        while stack:
            node = stack.pop()
            for edge in reduction:
                if edge[0] != edge[1] and edge[0] == node and edge[1].height <= node.height:
                    edge[1].height = node.height + 1
                    stack.insert(0, edge[1])


concept_cache = dict()
class Concept:
    _instances = dict()

    def __new__(cls, A, B, I):

        # Check if instance already exists; if so, return it
        for instance in cls._instances.values():
            if instance.A == A and instance.B == B and instance.I == I:
                return instance

        instance = super().__new__(cls)
        cls._instances['c' + str(len(cls._instances))] = instance
        concept_cache['c' + str(len(cls._instances))] = instance
        return instance

    def __init__(self, A, B, I):
        # Check whether A and B form a concept given I and whether I is its own derivation
        if A == I.down(B) and B == I.up(A):
            self.A = A
            self.B = B
            self.I = I
        else:
            raise ValueError(str(A) + " and " + str(B) + " do not form a concept in " + str(I))
        self.id = 'c' + str(len(Concept._instances)-1)
        self.lvl = 0
        self.height = 0

    def __str__(self, auxiliary_info=True):
        output_str = ''
        X = {x for (x, y) in self.I.edges}
        Y = {y for (x, y) in self.I.edges}

        # Define function to avoid recursion over __str__ when concepts are in incidence tuples
        def str_or_cid(value):
            if isinstance(value, Concept):
                return value.id
            else:
                return str(value)

        # Create a set of all attributes and objects
        # Determine the maximum width of each column
        max_x_width = max(len(str_or_cid(x)) for x in X)
        max_y_width = max(len(str_or_cid(y)) for y in Y)

        if auxiliary_info:
            output_str += f"\nA: {self.A}\nB: {self.B}\nI: {self.I}\n"

        # Print the header row
        output_str += " " * (max_x_width + 2)
        for y in Y:
            output_str += str_or_cid(y).center(max_y_width) + " "
        output_str += "\n"

        # Print the horizontal line
        output_str += "-" * (max_x_width + 2) + "-" * (max_y_width + 1) * len(Y) + "\n"

        # Print the table rows
        for x in X:
            output_str += str_or_cid(x).rjust(max_x_width) + " |"
            for y in Y:
                if (x, y) in self.I.edges:
                    if x in self.A and y in self.B:
                        # Show concept incidences
                        output_str += chr(0x25A0).center(max_y_width) + "|"
                    else:
                        # Show other incidences
                        output_str += chr(0x25A1).center(max_y_width) + "|"
                else:
                    output_str += "".center(max_y_width) + "|"
            output_str += "\n"

        return output_str

    def __repr__(self):
        return str(self.id)

    def __hash__(self):
        return hash((frozenset(self.A), frozenset(self.B), self.I))

    def __eq__(self, other):
        if isinstance(other, Concept):
            return self.A == other.A and self.B == other.B and self.I == other.I
        else:
            raise TypeError(str(other) + " is not a Concept, but a " + str(type(other)))


# Class that contains a set of concepts and the specifications and precedences between them
class Episteme:
    def __init__(self, concepts):
        self.concepts = concepts
        specifications = set()
        precedences = set()
        homeomerosities = set()

        for c1 in concepts:
            for c2 in concepts:
                if isinstance(c1, Concept) and isinstance(c2, Concept):

                    # Specification relation
                    if c1.A.issubset(c2.A):
                        specifications.add((c1, c2))

                else:
                    raise TypeError("Set of concepts expected. Found " + str(type(c1)) + ' and ' + str(type(c2)))

        self.specification = Lattice(specifications)


    def concepts_to_graphml(self, file, order_by_subsets=False):
        g = nx.DiGraph()
        nodes = list()
        # Add concepts as triples

        for concept in self.concepts:
            g.add_node(''.join(sorted(str(concept.A))), objects=str(set(concept.A)))
            g.add_node(''.join(sorted(str(concept.B))), objects=str(set(concept.B)))
            g.add_edge(''.join(sorted(str(concept.A))), ''.join(sorted(str(concept.B))))
            if order_by_subsets:
                nodes.append(concept.A)
                nodes.append(concept.B)

        if order_by_subsets:
            for node1 in nodes:
                for node2 in nodes:
                    if set.issubset(node1, node2) \
                            and ''.join(sorted(str(set(node1)))) != ''.join(sorted(str(set(node2)))):
                        g.add_edge(''.join(sorted(str(set(node1)))),
                                   ''.join(sorted(str(set(node2)))),
                                   arrowtail='diamond')

            reduction = set(g.edges)

            for x in g.nodes:
                for y in g.nodes:
                    for z in g.nodes:
                        if not (x == y or y == z):
                            if (x, z) in reduction:
                                if {(x, y), (y, z)}.issubset(g.edges):
                                    reduction.remove((x, z))
            for edge in reduction:
                g.remove_edge(edge[0], edge[1])
            for concept in self.concepts:
                g.add_edge(''.join(sorted(str(concept.A))), ''.join(sorted(str(concept.B))))

        nx.write_graphml(g, path=file)
