###############################################################################
# Imports

import sys
import argparse # Argument parser

from termcolor import colored
from mgtoolkit.library import *

from bitarray import bitarray, frozenbitarray, util
from pprint import pprint


###############################################################################
# General utility

# Exit the program
def terminate_app(code, message=None):
    if message:
        print("Exiting program with code {}: {}.".format(code, message))
    else:
        print("Exiting program with code {}.".format(code))
    sys.exit(code)

# Print section
def print_section(title):
    print("\n\n###############################################################################")
    print(title)
    print("###############################################################################")


###############################################################################
# Functions

def dom_print(cm, redundancies=[], conflicts=[], dominants=[], metapaths=[], glob_verbose=0):
    print("Redundancies: {}".format(len(redundancies)))
    if glob_verbose >= 1:
        if redundancies:
            for metapath in redundancies:
                edgep = []
                for edge in metapath.edge_list:
                    edgep.append((sorted(edge.invertex), sorted(edge.outvertex)))
                print("{} to {} - {}".format(colored(sorted(list(metapath.source)), "blue"), colored(sorted(list(metapath.target)), "yellow"), colored(sorted(edgep), "red")))
                if glob_verbose >= 3:
                    print("Input-dominant: {}; Edge-dominant: {}".format(cm.is_input_dominant_metapath(metapath), cm.is_edge_dominant_metapath(metapath)))
    print("Conflicts: {}".format(len(conflicts)))
    if glob_verbose >= 1:
        if conflicts:
            for metapath in conflicts:
                edgep = []
                for edge in metapath.edge_list:
                    edgep.append((sorted(edge.invertex), sorted(edge.outvertex)))
                print("{} to {} - {}".format(colored(list(metapath.source), "blue"), colored(list(metapath.target), "yellow"), colored(sorted(edgep), "red")))
                if glob_verbose >= 3:
                    print("Input-dominant: {}; Edge-dominant: {}".format(cm.is_input_dominant_metapath(metapath), cm.is_edge_dominant_metapath(metapath)))
    print("Dominants: {}".format(len(dominants)))
    if glob_verbose >= 1:
        if dominants:
            for metapath in dominants:
                edgep = []
                for edge in metapath.edge_list:
                    edgep.append((sorted(edge.invertex), sorted(edge.outvertex)))
                print("{} to {} - {}".format(colored(list(metapath.source), "blue"), colored(list(metapath.target), "yellow"), colored(sorted(edgep), "red")))
                if glob_verbose >= 3:
                    print("Input-dominant: {}; Edge-dominant: {}".format(cm.is_input_dominant_metapath(metapath), cm.is_edge_dominant_metapath(metapath)))
    print("Total metapaths: {}".format(len(metapaths)))
    if glob_verbose >= 2:
        if metapaths:
            for metapath in metapaths:
                edgep = []
                for edge in metapath.edge_list:
                    edgep.append((sorted(edge.invertex), sorted(edge.outvertex)))
                print("{} to {} - {}".format(colored(sorted(list(metapath.source)), "blue"), colored(sorted(list(metapath.target)), "yellow"), colored(sorted(edgep), "red")))
                if glob_verbose >= 3:
                    print("Input-dominant: {}; Edge-dominant: {}".format(cm.is_input_dominant_metapath(metapath), cm.is_edge_dominant_metapath(metapath)))

def print_metapaths(cm, metapaths, glob_verbose=1):
    print("Metapaths: {}".format(len(metapaths)))
    if glob_verbose >= 1:
        if metapaths:
            for metapath in metapaths:
                edgep = []
                for edge in metapath.edge_list:
                    edgep.append((sorted(edge.invertex), sorted(edge.outvertex)))
                print("{} to {} - {}".format(colored(sorted(list(metapath.source)), "blue"), colored(sorted(list(metapath.target)), "yellow"), colored(sorted(edgep), "red")))
                if glob_verbose >= 3:
                    print("Input-dominant: {}; Edge-dominant: {}".format(cm.is_input_dominant_metapath(metapath), cm.is_edge_dominant_metapath(metapath)))

def print_mg(mg):
    print("Variables set: {}".format(colored(list(mg.variables_set), "blue")))
    print("Propositions set: {}".format(colored(list(mg.propositions_set), "yellow")))
    print("Generating set: {}".format(colored(list(mg.generating_set), "green")))
    print("Edge set: {}".format(colored(mg.edges, "red")))

def print_net_redundancies(variables, propositions, edges):
    print("Redundant variables: {}".format(colored(list(variables), "blue")))
    print("Redundant propositions: {}".format(colored(list(propositions), "yellow")))
    print("Redundant edges: {}".format(colored(edges, "red")))


# Check if an edge is in a list of edges
def edge_in_list(edge, edges):
    if not edges: # Empty list
        return False
    for edge_from_list in edges:
        if edge.invertex == edge_from_list.invertex and edge.outvertex == edge_from_list.outvertex:
            return True
    return False

# Add metapath to list of metapaths if its not in it
def add_metapath(metapath, metapaths):
    metapath_in_list = False
    for mp in metapaths:
        if metapaths_equal(mp, metapath):
            metapath_in_list = True
            break
    if not metapath_in_list:
        metapaths.append(metapath)
        return metapaths
    else:
        #print("--- METAPATH ALREADY IN LIST ---")
        return metapaths

# Check if two metapaths are equal
def metapaths_equal(m1, m2):
    #TODO Verify edge comp is good by trying the fct with metapaths with same source and target but different edge lists with same number of edges
    return m1.source == m2.source and m1.target == m2.target and set(m1.edge_list) == set(m2.edge_list)

# Check if lists of metapaths are equal
def lists_equal(list):
    ms = list[0]
    for metapaths in list:
        for m, metapath in zip(ms, metapaths):
            if not metapaths_equal(m, metapath):
                return False
    return True


# Find metapaths which contain affected edges
def affected_metapaths_dominance_recalculation(metapaths, affected_edges):
    affected_metapaths = []
    for metapath in metapaths:
        if set(metapath.edge_list).intersection(affected_edges):
            affected_metapaths.append(metapath)

    return affected_metapaths


# Call find_all_metapaths(mg, B, set(), [], []) to populate the set of metapaths from B.
def find_all_metapaths(mg, B, covering=set(), edges_taken=[], glob_verbose=0):
    all_metapaths = []

    if glob_verbose >= 1:
        print("\nCalled with params:")
        print("B: {}".format(B))
        print("covering: {}".format(covering))
        print("edges_taken: {}".format(edges_taken))
        print("all_metapaths_before: {}".format(all_metapaths))
    if covering: # and "49" in covering:
        add_metapath(Metapath(B, covering, edges_taken), all_metapaths)
    if glob_verbose >= 1:
        print("all_metapaths_after: {}\n".format(all_metapaths))

    # Compute valid edges
    valid_edges = set()
    edges_not_taken = set()
    for edge in mg.edges:
        if not edge_in_list(edge, edges_taken):
            edges_not_taken.add(edge)
    if glob_verbose >= 1:
        print("edges_not_taken: {}".format(edges_not_taken))
    for edge in edges_not_taken:
        if covering.union(B).issuperset(edge.invertex):
            valid_edges.add(edge)
    if glob_verbose >= 1:
        print("valid_edges: {}".format(valid_edges))

    # Compute next edges from valid edges (recursive)
    for edge in valid_edges:
        new_covering = covering.union(edge.outvertex)
        new_edges_taken = list(edges_taken)
        new_edges_taken.append(edge)

        new_metapaths = find_all_metapaths(mg, B, new_covering, new_edges_taken)
        for metapath in new_metapaths:
            add_metapath(metapath, all_metapaths)

    return all_metapaths


# Call find_all_metapaths(mg, B, set(), []) to populate the set of metapaths from B.
def find_all_metapaths_from(mg, B, C, covering=set(), edges_taken=[], glob_verbose=0):
    all_metapaths = []

    if glob_verbose >= 1:
        print("\nCalled with params:")
        print("B: {}".format(B))
        print("covering: {}".format(covering))
        print("edges_taken: {}".format(edges_taken))
    if glob_verbose >= 2:
        print("all_metapaths_before: {}".format(all_metapaths))
    if covering and C in covering:
        all_metapaths.append(Metapath(B, C, edges_taken)) # .add(B, C, edges)
    if glob_verbose >= 2:
        print("all_metapaths_after: {}\n".format(all_metapaths))

    valid_edges = set()
    edges_not_taken = set()
    for edge in mg.edges:
        if not edge_in_list(edge, edges_taken):
            edges_not_taken.add(edge)
    if glob_verbose >= 1:
        print("edges_not_taken: {}".format(edges_not_taken))
    for edge in edges_not_taken:
        if covering.union(B).issuperset(edge.invertex):
            valid_edges.add(edge)
    if glob_verbose >= 1:
        print("valid_edges: {}".format(valid_edges))

    for edge in valid_edges:
        new_covering = covering.union(edge.outvertex)
        new_edges_taken = list(edges_taken)
        new_edges_taken.append(edge)

        new_metapaths = find_all_metapaths_from(mg, B, C, new_covering, new_edges_taken)
        for metapath in new_metapaths:
            all_metapaths.append(metapath)

    return all_metapaths



def break_method(metagraph, B, C):
    print("Source: {}; Target: {}".format(B, C))
    dominant_edges = []
    redundant_edges = []

    for edge in metagraph.edges:
        print("\nTesting edge {}".format(edge))

        B_to_invertex = False
        outvertex_to_C = False

        print(B, edge.invertex, edge.outvertex, C)
        if B.intersection(edge.invertex) == B:
            B_to_invertex = True
        elif len(find_a_metapath_from(metagraph, B, edge.invertex)) > 0:
            B_to_invertex = True

        if C.intersection(edge.outvertex) == C:
            outvertex_to_C = True
        elif len(find_a_metapath_from(metagraph, edge.outvertex, C)) > 0:
            outvertex_to_C = True


        if B_to_invertex and outvertex_to_C: # There is a dominant metapath from B to C using this edge
            dominant_edges.append(edge)
        else:
            redundant_edges.append(edge)

    return dominant_edges, redundant_edges


# Call find_all_metapaths(mg, B, set(), []) to populate the set of metapaths from B.
def find_a_metapath_from(mg, B, C, covering=set(), edges_taken=[], glob_verbose=0):
    all_metapaths = []

    if glob_verbose >= 1:
        print("\nCalled with params:")
        print("B: {}".format(B))
        print("C: {}".format(C))
        print("covering: {}".format(covering))
        print("edges_taken: {}".format(edges_taken))
    if glob_verbose >= 2:
        print("all_metapaths_before: {}".format(all_metapaths))
    if covering and C.issubset(covering):
        all_metapaths.append(Metapath(B, C, edges_taken)) # .add(B, C, edges)
        return all_metapaths
    if glob_verbose >= 2:
        print("all_metapaths_after: {}\n".format(all_metapaths))

    valid_edges = set()
    edges_not_taken = set()
    for edge in mg.edges:
        if not edge_in_list(edge, edges_taken):
            edges_not_taken.add(edge)
    if glob_verbose >= 1:
        print("edges_not_taken: {}".format(edges_not_taken))
    for edge in edges_not_taken:
        if covering.union(B).issuperset(edge.invertex):
            valid_edges.add(edge)
    if glob_verbose >= 1:
        print("valid_edges: {}".format(valid_edges))

    for edge in valid_edges:
        new_covering = covering.union(edge.outvertex)
        new_edges_taken = list(edges_taken)
        new_edges_taken.append(edge)

        new_metapaths = find_a_metapath_from(mg, B, C, new_covering, new_edges_taken)
        all_metapaths += new_metapaths

        if len(all_metapaths) > 0:
            return all_metapaths

    return all_metapaths



def breadth_first_search(metagraph, source):
    # Mark all the vertices as not visited
    visited = [False] * (max(self.graph) + 1)

    # Create a queue for BFS
    queue = []

    # Mark the source node as
    # visited and enqueue it
    queue.append(source)
    visited[source] = True

    while queue:
        # Dequeue a vertex from
        # queue and print it
        s = queue.pop(0)
        print(s, end = " ")

        # Get all adjacent vertices of the
        # dequeued vertex s. If a adjacent
        # has not been visited, then mark it
        # visited and enqueue it
        for i in self.graph[s]:
            if visited[i] == False:
                queue.append(i)
                visited[i] = True


def tarjan_scc(metagraph):
    nodes = list(metagraph_nodes(metagraph)) # Nodes in graph
    n = len(nodes) # Number of nodes in graph
    g = metagraph_adjacency_list(metagraph) # Adjacency list with directed edges

    stack = [] # Stack for dfs

    unvisited = -1 # Mark nodes unvisited
    id = 0 # Used to give each node an id
    scc_count = 0 # Used to count the number of SCCs

    # Index i represents node i
    ids = [unvisited] * n
    low = [0] * n
    on_stack = [False] * n

    for idx, node in enumerate(nodes):
        if ids[idx] == unvisited:
            g, stack, unvisited, id, scc_count, ids, low, on_stack = dfs_tarjan(nodes[idx], idx, nodes, g, stack, unvisited, id, scc_count, ids, low, on_stack)

    return (nodes, low)


# Find id of node in list of nodes (frozensets)
def find_id(nodes, target_node):
    for idx, node in enumerate(nodes):
        if node == target_node:
            return idx
    return -1

def dfs_tarjan(at, at_id, nodes, g, stack, unvisited, id, scc_count, ids, low, on_stack):
    print('Called with:')
    print("Stack: {}".format(stack))
    print("ids: {}".format(ids))
    print("low: {}".format(low))
    print("on_stack: {}".format(on_stack))
    print("id: {}".format(id))
    print()
    #print(at, at_id, stack, unvisited, id, scc_count, ids, low, on_stack)

    stack.append(at_id)
    on_stack[at_id] = True
    low[at_id] = id
    ids[at_id] = id
    id += 1

    # Visit all neighbours & min low-link on callback
    if frozenset(at) in g.keys():
        for next_node in g[frozenset(at)]:
            next_node_id = find_id(nodes, next_node)
            if ids[next_node_id] == unvisited:
                g, stack, unvisited, id, scc_count, ids, low, on_stack = dfs_tarjan(next_node, next_node_id, nodes, g, stack, unvisited, id, scc_count, ids, low, on_stack)
            if on_stack[next_node_id]:
                low[at_id] = min(low[at_id], low[next_node_id])

    # After having visited all the neighbours of 'at'
    # if we're at the start of a SCC empty the seen
    # stack until we're back to the start of the SCC.
    if ids[at_id] == low[at_id]:
        for idx in range(len(stack)):
            node_id = stack.pop()
            on_stack[node_id] = False
            low[node_id] = ids[at_id]
            if nodes[node_id] == at:
                break
        scc_count += 1

    return (g, stack, unvisited, id, scc_count, ids, low, on_stack)



def edges_order(metagraph, source, mode="bfs"):
    print("Mode = {}".format(mode))
    nodes = list(metagraph_nodes(metagraph)) # Nodes in graph
    n = len(nodes) # Number of nodes in graph
    g = metagraph_adjacency_list(metagraph) # Adjacency list with directed edges

    # Put node containing source at the start of nodes list, to begin dfs
    for idx, node in enumerate(nodes):
        print(idx, node, source)
        if source.issubset(node):
            print("Node found at idx {}".format(idx))
            temp = nodes[0]
            nodes[0] = source
            nodes[idx] = temp
            break


    stack = [] # Stack for dfs

    unvisited = -1 # Mark nodes unvisited
    id = 0 # Used to give each node an id

    # Index i represents node i
    ids = [unvisited] * n
    on_stack = [False] * n

    edges_by_order = [] # Edges sorted by visit in dfs

    for idx, node in enumerate(nodes):
        if ids[idx] == unvisited:
            if mode == "dfs":
                g, unvisited, id, ids, sorted_edges = dfs(nodes[idx], idx, nodes, g, unvisited, id, ids)
            else:
                g, unvisited, id, ids, sorted_edges = bfs(nodes[idx], idx, nodes, g, unvisited, id, ids, stack, on_stack)
            edges_by_order += sorted_edges

    return edges_by_order

def dfs(at, at_id, nodes, g, unvisited, id, ids):
    print('Called with:')
    print("ids: {}".format(ids))
    print("id: {}".format(id))
    print()

    ids[at_id] = id
    id += 1

    sorted_edges_l = [] # Edges sorted by visit in dfs

    # Visit all neighbours & min low-link on callback
    if frozenset(at) in g.keys():
        for next_node in g[frozenset(at)]:
            # Add edge to sorted edges list
            sorted_edges_l.append(Edge(set(at), next_node))

            next_node_id = find_id(nodes, next_node)
            if ids[next_node_id] == unvisited:
                g, unvisited, id, ids, sorted_edges = dfs(next_node, next_node_id, nodes, g, unvisited, id, ids)
                sorted_edges_l += sorted_edges

    return (g, unvisited, id, ids, sorted_edges_l)


def bfs(at, at_id, nodes, g, unvisited, id, ids, stack, on_stack):
    print('Called with:')
    print("ids: {}".format(ids))
    print("id: {}".format(id))
    print()

    ids[at_id] = id
    id += 1

    sorted_edges_l = [] # Edges sorted by visit in dfs

    # Visit all neighbours & min low-link on callback
    if frozenset(at) in g.keys():
        for next_node in g[frozenset(at)]:
            # Add edge to sorted edges list
            sorted_edges_l.append(Edge(set(at), next_node))

            next_node_id = find_id(nodes, next_node)
            if ids[next_node_id] == unvisited:
                stack.append((next_node, next_node_id))

    for idx in range(len(stack)):
        node, node_id = stack.pop()
        on_stack[node_id] = False
        g, unvisited, id, ids, sorted_edges = dfs(node, node_id, nodes, g, unvisited, id, ids)
        sorted_edges_l += sorted_edges


    return (g, unvisited, id, ids, sorted_edges_l)



def dijkstra(metagraph, source):
    dist = [-1] * metagraph_node_count(metagraph)


def find_all_metapaths_from_edges(metagraph, edges, source, target):
    starting_set = {}


def bit_array_to_edges(edges, bit_array):
    edges_from_bit_array = []
    indices = bit_array.search(1)
    for index in indices:
        edges_from_bit_array.append(edges[index])
    return edges_from_bit_array


def edges_to_bit_array(edges, input_edges):
    edges_bit_array = bitarray(len(edges))
    edges_bit_array.setall(0)
    for input_edge in input_edges:
        for index, edge in enumerate(edges):
            if input_edge == edge:
                edges_bit_array[index] = 1
                break
    return frozenbitarray(edges_bit_array)


# Construct one level of the Hasse diagram
def hasse_construct_next_level(metagraph, source, target, edges, hasse_diagram, level, previous_level_sets, glob_verbose=0):
    print("\n-- LEVEL {} --".format(level))

    dominant_metapaths = []
    new_previous_level_sets = []

    if level == 1:
        for edge in edges: # First iteration, edges_set is only one edge
            mp = Metapath(source, target, [edge])
            if glob_verbose >= 1:
                print(mp)
            if metagraph.is_dominant_metapath(mp):
                dominant_metapaths.append(mp)
            else:
                new_previous_level_sets.append([edge])
            hasse_diagram[edges_to_bit_array(edges, [edge])] = []
        if glob_verbose >= 2:
            pprint(hasse_diagram)
            print()
    else:
        if glob_verbose >= 2:
            print(previous_level_sets)

        # Prendre sets deux a deux et combiner en nouveau set.
        # Uniquement fait partie du niveau suivant si bon nombre d'elements dans le combined set
        for idx1, edges_set_1 in enumerate(previous_level_sets):
            for idx2, edges_set_2 in enumerate(previous_level_sets):
                if glob_verbose >= 2:
                    print(edges_set_1, edges_set_2)
                if idx1 < idx2: # Do not redo combinations
                    edges_set_1_bit_array = edges_to_bit_array(edges, edges_set_1)
                    edges_set_2_bit_array = edges_to_bit_array(edges, edges_set_2)
                    combined_edges_set_bit_array = edges_set_1_bit_array | edges_set_2_bit_array
                    combined_edges_set = bit_array_to_edges(edges, combined_edges_set_bit_array)
                    if glob_verbose >= 2:
                        print(edges_set_1_bit_array, edges_set_2_bit_array, combined_edges_set_bit_array)
                        print(combined_edges_set)

                    if edges_to_bit_array(edges, combined_edges_set) not in hasse_diagram.keys() and len(combined_edges_set) == level:
                        mp = Metapath(source, target, combined_edges_set)
                        if glob_verbose >= 1:
                            print(mp)
                        if metagraph.is_dominant_metapath(mp):
                            dominant_metapaths.append(mp)
                        else:
                            new_previous_level_sets.append(combined_edges_set)
                        hasse_diagram[edges_set_1_bit_array].append(combined_edges_set_bit_array)
                        hasse_diagram[edges_set_2_bit_array].append(combined_edges_set_bit_array)
                        hasse_diagram[combined_edges_set_bit_array] = []
        if glob_verbose >= 2:
            pprint(hasse_diagram)
            print()

    if glob_verbose >= 2:
        print(new_previous_level_sets)
    return dominant_metapaths, hasse_diagram, new_previous_level_sets

# Constructs hasse diagram by combining elements of each level two by two to construct next level
def hasse(metagraph, source, target, edges=None):
    if edges is None:
        edges = metagraph.edges

    dominant_metapaths = [] # Dominant metapaths found
    hasse_diagram = {} # Adjacency list of hasse diagram

    edges_bit_array_size = len(edges) # Size of bit vector
    #edges_bit_array = bitarray(edges_bit_array_size) # Bit vector representing edges in set
    #edges_bit_array.setall(0)
    previous_level_sets = []

    #edges_bit_array_size = 2

    # Construct Hasse adjacency_list
    for level in range(1, edges_bit_array_size + 1):
        dominant_metapaths_of_level, hasse_diagram_of_level, previous_level_sets = hasse_construct_next_level(metagraph, source, target, edges, hasse_diagram, level, previous_level_sets)
        dominant_metapaths += dominant_metapaths_of_level # Add new metapaths
        hasse_diagram = hasse_diagram_of_level

    return dominant_metapaths


def edge_set_tree_construct_next_level(metagraph, source, target, edges, level, dominant_metapaths_bit_arrays, previous_level_sets, glob_verbose=0):
    print("\n-- LEVEL {} --".format(level))

    dominant_metapaths = []
    new_previous_level_sets = []
    level_bit_mask = bitarray(len(edges))
    level_bit_mask.setall(0)

    if level == 1:
        for edge in edges: # First iteration, set is only one edge
            mp = Metapath(source, target, [edge])
            if glob_verbose >= 2:
                print(mp)
            if metagraph.is_dominant_metapath(mp):
                dominant_metapaths.append(mp)
                dominant_metapaths_bit_arrays.append(edges_to_bit_array(edges, [edge]))
            else:
                new_previous_level_sets.append(edges_to_bit_array(edges, [edge]))
    else:
        new_edges_bit_arrays = []
        if glob_verbose >= 1:
            print("previous_level_sets: {}".format(previous_level_sets))
        for edges_bit_array in previous_level_sets:
            # Set bit mask
            index = util.rindex(edges_bit_array)
            level_bit_mask[0:index] = True
            level_bit_mask[index:] = False
            if glob_verbose >= 1:
                print(colored("SET bit mask", "green"))
                print("IDX: {}".format(index))
                print(colored("level_bit_mask: {}".format(level_bit_mask), "green"))

            # remove indices of elements in bit mask
            masked_bit_array = edges_bit_array | level_bit_mask
            if glob_verbose >= 1:
                print("edges_bit_array: {}".format(edges_bit_array))
                print("level_bit_mask: {}".format(level_bit_mask))
                print("masked_bit_array : {}".format(masked_bit_array))

            indices = masked_bit_array.search(0)

            for index in indices:
                new_edges_bit_array = bitarray(edges_bit_array)
                new_edges_bit_array[index] = True
                new_edges_bit_array = frozenbitarray(new_edges_bit_array)
                if glob_verbose >= 1:
                    print("new_edges_bit_array: {}".format(colored(new_edges_bit_array, "red")))

                mp = Metapath(source, target, bit_array_to_edges(edges, new_edges_bit_array))
                if glob_verbose >= 2:
                    print(mp)
                if metagraph.is_dominant_metapath(mp):
                    if glob_verbose >= 1:
                        print("DOMINANT: removing {}".format(colored(new_edges_bit_array, "yellow")))
                    dominant_metapaths.append(mp)
                    dominant_metapaths_bit_arrays.append(new_edges_bit_array)
                else:
                    new_previous_level_sets.append(new_edges_bit_array)

                new_edges_bit_arrays.append(new_edges_bit_array)

    if glob_verbose >= 2:
        print("new_previous_level_sets: {}".format(new_previous_level_sets))
    return dominant_metapaths, dominant_metapaths_bit_arrays, new_previous_level_sets

# Constructs a prefix tree for edge sets
def edge_set_tree(metagraph, source, target, edges=None):
    if edges is None:
        edges = metagraph.edges

    dominant_metapaths = [] # Dominant metapaths found
    dominant_metapaths_bit_arrays = []
    edges_bit_array_size = len(edges) # Size of bit vector
    previous_level_sets = []

    for level in range(1, edges_bit_array_size + 1):
        dominant_metapaths_of_level, dominant_metapaths_bit_arrays, previous_level_sets = edge_set_tree_construct_next_level(metagraph, source, target, edges, level, dominant_metapaths_bit_arrays, previous_level_sets)
        dominant_metapaths += dominant_metapaths_of_level # Add new metapaths

    return dominant_metapaths


def pascal_triangle_construct_level(metagraph, source, target, current_edges, level, dominant_metapaths_bit_arrays, previous_level_sets, glob_verbose=0):
    print("\n-- LEVEL {} --".format(level))
    if glob_verbose >= 1:
        print("previous_level_sets: {}".format(previous_level_sets))
        print("current_edges: {}".format(current_edges))

    dominant_metapaths = [] # Dominant metapaths found
    check_dominants = False

    level_sets = [] # List containing sets for each element of the level of Pascal's triangle.
    if level == 1:
        # Construct sets corresponding to the first level of Pascal's triangle
        empty_bit_array = bitarray(1)
        empty_bit_array.setall(0)
        level_sets = [[empty_bit_array]]

        full_bit_array = bitarray(1)
        full_bit_array.setall(1)

        mp = Metapath(source, target, bit_array_to_edges(current_edges, full_bit_array))
        if glob_verbose >= 1:
            print(mp)
        if metagraph.is_dominant_metapath(mp):
            dominant_metapaths.append(mp)
            dominant_metapaths_bit_arrays.append(full_bit_array)
            if glob_verbose >= 1:
                print("full_bit_array: {}".format(colored(full_bit_array, "green")))
            level_sets.append([])
        else:
            level_sets.append([full_bit_array])

    else: # Construct sets corresponding to the nth level of Pascal's triangle

        # Append the 1 on the left of Pascal's triangle
        empty_bit_array = bitarray(len(current_edges))
        empty_bit_array.setall(0)
        if glob_verbose >= 1:
            print("empty_bit_array: {}".format(colored(empty_bit_array, "red")))
        level_sets.append([empty_bit_array])

        # Iterate previous level two by two to construct middle of Pascal's triangle
        for left_level_set, right_level_set in zip(previous_level_sets, previous_level_sets[1:]):
            # Compute combination of set: new_edge * left_level_set + right_level_set
            combined_set = list() # Combined set corresponding to one element on this level of Pascal's triangle

            # new_edge * left_level_set
            if glob_verbose >= 1:
                print("left_level_set: {}".format(left_level_set))
            for level_set in left_level_set:
                if glob_verbose >= 1:
                    print("level_set: {}".format(level_set))
                new_level_set = bitarray(level_set)
                new_level_set.append(1) # Add new edge to each level_set
                if glob_verbose >= 1:
                    print("new_level_set: {}".format(colored(new_level_set, "red")))
                    print(current_edges)

                # Check if dominant metapath which is a subset already exists
                dominant_subset_exists = False
                if check_dominants:
                    if glob_verbose >= 1:
                        print(dominant_metapaths_bit_arrays)
                    for dominant_metapaths_bit_array in dominant_metapaths_bit_arrays:
                        if glob_verbose >= 1:
                            print(len(dominant_metapaths_bit_array))
                            print(len(new_level_set))

                        # Extend length of previous bit strings for comparison
                        if len(new_level_set) != len(dominant_metapaths_bit_array):
                            toapp = [0] * (len(new_level_set) - len(dominant_metapaths_bit_array))
                            if glob_verbose >= 1:
                                print(toapp)
                            dominant_metapaths_bit_array.extend(toapp)

                        if new_level_set & dominant_metapaths_bit_array == dominant_metapaths_bit_array:
                            # A dominant metapath which is a subset exists
                            dominant_subset_exists = True


                if not dominant_subset_exists:
                    mp = Metapath(source, target, bit_array_to_edges(current_edges, new_level_set))
                    if glob_verbose >= 1:
                        print(mp)
                    if metagraph.is_dominant_metapath(mp):
                        dominant_metapaths.append(mp)
                        dominant_metapaths_bit_arrays.append(new_level_set)
                        check_dominants = True
                        if glob_verbose >= 1:
                            print("new_level_set: {}".format(colored(new_level_set, "green")))
                    else:
                        combined_set.append(new_level_set)
                    if glob_verbose >= 1:
                        print()


            # + right_level_set
            if glob_verbose >= 1:
                print("right_level_set: {}".format(right_level_set))
            for level_set in right_level_set:
                if glob_verbose >= 1:
                    print("level_set: {}".format(level_set))
                new_level_set = bitarray(level_set)
                new_level_set.append(0) # Extend bit_array to consider new edge
                if glob_verbose >= 1:
                    print("new_level_set: {}\n".format(colored(new_level_set, "red")))

                # No need to check those for dominance, they are not new sets
                combined_set.append(new_level_set)

            level_sets.append(combined_set)

        # Append the 1 on the right of Pascal's triangle
        full_bit_array = bitarray(len(current_edges))
        full_bit_array.setall(1)
        if glob_verbose >= 1:
            print("full_bit_array: {}".format(colored(full_bit_array, "red")))

        mp = Metapath(source, target, bit_array_to_edges(current_edges, full_bit_array))
        if glob_verbose >= 1:
            print(mp)
        if metagraph.is_dominant_metapath(mp):
            dominant_metapaths.append(mp)
            dominant_metapaths_bit_arrays.append(full_bit_array)
            check_dominants = True
            if glob_verbose >= 1:
                print("full_bit_array: {}".format(colored(full_bit_array, "green")))
            level_sets.append([])
        else:
            level_sets.append([full_bit_array])

    return dominant_metapaths, dominant_metapaths_bit_arrays, level_sets

def pascal_triangle(metagraph, source, target, edges=None):
    if edges is None:
        edges = metagraph.edges
    else:
        print("Edges provided.")

    dominant_metapaths = [] # Dominant metapaths found
    dominant_metapaths_bit_arrays = [] # Bit arrays of dominant metapaths

    # Number of edges
    # The number of levels in Pascal triangle is the number of edges + 1  (level 0)
    edges_number = len(edges)
    previous_level_sets = []
    current_edges = []

    for level in range(1, edges_number + 1):
        new_edge = edges[level - 1] # Edge added to construct next level of Pascal's triangle
        current_edges.append(new_edge)
        dominant_metapaths_of_level, dominant_metapaths_bit_arrays, previous_level_sets = pascal_triangle_construct_level(metagraph, source, target, current_edges, level, dominant_metapaths_bit_arrays, previous_level_sets)
        dominant_metapaths += dominant_metapaths_of_level # Add new metapaths

    return dominant_metapaths


# Count the number of nodes in a metagraph
def metagraph_nodes(metagraph):
    nodes = set()
    for edge in metagraph.edges:
        nodes.add(frozenset(edge.invertex))
        nodes.add(frozenset(edge.outvertex))
    print(nodes)
    return nodes


# Create an adjacency list from the metagraph
def metagraph_adjacency_list(metagraph):
    adjacency_list = {}
    for edge in metagraph.edges:
        if frozenset(edge.invertex) in adjacency_list.keys():
            adjacency_list[frozenset(edge.invertex)].append(edge.outvertex)
        else:
            adjacency_list[frozenset(edge.invertex)] = [edge.outvertex]
    pprint(adjacency_list)
    return adjacency_list


###############################################################################
# Main

def main(verbose):
    global glob_verbose
    glob_verbose = verbose

    print_section("Description of task")



if __name__ == '__main__':
    print_section("Getting arguments")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose)

    terminate_app(0)


###############################################################################
