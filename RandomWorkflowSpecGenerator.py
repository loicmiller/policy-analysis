###############################################################################
# Imports

import sys
import argparse # Argument parser

import networkx as nx
import matplotlib.pyplot as plt

import random

from sympy import to_dnf
from sympy.parsing.sympy_parser import parse_expr

import ast # String to dict
from importlib import import_module # Import policy metagraph

from pathlib import Path # Create subfolders if not exists
import os

# Combinatorics
import operator as op
from functools import reduce


###############################################################################
# General utility

# Exit the program
def terminate_app(code):
    print("Exiting program...")
    sys.exit(code)


###############################################################################
# Argument parser

class Range(object):
    def __init__(self, start, end):
        self.start = start
        self.end = end
    def __eq__(self, other):
        return self.start <= other <= self.end

def get_parser():
    # Get parser for command line arguments
    parser = argparse.ArgumentParser(description="Random workflow specification generator", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("-p", "--plot", action="store_true", help="generate plot for this metagraph")
    parser.add_argument("-g", "--generating-set-size", type=int, metavar="GEN_SET_SIZE", default=10, help="size of generating set for the generated workflow")
    parser.add_argument("-e", "--edge-probability", type=float, choices=[Range(0.0, 1.0)], metavar="EDGE_PROB", default=1.0, help="probability of edges in the generated workflow")
    parser.add_argument("-s", "--policy-size", type=int, metavar="POLICY_SIZE", default=0, help="size of edge policies in the generated workflow")
    parser.add_argument("-m", "--max-vertex-size", type=int, metavar="MAX_VERTEX_SIZE", default=2, help="maximum size of vertices in the generated workflow")
    parser.add_argument("-f", "--edge-ratio", type=float, metavar="EDGE_RATIO", default=1.0, help="ratio of edges to elements of the generating set in the generated workflow")

    return parser


###############################################################################
# Functions

# Old graph generator - UNUSED
def generate_workflow_graph(node_number, edge_probability):
    G = nx.gnp_random_graph(node_number, edge_probability, directed=True)

    if glob_verbose >= 2:
        print("Graph nodes: {}".format(G.nodes))
        print("Graph edges: {}\n".format(G.edges))

    nodes = list(G.nodes)
    for src, dst in zip(nodes, nodes[1:]):
        if not G.has_edge(src, dst):
            if glob_verbose >= 2:
                print("Creating edge: {} {}".format(src, dst))
            G.add_edge(src, dst)

    if glob_verbose >= 1:
        print("Clean graph nodes: {}".format(G.nodes))
        print("Clean graph edges: {}\n".format(G.edges))

    return G


# Generates disjoint invertex and outvertex from generating set
def generate_vertices(generating_set, max_vertex_size):
    if max_vertex_size <= 1 or len(generating_set) <= 1:
        invertex = set(random.sample(generating_set, 1))
    else:
        invertex = set(random.sample(generating_set, random.randrange(1, min(len(generating_set) - 1, max_vertex_size)))) # Leave at least one element for outvertex

    remaining_elements = generating_set.difference(invertex)
    if len(remaining_elements) > 1:
        if max_vertex_size <= 1:
            outvertex = set(random.sample(remaining_elements, 1))
        else:
            outvertex = set(random.sample(remaining_elements, random.randrange(1, min(len(remaining_elements) + 1, max_vertex_size)))) # Pick from remaining elements
    else: # len(remaining_elements) == 1
        outvertex = remaining_elements

    if not invertex.isdisjoint(outvertex): # Make sure invertex and outvertex are disjoint
        terminate_app(1)

    return invertex, outvertex


def proposition_combination(propositions, operators):
    # Pick two random attributes
    first_rand = random.randrange(len(propositions))
    second_rand = random.randrange(len(propositions))
    while second_rand == first_rand:
        second_rand = random.randrange(len(propositions))

    first_prop = propositions[first_rand]
    second_prop = propositions[second_rand]

    # Generate expression
    expression = "((" + first_prop + ") " + operators[random.randrange(len(operators))] + " (" + second_prop + "))"

    return expression


def expr_generator(propositions, operators, size):
    if size == 0:
        return ""
    elif size == 1:
        return proposition_combination(propositions, operators)

    return "(" + expr_generator(propositions, operators, size-1)  + " " + operators[random.randrange(len(operators))] + " " + expr_generator(propositions, operators, size-1)  + ")"


###############################################################################
# Main

def main(verbose, plot, generating_set_size, edge_probability, policy_size, max_vertex_size, edge_ratio):
    global glob_verbose
    glob_verbose = verbose

    print("\n\n\n###############################################################################")
    print("Generating workflow metagraph")
    print("###############################################################################")

    print("Number of elements in generating set: {}".format(generating_set_size))
    print("Edge probability: {}".format(edge_probability))

    generating_set = {el for el in range(generating_set_size)}
    print("Generating set: {}".format(generating_set))

    edges_numb = int(abs(generating_set_size * edge_ratio)) # Match ratio of Matthew article

    if glob_verbose >= 1:
        subsets_numb = (2**generating_set_size) # Number of subsets
        proper_subsets_numb = subsets_numb - 2 # Proper subsets with no empty set

        # https://math.stackexchange.com/questions/1223425/total-number-of-unordered-pairs-of-disjoint-subsets-of-s/1223442
        disjoint_subsets_numb_ordered = 3**generating_set_size
        disjoint_subsets_numb_ordered_non_empty = disjoint_subsets_numb_ordered - ((2 * subsets_numb) - 1) # Remove ordered pairs with empty set
        disjoint_subsets_numb_unordered = int((((disjoint_subsets_numb_ordered) - 1) // 2) + 1)
        disjoint_subsets_numb_unordered_non_empty = disjoint_subsets_numb_unordered - subsets_numb # Remove unordered pairs with empty set
        max_edges_numb = generating_set_size * (generating_set_size - 1)

        print("Number of subsets: {}".format(subsets_numb))
        print("Number of proper subsets (no empty set): {}".format(proper_subsets_numb))
        print("Number of pairs of ordered disjoint subsets: {}".format(disjoint_subsets_numb_ordered))
        print("Number of pairs of ordered disjoint subsets (no empty set): {}".format(disjoint_subsets_numb_ordered_non_empty))
        print("Number of pairs of unordered disjoint subsets: {}".format(disjoint_subsets_numb_unordered))
        print("Number of pairs of unordered disjoint subsets (no empty set): {}".format(disjoint_subsets_numb_unordered_non_empty))
        print("Number of possible edges in simple graph: {}".format(max_edges_numb))

    print("Generate {} edges for {} nodes\n".format(edges_numb, generating_set_size))


    # Limit invertex/outvertex size to half of the generating set
    edges = []
    for i in range(edges_numb):
        if random.uniform(0,1) <= edge_probability: # Percent chance
            invertex, outvertex = generate_vertices(generating_set, max_vertex_size) # Generate disjoint invertex and outvertex

            while (invertex, outvertex) in edges: # Can't have edge already in set
                if glob_verbose >= 3:
                    print("{} already in list {}".format((invertex, outvertex), edges))
                invertex, outvertex = generate_vertices(generating_set, max_vertex_size)
            if glob_verbose >= 2:
                print("Invertex: {}".format(invertex))
                print("Outvertex: {}".format(outvertex))
            edges.append((invertex, outvertex))
    if glob_verbose >= 2:
        print("Edge set ({} elements)".format(len(edges)))
        print("Ratio of edges to possible edges vs edge probability: {:.3} --- {}".format((len(edges) / disjoint_subsets_numb_unordered_non_empty), edge_probability))
    if glob_verbose >= 3:
        print("Edges: {}".format(edges))

    # Add simple edges for workflow-like loop, except back to owner
    nodes = list(generating_set)
    for src, dst in zip(nodes, nodes[1:]):
        if ({src}, {dst}) not in edges:
            if glob_verbose >= 2:
                print("Creating edge: {} {}".format(src, dst))
            edges.append(({src}, {dst}))

    if glob_verbose >= 2:
        print("Edge set ({} elements)".format(len(edges)))
        print("Ratio of edges to possible edges vs edge probability: {:.3} --- {}".format((len(edges) / disjoint_subsets_numb_ordered_non_empty), edge_probability))
    if glob_verbose >= 3:
        print("Edges: {}".format(edges))



    print("\nPolicy size: {}".format(policy_size))

    # Adding attributes to graph
    propositions = ["tenure > 10", "time < 8", "time > 17", "is_customer", "is_employee", "is_admin"]
    if glob_verbose >= 1:
        print("Allowed propositions: {}".format(propositions))
    operators = ["&", "|"]
    if glob_verbose >= 1:
        print("Allowed operators: {}".format(operators))

    edges_with_policy = []
    for edge in edges:
        edge_policy = expr_generator(propositions, operators, policy_size)
        if glob_verbose >= 2:
            print("\nEdge policy: {}".format(edge_policy))
        edges_with_policy.append((edge[0], edge[1], edge_policy))
    if glob_verbose >= 2:
        print("\n")

    if glob_verbose >= 1:
        print("Generating set: {}".format(generating_set))
        print("Edges {}".format(edges_with_policy))


    print("\n\n###############################################################################")
    print("Generating workflow specification file")
    print("###############################################################################")

    # Generate output workflow specification name
    random_workflow_dir = "workflow-specs/randomly-generated/" + str(generating_set_size) + "-set-" + str(edge_probability).split('.')[0] + "-" + str(edge_probability).split('.')[-1] + "-edges-" + str(policy_size) + "-policy/"
    Path(random_workflow_dir).mkdir(parents=True, exist_ok=True)

    # Determine file uid
    random_workflow_filenames = os.listdir(random_workflow_dir)
    if not random_workflow_filenames: # Dir empty
        uid = "1"
    else:
        uids = []
        for random_workflow_filename in random_workflow_filenames:
            uids.append(int(random_workflow_filename.split('.')[0]))
        max_uid = max(uids)
        uid = str(max_uid + 1)

    output_spec_name = random_workflow_dir + uid + ".dat"
    print("Output spec file: {}".format(output_spec_name))

    workflow_spec = []
    for edge in edges_with_policy:
        if glob_verbose >= 1:
            print(edge)
        workflow_spec.append("{};{};{}\n".format(edge[0], edge[1], edge[2]))

    # Writing policy to file
    with open(output_spec_name, 'w') as output_spec:
        output_spec.writelines(workflow_spec)


    if plot: # Plot workflow
        print("\n\n###############################################################################")
        print("Plotting workflow graph")
        print("###############################################################################")

        plt.subplot(121)
        nx.draw(G, with_labels=True)

        plt.subplot(122)
        nx.draw(G, pos=nx.circular_layout(G), node_color='r', edge_color='b', with_labels=True)

        plt.show()


if __name__ == '__main__':
    print("\n\n###############################################################################")
    print("Getting arguments")
    print("###############################################################################")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.plot, args.generating_set_size, args.edge_probability, args.policy_size, args.max_vertex_size, args.edge_ratio)

    terminate_app(0)


###############################################################################
