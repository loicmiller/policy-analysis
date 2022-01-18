###############################################################################
# Imports

import sys
import argparse # Argument parser

from mgtoolkit.library import *
import networkx as nx

from sympy import to_dnf
from sympy.parsing.sympy_parser import parse_expr

import random # Random indices of list

import os


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
    parser = argparse.ArgumentParser(description="Workflow specification to Rego", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("workflow", type=str, metavar="FILE", help="workflow to generate policy from")
    parser.add_argument("-e", "--error-rate", type=float, choices=[Range(0.0, 1.0)], metavar="ERROR_RATE", default=0.0, help="rate of errors in the generated workflow")

    return parser


###############################################################################
# Functions


###############################################################################
# Main

def main(verbose, workflow):
    global glob_verbose
    glob_verbose = verbose

    print("\n\n###############################################################################")
    print("Loading workflow specification from file")
    print("###############################################################################")

    with open(workflow, 'r') as workflow_file:
        workflow_edges = workflow_file.readlines()
        workflow_edges = [(set(src.lstrip('{').rstrip('}').split(', ')), set(dst.lstrip('{').rstrip('}').split(', ')), attributes) for src, dst, attributes in (edge.rstrip().split(';') for edge in workflow_edges)]

    if glob_verbose >= 1:
        print("Edges")
        for edge in workflow_edges:
            print(edge)


    print("\n\n###############################################################################")
    print("Turning workflow graph into metagraph")
    print("###############################################################################")

    workflow_variables_set = set()
    workflow_propositions_set = set()
    workflow_edges_set = []

    # Simplify boolean expressions (Use simpy) https://stackoverflow.com/questions/52416781/how-to-simplify-these-boolean-statements
    for src, dst, attributes in workflow_edges:
        if glob_verbose >= 2:
            print("Edge: {} {} {}".format(src, dst, attributes))

        # Add src and dst to variable set if they are not present yet
        workflow_variables_set.update(src)
        workflow_variables_set.update(dst)


        # Parse policy into expression for simpy
        if attributes:
            edge_policy = parse_expr(attributes)
            if glob_verbose >= 2:
                print("Edge policy: {}".format(edge_policy))

            # Convert policy to Disjunctive Normal Form (DNF)
            # I think we don't want to simplify the expression for the comparison
            # since it is not simplified in the metagraph generated from the policy
            # https://en.wikipedia.org/wiki/Disjunctive_normal_form
            # https://docs.sympy.org/latest/modules/logic.html
            # https://docs.sympy.org/latest/modules/parsing.html
            edge_policy_dnf = to_dnf(edge_policy, simplify=False)
            if glob_verbose >= 2:
                print("DNF: {}".format(edge_policy_dnf))


            # Metagraph nodes
            # Each element in metagraph_nodes is the proposition part of a node in the metagraph
            metagraph_nodes = str(edge_policy_dnf).split("|")
            if glob_verbose >= 2:
                print("Metagraph nodes: {}".format(metagraph_nodes))

            # Policy elements in nodes
            # Each element is a part of the propositions_set
            for node_propositions in metagraph_nodes:
                policy_elements = node_propositions.split('&')
                policy_elements = [policy_element.strip().lstrip('(').rstrip(')') for policy_element in policy_elements] # Remove leading and trailing whitespaces, plus leading and trailing parentheses

                # Add policy_elements to propositions_set
                for index, policy_element in enumerate(policy_elements):
                    # Add ')' back for equalities
                    if 'Eq' in policy_element:
                        policy_element = policy_element + ')'
                        policy_elements[index] = policy_elements[index] + ')'
                    workflow_propositions_set.add(policy_element)
                workflow_edges_set.append(Edge(src, dst, attributes=policy_elements))

                if glob_verbose >= 2:
                    print("Policy elements: {}".format(policy_elements))

            if glob_verbose >= 2:
                print("\n")
        else:
            workflow_edges_set.append(Edge(src, dst, attributes=""))


    if glob_verbose >= 4:
        print("Variables set: {}".format(workflow_variables_set))
        print("Propositions set: {}\n".format(workflow_propositions_set))
        print("Metagraph edges: {}\n".format(workflow_edges_set))

    # Create workflow metagraph
    print("Creating workflow metagraph")
    workflow_metagraph = ConditionalMetagraph(workflow_variables_set, workflow_propositions_set)
    workflow_metagraph.add_edges_from(workflow_edges_set)

    if glob_verbose >= 4:
        print("Policy metagraph\n{}\n".format(repr(workflow_metagraph)))

    if glob_verbose >= 4:
        print("Workflow metagraph edges")
        print("{} {}".format("INVERTEX", "OUTVERTEX"))
        for edge in workflow_metagraph.edges:
            print("{} {}".format(list(edge.invertex), list(edge.outvertex)))

    return workflow_metagraph



if __name__ == '__main__':
    print("\n\n###############################################################################")
    print("Getting arguments")
    print("###############################################################################")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.workflow)

    terminate_app(0)


###############################################################################
