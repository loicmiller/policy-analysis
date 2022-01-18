###############################################################################
# Imports

import sys
import argparse # Argument parser

import random
from mgtoolkit.library import *

import PolicyAnalysisHelper


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

# Function called to make atomic change to metagraph
def atomic_change(mg, atomic_change_type, max_vertex_size, max_new_vars=1, max_remove_vars=1):
    pick = -1
    if atomic_change_type == -1:
        pick = pick_random_atomic_change()
    else:
        pick = atomic_change_type

    if pick == 0: # add_random_edge - return (workflow_metagraph, new_edge)
        return (add_random_edge(mg, max_vertex_size), pick)
    elif pick == 1: # add_random_edge_vars - return (new_mg, new_vars, new_edge)
        return (add_random_edge_vars(mg, max_vertex_size, max_new_vars), pick)
    elif pick == 2: # remove_random_edge - return (new_mg, edge_to_remove, unused_variables, unused_propositions)
        return (remove_random_edge(mg), pick)
    elif pick == 3: # remove_random_edge_vars - return (new_mg, modified_edges, removed_edges, unused_variables, unused_propositions)
        return (remove_random_edge_vars(mg, max_remove_vars), pick)

    terminate_app(1, "atomic_change - no choice picked")

# Pick change at random
def pick_random_atomic_change():
    # 0 - add_random_edge
    # 1 - add_random_edge_vars
    # 2 - remove_random_edge
    # 3 - remove_random_edge_vars
    return random.randrange(0, 4)


# Pick #0
def add_random_edge(mg, max_vertex_size):
    edge_count_before = len(mg.edges)

    new_edge = add_random_edge_helper(mg, max_vertex_size)
    while PolicyAnalysisHelper.edge_in_list(new_edge, mg.edges): # Make sure new edge does not already exist in mg
        new_edge = add_random_edge_helper(mg, max_vertex_size)

    workflow_variables_set = mg.variables_set
    workflow_propositions_set = mg.propositions_set
    workflow_metagraph_edges = mg.edges
    workflow_metagraph_edges.append(new_edge)

    workflow_metagraph = ConditionalMetagraph(workflow_variables_set, workflow_propositions_set)
    workflow_metagraph.add_edges_from(workflow_metagraph_edges)

    return (workflow_metagraph, new_edge)

def add_random_edge_helper(mg, max_vertex_size):
    if max_vertex_size <= 1 or len(mg.variables_set) <= 1:
        invertex = set(random.sample(mg.variables_set, 1))
    else:
        invertex = set(random.sample(mg.variables_set, random.randrange(1, min(len(mg.variables_set), max_vertex_size)))) # Leave at least one element for outvertex

    remaining_elements = mg.variables_set.difference(invertex)
    if len(remaining_elements) > 1:
        if max_vertex_size <= 1:
            outvertex = set(random.sample(remaining_elements, 1))
        else:
            outvertex = set(random.sample(remaining_elements, random.randrange(1, min(len(remaining_elements) + 1, max_vertex_size)))) # Pick from remaining elements
    else: # len(remaining_elements) == 1
        outvertex = remaining_elements

    if not invertex.isdisjoint(outvertex): # Make sure invertex and outvertex are disjoint
        terminate_app(1, "add_random_edge_helper - invertex not disjoint from outvertex")

    # Add random number of propositions to invertex
    random_edge_propositions = random.sample(mg.propositions_set, random.randrange(0, len(mg.propositions_set) + 1))

    return Edge(invertex, outvertex, attributes=random_edge_propositions)


# Pick #1
# TODO Improve this atomic change so that new variables can also appear alone in invertex or outvertex. Right now the random generation cannot generate all possible cases
def add_random_edge_vars(mg, max_vertex_size, max_new_vars=1):
    new_vars = generate_new_vars(max_new_vars) # Generate new variables

    if max_vertex_size <= 1 or len(mg.variables_set) <= 1:
        invertex = set(random.sample(mg.variables_set, 1))
    else:
        invertex = set(random.sample(mg.variables_set, random.randrange(1, min(len(mg.variables_set), max_vertex_size)))) # Leave at least one element for outvertex

    remaining_elements = mg.variables_set.difference(invertex)
    if len(remaining_elements) > 1:
        if max_vertex_size <= 1:
            outvertex = set(random.sample(remaining_elements, 1))
        else:
            outvertex = set(random.sample(remaining_elements, random.randrange(1, min(len(remaining_elements) + 1, max_vertex_size)))) # Pick from remaining elements
    else: # len(remaining_elements) == 1
        outvertex = remaining_elements

    if not invertex.isdisjoint(outvertex): # Make sure invertex and outvertex are disjoint
        terminate_app(1, "add_random_edge_vars - invertex not disjoint from outvertex")

    # Add random number of propositions to invertex
    random_edge_propositions = random.sample(mg.propositions_set, random.randrange(0, len(mg.propositions_set) + 1))


    # Distribute new_vars between invertex and outvertex
    for new_var in new_vars:
        invertex_or_outvertex = random.randrange(0, 2) # Flip coin
        if invertex_or_outvertex:
            invertex.add(new_var)
        else:
            outvertex.add(new_var)


    # Construct new metagraph
    variables_set = set(list(mg.variables_set) + new_vars)
    propositions_set = set(mg.propositions_set)
    edges = list(mg.edges)
    new_edge = Edge(invertex, outvertex, attributes=random_edge_propositions)
    edges.append(new_edge)

    new_mg = ConditionalMetagraph(variables_set, propositions_set)
    new_mg.add_edges_from(edges)

    return (new_mg, new_vars, new_edge)

# Static variable for new_vars counter
def static_vars(**kwargs):
    def decorate(func):
        for k in kwargs:
            setattr(func, k, kwargs[k])
        return func
    return decorate

@static_vars(counter=0)
def generate_new_vars(max_new_vars, glob_verbose=0):
    new_vars_count = random.randrange(1, max_new_vars + 1)
    new_vars = []
    for i in range(generate_new_vars.counter, generate_new_vars.counter + new_vars_count):
        new_vars.append("new_var_{}".format(i))

    generate_new_vars.counter += new_vars_count
    if glob_verbose >= 2:
        print("New counter value: {}".format(generate_new_vars.counter))
    return new_vars


# Pick #2
def remove_random_edge(mg):
    edge_count_before = len(mg.edges)

    if edge_count_before == 0:
        print("remove_random_edge - metagraph already has no edges")
        return mg

    edge_to_remove_index = random.randrange(0, len(mg.edges))
    edge_to_remove = mg.edges[edge_to_remove_index]
    mg.remove_edge(edge_to_remove)

    edge_count_after = len(mg.edges)
    if edge_count_before == edge_count_after:
        print("remove_random_edge - edge_to_remove: {}".format(edge_to_remove))
        terminate_app(1, "remove_random_edge - no edge was removed")

    # Cleanup unused variables
    variables_set = set()
    for variable in mg.variables_set:
        for edge in mg.edges:
            if variable in edge.invertex or variable in edge.outvertex:
                variables_set.add(variable)
                break
    unused_variables = mg.variables_set - variables_set

    # Cleanup unused propositions
    propositions_set = set()
    for proposition in mg.propositions_set:
        for edge in mg.edges:
            if proposition in edge.invertex:
                propositions_set.add(proposition)
                break
    unused_propositions = mg.propositions_set - propositions_set

    # Construct new metagraph
    new_mg = ConditionalMetagraph(variables_set, propositions_set)
    new_mg.add_edges_from(mg.edges)

    return (new_mg, edge_to_remove, unused_variables, unused_propositions)


# Pick #3
def remove_random_edge_vars(mg, max_remove_vars=1):
    vars_to_remove_count = random.randrange(1, max_remove_vars + 1)
    vars_to_remove = set(random.sample(mg.variables_set, vars_to_remove_count))

    # Modify edges that contain any number of variables in vars_to_remove
    new_edges = []
    modified_edges = []
    removed_edges = []
    for edge in mg.edges:
        # Remove vars from invertex
        invertex = edge.invertex
        if invertex.intersection(vars_to_remove):
            invertex = invertex - vars_to_remove
        # Remove vars from outvertex
        outvertex = edge.outvertex
        if outvertex.intersection(vars_to_remove):
            outvertex = outvertex - vars_to_remove

        # Only append new edge if invertex and outvertex not empty w.r.t the variables set
        if len(invertex.intersection(mg.variables_set)) != 0 and len(outvertex.intersection(mg.variables_set)) != 0:
            new_edges.append(Edge(invertex, outvertex, attributes=edge.attributes))
            modified_edges.append(edge)
        else:
            removed_edges.append(edge)

    # Cleanup unused variables
    variables_set = set()
    for variable in mg.variables_set:
        for edge in new_edges:
            if variable in edge.invertex or variable in edge.outvertex:
                variables_set.add(variable)
                break
    unused_variables = mg.variables_set - variables_set

    # Cleanup unused propositions
    propositions_set = set()
    for proposition in mg.propositions_set:
        for edge in new_edges:
            if proposition in edge.invertex:
                propositions_set.add(proposition)
                break
    unused_propositions = mg.propositions_set - propositions_set


    # Check if there are still variables in the variables_set
    if len(variables_set) == 0:
        print("remove_random_edge_vars - variables_set is empty")
        return mg

    # Construct new metagraph
    new_mg = ConditionalMetagraph(variables_set, propositions_set)
    new_mg.add_edges_from(new_edges)

    return (new_mg, modified_edges, removed_edges, unused_variables, unused_propositions)


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
