###############################################################################
# Imports

import sys
import argparse # Argument parser

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

# Exhaustive algorithm but only between a source and a target
def detect_policy_inconsistencies_full_couple(pmg, source, target, glob_verbose=0):
    # Find all metapaths and redundancies between all disjoint subsets:
    redundancies = []
    conflicts = []
    dominants = []
    all_metapaths = []
    all_subsets = []

    if glob_verbose >= 3:
        print("source = {}; target = {};".format(source, target))
    if source.isdisjoint(target):
        metapaths = pmg.get_all_metapaths_from(source, target)
        print("Len mps for {} to {}: {}".format(source, target, len(metapaths)))
        if metapaths:
            for i, metapath in enumerate(metapaths):
                print(i)
                all_metapaths.append(metapath)

    print(len(all_metapaths))
    for i, metapath in enumerate(all_metapaths):
        print(i)
        if pmg.has_redundancies(metapath):
            redundancies.append(metapath)
        if pmg.has_conflicts(metapath):
            conflicts.append(metapath)
        if pmg.is_dominant_metapath(metapath):
            dominants.append(metapath)

    return (redundancies, conflicts, dominants, all_metapaths, all_subsets)



# Partial recalculation algorithm for couple
def partial_recalculation_couple(workflow_metagraph, source, target, response, metapaths):
    pick = response[1]
    response_tuple = response[0]

    redundancies_part = []
    conflicts_part = []
    dominants_part = []
    metapaths_part = []

    # Find metapaths with affected dominance
    recalc_metapaths = []
    if pick == 0: # add_random_edge
        new_edge = response_tuple[1]

        # 1 - Recalculation of dominance
        affected_edges = affected_edges_dominance_recalculation_couple(workflow_metagraph, new_edge, metapaths)
        if affected_edges:
            recalc_metapaths = affected_metapaths_dominance_recalculation_couple(metapaths, affected_edges)
        # Recalculate dominance for previously existing metapaths
        if recalc_metapaths:
            recalc_redundancies = []
            recalc_conflicts = []
            recalc_dominants = []
            for metapath in recalc_metapaths:
                if workflow_metagraph.has_redundancies(metapath):
                    recalc_redundancies = add_metapath(metapath, recalc_redundancies)
                if workflow_metagraph.has_conflicts(metapath):
                    recalc_conflicts = add_metapath(metapath, recalc_conflicts)
                if workflow_metagraph.is_dominant_metapath(metapath):
                    recalc_dominants = add_metapath(metapath, recalc_dominants)

        # 2 - Calculate new metapaths
        redundancies_part, conflicts_part , dominants_part, metapaths_part = detect_policy_inconsistencies_partial_add_random_edge_couple(workflow_metagraph, new_edge, source, target)

    elif pick == 1: # add_random_edge_vars
        new_vars = response_tuple[1]
        new_edge = response_tuple[2]

        # 1 - Recalculation of dominance
        affected_edges = affected_edges_dominance_recalculation(workflow_metagraph, new_edge)
        if affected_edges:
            recalc_metapaths = affected_metapaths_dominance_recalculation(metapaths_1, affected_edges)
        # Recalculate dominance for previously existing metapaths
        if recalc_metapaths:
            recalc_redundancies = []
            recalc_conflicts = []
            recalc_dominants = []
            for metapath in recalc_metapaths:
                if workflow_metagraph.has_redundancies(metapath):
                    recalc_redundancies = add_metapath(metapath, recalc_redundancies)
                if workflow_metagraph.has_conflicts(metapath):
                    recalc_conflicts = add_metapath(metapath, recalc_conflicts)
                if workflow_metagraph.is_dominant_metapath(metapath):
                    recalc_dominants = add_metapath(metapath, recalc_dominants)

        # 2 - Calculate new metapaths
        redundancies_part, conflicts_part , dominants_part, metapaths_part = detect_policy_inconsistencies_partial_add_random_edge_vars(workflow_metagraph, new_edge, new_variable, all_subsets)

    elif pick == 2: # remove_random_edge
        removed_edge = response_tuple[1]
        unused_variables = response_tuple[2]
        unused_propositions = response_tuple[3]

    elif pick == 3: # remove_random_edge_vars
        modified_edges = response_tuple[1]
        removed_edges = response_tuple[2]
        unused_variables = response_tuple[3]
        unused_propositions = response_tuple[4]

    else:
        terminate_app(1, "main - pick has illegal value")

    return (redundancies_part, conflicts_part , dominants_part, metapaths_part)

# Helper function for partial_recalculation_couple - Pick #0
def affected_edges_dominance_recalculation_couple(mg, edge, metapaths, glob_verbose=0):
    if glob_verbose >= 1:
        print("Looking for impact of edge {}".format(edge))

    # Get list of edges from metapaths
    metapath_edges = []
    for metapath in metapaths:
        for mp_edge in metapath.edge_list:
            if not PolicyAnalysisHelper.edge_in_list(mp_edge, metapath_edges):
                metapath_edges.append(mp_edge)


    affected_edges = []
    for mp_edge in metapath_edges:
        if edge.invertex < mp_edge.invertex: # is proper subset
            # Metapaths using this edge must be recalculated
            affected_edges.append(mp_edge)

    if glob_verbose >= 3:
        print("Affected edges: {}".format(affected_edges))

    return affected_edges

# Helper function for partial_recalculation_couple - Pick #0
def affected_metapaths_dominance_recalculation_couple():
    return []

# Helper function for partial_recalculation_couple - Pick #0
def detect_policy_inconsistencies_partial_add_random_edge_couple(pmg, added_edge, source, target, glob_verbose=0):
    # Find all metapaths and redundancies between all disjoint subsets:
    redundancies = []
    conflicts = []
    dominants = []
    all_metapaths = []

    if glob_verbose >= 3:
        print("source = {}; target = {};".format(source, target))
    if source.isdisjoint(target) and len(source.intersection(added_edge.invertex)) != 0:
        print("NO")
        print(source)
        print(added_edge.invertex)
        metapaths = pmg.get_all_metapaths_from(source, target)
        if metapaths:
            for metapath in metapaths:
                all_metapaths = PolicyAnalysisHelper.add_metapath(metapath, all_metapaths)

                if pmg.has_redundancies(metapath):
                    redundancies = PolicyAnalysisHelper.add_metapath(metapath, redundancies)
                if pmg.has_conflicts(metapath):
                    conflicts = PolicyAnalysisHelper.add_metapath(metapath, conflicts)
                if pmg.is_dominant_metapath(metapath):
                    dominants = PolicyAnalysisHelper.add_metapath(metapath, dominants)


    return (redundancies, conflicts, dominants, all_metapaths)



# Calculate net redundancy from policy metagraph, a list of dominant metapaths and a list of source/destination couples
def net_redundancy_from_couples(pmg, couples):
    dominants = []

    for source, target in couples:
        _, _, dominants_couple, _, _ = detect_policy_inconsistencies_full_couple(pmg, source, target)
        for dominant in dominants_couple:
            dominants = add_metapath(dominant, dominants)

    dominants_variables_set = set()
    dominants_propositions_set = set()
    dominants_edges = []
    for dominant in dominants:
        for edge in dominant.edge_list:
            dominants_variables_set.update(edge.invertex.intersection(pmg.variables_set))
            dominants_variables_set.update(edge.outvertex.intersection(pmg.variables_set))
            dominants_propositions_set.update(edge.invertex.intersection(pmg.propositions_set))
            dominants_propositions_set.update(edge.outvertex.intersection(pmg.propositions_set))
            if not edge_in_list(edge, dominants_edges):
                dominants_edges.append(edge)

    net_edges = pmg.edges
    net_variables = pmg.variables_set - dominants_variables_set
    net_propositions = pmg.propositions_set - dominants_propositions_set
    for edge in dominants_edges:
        net_edges.remove(edge)

    if glob_verbose >= 0:
        print_net_redundancies(net_variables, net_propositions, net_edges)

    return (net_variables, net_propositions, net_edges)


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
