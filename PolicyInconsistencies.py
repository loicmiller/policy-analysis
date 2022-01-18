###############################################################################
# Imports

import sys
import argparse # Argument parser

import itertools
import copy

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

# Original algorithm from the paper
def detect_policy_inconsistencies(pmg, glob_verbose=0):
    r1 = {}
    r2 = {}
    processed = []
    redundancies = []
    conflicts = []

    # Identify edge sets with overlapping vertices
    for edge1 in pmg.edges:
        for edge2 in pmg.edges:
            if edge1 != edge2 and (edge2, edge1) not in processed:
                i1 = edge1.invertex.intersection(edge2.invertex)
                i2 = edge1.outvertex.intersection(edge2.outvertex)
                edge1_propositions = edge1.invertex.intersection(pmg.propositions_set)
                edge2_propositions = edge2.invertex.intersection(pmg.propositions_set)
                i3 = edge1_propositions.intersection(edge2_propositions)

                if len(i1) > 0 and len(i3) > 0:
                    if edge1 not in r1:
                        r1[edge1] = []
                    r1[edge1].append(edge2)
                if len(i2) > 0 and len(i3) > 0:
                    if edge1 not in r2:
                        r2[edge1] = []
                    r2[edge1].append(edge2)

            processed.append((edge1, edge2))

    all_metapaths = []

    if glob_verbose >= 1:
        print("R1")
        pprint(r1)
        print("R2")
        pprint(r2)
        print()

    # Search for feasible metapaths
    for edge1, vertex1 in r1.items():
        # Source = union of invertices
        source = edge1.invertex
        for edge2 in r1[edge1]:
            source = source.union(edge2.invertex)

        # Target = outvertex of edge in r2
        for edge3, vertex3 in r2.items():
            target = edge3.outvertex
            edge1_propositions = edge1.invertex.intersection(pmg.propositions_set)
            edge3_propositions = edge3.invertex.intersection(pmg.propositions_set)
            i4 = edge1_propositions.intersection(edge3_propositions)
            if len(i4) > 0:
                metapaths = pmg.get_all_metapaths_from(source, target)
                for metapath in metapaths:
                    all_metapaths = PolicyAnalysisHelper.add_metapath(metapath, all_metapaths)

                    if pmg.has_redundancies(metapath):
                        redundancies = PolicyAnalysisHelper.add_metapath(metapath, redundancies)
                    if pmg.has_conflicts(metapath):
                        conflicts = PolicyAnalysisHelper.add_metapath(metapath, conflicts)

    return (redundancies, conflicts, all_metapaths, r1, r2)

# Modified matt algorithm to include dominant metapaths listing
def detect_policy_inconsistencies_fixed(pmg, glob_verbose=0):
    r1 = {}
    r2 = {}
    processed = []
    redundancies = []
    conflicts = []
    dominants = []
    all_subsets = []

    # Identify edge sets with overlapping vertices
    for edge1 in pmg.edges:
        for edge2 in pmg.edges:
            if edge1 != edge2 and (edge2, edge1) not in processed:
                i1 = edge1.invertex.intersection(edge2.invertex)
                i2 = edge1.outvertex.intersection(edge2.outvertex)
                edge1_propositions = edge1.invertex.intersection(pmg.propositions_set)
                edge2_propositions = edge2.invertex.intersection(pmg.propositions_set)
                i3 = edge1_propositions.intersection(edge2_propositions)

                if len(i1) > 0 and len(i3) > 0:
                    if edge1 not in r1:
                        r1[edge1] = []
                    r1[edge1].append(edge2)
                if len(i2) > 0 and len(i3) > 0:
                    if edge1 not in r2:
                        r2[edge1] = []
                    r2[edge1].append(edge2)

            processed.append((edge1, edge2))

    all_metapaths = []

    if glob_verbose >= 1:
        print("R1")
        pprint(r1)
        print("R2")
        pprint(r2)
        print()

    # Search for feasible metapaths
    for edge1, vertex1 in r1.items():
        # Source = union of invertices
        source = edge1.invertex
        for edge2 in r1[edge1]:
            source = source.union(edge2.invertex)

        # Target = outvertex of edge in r2
        for edge3, vertex3 in r2.items():
            target = edge3.outvertex
            edge1_propositions = edge1.invertex.intersection(pmg.propositions_set)
            edge3_propositions = edge3.invertex.intersection(pmg.propositions_set)
            i4 = edge1_propositions.intersection(edge3_propositions)
            if len(i4) > 0:
                metapaths = pmg.get_all_metapaths_from(source, target)
                #metapaths = PolicyAnalysisHelper.find_all_metapaths_from(pmg, source, target)
                if metapaths:
                    for metapath in metapaths:
                        all_metapaths = PolicyAnalysisHelper.add_metapath(metapath, all_metapaths)

                        if pmg.has_redundancies(metapath):
                            redundancies = PolicyAnalysisHelper.add_metapath(metapath, redundancies)
                        if pmg.has_conflicts(metapath):
                            conflicts = PolicyAnalysisHelper.add_metapath(metapath, conflicts)
                        if pmg.is_dominant_metapath(metapath):
                            dominants = PolicyAnalysisHelper.add_metapath(metapath, dominants)

    return (redundancies, conflicts, dominants, all_metapaths, all_subsets)

# Modified matt fixed algorithm to compute metapaths on all outvertices in R2
def detect_policy_inconsistencies_plus(pmg, glob_verbose=0):
    r1 = {}
    r2 = {}
    processed = []
    redundancies = []
    conflicts = []
    dominants = []
    all_subsets = []

    # Identify edge sets with overlapping vertices
    for edge1 in pmg.edges:
        for edge2 in pmg.edges:
            if edge1 != edge2 and (edge2, edge1) not in processed:
                i1 = edge1.invertex.intersection(edge2.invertex)
                i2 = edge1.outvertex.intersection(edge2.outvertex)
                edge1_propositions = edge1.invertex.intersection(pmg.propositions_set)
                edge2_propositions = edge2.invertex.intersection(pmg.propositions_set)
                i3 = edge1_propositions.intersection(edge2_propositions)

                if len(i1) > 0 and len(i3) > 0:
                    if edge1 not in r1:
                        r1[edge1] = []
                    r1[edge1].append(edge2)
                if len(i2) > 0 and len(i3) > 0:
                    if edge1 not in r2:
                        r2[edge1] = []
                    r2[edge1].append(edge2)

            processed.append((edge1, edge2))

    all_metapaths = []

    if glob_verbose >= 1:
        print("R1")
        pprint(r1)
        print("R2")
        pprint(r2)
        print()

    # Search for feasible metapaths
    for edge1, vertex1 in r1.items():
        # Source = union of invertices
        source = edge1.invertex
        for edge2 in r1[edge1]:
            source = source.union(edge2.invertex)

        # Target = outvertex of edge in r2
        for edge3, value3 in r2.items():
            targets = [edge3.outvertex]
            for edge4 in value3:
                if edge4.outvertex not in targets:
                    targets.append(edge4.outvertex)
            for target in targets:
                edge1_propositions = edge1.invertex.intersection(pmg.propositions_set)
                edge3_propositions = edge3.invertex.intersection(pmg.propositions_set)
                i4 = edge1_propositions.intersection(edge3_propositions)
                if len(i4) > 0:
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

    return (redundancies, conflicts, dominants, all_metapaths, all_subsets)

# My exhaustive search algorithm
def detect_policy_inconsistencies_full(pmg, glob_verbose=0):
    # Get all subsets of variables set
    if glob_verbose >= 3:
        print("Variable set = {}".format(pmg.variables_set))
    all_subsets = [list(subset) for i in range(0, len(pmg.variables_set) + 1) for subset in itertools.combinations(pmg.variables_set, i)]
    temp = []
    for subset in all_subsets:
        temp.append(sorted(subset))
    all_subsets = sorted(temp)
    if glob_verbose >= 3:
        print("Number of subsets: {}".format(len(all_subsets)))
        print(all_subsets)

    # Remove empty subset and generating_set
    all_subsets.remove([])
    if glob_verbose >= 3:
        print("Number of subsets (removed empty set): {}".format(len(all_subsets)))
    all_subsets.remove(sorted(list(pmg.variables_set)))
    if glob_verbose >= 3:
        print("Number of subsets (removed non-proper subset): {}".format(len(all_subsets)))

    # Find all metapaths and redundancies between all disjoint subsets:
    redundancies = []
    conflicts = []
    dominants = []
    all_metapaths = []
    #source = "2"
    #target = "4"
    for source in all_subsets:
        for target in all_subsets:
            source_set = set(source)
            target_set = set(target)
            if glob_verbose >= 3:
                print("source = {}; target = {};".format(source_set, target_set))
            if source_set.isdisjoint(target_set):
                metapaths = pmg.get_all_metapaths_from(source_set.intersection(pmg.variables_set), target_set, prop_subset=(source_set.intersection(pmg.propositions_set)))
                if metapaths:
                    for metapath in metapaths:
                        all_metapaths = PolicyAnalysisHelper.add_metapath(metapath, all_metapaths)

                        if pmg.has_redundancies(metapath):
                            redundancies = PolicyAnalysisHelper.add_metapath(metapath, redundancies)
                        if pmg.has_conflicts(metapath):
                            conflicts = PolicyAnalysisHelper.add_metapath(metapath, conflicts)
                        if pmg.is_dominant_metapath(metapath):
                            dominants = PolicyAnalysisHelper.add_metapath(metapath, dominants)
                elif glob_verbose >= 4:
                    print("No metapaths found!")
            elif glob_verbose >= 4:
                print("Source and target not disjoint!")


    return (redundancies, conflicts, dominants, all_metapaths, all_subsets)


# Matt+ algorithm but only considering an added edge, saving R1/R2 compute time
def detect_policy_inconsistencies_plus_partial(pmg, added_edge, r1, r2, glob_verbose=0):
    r1_p = copy.deepcopy(r1)
    r2_p = copy.deepcopy(r2)
    processed = []
    redundancies = []
    conflicts = []
    dominants = []
    all_subsets = []

    for edge in pmg.edges:
        if edge != added_edge:
            i1 = edge.invertex.intersection(added_edge.invertex)
            i2 = edge.outvertex.intersection(added_edge.outvertex)
            edge_propositions = edge.invertex.intersection(pmg.propositions_set)
            added_edge_propositions = added_edge.invertex.intersection(pmg.propositions_set)
            i3 = edge_propositions.intersection(added_edge_propositions)

            if len(i1) > 0 and len(i3) > 0:
                if added_edge not in r1_p:
                    r1_p[added_edge] = []
                r1_p[added_edge].append(edge)
            if len(i2) > 0 and len(i3) > 0:
                if added_edge not in r2_p:
                    r2_p[added_edge] = []
                r2_p[added_edge].append(edge)

    all_metapaths = []

    if glob_verbose >= 1:
        print("R1_p")
        pprint(r1_p)
        print("R2_p")
        pprint(r2_p)
        print("")

    # Search for feasible metapaths
    for edge1, vertex1 in r1.items():
        # Source = union of invertices
        source = edge1.invertex
        for edge2 in r1[edge1]:
            source = source.union(edge2.invertex)

        # Target = outvertex of edge in r2
        for edge3, value3 in r2.items():
            targets = [edge3.outvertex]
            for edge4 in value3:
                if edge4.outvertex not in targets:
                    targets.append(edge4.outvertex)
            for target in targets:
                edge1_propositions = edge1.invertex.intersection(pmg.propositions_set)
                edge3_propositions = edge3.invertex.intersection(pmg.propositions_set)
                i4 = edge1_propositions.intersection(edge3_propositions)
                if len(i4) > 0:
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

    return (redundancies, conflicts, dominants, all_metapaths, all_subsets)

# Exhaustive search algorithm but only considering relevant changes when adding an edge and variable
def detect_policy_inconsistencies_partial(pmg, added_edge, added_variable, all_subsets):
    # Get all subsets of variables set
    if glob_verbose >= 3:
        print("Variable set = {}".format(pmg.variables_set))
    source_subsets = []
    for subset in all_subsets:
        source_subset = list(subset)
        source_subset.append(added_variable)
        source_subsets.append(source_subset)
    source_subsets.append([added_variable])

    temp = []
    for subset in source_subsets:
        temp.append(sorted(subset))
    source_subsets = sorted(temp)

    if glob_verbose >= 3:
        print(len(source_subsets))
        print(source_subsets)
        print(len(all_subsets))
        print(all_subsets)

    # Remove empty subset and generating_set. Shouldn't remove any elements
    if [] in source_subsets:
        source_subsets.remove([])
    if glob_verbose >= 3:
        print(len(source_subsets))
    if sorted(list(pmg.variables_set)) in source_subsets:
        source_subsets.remove(sorted(list(pmg.variables_set)))
    if glob_verbose >= 3:
        print(len(source_subsets))

    # Find all metapaths and redundancies between all disjoint subsets:
    redundancies = []
    conflicts = []
    dominants = []
    all_metapaths = []
    for source in source_subsets:
        for target in all_subsets:
            source_set = set(source)
            target_set = set(target)
            if glob_verbose >= 3:
                print("source = {}; target = {};".format(source_set, target_set))
            if source_set.isdisjoint(target_set):
                metapaths = pmg.get_all_metapaths_from(source_set, target_set)
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



# Partial recalculation algorithm
def partial_recalculation(workflow_metagraph):
    # Find metapaths with affected dominance
    recalc_metapaths = []
    if pick == 0: # add_random_edge
        new_edge = response_tuple[1]

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
                    recalc_redundancies = PolicyAnalysisHelper.add_metapath(metapath, recalc_redundancies)
                if workflow_metagraph.has_conflicts(metapath):
                    recalc_conflicts = PolicyAnalysisHelper.add_metapath(metapath, recalc_conflicts)
                if workflow_metagraph.is_dominant_metapath(metapath):
                    recalc_dominants = PolicyAnalysisHelper.add_metapath(metapath, recalc_dominants)

        # 2 - Calculate new metapaths
        redundancies_part, conflicts_part , dominants_part, metapaths_part = detect_policy_inconsistencies_partial_add_random_edge(workflow_metagraph, new_edge, all_subsets)

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
                    recalc_redundancies = PolicyAnalysisHelper.add_metapath(metapath, recalc_redundancies)
                if workflow_metagraph.has_conflicts(metapath):
                    recalc_conflicts = PolicyAnalysisHelper.add_metapath(metapath, recalc_conflicts)
                if workflow_metagraph.is_dominant_metapath(metapath):
                    recalc_dominants = PolicyAnalysisHelper.add_metapath(metapath, recalc_dominants)

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

    #redundancies_part += recalc_redundancies
    #conflicts_part += recalc_conflicts
    #dominants_part += recalc_dominants
    #print("Metapaths to recalculate: {}\n".format(recalc_metapaths))
    return (redundancies_part, conflicts_part , dominants_part, metapaths_part)

# This function detects if the edge's invertex is a proper subset of any invertex of edges of the metagraph
def affected_edges_dominance_recalculation(mg, edge):
    if glob_verbose >= 3:
        print("Looking for impact of edge {}".format(edge))

    affected_edges = []
    for mg_edge in mg.edges:
        if edge.invertex < mg_edge.invertex: # is proper subset
            # Metapaths using this edge must be recalculated
            affected_edges.append(mg_edge)

    if glob_verbose >= 3:
        print("Affected edges: {}".format(affected_edges))

    return affected_edges

# Helper function for partial_recalculation - Pick #0
def detect_policy_inconsistencies_partial_add_random_edge(pmg, added_edge, all_subsets):
    # Find all metapaths and redundancies between all disjoint subsets:
    redundancies = []
    conflicts = []
    dominants = []
    all_metapaths = []
    for source in all_subsets:
        for target in all_subsets:
            source_set = set(source)
            target_set = set(target)
            if glob_verbose >= 3:
                print("source = {}; target = {};".format(source_set, target_set))
            if source_set.isdisjoint(target_set):
                metapaths = pmg.get_all_metapaths_from(source_set, target_set)
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

# Helper function for partial_recalculation - Pick #1
def detect_policy_inconsistencies_partial_add_random_edge_vars(pmg, added_edge, added_variable, all_subsets):
    # TODO Handle multiple variables as list in added_variable instead of single variable
    # TODO source_subset/all_subsets not accurate. new_vars can also end up in outvertex. The current version does not calculate subsets correctly, some are missing.
    # Might need to separe this into two cases? new_vars in invertex == users whereas new_vars in outvertex == resources

    # Get all subsets of variables set
    if glob_verbose >= 3:
        print("Variable set = {}".format(pmg.variables_set))
    source_subsets = []
    for subset in all_subsets:
        source_subset = list(subset)
        source_subset.append(added_variable)
        source_subsets.append(source_subset)
    source_subsets.append([added_variable])

    temp = []
    for subset in source_subsets:
        temp.append(sorted(subset))
    source_subsets = sorted(temp)

    if glob_verbose >= 3:
        print(len(source_subsets))
        print(source_subsets)
        print(len(all_subsets))
        print(all_subsets)

    # Remove empty subset and generating_set. Shouldn't remove any elements
    if [] in source_subsets:
        source_subsets.remove([])
    if glob_verbose >= 3:
        print(len(source_subsets))
    if sorted(list(pmg.variables_set)) in source_subsets:
        source_subsets.remove(sorted(list(pmg.variables_set)))
    if glob_verbose >= 3:
        print(len(source_subsets))

    # Find all metapaths and redundancies between all disjoint subsets:
    redundancies = []
    conflicts = []
    dominants = []
    all_metapaths = []
    for source in source_subsets:
        for target in all_subsets:
            source_set = set(source)
            target_set = set(target)
            if glob_verbose >= 3:
                print("source = {}; target = {};".format(source_set, target_set))
            if source_set.isdisjoint(target_set):
                metapaths = pmg.get_all_metapaths_from(source_set, target_set)
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



# Calculate net redundancy from policy metagraph and list of dominant metapaths
def net_redundancy(pmg, dominants):
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
