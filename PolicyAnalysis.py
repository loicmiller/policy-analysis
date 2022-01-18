###############################################################################
# Imports

import sys
import argparse # Argument parser

import cProfile
import pstats
import io
from pprint import pprint

import os
import math
from mgtoolkit.library import *


import PolicyAnalysisHelper
import PolicyInconsistencies
import PolicyInconsistenciesCouple
import AtomicChange

import YawlToMetagraph
import TriplesToMetagraph


###############################################################################
# General utility

# Exit the program
def terminate_app(code, message=None):
    if message:
        print("Exiting program with code {}: {}".format(code, message))
    else:
        print("Exiting program with code {}.".format(code))
    sys.exit(code)

# Print section
def print_section(title):
    print("\n\n###############################################################################")
    print(title)
    print("###############################################################################")


###############################################################################
# Argument parser

def get_parser():
    # Get parser for command line arguments
    parser = argparse.ArgumentParser(description="Policy Metagraph Analysis", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("-w", "--workflow", type=str, metavar="FILE", help="workflow to generate policy from")
    parser.add_argument("-c", "--atomic-change-type", type=int, metavar="ATOMIC_CHANGE_TYPE", default="-1", help="Atomic change to metagraph. '-1' for random")
    parser.add_argument("-o", "--output-file", type=str, metavar="OUTPUT_FILE", default="measures/equivalence.dat", help="path to output file")
    parser.add_argument("-t", "--test", action="store_true", help="Test random atomic changes on movie workflow")
    parser.add_argument("-y", "--yawl-mode", action="store_true", help="specification is in YAWL")

    return parser


###############################################################################
# Functions

# Load workflow from test configuration
def load_workflow_from_test():
    print_section("Creating test metagraph")
    """
    variables_set = {"owner", "vfx"}
    propositions_set = {'Eq(method, POST)'}
    workflow_edges_set = [ Edge({"owner"}, {"vfx"}, attributes=['Eq(method, POST)']), ]
    """
    """
    variables_set = {"owner", "vfx", "color"}
    propositions_set = {'Eq(method, POST)'}
    edges_set = [ Edge({"owner"}, {"vfx"}, attributes=['Eq(method, POST)']),
                        Edge({"vfx"}, {"color"},  attributes=['Eq(method, POST)']),
                        ]
    """

    variables_set = {"owner", "vfx", "hdr", "color", "sound"}
    propositions_set = {'Eq(method, POST)', 'time > 8', 'time < 17'}
    edges_set = [ Edge({"owner"}, {"vfx"}, attributes=['Eq(method, POST)']),
                        Edge({"vfx"}, {"color", "sound"},  attributes=['Eq(method, POST)', 'time < 17', 'time > 8']),
                        Edge({"color"}, {"hdr"},  attributes=['time > 8', 'time < 17']),
                        Edge({"hdr"}, {"owner"},  attributes=['time > 8', 'time < 17'])
                        ]

    """
    variables_set = {"owner", "vfx", "hdr", "color", "sound"}
    propositions_set = set()
    edges_set = [ Edge({"1"}, {"2"}, attributes=[]),
                  Edge({"2", "3"}, {"4"},  attributes=[])
                ]
    """
    """
    variables_set = {"u1", "u2", "create_form", "fill_form", "review_form", "transfer_money", "bypass"}
    propositions_set = {"tenure > 2", "tenure > 2"}
    edges_set = [ Edge({"u1", "u2"}, {"create_form", "fill_form"}, attributes=["tenure > 2"]),
                  Edge({"u1"}, {"create_form", "fill_form"}, attributes=["tenure > 2"]),

                  Edge({"u1", "u2"}, {"review_form"},  attributes=[]),
                  Edge({"u1"}, {"review_form"},  attributes=[]),

                  Edge({"fill_form", "review_form"}, {"transfer_money"},  attributes=[]),
                  Edge({"u1"}, {"bypass"},  attributes=[]),
                  Edge({"bypass"}, {"transfer_money"},  attributes=[])
                ]
    """
    '''
    variables_set = {"owner", "vfx"}
    propositions_set = {'Eq(method, POST)'}
    edges_set = [ Edge({"owner"}, {"vfx"}, attributes=['Eq(method, POST)']),
                        Edge({"vfx"}, {"owner"},  attributes=['Eq(method, POST)']),
                        ]
    '''

    workflow_metagraph = ConditionalMetagraph(variables_set, propositions_set)
    workflow_metagraph.add_edges_from(edges_set)

    return workflow_metagraph


# Profile function
def perf_profile(function, *args):
    output_stream = io.StringIO()
    profiler_status = pstats.Stats(stream=output_stream)
    profiler = cProfile.Profile()
    profiler.enable()

    # Function to profile
    function_results = function(*args)

    profiler.disable()
    profiler_status.add(profiler)

    results = vars(profiler_status)

    if glob_verbose >= 3:
        pprint(results)
    if glob_verbose >= 2:
        stats = pstats.Stats(profiler)
        stats.sort_stats('tottime')
        stats.print_stats()

    stats_keys = results['stats'].keys()
    for stat_key in stats_keys:
        if function.__name__ in stat_key:
            profile_key = stat_key
    profile_time = results['stats'][profile_key][3]
    return (function_results, profile_time)

# Launch and profile algorithm
def conf_and_red_matt(algorithm, *args):
    print_section("Calculating conflicts and redundancies ({})".format(algorithm.__name__))
    results, et = perf_profile(algorithm, *args)
    PolicyAnalysisHelper.dom_print(args[0], redundancies=results[0], conflicts=results[1], metapaths=results[2], glob_verbose=glob_verbose)
    print("Execution time: {}".format(et))
    return results, et

# Launch and profile algorithm
def conf_and_red(algorithm, *args):
    print_section("Calculating conflicts and redundancies ({})".format(algorithm.__name__))
    results, et = perf_profile(algorithm, *args)
    PolicyAnalysisHelper.dom_print(args[0], redundancies=results[0], conflicts=results[1], dominants=results[2], metapaths=results[3], glob_verbose=glob_verbose)
    print("Execution time: {}".format(et))
    return results, et

# Launch and profile algorithm
def find_doms(algorithm, *args):
    print_section("Searching for dominant metapaths ({})".format(algorithm.__name__))
    results, et = perf_profile(algorithm, *args)
    pprint(results)
    print("Execution time: {}".format(et))
    return results, et


# Dump measures to file
def dump_measures(workflow, output_file, atomic_change_type, et_matt, et_fixed, et_full, et_plus):
    print_section("Dumping measures to file")

    workflow_chunks = workflow.split('/') # workflow-specs/randomly-generated/10-set-0-3-edges-1-policy/1.dat
    parameter_chunks = workflow_chunks[-2].split('-')
    variables_count = int(parameter_chunks[0])
    edge_prob = float(parameter_chunks[2] + '.' + parameter_chunks[3])
    policy_size = int(parameter_chunks[5])
    edge_number = len(workflow_metagraph.edges)

    # Create directory
    measures_dir = ''.join(output_file.split('/')[:-1]) + '/'
    if not os.path.exists(measures_dir):
        os.makedirs(measures_dir)

    with open(output_file, 'a+') as output:
        output.write("{};{};{};{};{};{};{};{};{};{}\n".format(workflow, variables_count, edge_prob, policy_size, edge_number, atomic_change_type, et_matt, et_fixed, et_full, et_plus))


# Make atomic changer to test metagraph
def test_change(workflow_metagraph, max_vertex_size):
    print_section("Modifying metagraph")

    print("---BEFORE---")
    print_mg(workflow_metagraph)

    # Add variable and edge
    new_variable = "redundancy"
    new_edge = Edge({"owner", "redundancy"}, {"vfx"}, attributes=['Eq(method, POST)']) # Added edge

    variables_set.add(new_variable)
    new_edges = list(starting_edges)
    new_edges.append(new_edge)

    workflow_metagraph = ConditionalMetagraph(variables_set, propositions_set)
    workflow_metagraph.add_edges_from(new_edges)

    print("\n---AFTER---")
    print_mg(workflow_metagraph)

    return workflow_metagraph

# Make atomic changer to metagraph
def workflow_change(workflow_metagraph, atomic_change_type, max_vertex_size):
    print_section("Modifying metagraph")

    response = AtomicChange.atomic_change(workflow_metagraph, atomic_change_type, max_vertex_size)

    print("Change was #{}".format(response[1]))
    PolicyAnalysisHelper.print_mg(response[0][0])

    return (response[0][0], response)


# Check if numbers and properties of metapaths are consistent
def consistency_tests():
    print_section("Consistency tests")

    if len(redundancies_1) + len(redundancies_part) == len(redundancies_2):
        print("Redundancies length: {}".format(colored("PASS", "green")))
    else:
        print("Redundancies length: {}".format(colored("FAIL", "red")))
    if len(conflicts_1) + len(conflicts_part) == len(conflicts_2):
        print("Conflicts length: {}".format(colored("PASS", "green")))
    else:
        print("Conflicts length: {}".format(colored("FAIL", "red")))
    if len(dominants_1) + len(dominants_part) == len(dominants_2):
        print("Dominants length: {}".format(colored("PASS", "green")))
    else:
        print("Dominants length: {}".format(colored("FAIL", "red")))

# Print execution times of algorithms
def print_results(et_full_couple, et_couple_recalc, et_full_couple_2):
    print_section("Results")
    print("Full execution time (1): {}".format(et_full_couple))
    print("     Recalculation time: {}".format(et_couple_recalc))
    print("Full execution time (2): {}".format(et_full_couple_2))
    print("")


###############################################################################
# Main

def main(verbose, workflow, atomic_change_type, output_file, test, yawl_mode):
    global glob_verbose
    glob_verbose = verbose

    if workflow:
        if yawl_mode:
            workflow_metagraph = YawlToMetagraph.main(verbose, workflow)
        else:
            workflow_metagraph = TriplesToMetagraph.main(verbose, workflow)
    elif test:
        workflow_metagraph = load_workflow_from_test()

    if glob_verbose >= 0:
        PolicyAnalysisHelper.print_mg(workflow_metagraph)


    # Define source and target sets for couple redundancy detection
    source = set(sorted(list(workflow_metagraph.variables_set))[0])
    target = set(sorted(list(workflow_metagraph.variables_set))[-1])
    print("Source: {}, Target: {}".format(source, target))

    '''
    print("\n\n-- Hasse --")
    dominant_metapaths = PolicyAnalysisHelper.hasse(workflow_metagraph, source, target)
    pprint(dominant_metapaths)

    print("\n\n-- Edge set tree --")
    dominant_metapaths = PolicyAnalysisHelper.edge_set_tree(workflow_metagraph, source, target)
    pprint(dominant_metapaths)

    print("\n\n-- Pascal's triangle --")
    dominant_metapaths = PolicyAnalysisHelper.pascal_triangle(workflow_metagraph, source, target)
    pprint(dominant_metapaths)
    '''

    nodes, scc = PolicyAnalysisHelper.tarjan_scc(workflow_metagraph)
    print(nodes)
    print(scc)
    #terminate_app(0)

    edges_by_order = PolicyAnalysisHelper.edges_order(workflow_metagraph, source)
    pprint(edges_by_order)


    a_metapath = PolicyAnalysisHelper.find_a_metapath_from(workflow_metagraph, source, target)
    print("A metapath")
    print(a_metapath)

    dominant_edges, redundant_edges = PolicyAnalysisHelper.break_method(workflow_metagraph, source, target)
    print(dominant_edges)
    print(redundant_edges)

    (results_tri, et_tri) = find_doms(PolicyAnalysisHelper.pascal_triangle, workflow_metagraph, source, target, edges_by_order)
    #(results_prefix, et_prefix) = find_doms(PolicyAnalysisHelper.edge_set_tree, workflow_metagraph, source, target)
    #(results_hasse, et_hasse) = find_doms(PolicyAnalysisHelper.hasse, workflow_metagraph, source, target)

    #print(et_tri, et_prefix)

    terminate_app(0)


    print_section("NEW")
    all_metapaths = PolicyAnalysisHelper.find_all_metapaths(workflow_metagraph, source)
    PolicyAnalysisHelper.print_metapaths(workflow_metagraph, all_metapaths)

    print_section("NEW SOURCE/TARGET")
    all_metapaths = PolicyAnalysisHelper.find_all_metapaths_from(workflow_metagraph, source, target)
    PolicyAnalysisHelper.print_metapaths(workflow_metagraph, all_metapaths)

    #terminate_app(0)

    # results = (redundancies, conflicts, dominants, all_metapaths, all_subsets)
    (results_matt, et_matt) = conf_and_red_matt(PolicyInconsistencies.detect_policy_inconsistencies, workflow_metagraph)
    (results_fixed, et_fixed) = conf_and_red(PolicyInconsistencies.detect_policy_inconsistencies_fixed, workflow_metagraph)
    (results_plus, et_plus) = conf_and_red(PolicyInconsistencies.detect_policy_inconsistencies_plus, workflow_metagraph)
    (results_full, et_full) = conf_and_red(PolicyInconsistencies.detect_policy_inconsistencies_full, workflow_metagraph)

    #PolicyAnalysisHelper.print_metapaths(workflow_metagraph, results_full[-2])

    #PolicyInconsistencies.net_redundancy(workflow_metagraph, results_full[2])

    terminate_app(0)


    (results_full_couple, et_full_couple) = conf_and_red(PolicyInconsistenciesCouple.detect_policy_inconsistencies_full_couple, workflow_metagraph, source, target)

    return 0

    #PolicyInconsistencies.net_redundancy(workflow_metagraph, dominants_full_couple)



    # Making an atomic modification to the metagraph
    max_vertex_size = math.trunc(len(workflow_metagraph.generating_set) / 2) # Max vertex size of new edges
    if test:
        workflow_metagraph = test_change(workflow_metagraph, max_vertex_size)
    else:
        workflow_metagraph, response = workflow_change(workflow_metagraph, atomic_change_type, max_vertex_size)
        response_tuple = response[0]
        pick = response[1]

        workflow_metagraph = response_tuple[0]


    # Partial recalculation (couple)
    (results_couple_recalc, et_couple_recalc) = conf_and_red(PolicyInconsistenciesCouple.partial_recalculation_couple, workflow_metagraph, source, target, response, results_full_couple[3])

    # Partial recalculation
    #(results_recalc, et_recalc) = conf_and_red(PolicyInconsistencies.partial_recalculation, workflow_metagraph)



    # Calculating conflicts and redundancies a second time
    workflow_metagraph = copy.deepcopy(workflow_metagraph)
    (results_full_couple_2, et_full_couple_2) = conf_and_red(PolicyInconsistenciesCouple.detect_policy_inconsistencies_full_couple,  workflow_metagraph, source, target)



    #consistency_tests()
    print_results(et_full_couple, et_couple_recalc, et_full_couple_2)

    return 0


    if workflow:
        dump_measures(workflow, output_file, atomic_change_type, et_matt, et_fixed, et_full_couple, et_plus)




if __name__ == '__main__':
    print_section("Getting arguments")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.workflow, args.atomic_change_type, args.output_file, args.test, args.yawl_mode)

    terminate_app(0)


###############################################################################
