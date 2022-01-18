###############################################################################
# Imports

import argparse # Argument parser
import logging # DEBUG, INFO, WARNING, ERROR, CRITICAL

import Utility

import cProfile
import pstats
import io
from pprint import pprint


###############################################################################
# Argument parser

def get_parser():
    # Get parser for command line arguments
    parser = argparse.ArgumentParser(description="Compare execution times", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")

    parser.add_argument("specification", type=str, metavar="SPEC_FILE", help="workflow specification to use for verification")
    parser.add_argument("-o", "--output-file", type=str, metavar="OUTPUT_FILE", default="measures/equivalence.dat", help="path to output file")
    parser.add_argument("-y", "--yawl-mode", action="store_true", help="specification is in YAWL")

    return parser


###############################################################################
# Functions

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


###############################################################################
# Main

def main(verbose, specification, output_file, yawl_mode, function, *args):
    # Get


    perf_profile(function, *args)

    with open(output_file, 'a+') as output:
        output.write("{};{};{};{};{};{};{};{};{};{};{};{};{}\n".format(specification, implementation, node_number, edge_prob, policy_size, spec_len, rego_lines_of_code, error_rate, edge_number, comp_time, sameness, spec_edges, impl_edges))




if __name__ == '__main__':
    Utility.print_section("Getting arguments")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.specification, args.output_file, args.yawl_mode, args.function, *args.args)

    Utility.terminate_app(0)


###############################################################################
