###############################################################################
# Imports

import sys
import argparse # Argument parser

import RandomWorkflowSpecGenerator
import RandomYawlSpecGenerator


###############################################################################
# General utility

# Exit the program
def terminate_app(code):
    print("Exiting program...")
    sys.exit(code)


###############################################################################
# Argument parser

def get_parser():
    # Get parser for command line arguments
    parser = argparse.ArgumentParser(description="Random workflow specification generator", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("-n", "--generating-set-sizes", type=str, metavar="GEN_SET_SIZES", default="10", help="size of generating sets for the generated metagraph")
    parser.add_argument("-e", "--edge-probabilities", type=str, metavar="EDGE_PROBS", default="1.0", help="probability of edges in the generated workflow")
    parser.add_argument("-s", "--policy-sizes", type=str, metavar="POLICY_SIZES", default="2", help="size of edge policies in the generated workflow")
    parser.add_argument("-r", "--repeats", type=int, metavar="REPEATS", default="30", help="number of policy specifications to generate per parameter combination")
    parser.add_argument("-y", "--yawl-mode", action="store_true", help="specification is in YAWL")
    parser.add_argument("-m", "--max-vertex-size", type=int, metavar="MAX_VERTEX_SIZE", default=0, help="maximum size of vertices in the generated workflow")
    parser.add_argument("-f", "--edge-ratio", type=float, metavar="EDGE_RATIO", default=1.0, help="ratio of edges to elements of the generating set in the generated workflow")

    return parser


###############################################################################
# Functions


###############################################################################
# Main

def main(verbose, generating_set_sizes, edge_probabilities, policy_sizes, repeats, yawl_mode, max_vertex_size, edge_ratio):
    print("\n\n###############################################################################")
    print("Generating random workflow specifications")
    print("###############################################################################")

    generating_set_sizes = [int(generating_set_size) for generating_set_size in generating_set_sizes.split(',')]
    edge_probabilities = [float(edge_probability) for edge_probability in edge_probabilities.split(',')]
    policy_sizes = [int(policy_size) for policy_size in policy_sizes.split(',')]

    if verbose >= 1:
        print("Generating set sizes: {}".format(generating_set_sizes))
        print("Edge probabilities: {}".format(edge_probabilities))
        print("Policy sizes: {}".format(policy_sizes))

    total_runs = len(generating_set_sizes) * len(edge_probabilities) * len(policy_sizes) * repeats
    print("Total number of runs: {}".format(total_runs))
    run_ctr = 0

    for generating_set_size in generating_set_sizes:
        for edge_probability in edge_probabilities:
            for policy_size in policy_sizes:
                for repeat in range(repeats):
                    run_ctr += 1
                    print("\n\n\nRun {} out of {} (repeat {})".format(run_ctr, total_runs, repeat+1))
                    if yawl_mode:
                        RandomYawlSpecGenerator.main(verbose, generating_set_size, edge_probability, policy_size)
                    else:
                        RandomWorkflowSpecGenerator.main(verbose, False, generating_set_size, edge_probability, policy_size, max_vertex_size, edge_ratio)


if __name__ == '__main__':
    print("\n\n###############################################################################")
    print("Getting arguments")
    print("###############################################################################")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.generating_set_sizes, args.edge_probabilities, args.policy_sizes, args.repeats, args.yawl_mode, args.max_vertex_size, args.edge_ratio)

    terminate_app(0)


###############################################################################
