###############################################################################
# Imports

import sys
import argparse # Argument parser

import os
import re

import PolicyAnalysis


###############################################################################
# General utility

# Exit the program
def terminate_app(code, message=None):
    if message:
        print("Exiting program with code {}: {}.".format(code, message))
    else:
        print("Exiting program with code {}.".format(code))
    sys.exit(code)


###############################################################################
# Argument parser

def get_parser():
    # Get parser for command line arguments
    parser = argparse.ArgumentParser(description="Policy Metagraph Analysis", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("-r", "--repeats", type=int, metavar="REPEATS", default="30", help="number of policy specifications to generate per parameter combination")
    parser.add_argument("--gen-set-filter", type=str, metavar="GEN_SET_FILTER", default=None, help="generating sets to generate Rego for")
    parser.add_argument("--edge-filter", type=str, metavar="EDGE_FILTER", default=None, help="edges to generate Rego for")
    parser.add_argument("--policy-filter", type=str, metavar="POLICY_FILTER", default=None, help="policy sizes to generate Rego for")
    parser.add_argument("--id-filter", type=str, metavar="ID_FILTER", default=None, help="IDs to generate data for")
    parser.add_argument("-o", "--output-file", type=str, metavar="OUTPUT_FILE", default="measures/equivalence.dat", help="path to output file")
    parser.add_argument("-t", "--test", action="store_true", help="Test random atomic changes on movie workflow")

    return parser


###############################################################################
# Functions


###############################################################################
# Main

def main(verbose, repeats, gen_set_filter, edge_filter, policy_filter, id_filter, output_file, test):
    global glob_verbose
    glob_verbose = verbose

    print("\n\n###############################################################################")
    print("Generating Rego policies from random workflow specifications")
    print("###############################################################################")

    if gen_set_filter:
        gen_set_filter = [generating_set_size + "-" for generating_set_size in gen_set_filter.split(',')]
        if verbose >= 2:
            print("Generating set sizes to generate Rego for: {}".format(gen_set_filter))

    if edge_filter:
        edge_filter = [edge for edge in edge_filter.split(',')]
        if verbose >= 2:
            print("Edges to generate Rego for: {}".format(edge_filter))

    if policy_filter:
        policy_filter = [policy for policy in policy_filter.split(',')]
        if verbose >= 2:
            print("Policies to generate Rego for: {}".format(policy_filter))

    spec_dir = "workflow-specs/randomly-generated/"
    print("Spec dir: {}".format(spec_dir))
    workflow_categories = sorted(os.listdir(spec_dir))
    if verbose >= 2:
        print("Workflow categories: {}".format(workflow_categories))

    # Filtering generating set sizes
    if gen_set_filter:
        categories_to_keep = []
        for workflow_category in workflow_categories:
            if workflow_category.startswith(tuple(gen_set_filter)):
                if verbose >= 2:
                    print("Workflow category kept: {}".format(workflow_category))
                categories_to_keep.append(workflow_category)
        workflow_categories = [workflow_category for workflow_category in workflow_categories if workflow_category in categories_to_keep]
    if verbose >= 2:
        print("Workflow categories: {}".format(workflow_categories))

    # Filtering edges
    if edge_filter:
        categories_to_keep = []
        for workflow_category in workflow_categories:
            for filter in edge_filter:
                if "{}-{}-edges".format(filter.split('.')[0], filter.split('.')[1]) in workflow_category:
                    if verbose >= 2:
                        print("Workflow category kept: {}".format(workflow_category))
                    categories_to_keep.append(workflow_category)
        workflow_categories = [workflow_category for workflow_category in workflow_categories if workflow_category in categories_to_keep]
    if verbose >= 2:
        print("Workflow categories: {}".format(workflow_categories))

    # Filtering policy sizes
    if policy_filter:
        categories_to_keep = []
        for workflow_category in workflow_categories:
            for filter in policy_filter:
                if "{}-policy".format(filter) in workflow_category:
                    if verbose >= 2:
                        print("Workflow category kept: {}".format(workflow_category))
                    categories_to_keep.append(workflow_category)
        workflow_categories = [workflow_category for workflow_category in workflow_categories if workflow_category in categories_to_keep]
    print("Workflow categories: {}".format(workflow_categories))

    if id_filter:
        id_filter = [id for id in id_filter.split(',')]
        if verbose >= 2:
            print("IDs to generate Rego for: {}".format(id_filter))

    # Gather all specification filenames for processing
    workflow_specs = []
    for workflow_category in workflow_categories:
        workflow_specs.extend(sorted([spec_dir + workflow_category + "/" + workflow_spec for workflow_spec in os.listdir(spec_dir + workflow_category)]))
    print("Workflow specs: {}".format(len(workflow_specs)))
    if verbose >= 2:
        for workflow_spec in workflow_specs:
            print(workflow_spec)
        print("")

    # Filtering IDs for specification filenames
    if id_filter:
        workflow_specs_to_keep = []
        for workflow_spec in workflow_specs:
            for filter in id_filter:
                if "/{}.dat".format(filter) in workflow_spec:
                    if verbose >= 2:
                        print("Specification kept: {}".format(workflow_spec))
                    workflow_specs_to_keep.append(workflow_spec)
        workflow_specs = [workflow_spec for workflow_spec in workflow_specs if workflow_spec in workflow_specs_to_keep]
    print("Specifications: {}".format(len(workflow_specs)))
    if verbose >= 1:
        for workflow_spec in workflow_specs:
            print("{}".format(workflow_spec))
        print("")


    atomic_change_count = 4
    print("Number of atomic changes: {}".format(atomic_change_count))
    print("Repeats: {}".format(repeats))
    total_runs = len(workflow_specs) * atomic_change_count * repeats
    print("Total number of runs: {}".format(total_runs))
    run_ctr = 0

    # Loop to generate rego from specifications
    for workflow_spec in workflow_specs:
        for atomic_change_type in range(atomic_change_count):
            for repeat in range(repeats):
                run_ctr += 1
                print("\n\n\nRun {} out of {} (repeat {})".format(run_ctr, total_runs, repeat+1))
                print("Processing spec: {}".format(workflow_spec))
                PolicyAnalysis.main(verbose, workflow_spec, atomic_change_type, output_file, test)




if __name__ == '__main__':
    print("\n\n###############################################################################")
    print("Getting arguments")
    print("###############################################################################")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.repeats, args.gen_set_filter, args.edge_filter, args.policy_filter, args.id_filter, args.output_file, args.test)

    terminate_app(0)


###############################################################################
