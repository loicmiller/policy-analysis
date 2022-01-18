###############################################################################
# Imports

import argparse # Argument parser
import logging # DEBUG, INFO, WARNING, ERROR, CRITICAL

import Utility


import os
import re

import SpecImplEquivalence


###############################################################################
# Argument parser

def get_parser():
    # Get parser for command line arguments
    parser = argparse.ArgumentParser(description="Random workflow specification generator", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("-r", "--repeats", type=int, metavar="REPEATS", default="30", help="number of policy specifications to generate per parameter combination")
    parser.add_argument("--gen-set-filter", type=str, metavar="GEN_SET_FILTER", default=None, help="generating sets to generate data for")
    parser.add_argument("--policy-filter", type=str, metavar="POLICY_FILTER", default=None, help="policy sizes to generate data for")
    parser.add_argument("--error-rate-filter", type=str, metavar="ERR_RATE_FILTER", default=None, help="error rates to generate data for")
    parser.add_argument("--id-filter", type=str, metavar="ID_FILTER", default=None, help="IDs to generate data for")
    parser.add_argument("-o", "--output-file", type=str, metavar="OUTPUT_FILE", default="measures/equivalence.dat", help="path to output file")
    parser.add_argument("-c", "--check", action="store_true", help="Check that the comparison returns the right result")
    parser.add_argument("-y", "--yawl-mode", action="store_true", help="specification is in YAWL")

    return parser


###############################################################################
# Functions


###############################################################################
# Main

def main(verbose, repeats, output_file, gen_set_filter, policy_filter, error_rate_filter, id_filter, check, yawl_mode):
    Utility.print_section("Comparing specification metagraphs to implementation metagraphs")

    if gen_set_filter:
        gen_set_filter = [generating_set_size + "-" for generating_set_size in gen_set_filter.split(',')]
        if verbose >= 2:
            print("Generating set sizes to generate data for: {}".format(gen_set_filter))

    if policy_filter:
        policy_filter = [policy for policy in policy_filter.split(',')]
        if verbose >= 2:
            print("Policy sizes to generate metagraph generators for: {}".format(gen_set_filter))

    if error_rate_filter:
        error_rate_filter = [error_rate for error_rate in error_rate_filter.split(',')]
        if verbose >= 2:
            print("Error rates to generate Rego for: {}".format(error_rate_filter))

    if id_filter:
        id_filter = [id for id in id_filter.split(',')]
        if verbose >= 2:
            print("IDs to generate Rego for: {}".format(id_filter))

    if yawl_mode:
        spec_dir = "workflow-specs/randomly-generated-yawl/"
    else:
        spec_dir = "workflow-specs/randomly-generated/"
    print("Spec dir: {}".format(spec_dir))
    spec_categories = sorted(os.listdir(spec_dir))
    if verbose >= 2:
        print("Specification categories: {}".format(spec_categories))

    # Filtering generating set sizes for specification categories
    if gen_set_filter:
        categories_to_keep = []
        for spec_category in spec_categories:
            if spec_category.startswith(tuple(gen_set_filter)):
                if verbose >= 2:
                    print("Spec category kept: {}".format(spec_category))
                categories_to_keep.append(spec_category)
        spec_categories = [spec_category for spec_category in spec_categories if spec_category in categories_to_keep]
    if verbose >= 2:
        print("Spec categories: {}".format(spec_categories))

    # Filtering policy sizes for specification categories
    if policy_filter:
        categories_to_keep = []
        for spec_category in spec_categories:
            for filter in policy_filter:
                if "{}-policy".format(filter) in spec_category:
                    if verbose >= 2:
                        print("Spec category kept: {}".format(spec_category))
                    categories_to_keep.append(spec_category)
        spec_categories = [spec_category for spec_category in spec_categories if spec_category in categories_to_keep]
    print("Spec categories: {}".format(spec_categories))

    # Gather all specification filenames for processing
    specifications = []
    for spec_category in spec_categories:
        specifications.extend([spec_dir + spec_category + "/" + specification for specification in sorted(os.listdir(spec_dir + spec_category))])
    if verbose >= 2:
        print("Specifications: {}".format(specifications))

    # Filtering IDs for specification filenames
    if id_filter:
        specifications_to_keep = []
        for specification in specifications:
            for filter in id_filter:
                if "/{}.dat".format(filter) in specification:
                    if verbose >= 2:
                        print("Specification kept: {}".format(specification))
                    specifications_to_keep.append(specification)
        specifications = [specification for specification in specifications if specification in specifications_to_keep]
    print("Specifications: {}".format(len(specifications)))
    if verbose >= 1:
        for specification in specifications:
            print("{}".format(specification))
        print("")


    if yawl_mode:
        impl_dir = "impl-metagraph-generators/generated-from-random-yawl/"
    else:
        impl_dir = "impl-metagraph-generators/generated-from-random/"
    print("Impl dir: {}".format(impl_dir))
    impl_categories = sorted([impl_category for impl_category in os.listdir(impl_dir) if "__" not in impl_category])
    if verbose >= 2:
        print("Implementation categories: {}".format(impl_categories))

    # Filtering generating set sizes for implementation categories
    if gen_set_filter:
        categories_to_keep = []
        for impl_category in impl_categories:
            if impl_category.startswith(tuple(gen_set_filter)):
                if verbose >= 2:
                    print("Impl category kept: {}".format(impl_category))
                categories_to_keep.append(impl_category)
        impl_categories = [impl_category for impl_category in impl_categories if impl_category in categories_to_keep]
    if verbose >= 2:
        print("Impl categories: {}".format(impl_categories))

    # Filtering policy sizes for implementation categories
    if policy_filter:
        categories_to_keep = []
        for impl_category in impl_categories:
            for filter in policy_filter:
                if "{}-policy".format(filter) in impl_category:
                    if verbose >= 3:
                        print("Impl category kept: {}".format(impl_dir))
                    categories_to_keep.append(impl_category)
        impl_categories = [impl_category for impl_category in impl_categories if impl_category in categories_to_keep]
    if verbose >= 2:
        print("Impl categories: {}".format(impl_categories))

    # Filtering error rates for implementation categories
    if error_rate_filter:
        categories_to_keep = []
        for impl_category in impl_categories:
            for filter in error_rate_filter:
                if "{}-{}-error".format(filter.split('.')[0], filter.split('.')[1]) in impl_category:
                    if verbose >= 3:
                        print("Impl category kept: {}".format(impl_dir))
                    categories_to_keep.append(impl_category)
        impl_categories = [impl_category for impl_category in impl_categories if impl_category in categories_to_keep]
    print("Impl categories: {}".format(impl_categories))

    # Gather all specification filenames for processing
    implementations = []
    for impl_category in impl_categories:
        implementations.extend(sorted([impl_dir + impl_category + "/" + implementation for implementation in os.listdir(impl_dir + impl_category) if "__" not in implementation]))
    if verbose >= 2:
        print("Implementations: {}".format(implementations))

    # Filtering IDs for implementation filenames
    if id_filter:
        implementations_to_keep = []
        for implementation in implementations:
            for filter in id_filter:
                pattern = re.compile("^.*/{}-[0-9]+\.py$".format(filter))
                #if "/{}-.py".format(filter) in implementation:
                if pattern.match(implementation):
                    if verbose >= 2:
                        print("Implementation kept: {}".format(implementation))
                    implementations_to_keep.append(implementation)
        implementations = [implementation for implementation in implementations if implementation in implementations_to_keep]
    print("Implementations: {}".format(len(implementations)))
    if verbose >= 1:
        for implementation in implementations:
            print("{}".format(implementation))
        print("")


    total_runs = len(implementations) * repeats
    print("Total number of runs: {}".format(total_runs))
    run_ctr = 0

    # Loop to generate rego from specifications
    for specification in specifications:
        # specification parameters: workflow-specs/randomly-generated/10-nodes-0-3-edges-1-policy/14.dat
        specification_chunks = specification.split('/')
        spec_parameter_chunks = specification_chunks[-2].split('-')
        spec_node_number = int(spec_parameter_chunks[0])
        spec_edge_prob = float(spec_parameter_chunks[2] + '.' + spec_parameter_chunks[3])
        spec_policy_size = int(spec_parameter_chunks[5])
        spec_uid = specification_chunks[-1].split('.')[0]
        for index, implementation in enumerate(implementations):
            # implementation parameters: impl-metagraph-generators/generated-from-random/20-nodes-0-9-edges-2-policy-0-9-error/14-1.py
            implementation_chunks = implementation.split('/')
            impl_parameter_chunks = implementation_chunks[-2].split('-')
            impl_node_number = int(impl_parameter_chunks[0])
            impl_edge_prob = float(impl_parameter_chunks[2] + '.' + impl_parameter_chunks[3])
            impl_policy_size = int(impl_parameter_chunks[5])
            impl_error_rate = float(impl_parameter_chunks[7] + '.' + impl_parameter_chunks[8])
            impl_uid = implementation_chunks[-1].split('-')[0]
            if spec_node_number == impl_node_number and spec_edge_prob == impl_edge_prob and spec_policy_size == impl_policy_size and spec_uid == impl_uid: # Launch if same parameters
                for repeat in range(repeats):
                    run_ctr += 1
                    print("\n\n\nRun {} out of {} (repeat {})".format(run_ctr, total_runs, repeat+1))
                    print("Processing spec: {}".format(specification))
                    print("Processing impl: {}".format(implementation))
                    SpecImplEquivalence.main(verbose, specification, implementation, output_file, check, yawl_mode)


if __name__ == '__main__':
    Utility.print_section("Getting arguments")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.repeats, args.output_file, args.gen_set_filter, args.policy_filter, args.error_rate_filter, args.id_filter, args.check, args.yawl_mode)

    Utility.terminate_app(0)


###############################################################################
