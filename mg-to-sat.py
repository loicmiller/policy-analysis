###############################################################################
# Imports

import argparse # Argument parser
import logging # DEBUG, INFO, WARNING, ERROR, CRITICAL

import Utility

import YawlToMetagraph
import TriplesToMetagraph
import PolicyAnalysisHelper

from mgtoolkit.library import *

from ortools.linear_solver import pywraplp

import sympy as sp
from sympy.logic.boolalg import to_cnf


###############################################################################
# Argument parser

def get_parser():
    # Get parser for command line arguments
    parser = argparse.ArgumentParser(description="DESCRIPTION", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("-w", "--workflow", type=str, metavar="FILE", help="workflow to generate policy from")
    parser.add_argument("-y", "--yawl-mode", action="store_true", help="specification is in YAWL")


    return parser


###############################################################################
# Functions

# Load workflow from test configuration
def load_workflow_from_test():
    Utility.print_section("Creating test metagraph")

    variables_set = {"owner", "vfx", "hdr", "color", "sound"}
    propositions_set = {'Eq(method, POST)', 'time > 8', 'time < 17'}
    edges_set = [ Edge({"owner"}, {"vfx"}, attributes=['Eq(method, POST)']),
                        Edge({"vfx"}, {"color", "sound"},  attributes=['Eq(method, POST)', 'time < 17', 'time > 8']),
                        Edge({"color"}, {"hdr"},  attributes=['time > 8', 'time < 17']),
                        Edge({"hdr"}, {"owner"},  attributes=['time > 8', 'time < 17'])
                        ]

    workflow_metagraph = ConditionalMetagraph(variables_set, propositions_set)
    workflow_metagraph.add_edges_from(edges_set)

    return workflow_metagraph


# Creates a file that contains the SAT instantiation of the MG-FE-SPP
def solver_instantiation(workflow, mg, yawl_mode):
    # Generate output file name
    if "manually-generated" in workflow:
        output_sat_name = "generated-sat-from-mg/generated-from-manual/" + workflow.split('.')[0].split('/')[-1] + ".py"
    elif "randomly-generated" in workflow:
        path_chunks = workflow.split("/")
        if yawl_mode:
            generated_sat_dir_path = "generated-sat-from-mg/generated-from-random-yawl/" + path_chunks[-2] + "/"
        else:
            generated_sat_dir_path = "generated-sat-from-mg/generated-from-random/" + path_chunks[-2] + "/"
        if not os.path.exists(generated_sat_dir_path):
            os.makedirs(generated_sat_dir_path)
        print("SAT dir path: {}".format(generated_sat_dir_path))

        output_sat_name = generated_sat_dir_path + path_chunks[-1].split('.')[0] + "-" + uid + ".rego"
    else:
        terminate_app(0) #TODO Handle error
    print("Output SAT file: {}\n".format(output_sat_name))


    # Make tuple list associating names of variables/edges in the metagraph to those in SAT
    variable_name_conversion = []
    for variable in sorted(mg.variables_set):
        print(variable)
        variable_name_conversion.append((variable, "x_{}".format(variable)))
    edge_name_conversion = []
    for idx, edge in enumerate(mg.edges):
        print(edge)
        edge_name_conversion.append((edge, "e_{}".format(idx)))


    # Basic SAT structure
    global sat
    sat = []
    sat.append("from ortools.linear_solver import pywraplp\n\n")
    sat.append("def LinearProgramming():\n")
    sat.append("    # Instantiate a Glop solver.\n")
    sat.append("    solver = pywraplp.Solver.CreateSolver('GLOP')\n\n")

    # For each variable in the generating set, create a logic variable
    sat.append("    # For each variable in the generating set, create a logic variable\n")
    for variable in variable_name_conversion:
        sat.append("    {} = solver.NumVar(0, 1, '{}')\n".format(variable[1], variable[1]))
    sat.append("")

    # For each edge in the edges set, create a logic variable
    for edge in edge_name_conversion:
        sat.append("    {} = solver.NumVar(0, 1, '{}')\n".format(edge[1], edge[1]))
    sat.append("")

    sat.append("    print('Number of variables = {}'.format(solver.NumVariables()))\n\n")


    # Create sympy symbols for logic variables
    variable_symbols = sp.symbols('x_0:{}'.format(len(variable_name_conversion)))
    edge_symbols = sp.symbols('e_0:{}'.format(len(edge_name_conversion)))
    print(variable_symbols)
    print(edge_symbols)


    # For each edge in the edges set, add constraints for variables and edges
    sat.append("    # For each edge in the edges set, add constraints for variables and edges")
    for edge in edge_name_conversion:
        print(edge)

        # Add constraints for variables: invertex => edge
        invertex_variables = edge.invertex
        sat.append("    solver.Add(1-x_{} + e_{} >= 1)".format(invertex_variables, idx))

        # Add constraints for edges: edge => outvertex
        outvertex_variables = edge.outvertex
        sat.append("    solver.Add(1-e_{} + x_{} >= 1)".format(idx, outvertex_variables))

    sat.append("")

    # Add constraints set to True

    # Add constraints for input dominance


    sat.append("    print('Number of constraints = {}'.format(solver.NumConstraints()))\n\n")

    # Minimization function
    edges = []
    for conversion in edge_name_conversion:
        edges.append(conversion[1])
    minimization_string = " + ".join(edges)
    sat.append("    solver.Minimize({})\n\n".format(minimization_string))

    # Solve the system.
    sat.append("    status = solver.Solve()\n\n")

    sat.append("    if status == pywraplp.Solver.OPTIMAL:\n")
    sat.append("        print('Solution:')\n")
    sat.append("        print('Objective value =', solver.Objective().Value())\n")
    for mg_variable, variable in variable_name_conversion:
        sat.append("        print('{} =', {}.solution_value())\n".format(variable, variable))
    for mg_edge, edge in edge_name_conversion:
        sat.append("        print('{} =', {}.solution_value())\n".format(edge, edge))
    sat.append("    else:\n")
    sat.append("        print('The problem does not have an optimal solution.')\n\n")

    sat.append("    print('Advanced usage:')\n")
    sat.append("    print('Problem solved in %f milliseconds' % solver.wall_time())\n")
    sat.append("    print('Problem solved in %d iterations' % solver.iterations())\n")


    # Writing policy to file
    for line in sat:
        print(line)
    #with open(output_sat_name, 'w') as output_sat:
        #output_sat.writelines(sat)


###############################################################################
# Main

def main(verbose, workflow, yawl_mode):
    global glob_verbose
    glob_verbose = verbose

    logging.basicConfig(level=logging.DEBUG)

    if workflow:
        if yawl_mode:
            workflow_metagraph = YawlToMetagraph.main(verbose, workflow)
        else:
            workflow_metagraph = TriplesToMetagraph.main(verbose, workflow)
    else:
        workflow_metagraph = load_workflow_from_test()

    if glob_verbose >= 0:
        PolicyAnalysisHelper.print_mg(workflow_metagraph)


    # Define source and target sets for couple redundancy detection
    source = sorted(list(workflow_metagraph.variables_set))[0]
    target = sorted(list(workflow_metagraph.variables_set))[-1]
    print("Source: {}, Target: {}".format(source, target))


    solver_instantiation(workflow, workflow_metagraph, yawl_mode)





if __name__ == '__main__':
    Utility.print_section("Getting arguments")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.workflow, args.yawl_mode)

    Utility.terminate_app(0)


###############################################################################
