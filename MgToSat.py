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

import os
import time


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


def find_all_reachable_elements(mg, B, covering=set(), edges_taken=[]):
    covering = covering.union(B) # Add B to the covering

    edges_not_taken = mg.edges # Initialize edges not taken
    valid_edges = mg.edges[0] # Initialize to any edge to trigger while loop

    while valid_edges:
        # Compute valid edges from edges not yet taken
        valid_edges = set()
        for edge in edges_not_taken:
            if covering.issuperset(edge.invertex):
                valid_edges.add(edge)

        # Add outvertex variables coming from valid edges
        # Add edges to edges_taken
        # Remove edges from edges_not_taken
        for edge in valid_edges:
            covering = covering.union(edge.outvertex)
            edges_taken.append(edge)
            edges_not_taken.remove(edge)

    return covering, edges_taken

def find_all_unreachable_elements(mg, B, covering=set(), edges_taken=[]):
    reachable_variables, reachable_edges = find_all_reachable_elements(mg, B, covering, edges_taken)

    unreachable_variables = mg.variables_set - reachable_variables
    unreachable_edges = []
    for edge in mg.edges:
        if edge not in reachable_edges:
            unreachable_edges.append(edge)

    if glob_verbose >= 2:
        print("Reachable variables: {}".format(reachable_variables))
        print("Unreachable variables: {}".format(unreachable_variables))
        print("Reachable edges: {}".format(reachable_edges))
        print("Unreachable edges: {}".format(unreachable_edges))

    return unreachable_variables, unreachable_edges


def generate_output_file_name(workflow, yawl_mode):
    # Generate output file name
    Utility.print_section("Generating output file name")

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

        output_sat_name = generated_sat_dir_path + path_chunks[-1].split('.')[0] + ".py"
    else:
        Utility.terminate_app(0) #TODO Handle error
    print("Output SAT file: {}\n".format(output_sat_name))
    return output_sat_name

def conversions(mg):
    # Make tuple list associating names of variables/edges in the metagraph to those in SAT
    Utility.print_section("Generating tuple list associating names of MG variables to SAT variables")

    variable_name_conversion = []
    for idx, variable in enumerate(sorted(mg.variables_set)):
        if glob_verbose >= 2:
            print("Variable: {}".format(variable))
        variable_name_conversion.append((variable, "x_{}".format(idx)))
    edge_name_conversion = []
    for idx, edge in enumerate(mg.edges):
        if glob_verbose >= 2:
            print("Edge: {}".format(edge))
        edge_name_conversion.append((edge, "e_{}".format(idx)))

    if glob_verbose >= 0:
        print("Variable name conversion: {}".format(variable_name_conversion))
        print("Edge name conversion: {}".format(edge_name_conversion))

    return variable_name_conversion, edge_name_conversion

def basic_sat_structure(variable_name_conversion, edge_name_conversion):
    Utility.print_section("Generating basic SAT structure")

    sat = []
    sat.append("from mgtoolkit.library import *\n")
    sat.append("from ortools.linear_solver import pywraplp\n\n")
    sat.append("def LinearProgramming():\n")
    sat.append("    # Instantiate a Glop solver.\n")
    sat.append("    solver = pywraplp.Solver('SolveSimpleSystem', pywraplp.Solver.SAT_INTEGER_PROGRAMMING)\n\n")

    # Add list of equivalence for variables and edges
    sat.append("    var_equivalence = {}\n".format(variable_name_conversion))
    sat.append("    edge_equivalence = {}\n\n".format(edge_name_conversion))

    timesteps = len(edge_name_conversion)

    # For each variable in the generating set, create a logic variable for each timestep
    sat.append("    # For each variable in the generating set, create a logic variable\n")
    for variable in variable_name_conversion:
        for step in range(0, timesteps):
            sat.append("    {}_{} = solver.IntVar(0, 1, '{}_{}')\n".format(variable[1], step, variable[1], step))
    sat.append("")

    # For each edge in the edges set, create a logic variable for each timestep
    for edge in edge_name_conversion:
        for step in range(0, timesteps):
            sat.append("    {}_{} = solver.IntVar(0, 1, '{}_{}')\n".format(edge[1], step, edge[1], step))
    sat.append("")

    sat.append("    print('Number of variables = {}'.format(solver.NumVariables()))\n\n")

    return sat


def constraints_variables_unique_time(constraints, variable_name_conversion, edge_name_conversion):
    # Each edge and variable must be set to True only once in all time, or not used
    Utility.print_section("Generating constraints: Variables must only be unlocked once in time")

    timesteps = len(edge_name_conversion)

    # Each variable must be set to True only once
    for variable_idx, (variable, variable_name) in enumerate(variable_name_conversion):
        formula_list = [] # Each element corresponds to one variable being True at one time

        for i in range(0, timesteps): # index indicating which time to set the variable to True
            formula_part_list = [] # Each element is a variable, either True or not

            for step in range(0, timesteps):
                if i == step: # This is the variable to set to True
                    formula_part_list.append("{}_{}".format(variable_name, step))
                else:
                    formula_part_list.append("~{}_{}".format(variable_name, step))

            formula_part = " & ".join(formula_part_list) # formula unlocking one variable at a specific time
            formula_list.append("({})".format(formula_part))

        # or not used
        formula_part_list = [] # Each element is a variable, either True or not
        for step in range(0, timesteps):
            formula_part_list.append("~{}_{}".format(variable_name, step))
        formula_part = " & ".join(formula_part_list) # formula unlocking one variable at a specific time
        formula_list.append("({})".format(formula_part))


        formula = " | ".join(formula_list)
        print(formula)
        constraints.append(to_cnf("{}".format(formula)))


    # Each edge must be set to True only once
    for edge_idx, (edge, edge_name) in enumerate(edge_name_conversion):
        formula_list = [] # Each element corresponds to one variable being True at one time

        for i in range(0, timesteps): # index indicating which time to set the variable to True
            formula_part_list = [] # Each element is a variable, either True or not

            for step in range(0, timesteps):
                if i == step: # This is the variable to set to True
                    formula_part_list.append("{}_{}".format(edge_name, step))
                else:
                    formula_part_list.append("~{}_{}".format(edge_name, step))

            formula_part = " & ".join(formula_part_list) # formula unlocking one variable at a specific time
            formula_list.append("({})".format(formula_part))

        # or not used
        formula_part_list = [] # Each element is a variable, either True or not
        for step in range(0, timesteps):
            formula_part_list.append("~{}_{}".format(edge_name, step))
        formula_part = " & ".join(formula_part_list) # formula unlocking one variable at a specific time
        formula_list.append("({})".format(formula_part))


        formula = " | ".join(formula_list)
        print(formula)
        constraints.append(to_cnf("{}".format(formula)))

    return constraints

def constraints_edge_unlocking(constraints, edge_name_conversion, source, target):
    Utility.print_section("Generating constraints: Edges unlock at least one useful variable")

    timesteps = len(edge_name_conversion)
    for ei_idx, (ei, ei_name) in enumerate(edge_name_conversion):
        for u in range(0, timesteps):
            # Condition 1: at least one variable in the outvertex is unlocked
            # "e_{i,u} => ~e_{j,0} & ~e_{j,1} & ... & ~e_{j,u-1}"
            formula_part_list = [] # Parts of the formula for unlocking at least one variable
            for var in ei.outvertex:
                if var not in source:
                    for ej_idx, (ej, ej_name) in enumerate(edge_name_conversion):
                        if ei != ej and var in ej.outvertex:
                            formula_part_list_variable = [] # Parts of the formula for unlocking one variable
                            for v in range(0, u): # Enforces v < u timesteps
                                formula_part_list_variable.append("~{}_{}".format(ej_name, v))
                            if not formula_part_list_variable:
                                formula_part_list_variable = ["True"]
                            formula_part_variable = " & ".join(formula_part_list_variable) # formula for unlocking one variable
                            formula_part_list.append("({})".format(formula_part_variable))
            formula_part = " | ".join(formula_part_list) # formula for unlocking at least one variable

            if glob_verbose >= 2:
                print("Formulas for {}_{}: {} at timestep {}".format(ei_name, u, ei, u))
                print("Formula part list: {}".format(formula_part_list))
                print("Formula part: {}\n".format(formula_part))

            if formula_part: # If no other edge has intersecting outvertex variables, there is no constraint from condition 1
                if glob_verbose >= 1:
                    print("({}_{}) >> ({})".format(ei_name, u, formula_part))
                constraints.append(to_cnf("({}_{}) >> ({})".format(ei_name, u, formula_part))) # Full clause for unlocking at least one variable



            # Condition 2: at least one unlocked variable is either in T, or used at a later time by an edge
            formula_part_2 = ""
            for var in ei.outvertex:
                if var not in source:
                    if var in target: # Condition 2.a
                        # e_{i,u} => e_{i,u} unlocks var
                        # Do nothing? This condition is already condition 1
                        pass

                    else: # Conditions 2.b and 2.c
                        formula_part_list_2b = [] # Parts for all edges that can use var
                        for ej_idx, (ej, ej_name) in enumerate(edge_name_conversion):
                            if ei != ej and var in ej.invertex:

                                # Condition 2.b
                                formula_part_list_2b_ej = [] # Parts (times) for edge e_j that can use var
                                for v in range(u+1, timesteps): # Enforces v > u timesteps
                                    formula_part_list_2b_ej.append("{}_{}".format(ej_name, v))
                                formula_part_ej = " | ".join(formula_part_list_2b_ej) # All times when e_j can use var
                                if formula_part_ej:
                                    formula_part_list_2b.append("({})".format(formula_part_ej))

                                # Condition 2.c
                                for v in range(u+1, timesteps):
                                    formula_part_list_2c = [] # Parts for all edges that can unlock var in the meantime
                                    for ek_idx, (ek, ek_name) in enumerate(edge_name_conversion):
                                        if ei != ek and ej != ek and var in ek.outvertex:
                                            formula_part_list_2c_ek = [] # Parts (times) for edge e_k that can unlock var in the meantime
                                            for w in range(u+1, v): # Enforces u < w < v timesteps
                                                formula_part_list_2c_ek.append("~{}_{}".format(ek_name, w))

                                            formula_part_ek = " & ".join(formula_part_list_2c_ek) # All times when e_k can unlock var in the meantime
                                            if formula_part_ek:
                                                formula_part_list_2c.append("({})".format(formula_part_ek))

                                    formula_part_2c = " & ".join(formula_part_list_2c) # formula for not unlocking in the meantime
                                    if formula_part_2c:
                                        formula_part_2c += " & {}_{}".format(ej_name, v)


                        if not formula_part_list_2b:
                            continue
                        formula_part_2b = " | ".join(formula_part_list_2b) # formula for unlocking at least one variable


                        if glob_verbose >= 2:
                            print("Formulas for {}_{}: {} at timestep {}".format(ei_name, u, ei, u))
                            print("Formula part 2b: {}".format(formula_part_2b))
                            print("Formula part 2c: {}".format(formula_part_2c))

                        if formula_part_2c:
                            if glob_verbose >= 1:
                                print("({}_{}) >> (({}) & ({}))".format(ei_name, u, formula_part_2b, formula_part_2c))
                            constraints.append(to_cnf("({}_{}) >> (({}) & ({}))".format(ei_name, u, formula_part_2b, formula_part_2c))) # Full clause for unlocking at least one variable
                        else:
                            if glob_verbose >= 1:
                                print("({}_{}) >> ({})".format(ei_name, u, formula_part_2b))
                            constraints.append(to_cnf("({}_{}) >> ({})".format(ei_name, u, formula_part_2b))) # Full clause for unlocking at least one variable

    return constraints


def forced_edge_true(constraints, edge_name_conversion, forced_edge):
    # The forced edge must be True at some point in time
    # No need to XOR since it is already enforced by constraints_variables_unique_time
    Utility.print_section("Generating constraints: Forced edge is True at some point")

    forced_edge_index = [idx for idx, conversion in enumerate(edge_name_conversion) if conversion[0] == forced_edge][0]
    timesteps = len(edge_name_conversion)

    formula_list = []
    for step in range(0, timesteps):
        formula_list.append("{}_{}".format(edge_name_conversion[forced_edge_index][1], step))

    formula = " | ".join(formula_list)
    if glob_verbose >= 1:
            print("{}".format(formula))

    constraints.append(to_cnf("({})".format(formula)))

    return constraints

def target_true(constraints, variable_name_conversion, edge_name_conversion, target_indices):
    # The target must be true at some point in time
    # No need to XOR since it is already enforced by constraints_variables_unique_time
    Utility.print_section("Generating constraints: Target is True at some point")

    timesteps = len(edge_name_conversion)

    for target_index in target_indices:
        formula_list = []
        for step in range(0, timesteps):
            formula_list.append("{}_{}".format(variable_name_conversion[target_index][1], step))

        formula = " | ".join(formula_list)
        if glob_verbose >= 1:
            print("{}".format(formula))

        constraints.append(to_cnf("({})".format(formula)))

    return constraints

def constraints_on_input_dominance(constraints, variable_name_conversion, edge_name_conversion, source, source_indices):
    # Add constraints for input dominance
    # Each variable in the source must have an edge using it at some point
    Utility.print_section("Generating constraints: Edge dominance - Each variable in the source must have an edge using it at some point")

    timesteps = len(edge_name_conversion)

    for source_index in source_indices:
        formula_list = []

        for edge_idx, (edge, edge_name) in enumerate(edge_name_conversion):
            formula_part_list_edge = []
            if variable_name_conversion[source_index][0] in edge.invertex:
                for step in range(0, timesteps):
                    formula_part_list_edge.append("{}_{}".format(edge_name, step))
                formula_part_edge = " | ".join(formula_part_list_edge)
            if formula_part_list_edge:
                formula_list.append("({})".format(formula_part_edge))

        formula = " | ".join(formula_list)
        if glob_verbose >= 1:
            print("{}".format(formula))

        constraints.append(to_cnf("{}".format(formula)))

    return constraints


def convert_to_lp(constraints):
    # For each constraint, convert to LP writing. The constraints must be in CNF form.
    Utility.print_section("Convert constrains to LP")

    for constraint in constraints:
        if glob_verbose >= 2:
            print("\n## {} ##".format(constraint))
        constraint_parts = str(constraint).split(' & ')

        if glob_verbose >= 3:
            print("Constraint parts: {}".format(constraint_parts))
        for constraint_part in constraint_parts:
            lp_constraint_parts = []

            constraint_subparts = constraint_part.split(' | ')

            if glob_verbose >= 3:
                print("Constraint part: {}".format(constraint_part))
                print("Constraint subparts: {}".format(constraint_subparts))
            for constraint_subpart in constraint_subparts:
                if "~" in constraint_subpart:
                    lp_constraint_parts.append(constraint_subpart.replace("~", "1-")) # not
                else:
                    lp_constraint_parts.append("{}".format(constraint_subpart))

            if glob_verbose >= 3:
                print("LP parts: {}".format(lp_constraint_parts))

            lp_constraint = " + ".join(lp_constraint_parts)
            lp_constraint += " >= 1"

            if glob_verbose >= 2:
                print("LP constraint: {}".format(lp_constraint))
            sat.append("    solver.Add({})\n".format(lp_constraint))
    sat.append("")

    return sat


def constraints_false(mg, variable_name_conversion, edge_name_conversion, source):
    # Add constraints set to False
    # This consists of unreachable variables and edges at all times
    Utility.print_section("Generating constraints: Unreachable variables and edges set to False (all times)")

    timesteps = len(edge_name_conversion)
    unreachable_variables, unreachable_edges = find_all_unreachable_elements(mg, source)
    unreachable_variables_solver = [conversion[1] for conversion in variable_name_conversion if conversion[0] in unreachable_variables]
    for unreachable_variable_solver in unreachable_variables_solver:
        for step in range(0, timesteps):
            sat.append("    solver.Add({}_{} == 0)\n".format(unreachable_variable_solver, step))

    unreachable_edges_solver = [conversion[1] for conversion in edge_name_conversion if conversion[0] in unreachable_edges]
    for unreachable_edge_solver in unreachable_edges_solver:
        for step in range(0, timesteps):
            sat.append("    solver.Add({}_{} == 0)\n".format(unreachable_edge_solver, step))
            if glob_verbose >= 1:
                print("{}_{} == 0".format(unreachable_edge_solver, step))

    return sat

def constraints_true(variable_name_conversion, edge_name_conversion, source_indices):
    # Add constraints set to True
    # This consists of the variables of the source.
    Utility.print_section("Generating constraints: Source is True (t=0)")

    # Variables of source to True at time 0
    for source_index in source_indices:
        sat.append("    solver.Add({}_0 == 1)\n".format(variable_name_conversion[source_index][1]))
        if glob_verbose >= 1:
            print("{}_0 == 1".format(variable_name_conversion[source_index][1]))

    return sat


def minimize(edge_name_conversion):
    # Minimization function
    Utility.print_section("Minimize the number of edges")

    edges = []
    timesteps = len(edge_name_conversion)
    for conversion in edge_name_conversion:
        for step in range(0, timesteps):
             edges.append("{}_{}".format(conversion[1], step))
    minimization_string = " + ".join(edges)
    sat.append("    solver.Minimize({})\n\n".format(minimization_string))

    return sat

def solve(variable_name_conversion, edge_name_conversion):
    # Solve the system.
    Utility.print_section("Generate solving")

    sat.append("    status = solver.Solve()\n\n")

    sat.append("    if status == pywraplp.Solver.OPTIMAL:\n")
    sat.append("        print('Solution:')\n")
    sat.append("        print('Objective value =', solver.Objective().Value())\n")
    timesteps = len(edge_name_conversion)
    for step in range(0, timesteps):
        for mg_variable, variable in variable_name_conversion:
            sat.append("        print('{}_{} =', {}_{}.solution_value())\n".format(variable, step, variable, step))
        for mg_edge, edge in edge_name_conversion:
            sat.append("        print('{}_{} =', {}_{}.solution_value())\n".format(edge, step, edge, step))
    sat.append("    else:\n")
    sat.append("        print('The problem does not have an optimal solution.')\n\n")

    sat.append("    print('Advanced usage:')\n")
    sat.append("    print('Problem solved in %f milliseconds' % solver.wall_time())\n")
    sat.append("    print('Problem solved in %d iterations' % solver.iterations())\n\n")

    sat.append("    for edge in edge_equivalence:\n")
    sat.append("        print(edge)\n\n")

    sat.append("LinearProgramming()\n")

    return sat




def constraints_on_edge_invertex(constraints, variable_name_conversion, edge_name_conversion, variable_symbols, edge_symbols):
    if glob_verbose >= 1:
        print("Constraints on edge >> invertex")
    for edge_idx, edge in enumerate(edge_name_conversion):
        if glob_verbose >= 1:
            print(edge)

        # Get indices of invertex_variables which correspond to indices in variable_symbols
        invertex_variables = edge[0].invertex
        invertex_variables_indices = [idx for idx, conversion in enumerate(variable_name_conversion) if conversion[0] in invertex_variables]

        # Formulate edge >> invertex constraint in sympy
        formula_part_list = []
        for invertex_variable_index in invertex_variables_indices:
            formula_part_list.append("{}".format(variable_symbols[invertex_variable_index]))
        formula_part = " & ".join(formula_part_list)
        if glob_verbose >= 1:
            print("({}) >> ({})".format(edge_symbols[edge_idx], formula_part))
        constraints.append(to_cnf("({}) >> ({})".format(edge_symbols[edge_idx], formula_part)))
    return constraints

def constraints_on_elements_edges(constraints, variable_name_conversion, edge_name_conversion, variable_symbols, source):
    if glob_verbose >= 1:
        print("Constraints on element >> edges")
    for variable_idx, conversion in enumerate(variable_name_conversion):
        if conversion[0] not in source:
            if glob_verbose >= 1:
                print(conversion)
            inbound_edges = []
            for edge in edge_name_conversion:
                if conversion[0] in edge[0].outvertex:
                    inbound_edges.append(edge)

            if inbound_edges: # Make sure at least one edge is inbound
                # Formulate element >> edges constraint in sympy
                formula_part_list = []
                for edge in inbound_edges:
                    formula_part_list.append("{}".format(edge[1]))
                formula_part = " | ".join(formula_part_list)
                if glob_verbose >= 1:
                    print("({}) >> ({})\n".format(variable_symbols[variable_idx], formula_part))
                constraints.append(to_cnf("({}) >> ({})".format(variable_symbols[variable_idx], formula_part)))

        # Get indices of outvertex_variables which correspond to indices in variable_symbols
        #outvertex_variables = edge[0].outvertex
        #outvertex_variables_indices = [idx for idx, conversion in enumerate(variable_name_conversion) if conversion[0] in outvertex_variables]

        # Formulate edge >> outvertex constraint in sympy
        #formula_part_list = []
        #for outvertex_variable_index in outvertex_variables_indices:
        #    formula_part_list.append("{}".format(variable_symbols[outvertex_variable_index]))
        #formula_part = " & ".join(formula_part_list)
        #if glob_verbose >= 1:
        #    print("({}) >> ({})\n".format(edge_symbols[edge_idx], formula_part))
        #constraints.append(to_cnf("({}) >> ({})".format(edge_symbols[edge_idx], formula_part)))

    return constraints

def constraints_on_destination(constraints, variable_name_conversion, edge_name_conversion, edge_symbols, target, target_indices):
    # Add constraints to make sure destination is reached
    # Each variable in the destination must have an edge reaching it
    if glob_verbose >= 1:
        print("Constraints on destination")
    for target_index in target_indices:
        formula_part_list = []
        for edge_idx, edge in enumerate(edge_name_conversion):
            if variable_name_conversion[target_index][0] in edge[0].outvertex:
                formula_part_list.append("{}".format(edge_symbols[edge_idx]))
        formula_part = " | ".join(formula_part_list)

        if glob_verbose >= 1:
            print("{}".format(formula_part))
        constraints.append(to_cnf("{}".format(formula_part)))

    return constraints


def solver_instantiation(workflow, mg, yawl_mode, source, target, forced_edge):
    ### Creates a file that contains the SAT instantiation of the MG-FE-SPP

    # Generate output file name
    output_sat_name = generate_output_file_name(workflow, yawl_mode)

    # Make tuple list associating names of variables/edges in the metagraph to those in SAT
    variable_name_conversion, edge_name_conversion = conversions(mg)

    # Basic SAT structure
    global sat
    sat = basic_sat_structure(variable_name_conversion, edge_name_conversion)


    # Create sympy symbols for logic variables
    #Utility.print_section("Generating sympy symbols for the variables")
    #variable_symbols = sp.symbols('x_0:{}'.format(len(variable_name_conversion)))
    #edge_symbols = sp.symbols('e_0:{}'.format(len(edge_name_conversion)))
    #if glob_verbose >= 1:
        #print("Sympy symbols")
        #print(variable_symbols)
        #print(edge_symbols)


    # Constraints in sympy
    constraints = []
    source_indices = [idx for idx, conversion in enumerate(variable_name_conversion) if conversion[0] in source]
    target_indices = [idx for idx, conversion in enumerate(variable_name_conversion) if conversion[0] in target]

    constraints_variables_unique_time(constraints, variable_name_conversion, edge_name_conversion)

    constraints_edge_unlocking(constraints, edge_name_conversion, source, target)

    forced_edge_true(constraints, edge_name_conversion, forced_edge)
    target_true(constraints, variable_name_conversion, edge_name_conversion, target_indices)

    constraints_on_input_dominance(constraints, variable_name_conversion, edge_name_conversion, source, source_indices)

    #constraints_on_edge_invertex(constraints, variable_name_conversion, edge_name_conversion, variable_symbols, edge_symbols)
    #constraints_on_elements_edges(constraints, variable_name_conversion, edge_name_conversion, variable_symbols, source)

    #constraints_on_destination(constraints, variable_name_conversion, edge_name_conversion, edge_symbols, target, target_indices)

    if glob_verbose >= 2:
        print("\nConstraints")
        for constraint in constraints:
            print("{}\n".format(constraint))

    convert_to_lp(constraints) # For each constraint, convert to LP writing


    constraints_false(mg, variable_name_conversion, edge_name_conversion, source) # Add constraints set to False
    constraints_true(variable_name_conversion, edge_name_conversion, source_indices) # Add constraints set to True

    sat.append("    print('Number of constraints = {}'.format(solver.NumConstraints()))\n\n")

    minimize(edge_name_conversion) # Minimization function
    solve(variable_name_conversion, edge_name_conversion)  # Solve the system.

    if glob_verbose >= 3:
        for line in sat:
            print(line)

    # Writing policy to file
    with open(output_sat_name, 'w') as output_sat:
        output_sat.writelines(sat)
    print("Output written to {}".format(output_sat_name))


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

    if glob_verbose >= 1:
        PolicyAnalysisHelper.print_mg(workflow_metagraph)


    # Define source and target sets for couple redundancy detection
    source = sorted(list(workflow_metagraph.variables_set))[0]
    target = sorted(list(workflow_metagraph.variables_set))[-1]
    print("Source: {}, Target: {}".format(source, target))


    #for forced_edge in workflow_metagraph.edges:
    forced_edge = workflow_metagraph.edges[-1]
    print("Forced edge: {}".format(forced_edge))
    solver_instantiation(workflow, workflow_metagraph, yawl_mode, source, target, forced_edge)





if __name__ == '__main__':
    Utility.print_section("Getting arguments")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.workflow, args.yawl_mode)

    Utility.terminate_app(0)


###############################################################################
