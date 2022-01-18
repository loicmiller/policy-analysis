###############################################################################
# Imports

import sys
import argparse # Argument parser

from mgtoolkit.library import *
import xml.etree.ElementTree as ET

from termcolor import colored
from pprint import pprint

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
    parser = argparse.ArgumentParser(description="Convert YAWL file to a conditional metagraph", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--version", action="version", version='%(prog)s 1.0')
    parser.add_argument("-v", "--verbose", action="count", default=0, help="increase output verbosity")
    parser.add_argument("yawl", type=str, metavar="FILE", help="YAWL file to generate metagraph from")

    return parser


###############################################################################
# Functions

def print_mg(mg):
    print("Variables set: {}".format(colored(list(mg.variables_set), "blue")))
    print("Propositions set: {}".format(colored(list(mg.propositions_set), "yellow")))
    print("Generating set: {}".format(colored(list(mg.generating_set), "green")))
    #print("Edge set: {}".format(colored(mg.edges, "red")))
    print("Edge set ({}):".format(len(mg.edges)))
    for edge in mg.edges:
        print("{} - {} to {}".format(colored(edge.label, "magenta"), colored(sorted(list(edge.invertex)), "cyan"), colored(sorted(list(edge.outvertex)), "red")))


def print_img(mg):
    print("Generating set: {}".format(colored(list(mg.generating_set), "green")))
    #print("Edge set: {}".format(colored(mg.edges, "red")))
    print("Edge set ({}):".format(len(mg.edges)))
    for edge in mg.edges:
        print("{} - {} to {}".format(colored(edge.label, "magenta"), colored(sorted(list(edge.invertex)), "cyan"), colored(sorted(list(edge.outvertex)), "red")))


# Add placeholder variable in case vertex is empty
def add_placeholder():
    add_placeholder.count += 1
    placeholder = "placeholder_" + str(add_placeholder.count)
    return placeholder
add_placeholder.count = 0


###############################################################################
# Main

def main(verbose, yawl):
    global glob_verbose
    glob_verbose = verbose

    print("\n\n###############################################################################")
    print("Importing and parsing YAWL file")
    print("###############################################################################")

    schema = "{http://www.yawlfoundation.org/yawlschema}"

    tree = ET.parse(yawl)
    root = tree.getroot()

    workflow_variables_set = set()
    workflow_propositions_set = set()
    workflow_metagraph_edges = []

    tasks_variables_set = set()
    tasks_propositions_set = set()
    tasks_metagraph_edges = []

    # Filling dictionaries with YAWL info
    task_dict = {} # Dictionary containing info about YAWL workflow
    reverse_flow_dict = {} # Dictionary mapping tasks to tasks flowing into them
    for decomposition in root.iter(schema + 'decomposition'):
        if 'isRootNet' in decomposition.attrib: # rootNet decomposition
            # Get input parameters, add to variables_set
            for input_param in decomposition.findall(schema + 'inputParam'):
                name = input_param.find(schema + 'name').text
                workflow_variables_set.add(name)

            # Get output parameters, add to variables_set
            for output_param in decomposition.findall(schema + 'outputParam'):
                name = output_param.find(schema + 'name').text
                workflow_variables_set.add(name)

            # Get tasks
            processControlElements = decomposition.find(schema + 'processControlElements')
            for task in processControlElements.findall(schema + 'task'):
                id = task.get('id') # id of task (== name of task)
                if glob_verbose >= 1:
                    print("Task id: {}".format(id))

                # Find join and split codes
                join_code = task.find(schema + 'join').get('code')
                split_code = task.find(schema + 'split').get('code')

                # Find predicates
                next_elements = []
                predicates = []
                for flows_into in task.findall(schema + 'flowsInto'):
                    next_element = flows_into.find(schema + 'nextElementRef').get('id')
                    if glob_verbose >= 2:
                        print("Next element: {}".format(next_element))

                    next_elements.append(next_element)
                    if not next_element in reverse_flow_dict:
                        reverse_flow_dict[next_element] = []
                    reverse_flow_dict[next_element].append(id)

                    if flows_into.findall(schema + 'predicate') is not None:
                        for predicate in flows_into.findall(schema + 'predicate'):
                            predicates.append(predicate.text)

                # Invertex
                starting_mappings_elements = []
                if task.find(schema + 'startingMappings') is not None:
                    starting_mappings = task.find(schema + 'startingMappings')
                    for mapping in starting_mappings.findall(schema + 'mapping'):
                        maps_to = mapping.find(schema + 'mapsTo').text
                        starting_mappings_elements.append(maps_to)

                # Outvertex
                completed_mappings_elements = []
                if task.find(schema + 'completedMappings') is not None:
                    completed_mappings = task.find(schema + 'completedMappings')
                    for mapping in completed_mappings.findall(schema + 'mapping'):
                        maps_to = mapping.find(schema + 'mapsTo').text
                        completed_mappings_elements.append(maps_to)

                if not id in task_dict:
                    task_dict[id] = {}
                else:
                    terminate_app(message="ERR: Task already in dict")
                task_dict[id]["join_code"] = join_code
                task_dict[id]["split_code"] = split_code
                task_dict[id]["next_elements"] = next_elements
                task_dict[id]["starting_mappings"] = starting_mappings_elements
                task_dict[id]["completed_mappings"] = completed_mappings_elements
                task_dict[id]["predicates"] = predicates
                task_dict[id]["type"] = "task"

            # Get conditions
            for condition in processControlElements.findall(schema + 'condition'):
                id = condition.get('id') # id of task (== name of task)
                if glob_verbose >= 1:
                    print("Condition id: {}".format(id))

                join_code = "xor" # Default value for tasks
                split_code = "and" # Default value for tasks

                # Find predicates
                next_elements = []
                predicates = []
                for flows_into in condition.findall(schema + 'flowsInto'):
                    next_element = flows_into.find(schema + 'nextElementRef').get('id')
                    if glob_verbose >= 2:
                        print("Next element: {}".format(next_element))

                    next_elements.append(next_element)
                    if not next_element in reverse_flow_dict:
                        reverse_flow_dict[next_element] = []
                    reverse_flow_dict[next_element].append(id)

                    if flows_into.findall(schema + 'predicate') is not None:
                        for predicate in flows_into.findall(schema + 'predicate'):
                            predicates.append(predicate.text)

                # Invertex
                starting_mappings_elements = []

                # Outvertex
                completed_mappings_elements = []

                if not id in task_dict:
                    task_dict[id] = {}
                else:
                    terminate_app(message="ERR: Task already in dict")
                task_dict[id]["join_code"] = join_code
                task_dict[id]["split_code"] = split_code
                task_dict[id]["next_elements"] = next_elements
                task_dict[id]["starting_mappings"] = starting_mappings_elements
                task_dict[id]["completed_mappings"] = completed_mappings_elements
                task_dict[id]["predicates"] = predicates
                task_dict[id]["type"] = "condition"

    if glob_verbose >= 3:
        print("Task dict")
        pprint(task_dict)
        print("\n\nReverse flow dict")
        pprint(reverse_flow_dict)


    # Fix tasks that have no input and/or no output
    for task_id in task_dict:
        if not task_dict[task_id]["starting_mappings"]:
            task_dict[task_id]["starting_mappings"].append(add_placeholder())
        if not task_dict[task_id]["completed_mappings"]:
            task_dict[task_id]["completed_mappings"].append(add_placeholder())

    if glob_verbose >= 1:
        print("Task dict")
        pprint(task_dict)
        print("\n\nReverse flow dict")
        pprint(reverse_flow_dict)



    print("\n\n###############################################################################")
    print("Creating sets for metagraph generation")
    print("###############################################################################")

    # Used to check if completion propositions are already created
    completion_propositions_duplicate_check = []

    for task_id in task_dict:
        invertex = set()
        outvertex = set()
        propositions = set()
        task_invertex = set()
        task_outvertex = set()

        if glob_verbose >= 1:
            print("Task id: {}".format(task_id))
        task_invertex = set([task_id])
        tasks_variables_set.add(task_id)

        for next_element in task_dict[task_id]["next_elements"]:
            task_outvertex = set([next_element])
            tasks_variables_set.update(task_outvertex)

        # Propositions
        workflow_propositions_set.update(task_dict[task_id]["predicates"])
        tasks_propositions_set.update(task_dict[task_id]["predicates"])
        propositions.update(task_dict[task_id]["predicates"])

        # Invertex
        workflow_variables_set.update(task_dict[task_id]["starting_mappings"])
        invertex.update(task_dict[task_id]["starting_mappings"])

        # Outvertex
        workflow_variables_set.update(task_dict[task_id]["completed_mappings"])
        outvertex.update(task_dict[task_id]["completed_mappings"])


        if glob_verbose >= 3:
            print("Invertex: {}".format(invertex))
            print("Outvertex: {}".format(outvertex))
            print("Propositions: {}".format(propositions))
            print("\n\n")

        tasks_metagraph_edges.append(Edge(task_invertex, task_outvertex, attributes=list(propositions), label=task_id))

        # Fixing AND/OR/XOR joins when there is no overlap
        if task_dict[task_id]["join_code"] == "and":
            if glob_verbose >= 1:
                print("Case: AND-join - id: {}".format(task_id))
            for previous_task in reverse_flow_dict[task_id]: # Iterate on tasks flowing to current task
                if set(task_dict[previous_task]["completed_mappings"]).isdisjoint(set(task_dict[task_id]["starting_mappings"])):
                    # Create virtual task between output of previous task and a completion proposition
                    new_invertex = set(task_dict[previous_task]["completed_mappings"])
                    completion_proposition = previous_task + "_completed"
                    workflow_propositions_set.add(completion_proposition)
                    new_outvertex = set([completion_proposition])
                    workflow_metagraph_edges.append(Edge(new_invertex, new_outvertex, label=completion_proposition))

                    # Modifify propositions of current task to include proposition
                    propositions.add(completion_proposition)
            workflow_metagraph_edges.append(Edge(invertex, outvertex, attributes=list(propositions), label=task_id))

        elif task_dict[task_id]["join_code"] == "or":
            if glob_verbose >= 1:
                print("Case: OR-join  - id: {}".format(task_id))
            default_edge_added = False
            for previous_task in reverse_flow_dict[task_id]: # Iterate on tasks flowing to current task
                if set(task_dict[previous_task]["completed_mappings"]).isdisjoint(set(task_dict[task_id]["starting_mappings"])):
                    # Create virtual task between output of previous task and a completion proposition
                    new_invertex = set(task_dict[previous_task]["completed_mappings"])
                    completion_proposition = previous_task + "_completed"
                    workflow_propositions_set.add(completion_proposition)
                    new_outvertex = set([completion_proposition])
                    workflow_metagraph_edges.append(Edge(new_invertex, new_outvertex, label=completion_proposition))

                    # Modifify propositions of current task to include proposition
                    propositions.add(completion_proposition)
                    workflow_metagraph_edges.append(Edge(invertex, outvertex, attributes=list(propositions), label=task_id))
                    propositions.remove(completion_proposition)
                elif not default_edge_added: # If not disjoint, simply add edge
                    workflow_metagraph_edges.append(Edge(invertex, outvertex, attributes=list(propositions), label=task_id))
                    default_edge_added = True

        elif task_dict[task_id]["join_code"] == "xor" and task_id in reverse_flow_dict and len(reverse_flow_dict[task_id]) > 1: # 'task_id in reverse_flow_dict' fixes "KeyError: 'Welcome_to_Start_Process_3258'"
            if glob_verbose >= 1:
                print("Case: XOR-join - id: {}".format(task_id))
            completion_propositions = []
            for previous_task in reverse_flow_dict[task_id]: # Iterate on tasks flowing to current task
                # Create virtual task between output of previous task and a completion proposition
                completion_proposition = previous_task + "_completed"
                non_completion_proposition = previous_task + "_not_completed"
                completion_propositions.append((completion_proposition, non_completion_proposition))

                if (completion_proposition, non_completion_proposition) not in completion_propositions_duplicate_check:
                    workflow_propositions_set.add(completion_proposition)
                    workflow_propositions_set.add(non_completion_proposition)
                    completion_propositions_duplicate_check.append((completion_proposition, non_completion_proposition))

                    new_invertex = set(task_dict[previous_task]["completed_mappings"])
                    new_outvertex = set([completion_proposition])
                    workflow_metagraph_edges.append(Edge(new_invertex, new_outvertex, label=completion_proposition))
                    new_outvertex = set([non_completion_proposition])
                    workflow_metagraph_edges.append(Edge(new_invertex, new_outvertex, label=non_completion_proposition))

                    if glob_verbose >= 3:
                        print('Using edge label {}'.format(completion_proposition))
                        print('Using edge label {}'.format(non_completion_proposition))

            # Modifify propositions of current task to include proposition
            for i in range(len(completion_propositions)):
                additional_propositions = set()
                for j in range(len(completion_propositions)):
                    if i == j:
                        additional_propositions.add(completion_propositions[j][0])
                    else:
                        additional_propositions.add(completion_propositions[j][1])

                propositions.update(additional_propositions)
                workflow_metagraph_edges.append(Edge(invertex, outvertex, attributes=list(propositions), label=task_id))
                propositions -= additional_propositions

        elif task_dict[task_id]["join_code"] == "xor" and task_id in reverse_flow_dict: # Default case (normal tasks and conditions, with exactly one previous task)
            if glob_verbose >= 1:
                print("Case: default  - id: {}".format(task_id))
            # If those tasks are disjoint
            previous_task = reverse_flow_dict[task_id][0]
            if set(task_dict[previous_task]["completed_mappings"]).isdisjoint(set(task_dict[task_id]["starting_mappings"])):
                # Create virtual task between output of previous task and a completion proposition
                new_invertex = set(task_dict[previous_task]["completed_mappings"])
                completion_proposition = previous_task + "_completed"
                workflow_propositions_set.add(completion_proposition)
                new_outvertex = set([completion_proposition])
                workflow_metagraph_edges.append(Edge(new_invertex, new_outvertex, label=completion_proposition))

                # Modify propositions of current task to include proposition
                propositions.add(completion_proposition)
            # Add task edge
            workflow_metagraph_edges.append(Edge(invertex, outvertex, attributes=list(propositions), label=task_id))

        elif task_id not in reverse_flow_dict: # Starting task
            if glob_verbose >= 1:
                print("Case: start    - id: {}".format(task_id))
            # Add task edge
            workflow_metagraph_edges.append(Edge(invertex, outvertex, attributes=list(propositions), label=task_id))
        elif task_id in reverse_flow_dict:
            if glob_verbose >= 1:
                print("Caught unmanaged case!")
            print(task_id)

        '''
        # Alternative way to get tasks
        else: # not rootNet decomposition, each decomposition is a task
            # Get tasks (edges)
            invertex = set()
            outvertex = set()

            for input_param in decomposition.findall(schema + 'inputParam'):
                name = input_param.find(schema + 'name').text
                invertex.add(name)

            # Get output parameters
            for output_param in decomposition.findall(schema + 'outputParam'):
                name = output_param.find(schema + 'name').text
                outvertex.add(name)

            workflow_metagraph_edges.append(Edge(invertex, outvertex))
        '''



    print("\n\n###############################################################################")
    print("Generating metagraph")
    print("###############################################################################")

    workflow_metagraph = ConditionalMetagraph(workflow_variables_set, workflow_propositions_set)
    workflow_metagraph.add_edges_from(workflow_metagraph_edges)

    if glob_verbose >= 1:
        print_mg(workflow_metagraph)

    return workflow_metagraph

    """
    print("\nInverse")
    img = workflow_metagraph.get_inverse()
    print_img(img)
    """


    """
    print("\n\n###############################################################################")
    print("Generating task metagraph")
    print("###############################################################################")

    print("Tasks variables set: {}".format(workflow_variables_set))
    print("Tasks propositions set: {}\n".format(workflow_propositions_set))
    print("Tasks metagraph edges: {}\n".format(workflow_metagraph_edges))

    tasks_metagraph = ConditionalMetagraph(tasks_variables_set, tasks_propositions_set)
    tasks_metagraph.add_edges_from(tasks_metagraph_edges)

    print_mg(tasks_metagraph)
    """



if __name__ == '__main__':
    print("\n\n###############################################################################")
    print("Getting arguments")
    print("###############################################################################")

    parser = get_parser() # Create a parser
    args = parser.parse_args() # Parse arguments
    print(args)

    # Call main
    main(args.verbose, args.yawl)

    terminate_app(0)


###############################################################################
