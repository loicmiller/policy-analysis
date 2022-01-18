###############################################################################
# Imports

import sys


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