from ortools.linear_solver import pywraplp


def LinearProgrammingExample():
    """Linear programming sample."""
    # Instantiate a Glop solver, naming it LinearExample.
    solver = pywraplp.Solver.CreateSolver('GLOP')

    # Create the two variables and let them take on values 0 or 1
    x1 = solver.NumVar(0, 1, 'x1')
    x2 = solver.NumVar(0, 1, 'x2')
    x3 = solver.NumVar(0, 1, 'x3')
    x4 = solver.NumVar(0, 1, 'x4')
    x5 = solver.NumVar(0, 1, 'x5')

    e1 = solver.NumVar(0, 1, 'e1')
    e2 = solver.NumVar(0, 1, 'e2')
    e3 = solver.NumVar(0, 1, 'e3')

    print('Number of variables =', solver.NumVariables())

    # Constraint 0: x + 2y <= 14.
    solver.Add(1-x1 + e1 >= 1)

    # Constraint 1: 3x - y >= 0.
    solver.Add(1-x1 + e2 >= 1)

    # Constraint 2: x - y <= 2.
    solver.Add(1-x3 + 1-x4 + e3 >= 1)

    solver.Add(1-e1 + x2 >= 1)
    solver.Add(1-e1 + x3 >= 1)

    solver.Add(1-e2 + x4 >= 1)

    solver.Add(1-e3 + x5 >= 1)

    solver.Add(x1 == 1)
    solver.Add(e3 == 1)

    solver.Add(1-x1 + e1 + e2 >= 1)


    print('Number of constraints =', solver.NumConstraints())

    # Objective function: 3x + 4y.
    solver.Minimize(e1 + e2 + e3)

    # Solve the system.
    status = solver.Solve()

    if status == pywraplp.Solver.OPTIMAL:
        print('Solution:')
        print('Objective value =', solver.Objective().Value())
        print('e1 =', e1.solution_value())
        print('e2 =', e2.solution_value())
        print('e3 =', e3.solution_value())
    else:
        print('The problem does not have an optimal solution.')

    print('\nAdvanced usage:')
    print('Problem solved in %f milliseconds' % solver.wall_time())
    print('Problem solved in %d iterations' % solver.iterations())


LinearProgrammingExample()
