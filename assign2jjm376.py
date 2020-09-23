# The following program is used to generate binary instances and solving it using three strategies
# namely Backtracking, with and without Forward checking and Full Arc Consistency respectively.
# user has been given option to run arc consistency before actual backtracking strategies
# Name: Jay Joshi
# Student ID: 200440993
# University of Regina
# Department of Computer Science

import random
import math
import time
from collections import deque
from collections import defaultdict

# Function to prune domain value in arc consistency
def is_function_revise(X, Y, list_of_incompatible_tuples_values, domain):
    flag = 0
    if (X, Y) in list_of_incompatible_tuples_values.keys():
        for i in domain[X]:
            c = 0
            for j in domain[Y]:
                if (i, j) in list_of_incompatible_tuples_values[(X, Y)]:
                    c += 1
            if c == len(domain[Y]):
                domain[X].remove(i)
                flag = 1
    return flag

# Finds neighbors of current variables having constraints to add in queue
def find_neighbours(X, Y, list_of_incompatible_tuples_values):
    neighbors = []
    for edge in list_of_incompatible_tuples_values.keys():
        if X in edge:
            for x in edge:
                if x != X and x != Y:
                    if x not in neighbors:
                        neighbors.append(x)
    return neighbors

# Main function which performs arc consistency
def perform_arc_consistency(list_of_incompatible_tuples_values, domain, constraints_list):
    queue = deque(list_of_incompatible_tuples_values.keys())
    while len(queue) != 0:
        X, Y = queue.pop()
        if is_function_revise(X, Y, list_of_incompatible_tuples_values, domain):
            if len(domain[X]) == 0:
                return False
            neighbours_0f_X = find_neighbours(X, Y, list_of_incompatible_tuples_values)
            for j in neighbours_0f_X:
                if (X, j) in constraints_list:
                    queue.append((j, X))
    return True

# Selects next unassigned variable in list
def pick_unassigned_variables(assignment):
    for x in variables:
        if x not in assignment.keys():
            return x
            break

# Function which implements full arc consistency as a inference in backtracking
def perform_full_arc_consistency(var, value, assignment, list_of_incompatible_tuples_values, domain, constraints_list):
    undefined_variables = []
    future_constrains = {}
    new_assignments = {}
    for (v1, v2) in constraints_list:
        if var in (v1, v2):
            other_var = None
            if v1 == var:
                other_var = v1
            else:
                other_var = v2
            if not other_var in assignment.keys():
                undefined_variables.append(other_var)
                future_constrains[(v1, v2)] = list_of_incompatible_tuples_values[(v1, v2)]
    result = perform_arc_consistency(list_of_incompatible_tuples_values, domain, future_constrains)
    if not result:
        new_assignments = "False"
    return new_assignments

# Returns ordered domain of variables
def return_domain(var):
    return domain[var]

# Checks whether the current assignment to variable is consistent or not with assigned variables
def assignment_is_consistent(list_of_incompatible_tuples_values, assignment, var, value):
    for k, v in assignment.items():
        if (k, var) in list_of_incompatible_tuples_values.keys():
            if (v, value) in list_of_incompatible_tuples_values[(k, var)]:
                return False
        elif (var, k) in list_of_incompatible_tuples_values.keys():
            if (value, v) in list_of_incompatible_tuples_values[(var, k)]:
                return False
    return True

# Function prunes inconsistent values as a part of Forward checking
def prune_inconsistent_values(assignment, list_of_incompatible_tuples_values, var, value):
    deleted_domain_values = defaultdict(list)
    for k in list_of_incompatible_tuples_values.keys():
        if var in k:
            v1, v2 = k
            if v1 is var and v2 not in assignment.keys():
                for j in domain[v2]:
                    if (value, j) in list_of_incompatible_tuples_values[(v1, v2)]:
                        deleted_domain_values[v2].append(j)
                for i in deleted_domain_values[v2]:
                    domain[v2].remove(i)
                if len(domain[v2]) is 0:
                    return False, deleted_domain_values
            elif v2 is var and v1 not in assignment.keys():
                for j in domain[v1]:
                    if (j, value) in list_of_incompatible_tuples_values[(v1, v2)]:
                        deleted_domain_values[v1].append(j)
                for i in deleted_domain_values[v1]:
                    domain[v1].remove(i)
                if len(domain[v1]) is 0:
                    return False, deleted_domain_values
    return True, deleted_domain_values

# Restores pruned values if domain lenght is zero
def restore_pruned_values(pruned_dict):
    for k in pruned_dict.keys():
        if len(pruned_dict[k]) != 0:
            for i in pruned_dict[k]:
                domain[k].append(i)

# Main function which performs forward checking
def perform_forward_checking(assignment, list_of_incompatible_tuples_values):
    if len(assignment) == len(variables):
        return assignment
    var = pick_unassigned_variables(assignment)
    for i in domain[var]:
        if assignment_is_consistent(list_of_incompatible_tuples_values, assignment, var, i):
            assignment[var] = i
            flag, prune_list = prune_inconsistent_values(assignment, list_of_incompatible_tuples_values, var, i)
            if flag:
                result = perform_forward_checking(assignment, list_of_incompatible_tuples_values)
                if result != 0:
                    return result
            restore_pruned_values(prune_list)
            del assignment[var]
    return 0

# Performs recursive backtracking and also full arc consistency as part of inference
def standard_recursive_backtracking(assignment, list_of_incompatible_tuples_values, inf_type=None):
    if len(assignment) == len(variables):
        return assignment
    var = pick_unassigned_variables(assignment)
    for i in return_domain(var):
        if assignment_is_consistent(list_of_incompatible_tuples_values, assignment, var, i):
            assignment[var] = i
            if inf_type == "FAC":
                new_assignments = perform_full_arc_consistency(var, i, list_of_incompatible_tuples_values, )
                if new_assignments != "Failure":
                    for v in new_assignments.keys():
                        assignment[v] = new_assignments[v]
            result = standard_recursive_backtracking(assignment, list_of_incompatible_tuples_values)
            if result != 0:
                return result
            del assignment[var]
    return False

# Calls Main back tracking function
def backtracking(assignment, list_of_incompatible_tuples_values, inf_type=None):
    return standard_recursive_backtracking(assignment, list_of_incompatible_tuples_values, inf_type)

# This function generates and prints binary constraints
def generate_binary_csp_instance(n, p, alpha, r):
    global variables
    variables = list(range(0, n))
    d = round(math.pow(n, alpha))
    global domain
    domain = {}
    constraints_list = []
    for i in variables:
        domain[i] = list(range(0, d))
    print(domain)
    number_of_constraints = round((r * n * math.log(n, 2.7828)))
    while len(constraints_list) < number_of_constraints:
        v1, v2 = (random.choice(variables), random.choice(variables))
        if v1 != v2 and (v1, v2) not in constraints_list and (v2, v1) not in constraints_list:
            constraints_list.append((v1, v2))
    number_of_incompatible_tuples = int(round(p * (math.pow(d, 2))))
    list_of_incompatible_tuples_values = {}
    for i in range(len(constraints_list)):
        value_list = []
        while len(value_list) < number_of_incompatible_tuples:
            n1, n2 = (random.choice(range(d)), random.choice(range(d)))
            if (n1, n2) not in value_list:
                value_list.append((n1, n2))
        list_of_incompatible_tuples_values[constraints_list[i]] = value_list
    for k, v in list_of_incompatible_tuples_values.items():
        print('variables in csp={} list of incompatible values={}'.format(k, v))
    return variables, domain, constraints_list, list_of_incompatible_tuples_values

flag = True

while flag:
    print()
    print("Please enter require values to generate binary csp instance:")
    n = int(input("Number of variables n:"))
    p = float(input("Constraint Tightness p:"))
    alpha = float(input("Constant alpha:"))
    r = float(input("Constant r:"))
    print()
    print(">>> Do you wish to run Arc-Consistency before backtrack?")
    use_arc_c = input(" 1 for yes and 0 for no: ")
    print()
    use_arc_c = 0
    if use_arc_c == 1:
        use_arc_c = 1
    print(" Choose the Search algorithm")
    print("1) Backtrack Search Algorithm")
    print("2) Backtrack Search with Forward Checking Algorithm")
    print("3) Backtrack Search with Maintaining Arc Consistency (MAC) Algorithm")
    option = input("::")
    variables, domains, constrains_list, list_of_incompatible_tuples_values = generate_binary_csp_instance(n, p, alpha,                                                                                                       r)
    arc_result = True
    if use_arc_c:
        arc_result = perform_arc_consistency(list_of_incompatible_tuples_values, domains, constrains_list)
    assignment = {}
    if arc_result:
        start_time = time.time()
        result = None
        if option == "1":
            result = backtracking(assignment, list_of_incompatible_tuples_values)
        elif option == "2":
            result = perform_forward_checking(assignment, list_of_incompatible_tuples_values)
        elif option == "3":
            result = backtracking(assignment, list_of_incompatible_tuples_values, inf_type="MAC")
        for k, v in result.items():
            print(" Variable is {} Value is {}".format(k, v))
    else:
        print("Arc consistance returns false hence no solution")
    print("--- %s seconds ---" % (time.time() - start_time))

    print("Press 1 to continue else to exit press 0")
    again = input("::")

    if again != "1" and again != "1":
        keep_running = False
