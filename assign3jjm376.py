# Name: Jay Joshi
# University of Regina
# Dept of Computer Science
# 200440993
# jjm376@uregina.ca
# The below program solves
# a constrained cp-net to find k pareto optimal solutions for a randomly generated cp-net: Main parts of program: 1)
# The function_perform_topological_order_by_graph generates topological order to by using heuristic function of most
# constrained cp-net. Solving graph by a topological order with most constraint heuristic had a great impact on a
# search procedure in assigning values to variables 2) The function k pareto optimal solution is used to generate k
# pareto outcomes of a variable.It uses three techniques backtracking, forward checking, full arc consistency as a
# search procedure in a topological order. 3) Dominant query operations while finding k pareto solution are np-hard
# problems. 4) This program solves dominance queries with dominance tree operation and suffix pruning heuristics.
# Various heuristics such as least flipping values and forward pruning techniques can be applied to reduce search
# efforts in dominance tree operation. The complexity of dominance tree is linear in solving binary valued cp net
# instance. Hence program generates output as a function of linear time for binary valued cp net instances. Marker
# should enter whether he wants to run program with suffix pruning heuristic for dominance query or not The maximum
# nodes i.e path expanded can be analysed with or without suffix pruning technique The algorithm for dominance query
# operation i.e dominance tree searching might end up in a recursion in a search for infinite path


import operator
import itertools
import random
import math
import time
from collections import defaultdict
from collections import deque

count_constrained_variable = {}
count_max_paths_traversed = 0
visited_impression = []
domain = {}
variables = []
d = 0
c = 0


# returns topological order to according to most constrained heuristic
def perform_topological_order_by_graph(list_of_incompatible_tuples_values, variables_parents_list
                                       ):
    topological_order_list = []
    priority_list = {}
    indegree_of_variables = {}
    for v1, v in variables_parents_list.items():
        indegree_of_variables[v1] = len(variables_parents_list[v1])
    for i in variables_parents_list.keys():
        if indegree_of_variables[i] == 0:
            priority_list[i] = calculate_degree_of_variable_in_csp(list_of_incompatible_tuples_values, i)
    while len(priority_list) != 0:
        variable = return_max_value(priority_list)
        del priority_list[variable]
        topological_order_list.append(variable)
        for j in variables_parents_list.keys():
            if variable != j:
                if variable in variables_parents_list[j]:
                    indegree_of_variables[j] = indegree_of_variables[j] - 1
                    if indegree_of_variables[j] == 0:
                        priority_list[j] = calculate_degree_of_variable_in_csp(list_of_incompatible_tuples_values, j)
    print("----Topological order for most constrained heuristic is i.e. Nodes are expanded in order----")
    print(topological_order_list)
    return topological_order_list


# Function performs dominance query by searching in a dominance tree
def perform_dominance_by_suffixing(solution_set, new_assignment, variables_parents_list,
                                   variables_parents_combinations_preference_order, suffix_prune):
    node_to_be_expanded = []
    global count_max_paths_traversed
    count_max_paths_traversed = count_max_paths_traversed + 1
    if len(solution_set) == 0:
        return False
    for i in solution_set:
        if i == new_assignment:
            return True
            break
        else:
            if suffix_prune == 1:
                if count_max_paths_traversed > 1:
                    r_th_suffix = 0
                    for suffix, value in new_assignment.items():
                        if new_assignment[suffix] is i[suffix]:
                            r_th_suffix = r_th_suffix + 1
                        else:
                            r_th_suffix = 0
                    if r_th_suffix >= 1:
                        nodes_need_to_be_expanded = len(new_assignment) - r_th_suffix
                        temp_list_of_nodes = list(new_assignment.keys())
                        for h in range(nodes_need_to_be_expanded):
                            node_to_be_expanded.append(temp_list_of_nodes[h])
                    else:
                        node_to_be_expanded = list(new_assignment.keys())
                else:
                    node_to_be_expanded = list(new_assignment.keys())
            else:
                node_to_be_expanded = list(new_assignment.keys())
            for j in node_to_be_expanded:
                temp = new_assignment.copy()
                partial_assignments = []
                if len(variables_parents_list[j]) == 0:
                    partial_value = [more_prefer for more_prefer in
                                     variables_parents_combinations_preference_order[j] if
                                     variables_parents_combinations_preference_order[j].index(more_prefer) <
                                     variables_parents_combinations_preference_order[j].index(
                                         new_assignment[j])]
                else:
                    parents_values = ()
                    parents_names = tuple(variables_parents_list[j])
                    for parent in parents_names:
                        parents_values = parents_values + (new_assignment[parent],)
                    dict2 = dict(variables_parents_combinations_preference_order[j][0])
                    partial_value = [more_prefer for more_prefer in
                                     dict2[parents_values] if
                                     dict2[parents_values].index(more_prefer) <
                                     dict2[parents_values].index(
                                         new_assignment[j])]
                if len(partial_value) == 0:
                    continue
                else:
                    for values in partial_value:
                        temp[j] = values
                        partial_assignments.append(temp)
                    for assignments in partial_assignments:
                        if perform_dominance_by_suffixing(solution_set, assignments, variables_parents_list,
                                                          variables_parents_combinations_preference_order,
                                                          suffix_prune):
                            return True

    return False


# Finds neighbouring nodes in graph
def find_neighbours(X, Y, list_of_incompatible_tuples_values):
    neighbors = []
    for edge in list_of_incompatible_tuples_values.keys():
        if X in edge:
            for x in edge:
                if x != X and x != Y:
                    if x not in neighbors:
                        neighbors.append(x)
    return neighbors


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


# This main function performs arc consistency before beginning of search
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


# Checks consistency of assignment according to constraints
def assignment_is_consistent(new_assignment, list_of_incompatible_tuples_values):
    for i in list_of_incompatible_tuples_values.keys():
        x, y = i
        if x in new_assignment.keys() and y in new_assignment.keys():
            if (new_assignment[x], new_assignment[y]) in list_of_incompatible_tuples_values[i]:
                return False
    return True


# function prunes inconsistent values if any present in domain
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
    restore_pruned_values(deleted_domain_values)
    return True, deleted_domain_values


# function restores pruned values while backtracking
def restore_pruned_values(pruned_dict):
    for deleted in pruned_dict.keys():
        for pruned in range(0, d):
            if pruned not in domain[deleted]:
                domain[deleted].append(pruned)


# returns best variables for assignment in most constrained heuristic order
def return_best_variable_from_topological_order(new_assignment, topological_order):
    h = len(new_assignment)
    return topological_order[h]


# Function propogates values and prunes inconsistent values by forward checking or full arc consistency
def propogate(next_variable, next_value, new_assignment, list_of_incompatible_tuples_values, run_method):
    if run_method is "FAC":
        new_assignments_values = perform_full_arc_consistency(next_variable, next_value, new_assignment,
                                                              list_of_incompatible_tuples_values
                                                              , domain, constraints_list)
        return new_assignments_values
    if run_method is "FC":
        prune_inconsistent_values(new_assignment, list_of_incompatible_tuples_values, next_variable, next_value)


# Function performs full arc consistency technique
def perform_full_arc_consistency(var, value, assignment, list_of_incompatible_tuples_values, domain, constraints_list):
    undefined_variables = []
    future_constrains = {}
    new_assignments_values = {}
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
        new_assignments_values = "False"
    return new_assignments_values


# returns next best value of nodes in preference order and skips if value is pruned by forward checking thus returning
# next best available value in preferenced order
def return_best_value_according_to_cpt(variable, new_assignment, variables_parents_list,
                                       variables_parents_combinations_preference_order,
                                       ):
    d = round(math.pow(n, alpha))
    counter = visited_impression.count((variable, new_assignment))
    visited_impression.append((variable, new_assignment))
    if len(variables_parents_list[variable]) == 0:
        while counter < d:
            if variables_parents_combinations_preference_order[variable][counter] in domain[variable]:
                return variables_parents_combinations_preference_order[variable][counter]
                break
            else:
                counter = counter + 1
                # to count next unvisited visit
                visited_impression.append((variable, new_assignment))
        if counter >= d:
            return None
    elif len(variables_parents_list) > 0:
        if counter < d:
            parents_values = ()
            parents_names = tuple(variables_parents_list[variable])
            for i in parents_names:
                parents_values = parents_values + (new_assignment[i],)
            for x, y in variables_parents_combinations_preference_order.items():
                if x == variable:
                    q = dict(variables_parents_combinations_preference_order[variable][0])
                    while counter < d:
                        if q[parents_values][counter] in domain[variable]:
                            return q[parents_values][counter]
                            break
                        else:
                            counter = counter + 1
                            # to count unvisited visit.
                            visited_impression.append((variable, new_assignment))
                    if counter >= d:
                        return None
        elif counter >= d:
            return None

# main function to find k pareto solutions
def find_k_pareto_solutions(list_of_incompatible_tuples_values, variables_parents_list,
                            variables_parents_combinations_preference_order,
                            topological_order, k, suffix_prune, run_method=""):
    solution_set = []
    fringe = []

    end_search = "false"
    root = return_best_variable_from_topological_order({}, topological_order)
    best_value = return_best_value_according_to_cpt(root, {}, variables_parents_list,
                                                    variables_parents_combinations_preference_order)

    fringe.append({root: best_value})
    while len(solution_set) < k and end_search is "false":
        new_assignment = fringe.pop()
        if assignment_is_consistent(new_assignment, list_of_incompatible_tuples_values):
            if len(new_assignment) == n:
                final_assignment = new_assignment.copy()
                if not perform_dominance_by_suffixing(solution_set, new_assignment, variables_parents_list,
                                                      variables_parents_combinations_preference_order, suffix_prune):
                    solution_set.append(final_assignment)

            else:
                next_variable = return_best_variable_from_topological_order(new_assignment, topological_order)
                next_value = return_best_value_according_to_cpt(next_variable, new_assignment,
                                                                variables_parents_list,
                                                                variables_parents_combinations_preference_order)
                if run_method is "FC" or run_method is "FAC":
                    propogate(next_variable, next_value, new_assignment, list_of_incompatible_tuples_values, run_method)
                if next_value is not None:
                    fringe.append(new_assignment)
                    fringe.append({**new_assignment, **{next_variable: next_value}})

                else:
                    while 1:
                        deleted_assignment = new_assignment.popitem()
                        v1, v2 = deleted_assignment
                        next_value = return_best_value_according_to_cpt(v1, new_assignment, variables_parents_list,
                                                                        variables_parents_combinations_preference_order)
                        if next_value is None and v1 is not root:
                            continue
                        else:
                            break
                    if v1 is root and next_value is None:
                        end_search = "True"
                        global c
                        c = 1

                    else:
                        fringe.append(new_assignment)
                        fringe.append({**new_assignment, **{v1: next_value}})
        else:
            deleted_assignment = new_assignment.popitem()
            v1, v2 = deleted_assignment
            next_value = return_best_value_according_to_cpt(v1, new_assignment, variables_parents_list,
                                                            variables_parents_combinations_preference_order)
            if next_value is not None:
                # fringe.append(new_assignment)
                fringe.append({**new_assignment, **{v1: next_value}})
            else:
                while 1:
                    deleted_assignment = new_assignment.popitem()
                    v1, v2 = deleted_assignment
                    next_value = return_best_value_according_to_cpt(v1, new_assignment, variables_parents_list,
                                                                    variables_parents_combinations_preference_order)
                    if next_value is None and v1 is not root:
                        continue
                    else:
                        break
                if v1 is root and next_value is None:
                    c = 1
                    end_search = "True"
                else:
                    # fringe.append(new_assignment)
                    fringe.append({**new_assignment, **{v1: next_value}})
    return solution_set

# checks degree of variables in constraint graphs to determine most constrained variable
def calculate_degree_of_variable_in_csp(list_of_incompatible_tuples_values, i):
    degree_count = 0
    for j in list_of_incompatible_tuples_values.keys():
        if i in j:
            degree_count = degree_count + 1
    count_constrained_variable[i] = degree_count
    return degree_count


def return_max_value(priority_list):
    return max(priority_list.items(), key=operator.itemgetter(1))[0]


# randomly selects n*p maximum parents for variables
def assign_parents_to_variables(variables_parents_list, random_number, i):
    while len(variables_parents_list[i]) != random_number:
        if i is 0:
            break
        select_parent = random.choice(range(0, i))
        if i is not select_parent:
            if select_parent not in variables_parents_list[i]:
                variables_parents_list[i].append(select_parent)


# randomly generates prefrence order for root nodes and childrens for their domains
def assign_preference_order(variables_parents_combinations_preference_order, domain, count_parents, i):
    if count_parents is 0:
        count = 1
        while count <= len(domain[i]):
            select_random_value = random.choice(domain[i])
            if select_random_value not in variables_parents_combinations_preference_order[i]:
                variables_parents_combinations_preference_order[i].append(select_random_value)
                count += 1
    else:
        domain_list_combination = []
        temporary_dict = defaultdict(list)
        for c in range(0, count_parents):
            domain_list_combination.append(domain[i])
        possible_combination = list(itertools.product(*domain_list_combination))
        for j in possible_combination:
            count = 1
            while count <= len(domain[i]):
                select_random_value = random.choice(domain[i])
                if select_random_value not in temporary_dict[j]:
                    temporary_dict[j].append(select_random_value)
                    count += 1
        variables_parents_combinations_preference_order[i].append(temporary_dict)


# preference order for parents combinations
def generate_preference_order_for_parents_combinations(list_of_parents_of_variables, variables, domain):
    variables_parents_combinations_preference_order = defaultdict(list)
    for i in variables:
        count_parents = len(list_of_parents_of_variables[i])
        assign_preference_order(variables_parents_combinations_preference_order, domain, count_parents, i)
    print("----- The preference order is as follows---")
    for key, pair in variables_parents_combinations_preference_order.items():
        print("--- The preference order for " + str(key) + "th variable is")
        if len(list_of_parents_of_variables[key]) == 0:
            for order in variables_parents_combinations_preference_order[key]:
                print("> " + str(order))
        else:
            q = dict(variables_parents_combinations_preference_order[key][0])
            for k1, v1 in q.items():
                print("--- The preference order for " + str(k1) + "th value of its parent combination  is")
                for parent_order in q[k1]:
                    print("> " + str(parent_order))

    return variables_parents_combinations_preference_order


# generates constrained cp net instances
def generate_constrained_cp_net_instance(n, p, alpha, r):
    global variables
    variables = list(range(0, n))
    global d
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
    for v1, v in list_of_incompatible_tuples_values.items():
        print('variables in csp={} list of incompatible values={}'.format(v1, v))
    variables_parents_list = defaultdict(list)
    max_parents = round(n * p)
    for i in variables:
        if i < max_parents:
            random_number = random.choice(range(0, i + 1))
        else:
            random_number = random.choice(range(0, max_parents + 1))
        assign_parents_to_variables(variables_parents_list, random_number, i)
    for variable in variables_parents_list.keys():
        print("The list of parent of " + str(variable) + "is ")
        print(variables_parents_list[variable])
    return variables, domain, constraints_list, variables_parents_list, list_of_incompatible_tuples_values

# main callable functions
def solve_by_preference_order(variables, domain, list_of_parents_of_variables, list_of_incompatible_tuples_values,
                              suffix_prune, run_method=""):
    preference_order = generate_preference_order_for_parents_combinations(list_of_parents_of_variables, variables,
                                                                          domain)
    topological_sorting = perform_topological_order_by_graph(list_of_incompatible_tuples_values,
                                                             list_of_parents_of_variables
                                                             )
    final_solution = find_k_pareto_solutions(list_of_incompatible_tuples_values,
                                             list_of_parents_of_variables,
                                             preference_order,
                                             topological_sorting, k, suffix_prune, run_method)
    print("Solution after max traversed path in dominance tree is" + str(count_max_paths_traversed))
    for i in range(len(final_solution)):
        print("----Solution" + str(i + 1) + "---------")
        for m, v in final_solution[i].items():
            print(" ---- Variable is " + str(m) + " Value is " + str(v) + "----")

    if c == 1:
        print("There are no more Pareto optimal outcomes")


flag = True
while flag:
    print()
    print("Please enter require values to generate binary csp instance:")
    n = int(input("Number of variables n:"))
    p = float(input("Constraint Tightness p:"))
    alpha = float(input("Constant alpha:"))
    r = float(input("Constant r:"))
    k = int(input("The number of require k pareto solutions"))
    print()
    print(">>> Do you wish to run Arc-Consistency before finding optimal solutions?")
    use_arc_c = input(" 1 for yes and 0 for no: ")
    print()
    use_arc_c = 0
    if use_arc_c == 1:
        use_arc_c = 1
    suffix_prune = input(" Do you want to run suffix pruning heuristic for dominance query 1 for Yes 0 for no")
    print(" Choose the Search algorithm")
    print("1) Backtrack Search Algorithm to find pareto optimal solutions for constrained cp-net")
    print("2) Backtrack Search with Forward Checking Algorithm")
    print("3) Backtrack Search with Maintaining Arc Consistency (MAC) Algorithm")
    option = input("::")
    variables, domain, constraints_list, variables_parents_list, list_of_incompatible_tuples_values = \
        generate_constrained_cp_net_instance(n, p, alpha, r)
    arc_result = True
    if use_arc_c:
        arc_result = perform_arc_consistency(list_of_incompatible_tuples_values, domain, constraints_list)
    if arc_result:
        start_time = time.time()
        result = None
        if option == "1":
            solve_by_preference_order(variables, domain, variables_parents_list, list_of_incompatible_tuples_values,
                                      suffix_prune, run_method="")
        elif option == "2":
            solve_by_preference_order(variables, domain, variables_parents_list, list_of_incompatible_tuples_values,
                                      suffix_prune, run_method="FC")

        elif option == "3":
            solve_by_preference_order(variables, domain, variables_parents_list, list_of_incompatible_tuples_values,
                                      suffix_prune, run_method="FAC")
    else:
        print("Arc consistent returns false hence no solution")
    print("--- %s seconds ---" % (time.time() - start_time))
    print("Press 1 to continue else to exit press 0")
    again = input("::")
    if again != "1":
        keep_running = False
