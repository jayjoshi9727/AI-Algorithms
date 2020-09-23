""""
Name:Jay Joshi
Student Id:200440993

This program is an implementation of Unification algorithm which take literals as an input to unify
them where .1 Function or Predicate names are in small letters
            2 Variables are in Capital letters
            3.Constants are in small letters.
Compiling the python program: 1.Install python 3.6.4 and set the path in enviornment variable.
                              2.Open cmd.exe and set the path were assign1jjm376.py is store.
                              3.Type name of your python file and press enter.
                              4.Enter the inputs to get desire output.
"""
# import package to identify function variables and constants
import re

flag = "yes"


# update flag if unification is not possible
def update_flag():
    global flag
    flag = 'no'


# Taking inputs of literals in form of string
literal1 = input('Enter the literal 1:')
literal2 = input('Enter the literal 2:')
# Dictionary to store replacements while performing unification
map_update = {}


# Updates the value in dictionary as required.
def update_value(key, value):
    for k in map_update:
        if map_update[k] == key:
            map_update[k] = value
    map_update[key] = value


# Checks whether the string is function or predicate.
def is_function(f):
    result = re.match(r'[a-z]+\(', f)
    if result is not None:
        return 1


# Extracting list of function name, variable and constant from string literal.
def return_list_from_predicate_calculus(l1):
    result = re.findall(r'[a-z]+\(|[a-z]+|[A-Z]+|\)|\,', l1)
    return result


# Main function which performs unification.
def unify_check_with_occurs(l1, l2):
    if l1 == l2:
        return 1
    elif l1.isupper() and '(' not in l1:
        unify_if_l1_is_variable(l1, l2)
    elif l1.islower() and '(' not in l1:
        unify_if_l1_is_constant(l1, l2)
    elif is_function(l1):
        unify_if_l1_is_function(l1, l2)
    else:
        raise Exception("Unexpected exception found")


# Unifying literal if it is identified as function.
def unify_if_l1_is_function(l1, l2):
    if l2.isupper() and l2 not in l1 and '(' not in l2:
        update_value(l2, l1)
    elif l2.islower() and '(' not in l2:
        update_flag()
    elif is_function(l2):
        unify_arguments(l1, l2)


# Unifying literal if it is identified as constant.
def unify_if_l1_is_constant(l1, l2):
    if l2.isupper() and l1 != l2 and '(' not in l2:
        update_value(l2, l1)
    elif (l2.islower() and '(' not in l2 and l1 != l2) or (is_function(l2)):
        update_flag()


# Unifying literal if it is identified as variable.
def unify_if_l1_is_variable(l1, l2):
    if ((l2.isupper() or l2.islower()) and l1 != l2 and '(' not in l2) or (is_function(l2) and l1 not in l2):
        update_value(l1, l2)
    else:
        update_flag()


# Unifies each argument found in function or predicate
def unify_arguments(l1, l2):
    list1 = return_list_from_predicate_calculus(l1)
    list2 = return_list_from_predicate_calculus(l2)
    arg_list1 = extract_arguments_from_list_of_literal(list1)
    arg_list2 = extract_arguments_from_list_of_literal(list2)
    if arg_list1[0] == arg_list2[0] and len(arg_list1) == len(arg_list2):
        for i in range(1, len(arg_list1)):
            if (arg_list1[i] or arg_list2[i]) == ',':
                continue

            unify_check_with_occurs(arg_list1[i], arg_list2[i])
            if flag == 'no':
                break
            arg_list1, arg_list2 = update_remaining_arguments(arg_list1, arg_list2, i)
    else:
        raise Exception("function or predicate should have same name and same number of arguments")


# Updating values in remainder of strings if replacement is found
def update_remaining_arguments(arg_list1, arg_list2, i):
    for j in range(i, len(arg_list1)):
        for k, v in map_update.items():
            if k in arg_list1[j]:
                replace_1 = [sub.replace(k, v) for sub in arg_list1[j]]
                new_str1 = ''.join(replace_1)
                arg_list1[j] = new_str1
            if k in arg_list2[j]:
                replace_2 = [sub.replace(k, v) for sub in arg_list2[j]]
                new_str2 = ''.join(replace_2)
                arg_list2[j] = new_str2
    return arg_list1, arg_list2


# Extracting function arguments from list of literal.
def extract_arguments_from_list_of_literal(l1):
    i = 1
    while i < len(l1):
        nested_fun = ''
        b = 0
        if '(' in l1[i]:
            nested_fun += l1[i]
            b = b + 1
            extract_nested_function(b, i, l1, nested_fun)
        else:
            if ',' in l1[i]:
                del l1[i]
        i += 1
    return l1


# Extracting nested function if found in argument of main function or predicate
def extract_nested_function(b, i, l1, nested_fun):
    for j in range(i + 1, len(l1)):
        if '(' in l1[j]:
            b = b + 1
        elif ')' in l1[j]:
            b = b - 1
            if ')' in l1[j + 1] and b == 0:
                nested_fun += l1[j]
                l1.insert(i, nested_fun)
                del l1[i + 1:j + 2]
                break
        elif ',' in l1[j] and b == 0:
            l1.insert(i, nested_fun)
            del l1[i + 1:j + 2]
            break
        if b < 0:
            break
        nested_fun += l1[j]


'''
Function identifies if errors in syntax name of function,variables,constants and
returns index were error occurs which are identified in Regular expression identifies 
following Errors in function name variable and constant name and balanced paranthesis
'''


def syntax_analyzer(literal_1, literal_2):
    literal1_list = re.search(r'[A-Z]+\(|([A-Z]+[a-z]+)+|([a-z]+[A-Z]+)+', literal_1)
    literal2_list = re.search(r'[A-Z]+\(|([A-Z]+[a-z]+)+|([a-z]+[A-Z]+)+', literal_2)
    if (literal1_list is None and literal2_list is None) and (
            is_balanced_paranthesis(literal_1) and is_balanced_paranthesis(literal_2)):
        unify_check_with_occurs(literal_1, literal_2)
    elif not (is_balanced_paranthesis(literal_1)) or not (is_balanced_paranthesis(literal_2)):
        raise Exception("Unbalanced Paranthesis found in either of literal")
    else:
        if literal1_list is not None:
            i = literal_1.find(literal1_list.group())
            print("Syntax error at " + str(i) + " , th position in literal1 ")
        if literal2_list is not None:
            j = literal_2.find(literal2_list.group())
            print("Syntax error at " + str(j) + " th position in literal2 ")
        update_flag()
        return 0


def is_balanced_paranthesis(p):
    c = 0
    for i in range(len(p)):
        if '(' in p[i]:
            c += 1
        elif ')' in p[i]:
            c -= 1
    if c == 0:
        return True
    else:
        return False


syntax_analyzer(literal1, literal2)
if flag == 'yes':
    for k, v in map_update.items():
        print(k + " ===> " + v)
print(flag)
