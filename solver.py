import sys

sys.setrecursionlimit(10_000)

class Contradiction(Exception):
    """Raised if formula can't be satisfied"""

    pass


def update_exp(formula, inp_lit):
    """
    Returns a new formula (expression) given an orignal formula as a literal
    """
   
    opp_inp_lit = (inp_lit[0], not inp_lit[1])
    formula_copy = []
    for clause in formula:
        if inp_lit in clause:
            continue

        elif opp_inp_lit in clause:
            clause_add = clause.copy()
            clause_add = list(set(clause_add))
            clause_add.remove(opp_inp_lit)
            if not clause_add:
                return None
            formula_copy.append(clause_add)

        else:
            formula_copy.append(clause)
    return formula_copy

def set_literal(formula, string, boole):
    """
    Computes a new formula given a literal to set. 
    """

    to_add = {string: boole}

    reduced_form = update_exp(formula, (string, boole))

    if reduced_form is None:
        return None

    out_dict = satisfying_assignment(reduced_form, False)
    if out_dict is not None:
        out_dict.update(to_add)

    return out_dict

def clean_formula(formula):
    """
    Scrapes duplicates and semi-duplicates from formula. This is reduces total computation by decreasing steps of backtracking. 
    """
    new_formula = []

    for clause in formula:
        to_add = set()
        lit_dict = {False: set(), True: set()}
        for i, j in clause:
            if i in lit_dict[j]:
                continue
            elif i in lit_dict[not j]:
                to_add.remove((i, not j))
            to_add.add((i, j))
            lit_dict[j].add(i)
        lit_dict.clear()
        new_formula.append(list(to_add))

    return new_formula

def satisfying_assignment(formula, clean=True):
    """
    Finds a satisfying assignment for a given CNF formula.
    Returns that assignment if one exists, or None otherwise.

    >>> satisfying_assignment([])
    {}
    >>> x = satisfying_assignment([[('a', True), ('b', False), ('c', True)]])
    >>> x.get('a', None) is True or x.get('b', None) is False or x.get('c', None) is True
    True
    >>> satisfying_assignment([[('a', True)], [('a', False)]])
    """

    if formula == []:
        return {}

    first_literal = formula[0][0]

    second = True

    for clause in formula:
        if len(clause) == 1:
            first_literal = clause[0]
            second = False
            break

    first_attempt = set_literal(formula, first_literal[0], first_literal[1])

    if first_attempt is not None:
        return first_attempt

    elif second is True:
        second_attempt = set_literal(formula, first_literal[0], not first_literal[1])

        return second_attempt
    else:
        return None

def values_in_row(board, r):
    """
    Return a set containing all of the values in a given row.
    """
    return set(board[r]) - {0}

def values_in_column(board, c):
    """
    Return a set containing all of the values in a given column.
    """
    return {board[r][c] for r in range(len(board))} - {0}

def values_in_subgrid(board, sr, sc):
    """
    Return a set containing all of the values in a given subgrid.
    """
    return {
        board[r][c]
        for r in range(int(sr * 3), int((sr + 1) * 3))
        for c in range(int(sc * 3), int((sc + 1) * 3))
    } - {0}

def valid_moves(board, row, col):
    """
    Computes all initial valid numbers for a given cell. 
    """

    sr = int(row // (len(board) ** 0.5))
    sc = int(col // (len(board) ** 0.5))

    return (
        set(range(1, len(board) + 1))
        - values_in_row(board, row)
        - values_in_column(board, col)
        - values_in_subgrid(board, sr, sc)
    )

def gen_cell_coords(dim):
    """
    Generates all possibile coordiantes as a list of tuples. 
    """
    return [(i, j) for i in range(dim) for j in range(dim)]

def rule7(add_clause_row, been_added_row, add_clause_col, been_added_col, valid_num_coord):
    """
    Enforces the rule that, if it is initally possible for two numbers to occupy the same cell, 
    if one of them does, than the other cannot. This rule is seemingly redundant but it is included 
    to help with preformance. 
    """
    for x in add_clause_row:
        for y in add_clause_row:
            if (
                x != y
                and ((x[0], not x[1]), (y[0], not y[1])) not in been_added_row
            ):
                valid_num_coord.append([(x[0], not x[1]), (y[0], not y[1])])
                been_added_row.add(((y[0], not y[1]), (x[0], not x[1])))

    for x in add_clause_col:
        for y in add_clause_col:
            if (
                x != y
                and ((x[0], not x[1]), (y[0], not y[1])) not in been_added_col
            ):
                valid_num_coord.append([(x[0], not x[1]), (y[0], not y[1])])
                been_added_col.add(((y[0], not y[1]), (x[0], not x[1])))

    valid_num_coord.append(add_clause_row) 
    valid_num_coord.append(add_clause_col) 
    return valid_num_coord

def initial_looping(valid_num_coord, full_list):
    """
    Enforces the rule that each row, column, and subgrid contains every number. 
    """

    for num in range(1, board_dim + 1):
        # enforces rule: every row and column as every number
        for i in range(board_dim):
            add_clause_row = []
            add_clause_col = []
            been_added_row = set()
            been_added_col = set()
            for j in range(board_dim):
                add_clause_row.append(((num, (i, j)), True))  # row
                add_clause_col.append(((num, (j, i)), True))  # columns

            
            valid_num_coord = rule7(add_clause_row, been_added_row, add_clause_col, been_added_col, valid_num_coord)

        # enforces rule: every subgrid has every number
        for sub in range(0, board_dim, int(board_dim**0.5)):
            for sub2 in range(0, board_dim, int(board_dim**0.5)):
                add_clause_sub = []
                for i, j in full_list:
                    if (
                        sub <= i < int(board_dim**0.5) + sub
                        and sub2 <= j < int(board_dim**0.5) + sub2
                    ):
                        add_clause_sub.append(((num, (i, j)), True))

                valid_num_coord.append(add_clause_sub) 
    return valid_num_coord

def sudoku_board_to_sat_formula(sudoku_board):
    """
    Converts an input sudoku_board (n lists of n integers) to a SAT formula, to be passed into 
    satisfying_assignment. 
    """
    global board_dim
    board_dim = len(sudoku_board)
    full_list = gen_cell_coords(board_dim)
    coords_lst = full_list.copy()
    filled_lst = set()

    valid_num_coord = []

    for i, row in enumerate(sudoku_board):
        for j, val in enumerate(row):
            if val != 0:
                coords_lst.remove((i, j))
                filled_lst.add((val, (i, j)))

                valid_num_coord.append([((val, (i, j)), True)])

    # enforces rule: every row has all numbers AND every col has all numbers AND every subgrid has all numbers
    valid_num_coord = initial_looping(valid_num_coord, full_list)

    # enforces rule: at most 1 value per cell
    cur_added = set()
    for i, j in full_list:
        for num1 in range(1, board_dim + 1):
            for num2 in range(1, board_dim + 1):
                if (
                    num1 != num2
                    and (((num1, (i, j)), False), ((num2, (i, j)), False))
                    not in cur_added
                ):
                    valid_num_coord.append(
                        [((num1, (i, j)), False), ((num2, (i, j)), False)]
                    )
                    cur_added.add((((num2, (i, j)), False), ((num1, (i, j)), False)))
        # enforces rule: at least 1 value per cell
        add_clause = []
        for pos_val in range(1, board_dim + 1):
            add_clause.append(((pos_val, (i, j)), True))
        valid_num_coord.append(add_clause) 

    return valid_num_coord

def assignments_to_sudoku_board(assignments, n):
    """
    Given a list of variable assignments outputed by satisfying_assignment and 
    the dimension of the board, construct n lists of n values representing the
    filled out sudoku board. 

    If assignments is None, return None (no possible solutions).
    """
    if assignments is None:
        return None
    board = []
    for _ in range(n):
        board.append([0 for i in range(n)])

    for key in assignments:
        if assignments[key] is True:
            board[key[1][0]][key[1][1]] = key[0]

    return board


if __name__ == "__main__":
    pass
