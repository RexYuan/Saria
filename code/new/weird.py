# NOTE: chatgpt magic
def tseitin_or_and_or(formula):
    """
    Perform Tseitin transformation for a formula with AND groups of OR clauses.

    Formula is given as a list of AND groups, each containing OR clauses.
    Args:
        formula (list): The input formula, consisting of multiple AND groups of ORs.
    Returns:
        tuple: CNF clauses and the updated variable counter.
    """
    clauses = []
    and_group_vars = []  # To store the auxiliary variables for each AND group

    # Step 1: Encode each OR group with an auxiliary variable
    for and_group in formula:
        and_group_vars_in_group = []

        # Encode each OR group in the AND group
        for or_group in and_group:
            # Generate a new variable for this OR group
            group_var = v.id()
            and_group_vars_in_group.append(group_var)

            # Flatten the literals in the OR group
            group_literals = or_group

            # Encode the OR group as a set of clauses
            clauses.append([-group_var] + group_literals)  # (-group_var OR all literals)
            for literal in group_literals:
                clauses.append([group_var, -literal])  # (group_var OR -literal)

        # Step 2: Combine the OR groups in the AND group with a new AND auxiliary variable
        and_group_var = v.id()
        and_group_vars.append(and_group_var)

        # Add clause to combine the OR groups using AND (i.e., a new variable for the AND)
        and_group_clause = [and_group_var]
        for group_var in and_group_vars_in_group:
            and_group_clause.append(group_var)
        clauses.append(and_group_clause)

    # Step 3: Combine the AND groups using an OR operation
    or_var = v.id()
    for and_group_var in and_group_vars:
        clauses.append([-or_var] + [and_group_var])  # (-or_var OR each AND group variable)
    for and_group_var in and_group_vars:
        clauses.append([or_var, -and_group_var])  # (or_var OR -each AND group variable)

    return clauses, or_var
