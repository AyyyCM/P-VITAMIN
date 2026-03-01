"""
PCTL Verification Module
Implements probabilistic model checking for PCTL formulas
"""


def verifyPCTL(formula, scgs):
    """
    Verify a PCTL formula against an SCGS model

    Args:
        formula: PCTL formula (parsed or as string)
        scgs: SCGS model object

    Returns:
        Dictionary with verification results
    """

    # Parse formula if string
    if isinstance(formula, str):
        from vitamin_model_checker.logics.PCTL.parser import do_parsingPCTL
        parsed_formula = do_parsingPCTL(formula)
    else:
        parsed_formula = formula

    # Check if formula contains probability operator
    if is_probability_formula(parsed_formula):
        result_states = check_probability_formula(scgs, parsed_formula)
    else:
        # Fall back to CTL-style checking
        result_states = check_ctl_formula(scgs, parsed_formula)

    # Get initial state
    initial_state = scgs.get_initial_state()
    initial_state_idx = scgs.get_index_by_state_name(initial_state)

    # Check if formula is satisfied at initial state
    is_satisfied = initial_state_idx in result_states

    return {
        'satisfiable': is_satisfied,
        'states': result_states,
        'initial_state_result': is_satisfied
    }


def is_probability_formula(formula):
    """Check if formula contains probability operator"""
    if isinstance(formula, tuple):
        if formula and formula[0]:
            return str(formula[0]).startswith('P')
    return False


def check_probability_formula(scgs, formula):
    """
    Check P>=x, P<=x, P>x, P<x formulas

    Returns set of states satisfying the formula
    """
    import re

    prob_op = formula[0]  # e.g., 'P>=0.9'
    subformula = formula[1]

    # Parse 'P>=0.9'
    match = re.match(r'P(>=|<=|>|<)(\d+\.?\d*)', prob_op)
    if not match:
        return set()

    comparison = match.group(1)
    threshold = float(match.group(2))

    # Get states satisfying subformula
    subformula_states = check_ctl_formula(scgs, subformula)

    # Compute reachability probabilities
    return pre_image_prob_exist(scgs, subformula_states, threshold, comparison)


def check_ctl_formula(scgs, formula):
    """Check CTL-style formulas (fallback)"""
    # This is a simplified fallback - in production, integrate full CTL checking
    if isinstance(formula, str):
        # Check if it's an atomic proposition
        return get_states_prop_holds(scgs, formula)
    return set()


def get_states_prop_holds(scgs, prop):
    """Get states where atomic proposition holds"""
    states = set()
    prop_matrix = scgs.get_matrix_proposition()

    try:
        index = scgs.get_atom_index(prop)
    except:
        return states

    if index is None:
        return states

    for state_idx, row in enumerate(prop_matrix):
        if row[int(index)] == 1:
            states.add(state_idx)

    return states


def pre_image_prob_exist(scgs, target_states, threshold, comparison):
    """
    Compute states from which probability of reaching target_states meets threshold

    Uses value iteration algorithm
    """
    states = list(range(scgs.get_number_of_states()))
    n = len(states)

    # Initialize probabilities
    prob = {s: 0.0 for s in states}

    # Target states have probability 1.0
    for target in target_states:
        prob[target] = 1.0

    # Value iteration
    for iteration in range(100):  # max iterations for convergence
        new_prob = prob.copy()

        for state_idx in states:
            if state_idx in target_states:
                continue

            # Get transitions from this state
            graph = scgs.get_graph()
            if state_idx >= len(graph):
                continue

            transitions = graph[state_idx]
            total_prob = 0.0
            total_weight = 0.0

            for next_state_idx, action in enumerate(transitions):
                if action == 0 or action == '*':
                    continue

                # Get transition probability
                trans_prob = scgs.get_transition_probability(
                    state_idx, str(action), next_state_idx)

                # If not explicitly set, use equal distribution
                if trans_prob == 0.0:
                    trans_prob = 1.0

                total_prob += trans_prob * prob[next_state_idx]
                total_weight += trans_prob

            # Normalize
            if total_weight > 0:
                new_prob[state_idx] = total_prob / total_weight
            else:
                new_prob[state_idx] = 0.0

        prob = new_prob

    # Return states meeting probability threshold
    result = set()
    for state_idx, p in prob.items():
        if comparison == '>=':
            if p >= threshold:
                result.add(state_idx)
        elif comparison == '<=':
            if p <= threshold:
                result.add(state_idx)
        elif comparison == '>':
            if p > threshold:
                result.add(state_idx)
        elif comparison == '<':
            if p < threshold:
                result.add(state_idx)

    return result
