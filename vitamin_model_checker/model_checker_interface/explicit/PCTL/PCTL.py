from binarytree import Node
from vitamin_model_checker.logics.PCTL import verifyPCTL, do_parsingPCTL
from vitamin_model_checker.models.SCGS.SCGS import *

# -------------------------------
# FUNZIONI DI SUPPORTO E UTILITÀ # SUPPORT FUNCTIONS AND UTILITIES
# -------------------------------


def get_states_prop_holds(scgs, prop):
    """
    Restituisce l'insieme degli stati in cui la proposizione prop è vera.
    Returns the set of states in which the proposition prop is true.
    """
    states = set()
    prop_matrix = scgs.get_matrix_proposition()
    index = scgs.get_atom_index(prop)
    if index is None:
        return None
    for state, row in enumerate(prop_matrix):
        if row[int(index)] == 1:
            states.add(state)
    return states


def convert_state_set(scgs, state_set):
    """
    Converte un insieme di nomi di stati (es. {"s1", "s2"}) nel corrispondente insieme di indici.
    Converts a set of state names (e.g. {"s1", "s2"}) into the corresponding set of indices.
    """
    states = set()
    for elem in state_set:
        position = scgs.get_index_by_state_name(elem)
        states.add(int(position))
    return states


def string_to_set(string):
    """
    Converte una stringa rappresentante un insieme (es. "{s1, s2}") in un oggetto set.
    Converts a string representing a set (e.g. "{s1, s2}") into a set object.
    """
    if string == 'set()':
        return set()
    set_list = string.strip("{}").split(", ")
    new_string = "{" + ", ".join(set_list) + "}"
    return eval(new_string)


def build_tree(scgs, tpl):
    """
    Costruisce ricorsivamente l'albero della formula (di tipo binary tree).
    Se il nodo è un atomo, si sostituisce il nodo con la stringa dell'insieme degli stati
    in cui l'atomo è vero.
    Recursively constructs the formula tree (binary tree type).
    If the node is an atom, replace the node with the string of the set of states
    in which the atom is true.
    """
    if isinstance(tpl, tuple):
        root = Node(tpl[0])
        if len(tpl) > 1:
            left_child = build_tree(scgs, tpl[1])
            if left_child is None:
                return None
            root.left = left_child
            if len(tpl) > 2:
                right_child = build_tree(scgs, tpl[2])
                if right_child is None:
                    return None
                root.right = right_child
    else:
        # Nodo atomico: costruisce il set degli stati dove la proposizione è vera.
        states = set()
        states_proposition = get_states_prop_holds(scgs, str(tpl))
        if states_proposition is None:
            return None
        else:
            for element in states_proposition:
                # converti sempre in Python-str
                state_name = str(scgs.get_state_name_by_index(element))
                states.add(state_name)
            root = Node(str(states))
    return root

# ---------------------------------------------------------
# FUNZIONI PER IL CALCOLO DELLE PRE-IMMAGINI (SCTL)
# FUNCTIONS FOR CALCULATING PRE-IMAGES (SCTL)
# ---------------------------------------------------------


def pre_image_exist(transitions, list_holds_p):
    """
    Calcola la pre-immagine esistenziale:
    Restituisce l'insieme degli stati s tali che esista una transizione (s,t)
    con t appartenente a list_holds_p.
    Computes the existential pre-image:
    Returns the set of states s such that there exists a transition (s,t)
    with t belonging to list_holds_p.
    """
    pre_list = set()
    for state in list(list_holds_p):
        # Per ogni stato t in list_holds_p, si raccolgono tutti gli s tali che (s,t) è una transizione
        predecessors = {s for (s, t) in transitions if t == state}
        pre_list.update(predecessors)
    return pre_list


def pre_image_all(transitions, states_set, holds_p):
    """
    Calcola la pre-immagine universale (AX):
    Restituisce gli stati in states_set per i quali, se lo stato ha dei successori,
    tutti i successori appartengono a holds_p.
    (Per deadlock, si assume che AX sia vera.)
    Compute the universal preimage (AX):
    Returns the states in states_set for which, if the state has successors,
    all successors belong to holds_p.
    (For deadlocks, AX is assumed to be true.)
    """
    pre_states = set()
    for state in states_set:
        # Raccolgo i successori di 'state'
        successors = {t for (s, t) in transitions if s == state}
        if not successors or successors.issubset(holds_p):
            pre_states.add(state)
    return pre_states


def pre_release_A(cgs, holds_phi, holds_psi):
    """
    Calcola A(φ R ψ) attraverso il massimo fixpoint.
    Restituisce l'insieme dei stati in cui vale A(φ R ψ),
    cioè gli stati s tali che:
      - s soddisfa ψ, e
      - se s non soddisfa φ, allora ogni successore di s appartiene al fixpoint.

    Computes A(φ R ψ) through the maximum fixpoint.
    Returns the set of states where A(φ R ψ) holds,
    that is, the states s such that:
    - s satisfies ψ, and
    - if s does not satisfy φ, then every successor of s belongs to the fixpoint.
    """
    all_states = set(cgs.get_states())
    # Inizialmente, il risultato (fixpoint) è dato dagli stati che soddisfano ψ.
    result = holds_psi.copy()
    transitions = cgs.get_edges()
    while True:
        new_result = set()
        for s in all_states:
            if s in holds_psi:
                # Controllo: se s soddisfa φ oppure tutti i successori di s (se esistenti)
                # sono già in result, allora s entra in new_result.
                successors = {t for (s_, t) in transitions if s_ == s}
                if (s in holds_phi) or (not successors) or (successors.issubset(result)):
                    new_result.add(s)
        if new_result == result:
            break
        result = new_result
    return result

# ------------------------------
# FUNZIONE DI RISOLUZIONE DELL'ALBERO
# TREE RESOLUTION FUNCTION
# ------------------------------


def solve_tree(cgs, node):
    """
    Risolve ricorsivamente l'albero della formula in base all'operatore.
    La soluzione viene memorizzata in node.value, che contiene la stringa
    rappresentante l'insieme degli stati in cui la formula è vera.

    Recursively solves the formula tree based on the operator.
    The solution is stored in node.value, which contains the string
    representing the set of states in which the formula is true.
    """
    # Old CTL code removed - using new check_ctl_formula() instead

# -------------------------------------
# FUNZIONE DI MODEL CHECKING (CTL)
# -------------------------------------


def verify_initial_state(initial_state, result_str):
    """
    Verifica se lo stato iniziale è incluso nell'insieme risultante (espresso come stringa).
    """
    return str(initial_state) in result_str


def model_checking(formula, filename):
    """
    PCTL model checking following the standard pattern (formula, filename).
    Instantiates SCGS internally to match capCGS/costCGS architecture.
    """
    if not formula.strip():
        result = {
            'satisfiable': False,
            'states': set(),
            'initial_state_result': False
        }
        return result

    # Instantiate SCGS model internally (matching capCGS/costCGS pattern)
    scgs = SCGS()
    scgs.read_file(filename)

    # Parse formula
    parsed_formula = do_parsingPCTL(formula)

    # Check if formula contains probability operator
    if is_probability_formula(parsed_formula):
        result_states = check_probability_formula(scgs, parsed_formula)
    else:
        # Fall back to CTL checking
        result_states = check_ctl_formula(scgs, parsed_formula)

    # Check initial state
    initial_state = scgs.get_initial_state()
    try:
        initial_state_idx = scgs.get_index_by_state_name(initial_state)
    except:
        initial_state_idx = 0

    is_satisfied = initial_state_idx in result_states if result_states else False

    return {
        'satisfiable': is_satisfied,
        'states': result_states,
        'initial_state_result': is_satisfied
    }


def pre_image_prob_exist(scgs, list_holds_p, threshold, comparison):
    """
    Existential probabilistic pre-image.
    Returns states s where probability of reaching list_holds_p meets threshold.
    E.g., P>=0.5 (F goal)
    """
    pre_list = set()
    for state in scgs.get_states():
        # Compute probability of reaching list_holds_p from this state
        prob = compute_reachability_prob(scgs, state, list_holds_p)

        if comparison == '>=':
            if prob >= threshold:
                pre_list.add(state)
        elif comparison == '<=':
            if prob <= threshold:
                pre_list.add(state)
        elif comparison == '>':
            if prob > threshold:
                pre_list.add(state)
        elif comparison == '<':
            if prob < threshold:
                pre_list.add(state)
    return pre_list


def compute_reachability_prob(scgs, source_state, target_states):
    """
    Compute probability of reaching target_states from source_state.
    Use iterative method or value iteration.
    """
    states = scgs.get_states()
    n = len(states)

    # Initialize probabilities
    prob = {state: 0.0 for state in range(n)}

    # Target states have probability 1.0
    for target in target_states:
        prob[target] = 1.0

    # Value iteration
    for _ in range(100):  # convergence iterations
        new_prob = prob.copy()
        for state in range(n):
            if state in target_states:
                continue

            # Sum over all transitions from this state
            total_prob = 0.0
            transitions = scgs.get_outgoing_transitions(state)

            for next_state, action, transition_prob in transitions:
                total_prob += transition_prob * prob[next_state]

            new_prob[state] = total_prob

        prob = new_prob

    return prob[source_state]


def is_probability_formula(formula):
    """Check if formula contains P operator"""
    if isinstance(formula, tuple):
        if formula and formula[0]:
            return str(formula[0]).startswith('P')
    return False


def check_ctl_formula(scgs, formula):
    """
    Evaluate CTL-style formulas recursively.
    Handles: atomic propositions, logical operators (|, &, ¬), 
    and temporal operators (F, G, X, U, R)
    """
    if isinstance(formula, str):
        # Atomic proposition
        return get_states_prop_holds(scgs, formula)

    elif isinstance(formula, tuple) and len(formula) > 0:
        operator = formula[0]

        # Logical operators
        if operator == '|':  # OR
            left = check_ctl_formula(scgs, formula[1])
            right = check_ctl_formula(scgs, formula[2])
            return left.union(right) if left and right else (left or right or set())

        elif operator == '&':  # AND
            left = check_ctl_formula(scgs, formula[1])
            right = check_ctl_formula(scgs, formula[2])
            return left.intersection(right) if left and right else set()

        elif operator == '¬' or operator == 'NOT':  # NOT
            subformula_states = check_ctl_formula(scgs, formula[1])
            all_states = set(scgs.get_states())
            if subformula_states is None:
                return all_states
            return all_states - subformula_states

        # Temporal operators
        elif operator == 'F':  # Eventually (F)
            # States that can reach the goal states
            goal_states = check_ctl_formula(scgs, formula[1])
            if not goal_states:
                return set()
            return compute_eventually(scgs, goal_states)

        elif operator == 'G':  # Globally (G)
            # States where the property always holds on all paths
            goal_states = check_ctl_formula(scgs, formula[1])
            if not goal_states:
                return set()
            return compute_globally(scgs, goal_states)

        elif operator == 'X':  # Next (X)
            # States with a successor in the goal set
            goal_states = check_ctl_formula(scgs, formula[1])
            if not goal_states:
                return set()
            return compute_next(scgs, goal_states)

        elif operator in ('U', 'UNTIL'):  # Until (U)
            left_states = check_ctl_formula(scgs, formula[1])
            right_states = check_ctl_formula(scgs, formula[2])
            return compute_until(scgs, left_states, right_states)

        elif operator in ('R', 'RELEASE'):  # Release (R)
            left_states = check_ctl_formula(scgs, formula[1])
            right_states = check_ctl_formula(scgs, formula[2])
            return compute_release(scgs, left_states, right_states)

    return set()


def compute_eventually(scgs, goal_states):
    """Compute states that can eventually reach goal_states (E F goal)"""
    # Use backward reachability: states from which goal_states is reachable
    states = set(scgs.get_states())
    can_reach = set(goal_states)
    prev_size = -1

    # Fixed-point iteration
    while len(can_reach) != prev_size:
        prev_size = len(can_reach)
        for state in states:
            if state not in can_reach:
                # Check if this state has a successor in can_reach
                transitions = scgs.get_outgoing_transitions(state)
                for next_state, action, prob in transitions:
                    if next_state in can_reach:
                        can_reach.add(state)
                        break

    return can_reach


def compute_globally(scgs, goal_states):
    """Compute states where goal_states always holds (E G goal)"""
    # States from which all reachable states satisfy the property
    states = set(scgs.get_states())
    must_hold = set(goal_states)

    # Iteratively remove states that can reach non-goal states
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for state in must_hold:
            transitions = scgs.get_outgoing_transitions(state)
            for next_state, action, prob in transitions:
                if next_state not in must_hold:
                    to_remove.add(state)
                    changed = True
                    break
        must_hold = must_hold - to_remove

    return must_hold


def compute_next(scgs, goal_states):
    """Compute states with a successor in goal_states (E X goal)"""
    states_with_next = set()
    all_states = set(scgs.get_states())

    for state in all_states:
        transitions = scgs.get_outgoing_transitions(state)
        for next_state, action, prob in transitions:
            if next_state in goal_states:
                states_with_next.add(state)
                break

    return states_with_next


def compute_until(scgs, left_states, right_states):
    """Compute E(left U right): states where left holds until right holds"""
    # Reach right_states with left holding on the path
    all_states = set(scgs.get_states())
    can_reach = set(right_states)
    prev_size = -1

    while len(can_reach) != prev_size:
        prev_size = len(can_reach)
        for state in all_states:
            if state not in can_reach and state in left_states:
                transitions = scgs.get_outgoing_transitions(state)
                for next_state, action, prob in transitions:
                    if next_state in can_reach:
                        can_reach.add(state)
                        break

    return can_reach


def compute_release(scgs, left_states, right_states):
    """Compute E(left R right): states where right holds until both left and right hold"""
    # right must hold, can stay in right until left becomes true
    all_states = set(scgs.get_states())
    can_sustain = set(right_states)
    prev_size = -1

    while len(can_sustain) != prev_size:
        prev_size = len(can_sustain)
        for state in all_states:
            if state not in can_sustain and state in right_states:
                transitions = scgs.get_outgoing_transitions(state)
                if all_valid := all(
                    next_state in can_sustain or next_state in left_states
                    for next_state, action, prob in transitions
                ):
                    if transitions:  # Only if there are transitions
                        can_sustain.add(state)

    return can_sustain


def check_probability_formula(scgs, formula):
    """Parse and check P>=x, P<=x, P>x, P<x formulas"""
    operator, comparison, threshold, subformula = parse_probability_formula(
        formula)

    # Get states satisfying subformula
    subformula_states = check_ctl_formula(scgs, subformula)

    # Compute reachability probabilities
    return pre_image_prob_exist(scgs, subformula_states, float(threshold), comparison)


def parse_probability_formula(formula):
    """Extract P operator details"""
    # Example: ('P>=0.5', ('F', 'goal'))
    prob_op = formula[0]  # 'P>=0.5'
    subformula = formula[1]

    # Parse 'P>=0.5'
    import re
    match = re.match(r'P(>=|<=|>|<)(\d+\.?\d*)', prob_op)
    if match is None:
        # Fallback default values if regex doesn't match
        return 'P', '>=', '0.5', subformula

    comparison = match.group(1)
    threshold = match.group(2)

    return 'P', comparison, threshold, subformula
