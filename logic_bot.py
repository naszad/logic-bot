import itertools
import sys
import os
import argparse  # Add argument parser for better command line options
import visualizer  # Import our new visualizer module

# --- AST Construction and Evaluation ---

class Node:
    def __init__(self, node_type, value=None, left=None, right=None):
        self.type = node_type  # 'var', 'not', 'and', 'or', 'implies'
        self.value = value     # For variables (e.g., 'p', 'q')
        self.left = left       # Left subtree
        self.right = right     # Right subtree

def tokenize(expr):
    tokens = []
    i = 0
    while i < len(expr):
        if expr[i].isspace():
            i += 1
        elif expr[i] in ['(', ')', '!', '&', '|']:
            tokens.append(expr[i])
            i += 1
        elif expr[i] == '-' and i+2 < len(expr) and expr[i:i+3] == '-->':
            tokens.append('-->')
            i += 3
        elif expr[i].isalpha():
            tokens.append(expr[i])
            i += 1
        else:
            raise ValueError(f"Invalid character '{expr[i]}' in expression.")
    return tokens

def parse(tokens):
    def parse_expression(index):
        node, index = parse_implication(index)
        return node, index

    def parse_implication(index):
        left, index = parse_disjunction(index)
        while index < len(tokens) and tokens[index] == '-->':
            index += 1
            right, index = parse_implication(index)  # Right-associative
            left = Node('implies', left=left, right=right)
        return left, index

    def parse_disjunction(index):
        left, index = parse_conjunction(index)
        while index < len(tokens) and tokens[index] == '|':
            index += 1
            right, index = parse_conjunction(index)
            left = Node('or', left=left, right=right)
        return left, index

    def parse_conjunction(index):
        left, index = parse_negation(index)
        while index < len(tokens) and tokens[index] == '&':
            index += 1
            right, index = parse_negation(index)
            left = Node('and', left=left, right=right)
        return left, index

    def parse_negation(index):
        if tokens[index] == '!':
            index += 1
            child, index = parse_negation(index)
            return Node('not', left=child), index
        else:
            return parse_atom(index)

    def parse_atom(index):
        if tokens[index] == '(':
            index += 1
            node, index = parse_expression(index)
            if index >= len(tokens) or tokens[index] != ')':
                raise ValueError("Missing closing parenthesis.")
            index += 1
            return node, index
        elif tokens[index].isalpha():
            node = Node('var', value=tokens[index])
            index += 1
            return node, index
        else:
            raise ValueError("Unexpected token during parsing.")

    node, index = parse_expression(0)
    if index != len(tokens):
        raise ValueError("Extra tokens remaining after parsing.")
    return node

def evaluate(node, assignment):
    if node.type == 'var':
        return assignment[node.value]
    elif node.type == 'not':
        return not evaluate(node.left, assignment)
    elif node.type == 'and':
        return evaluate(node.left, assignment) and evaluate(node.right, assignment)
    elif node.type == 'or':
        return evaluate(node.left, assignment) or evaluate(node.right, assignment)
    elif node.type == 'implies':
        return (not evaluate(node.left, assignment)) or evaluate(node.right, assignment)
    else:
        raise ValueError("Unknown node type.")

def get_vars(node):
    if node.type == 'var':
        return {node.value}
    elif node.type == 'not':
        return get_vars(node.left)
    elif node.type in ['and', 'or', 'implies']:
        return get_vars(node.left) | get_vars(node.right)
    else:
        return set()

def ast_to_string(node):
    if node.type == 'var':
        return node.value
    elif node.type == 'not':
        return "!" + ast_to_string(node.left)
    elif node.type == 'and':
        return f"({ast_to_string(node.left)} & {ast_to_string(node.right)})"
    elif node.type == 'or':
        return f"({ast_to_string(node.left)} | {ast_to_string(node.right)})"
    elif node.type == 'implies':
        return f"({ast_to_string(node.left)} --> {ast_to_string(node.right)})"
    else:
        return ""

def equal_ast(n1, n2):
    if n1.type != n2.type:
        return False
    if n1.type == 'var':
        return n1.value == n2.value
    if n1.type == 'not':
        return equal_ast(n1.left, n2.left)
    return equal_ast(n1.left, n2.left) and equal_ast(n1.right, n2.right)

def ast_complexity(node):
    if node.type == 'var':
        return 1
    elif node.type == 'not':
        return 1 + ast_complexity(node.left)
    else:
        return 1 + ast_complexity(node.left) + ast_complexity(node.right)

# --- Replacement (Rewrite) Functions ---
# Here we sketch some replacement rules. In practice these could be applied exhaustively.

def replace_material_implication(node):
    # A --> B  is equivalent to  !A | B
    if node.type == 'implies':
        return Node('or', left=Node('not', left=node.left), right=node.right)
    return node

def replace_double_negation(node):
    # !!A  becomes A
    if node.type == 'not' and node.left.type == 'not':
        return node.left.left
    return node

def replace_de_morgan(node):
    # ! (A & B) becomes (!A | !B) and similarly for or.
    if node.type == 'not':
        if node.left.type == 'and':
            return Node('or', left=Node('not', left=node.left.left), right=Node('not', left=node.left.right))
        if node.left.type == 'or':
            return Node('and', left=Node('not', left=node.left.left), right=Node('not', left=node.left.right))
    return node

# (Other replacement functions for associativity, commutativity, distributivity, transposition,
# exportation, etc. can be defined similarly.)

def apply_replacement_rules(node):
    # Try to rewrite the node using one of the replacement rules.
    new_node = replace_material_implication(node)
    new_node = replace_double_negation(new_node)
    new_node = replace_de_morgan(new_node)
    # (Extend with additional replacements as desired.)
    return new_node

def rule_replacement(conclusion, premises, visited, depth, max_depth, parent_id=None):
    # Try to replace the conclusion with an equivalent formula.
    rewritten = apply_replacement_rules(conclusion)
    if not equal_ast(rewritten, conclusion):
        subproof = recursive_proof(rewritten, premises, visited.copy(), depth+1, max_depth, parent_id)
        if subproof is not None:
            return subproof + [f"By replacement, rewrite {ast_to_string(conclusion)} as {ast_to_string(rewritten)}"]
    return None

# --- Inference Rule Implementations ---

def rule_direct(conclusion, premises, visited, depth, max_depth, parent_id=None):
    for p in premises:
        if equal_ast(p, conclusion):
            return [f"Premise: {ast_to_string(conclusion)}"]
    return None

def rule_modus_ponens(conclusion, premises, visited, depth, max_depth, parent_id=None):
    for p in premises:
        if p.type == 'implies' and equal_ast(p.right, conclusion):
            subproof = recursive_proof(p.left, premises, visited.copy(), depth+1, max_depth, parent_id)
            if subproof is not None:
                return subproof + [f"Modus Ponens on {ast_to_string(p)} yields {ast_to_string(conclusion)}"]
    return None

def rule_implication_introduction(conclusion, premises, visited, depth, max_depth, parent_id=None):
    # Conditional proof: If conclusion is (A --> B), assume A and try to derive B.
    if conclusion.type == 'implies':
        new_premises = premises + [conclusion.left]
        subproof = recursive_proof(conclusion.right, new_premises, visited.copy(), depth+1, max_depth, parent_id)
        if subproof is not None:
            return subproof + [f"Implication Introduction yields {ast_to_string(conclusion)}"]
    return None

def rule_modus_tollens(conclusion, premises, visited, depth, max_depth, parent_id=None):
    if conclusion.type == 'not':
        A = conclusion.left
        for p in premises:
            if p.type == 'implies' and equal_ast(p.left, A):
                negB = Node('not', left=p.right)
                subproof = recursive_proof(negB, premises, visited.copy(), depth+1, max_depth, parent_id)
                if subproof is not None:
                    return subproof + [f"Modus Tollens on {ast_to_string(p)} yields {ast_to_string(conclusion)}"]
    return None

def rule_disjunctive_syllogism(conclusion, premises, visited, depth, max_depth, parent_id=None):
    for p in premises:
        if p.type == 'or':
            neg_left = Node('not', left=p.left)
            subproof = recursive_proof(neg_left, premises, visited.copy(), depth+1, max_depth, parent_id)
            if subproof is not None and equal_ast(p.right, conclusion):
                return subproof + [f"Disjunctive Syllogism on {ast_to_string(p)} with {ast_to_string(neg_left)} yields {ast_to_string(conclusion)}"]
            neg_right = Node('not', left=p.right)
            subproof = recursive_proof(neg_right, premises, visited.copy(), depth+1, max_depth, parent_id)
            if subproof is not None and equal_ast(p.left, conclusion):
                return subproof + [f"Disjunctive Syllogism on {ast_to_string(p)} with {ast_to_string(neg_right)} yields {ast_to_string(conclusion)}"]
    return None

def rule_disjunction_elimination(conclusion, premises, visited, depth, max_depth, parent_id=None):
    # Disjunction Elimination (Proof by cases):
    # If we have A ∨ B and from A we can derive conclusion and from B we can derive conclusion.
    for p in premises:
        if p.type == 'or':
            subproof1 = recursive_proof(conclusion, premises + [p.left], visited.copy(), depth+1, max_depth, parent_id)
            subproof2 = recursive_proof(conclusion, premises + [p.right], visited.copy(), depth+1, max_depth, parent_id)
            if subproof1 is not None and subproof2 is not None:
                return subproof1 + subproof2 + [f"Disjunction Elimination on {ast_to_string(p)} yields {ast_to_string(conclusion)}"]
    return None

def rule_conj_intro(conclusion, premises, visited, depth, max_depth, parent_id=None):
    if conclusion.type == 'and':
        subproof_left = recursive_proof(conclusion.left, premises, visited.copy(), depth+1, max_depth, parent_id)
        subproof_right = recursive_proof(conclusion.right, premises, visited.copy(), depth+1, max_depth, parent_id)
        if subproof_left is not None and subproof_right is not None:
            return subproof_left + subproof_right + [f"Conjunction Introduction yields {ast_to_string(conclusion)}"]
    return None

def rule_conj_elim(conclusion, premises, visited, depth, max_depth, parent_id=None):
    for p in premises:
        if p.type == 'and':
            if equal_ast(p.left, conclusion):
                return [f"Conjunction Elimination on {ast_to_string(p)} yields {ast_to_string(conclusion)}"]
            if equal_ast(p.right, conclusion):
                return [f"Conjunction Elimination on {ast_to_string(p)} yields {ast_to_string(conclusion)}"]
    return None

def rule_disj_intro(conclusion, premises, visited, depth, max_depth, parent_id=None):
    if conclusion.type == 'or':
        subproof = recursive_proof(conclusion.left, premises, visited.copy(), depth+1, max_depth, parent_id)
        if subproof is not None:
            return subproof + [f"Disjunction Introduction yields {ast_to_string(conclusion)}"]
        subproof = recursive_proof(conclusion.right, premises, visited.copy(), depth+1, max_depth, parent_id)
        if subproof is not None:
            return subproof + [f"Disjunction Introduction yields {ast_to_string(conclusion)}"]
    return None

def rule_hypothetical_syllogism(conclusion, premises, visited, depth, max_depth, parent_id=None):
    if conclusion.type == 'implies':
        A = conclusion.left
        C = conclusion.right
        for p in premises:
            if p.type == 'implies' and equal_ast(p.left, A):
                B = p.right
                for q in premises:
                    if q.type == 'implies' and equal_ast(q.left, B) and equal_ast(q.right, C):
                        return [f"Hypothetical Syllogism on {ast_to_string(p)} and {ast_to_string(q)} yields {ast_to_string(conclusion)}"]
    return None

def rule_double_neg_elim(conclusion, premises, visited, depth, max_depth, parent_id=None):
    if conclusion.type != 'not':
        double_neg = Node('not', left=Node('not', left=conclusion))
        subproof = recursive_proof(double_neg, premises, visited.copy(), depth+1, max_depth, parent_id)
        if subproof is not None:
            return subproof + [f"Double Negation Elimination yields {ast_to_string(conclusion)}"]
    return None

def rule_constructive_dilemma(conclusion, premises, visited, depth, max_depth, parent_id=None):
    # Constructive dilemma:
    # From (A --> C), (B --> D) and (A ∨ B), infer (C ∨ D).
    if conclusion.type == 'or':
        for p in premises:
            if p.type == 'implies':
                for q in premises:
                    if q.type == 'implies':
                        for r in premises:
                            if r.type == 'or':
                                C, D = p.right, q.right
                                if equal_ast(Node('or', left=C, right=D), conclusion):
                                    # Check that r is either A ∨ B matching the antecedents of p and q.
                                    return [f"Constructive Dilemma using {ast_to_string(p)}, {ast_to_string(q)} and {ast_to_string(r)} yields {ast_to_string(conclusion)}"]
    return None

def rule_destructive_dilemma(conclusion, premises, visited, depth, max_depth, parent_id=None):
    # Destructive dilemma:
    # From (p --> q), (r --> s), !q | !s, infer !p | !r.
    # And variations of this pattern.
    
    if conclusion.type == 'not':
        # Check if we're trying to prove !p
        for p in premises:
            if p.type == 'or' and p.left.value == conclusion.left.value:
                # We have p | v premise
                v = p.right.value
                
                # Look for p --> (q & r) and v --> (q & r)
                impl_p = None
                impl_v = None
                for prem in premises:
                    if prem.type == 'implies':
                        if prem.left.type == 'var' and prem.left.value == conclusion.left.value:
                            impl_p = prem
                        if prem.left.type == 'var' and prem.left.value == v:
                            impl_v = prem
                
                if impl_p and impl_v:
                    # Check if both implications lead to a contradiction
                    # First, try to derive a contradiction from p
                    contradiction_from_p = False
                    subproof = recursive_proof(Node('var', value='contradiction'), 
                                              premises + [conclusion.left], 
                                              visited.copy(), depth+1, max_depth, parent_id)
                    if subproof is not None:
                        contradiction_from_p = True
                    
                    # Then, try to derive a contradiction from v
                    contradiction_from_v = False
                    subproof = recursive_proof(Node('var', value='contradiction'), 
                                              premises + [Node('var', value=v)], 
                                              visited.copy(), depth+1, max_depth, parent_id)
                    if subproof is not None:
                        contradiction_from_v = True
                    
                    if contradiction_from_p and contradiction_from_v:
                        return [f"By Destructive Dilemma, since both {conclusion.left.value} and {v} lead to contradiction, " +
                               f"conclude {ast_to_string(conclusion)}"]
    
    return None

def rule_absorption(conclusion, premises, visited, depth, max_depth, parent_id=None):
    # Absorption: From A --> B, infer A --> (A & B).
    if conclusion.type == 'implies' and conclusion.right.type == 'and':
        A = conclusion.left
        if equal_ast(conclusion.left, conclusion.right.left):
            for p in premises:
                if p.type == 'implies' and equal_ast(p, Node('implies', left=A, right=conclusion.right.right)):
                    return [f"Absorption applied on {ast_to_string(p)} yields {ast_to_string(conclusion)}"]
    return None

def rule_negation_introduction(conclusion, premises, visited, depth, max_depth, parent_id=None):
    # Negation introduction (proof by contradiction):
    # If assuming A yields a contradiction, then infer ¬A.
    if conclusion.type == 'not':
        A = conclusion.left
        # Here we simulate contradiction by checking if both some B and !B can be derived.
        subproof1 = recursive_proof(Node('var', value="contradiction"), premises + [A], visited.copy(), depth+1, max_depth, parent_id)
        subproof2 = recursive_proof(Node('var', value="contradiction"), premises + [Node('not', left=A)], visited.copy(), depth+1, max_depth, parent_id)
        if subproof1 is not None and subproof2 is not None:
            return subproof1 + subproof2 + [f"Negation Introduction yields {ast_to_string(conclusion)}"]
    return None

def create_contradiction_node():
    """Create a node representing a contradiction (P & !P)"""
    var = Node('var', value='p')
    return Node('and', left=var, right=Node('not', left=var))

def rule_contradiction_detection(conclusion, premises, visited, depth, max_depth, parent_id=None):
    """Detect if premises contain or imply a contradiction"""
    # Look for direct contradictions in premises
    for p in premises:
        if p.type == 'and' and p.right.type == 'not' and equal_ast(p.left, p.right.left):
            return [f"Contradiction detected: {ast_to_string(p)}"]
        if p.type == 'and' and p.left.type == 'not' and equal_ast(p.right, p.left.left):
            return [f"Contradiction detected: {ast_to_string(p)}"]
            
    # Check if premises contain p and !p for some variable
    var_and_negations = {}
    for p in premises:
        if p.type == 'var':
            var_and_negations[p.value] = True
        elif p.type == 'not' and p.left.type == 'var':
            var_value = p.left.value
            if var_value in var_and_negations:
                return [f"Contradiction detected: both {var_value} and !{var_value} are true"]
    
    # Check if u and !u can be derived
    for p in premises:
        if p.type == 'not':
            # If !u is a premise and we can derive u, that's a contradiction
            u = p.left
            subproof = recursive_proof(u, premises, visited.copy(), depth+1, max_depth, parent_id)
            if subproof is not None:
                return subproof + [f"Contradiction: derived {ast_to_string(u)} but {ast_to_string(p)} is a premise"]
    
    return None

def rule_proof_by_cases(conclusion, premises, visited, depth, max_depth, parent_id=None):
    """Enhanced proof by cases (disjunction elimination)
    If we have A | B and can prove C from both A and from B, we can conclude C"""
    for p in premises:
        if p.type == 'or':
            A, B = p.left, p.right
            
            # Try to prove conclusion from A
            subproof_A = recursive_proof(conclusion, premises + [A], visited.copy(), depth+1, max_depth, parent_id)
            
            # Try to prove conclusion from B
            subproof_B = recursive_proof(conclusion, premises + [B], visited.copy(), depth+1, max_depth, parent_id)
            
            if subproof_A is not None and subproof_B is not None:
                steps = []
                steps.append(f"Case analysis on {ast_to_string(p)}:")
                steps.append(f"Case 1: Assume {ast_to_string(A)}")
                steps.extend(subproof_A)
                steps.append(f"Case 2: Assume {ast_to_string(B)}")
                steps.extend(subproof_B)
                steps.append(f"By proof by cases, conclude {ast_to_string(conclusion)}")
                return steps
    return None

def rule_proof_by_contradiction(conclusion, premises, visited, depth, max_depth, parent_id=None):
    """Enhanced proof by contradiction
    If assuming the negation of our conclusion leads to a contradiction, 
    then the conclusion is proved"""
    
    # For non-negation conclusions, negate them first
    if conclusion.type != 'not':
        neg_conclusion = Node('not', left=conclusion)
        
        # Try to derive a contradiction from negated conclusion
        contradiction = create_contradiction_node()
        subproof = recursive_proof(contradiction, premises + [neg_conclusion], visited.copy(), depth+1, max_depth, parent_id)
        
        if subproof is not None:
            return subproof + [f"By proof by contradiction, conclude {ast_to_string(conclusion)}"]
    
    # For negation conclusions like !p, assume p and try to derive a contradiction
    if conclusion.type == 'not':
        P = conclusion.left
        contradiction = create_contradiction_node()
        subproof = recursive_proof(contradiction, premises + [P], visited.copy(), depth+1, max_depth, parent_id)
        
        if subproof is not None:
            return subproof + [f"By proof by contradiction, conclude {ast_to_string(conclusion)}"]
    
    return None

# --- Rule List and Recursive Search ---

RULES = [
    rule_direct,
    rule_contradiction_detection,  # Check for contradictions first
    rule_proof_by_cases,  # Enhanced disjunction elimination
    rule_proof_by_contradiction,  # Enhanced proof by contradiction
    rule_modus_ponens,
    rule_implication_introduction,
    rule_modus_tollens,
    rule_disjunctive_syllogism,
    rule_disjunction_elimination,
    rule_conj_intro,
    rule_conj_elim,
    rule_disj_intro,
    rule_hypothetical_syllogism,
    rule_double_neg_elim,
    rule_constructive_dilemma,
    rule_destructive_dilemma,
    rule_absorption,
    rule_negation_introduction,
    rule_replacement  # Replacement rules are attempted last.
]

def recursive_proof(conclusion, premises, visited=None, depth=0, max_depth=10, parent_id=None):
    if visited is None:
        visited = set()
    if depth > max_depth:
        return None

    concl_str = ast_to_string(conclusion)
    if concl_str in visited:
        return None
    visited.add(concl_str)
    
    # Create node ID for current proof attempt
    current_node_id = visualizer.track_proof_step(concl_str, "Attempt", None, depth, parent_id)
    
    for rule in RULES:
        rule_name = rule.__name__.replace('rule_', '')
        rule_node_id = visualizer.track_proof_step(concl_str, rule_name, None, depth, current_node_id)
        
        # Try the rule
        result = rule(conclusion, premises, visited.copy(), depth, max_depth, rule_node_id)
        
        # Update the visualization with the result
        visualizer.proof_trace['node_attributes'][rule_node_id]['result'] = (result is not None)
        
        if result is not None:
            # Mark the attempt as successful
            visualizer.proof_trace['node_attributes'][current_node_id]['result'] = True
            return result
    
    # For compound conclusions, try decomposing into subgoals ordered by complexity.
    if conclusion.type in ['and', 'or', 'implies']:
        subgoals = []
        if conclusion.type == 'and':
            subgoals = [conclusion.left, conclusion.right]
        elif conclusion.type == 'or':
            subgoals = [conclusion.left, conclusion.right]
        elif conclusion.type == 'implies':
            subgoals = [conclusion.left, conclusion.right]
        
        # Track decomposition step
        decomp_id = visualizer.track_proof_step(concl_str, "Decomposition", None, depth, current_node_id)
        
        subgoals = sorted(subgoals, key=ast_complexity)
        steps = []
        success = True
        
        for sg in subgoals:
            subproof = recursive_proof(sg, premises, visited.copy(), depth+1, max_depth, decomp_id)
            if subproof is None:
                success = False
                break
            steps += subproof
        
        # Update the decomposition result
        visualizer.proof_trace['node_attributes'][decomp_id]['result'] = success
        
        if success:
            # Mark the attempt as successful
            visualizer.proof_trace['node_attributes'][current_node_id]['result'] = True
            steps.append(f"Combined subgoals yield {ast_to_string(conclusion)}")
            return steps
    
    # Mark the attempt as failed
    visualizer.proof_trace['node_attributes'][current_node_id]['result'] = False
    return None

def derive_proof(premises_expr, conclusion_expr, max_depth=10, visualize=False, save_viz=None, animate=False):
    # Initialize visualization if requested
    if visualize:
        visualizer.initialize_trace()
    
    premises = [parse(tokenize(expr)) for expr in premises_expr]
    conclusion = parse(tokenize(conclusion_expr))
    
    steps = recursive_proof(conclusion, premises, max_depth=max_depth)
    
    # Generate visualization if requested
    if visualize:
        visualizer.visualize_proof_search(save_path=save_viz, animate=animate)
        visualizer.print_statistics()
    
    if steps is None:
        return "No proof found using the available inference rules within the maximum search depth."
    else:
        return "\n".join(steps)

def validate_argument(premises_expr, conclusion_expr):
    premise_trees = [parse(tokenize(expr)) for expr in premises_expr]
    conclusion_tree = parse(tokenize(conclusion_expr))
    vars_set = set()
    for tree in premise_trees:
        vars_set |= get_vars(tree)
    vars_set |= get_vars(conclusion_tree)
    vars_list = list(vars_set)
    for values in itertools.product([False, True], repeat=len(vars_list)):
        assignment = dict(zip(vars_list, values))
        if all(evaluate(tree, assignment) for tree in premise_trees):
            if not evaluate(conclusion_tree, assignment):
                return False
    return True

def import_from_file(file_path):
    """Import multiple proofs from a text file.
    Format:
    PROOF: optional proof name
    PREMISE: logical expression
    PREMISE: logical expression
    ...
    CONCLUSION: logical expression
    
    PROOF: next proof name
    ...
    
    Lines starting with # are treated as comments.
    """
    if not os.path.exists(file_path):
        print(f"Error: File '{file_path}' not found.")
        return []

    proofs = []
    current_premises = []
    current_conclusion = None
    current_name = "Unnamed Proof"
    
    try:
        with open(file_path, 'r') as file:
            for line in file:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                    
                if line.upper().startswith('PROOF:'):
                    # If we have a complete proof, save it before starting a new one
                    if current_premises and current_conclusion:
                        proofs.append((current_premises, current_conclusion, current_name))
                        # Reset for the next proof
                        current_premises = []
                        current_conclusion = None
                    
                    # Start a new proof
                    current_name = line[len('PROOF:'):].strip() or f"Proof {len(proofs) + 1}"
                
                elif line.upper().startswith('PREMISE:'):
                    expr = line[len('PREMISE:'):].strip()
                    current_premises.append(expr)
                    
                elif line.upper().startswith('CONCLUSION:'):
                    expr = line[len('CONCLUSION:'):].strip()
                    current_conclusion = expr
            
            # Add the last proof if it's complete
            if current_premises and current_conclusion:
                proofs.append((current_premises, current_conclusion, current_name))
                
    except Exception as e:
        print(f"Error reading file: {e}")
        return []
        
    if not proofs:
        print("Error: No valid proofs found in the file.")
        
    return proofs

def process_argument(premises, conclusion, name="", visualize=False, save_viz=None, animate=False):
    """Process a logical argument and display results."""
    if not premises or not conclusion:
        return
        
    print(f"\n---{name}---")
    print("Premises:", ", ".join(premises))
    print("Conclusion:", conclusion)
    
    valid = validate_argument(premises, conclusion)
    print("The argument is", "valid." if valid else "invalid.")
    
    print("\n--- Derivation Steps ---")
    
    # Increase max_depth for more complex proofs
    max_depth = 25
    if len(premises) > 5:  # For very complex proofs with many premises
        max_depth = 35
    
    proof_steps = derive_proof(premises, conclusion, max_depth=max_depth, visualize=visualize, save_viz=save_viz, animate=animate)
    print(proof_steps)
    
    # Print a separator line for readability
    print("\n" + "-" * 50)

# --- Example Usage ---

if __name__ == "__main__":
    # Set up command line argument parsing
    parser = argparse.ArgumentParser(description="Logic Bot - Logical Proof Assistant")
    parser.add_argument("file", nargs="?", help="File containing proofs to process")
    parser.add_argument("--visualize", action="store_true", help="Visualize the proof search process")
    parser.add_argument("--animate", action="store_true", help="Create step-by-step animation of the proof search")
    parser.add_argument("--save", metavar="FILE", help="Save visualization to file")
    parser.add_argument("--example", type=int, help="Run specific example (1-3)", choices=[1, 2, 3])
    
    args = parser.parse_args()
    
    # Process file if provided
    if args.file and os.path.exists(args.file):
        proofs = import_from_file(args.file)
        if proofs:
            for i, (premises, conclusion, name) in enumerate(proofs):
                # Generate unique filename for each proof if --save is used
                save_path = None
                if args.save:
                    base, ext = os.path.splitext(args.save)
                    if not ext:
                        ext = ".gif" if args.animate else ".png"
                    save_path = f"{base}_{i+1}{ext}"
                
                process_argument(premises, conclusion, name, args.visualize, save_path, args.animate)
        sys.exit(0)
    
    # Run examples if requested
    example_num = args.example if args.example else 0
    
    examples = [
        # Example 1
        {
            "premises": ["p --> q", "p"],
            "conclusion": "q",
            "name": "Example 1: Modus Ponens"
        },
        # Example 2
        {
            "premises": ["p --> q", "q --> r"],
            "conclusion": "p --> r",
            "name": "Example 2: Hypothetical Syllogism"
        },
        # Example 3
        {
            "premises": ["!p & q", "r --> p", "!r --> s", "s --> t"],
            "conclusion": "t",
            "name": "Example 3: Complex Reasoning"
        }
    ]
    
    # Run specific example if requested, otherwise run all
    if example_num:
        if 1 <= example_num <= len(examples):
            ex = examples[example_num - 1]
            save_path = args.save if args.save else None
            if args.save and args.animate and not save_path.lower().endswith(('.gif', '.mp4')):
                save_path += ".gif"
            process_argument(ex["premises"], ex["conclusion"], ex["name"], args.visualize, save_path, args.animate)
    else:
        # Run all examples
        for i, ex in enumerate(examples):
            # Generate unique filename for each example if --save is used
            save_path = None
            if args.save:
                base, ext = os.path.splitext(args.save)
                if not ext:
                    ext = ".gif" if args.animate else ".png"
                save_path = f"{base}_{i+1}{ext}"
            
            process_argument(ex["premises"], ex["conclusion"], ex["name"], args.visualize, save_path, args.animate)
