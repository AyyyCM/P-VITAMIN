import ply.lex as lex
import ply.yacc as yacc

# Tokens
tokens = (
    'LPAREN',
    'RPAREN',
    'AND',
    'OR',
    'NOT',
    'IMPLIES',
    'UNTIL',
    'GLOBALLY',
    'NEXT',
    'EVENTUALLY',
    'PROP',
    'FORALL',
    'EXIST',
    # PCTL tokens
    'PROB',
    'COMPARISON',
    'NUMBER'
)

# Regular expressions for tokens
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_AND = r'&&|\&|and'
t_OR = r'\|\||\||or'
t_NOT = r'!|not'
t_IMPLIES = r'->|>|implies'
t_PROP = r'[a-z]+'
t_UNTIL = r'U|until'
t_GLOBALLY = r'G|globally|always'
t_NEXT = r'X|next'
t_EVENTUALLY = r'F|eventually'
t_FORALL = r'A|forall'
t_EXIST = r'E|exist'
# PCTL tokens
t_PROB = r'P'
t_COMPARISON = r'<=|>=|<|>|=|!='
t_NUMBER = r'\d+\.?\d*'  # digit + optional . + infinate and none digits

# Token error handling


def t_error(t):
    # Raise an explicit error instead of silently skipping invalid characters
    raise SyntaxError(
        f"Illegal character {repr(t.value[0])} at position {t.lexpos}"
    )

# Grammar


def p_expression_binary(p):
    '''expression : expression AND expression
                  | expression OR expression
                  | expression IMPLIES expression'''
    p[0] = (p[2], p[1], p[3])


def p_expression_ternary(p):
    '''expression : FORALL expression UNTIL expression
                  | EXIST expression UNTIL expression'''
    p[0] = (p[1] + p[3], p[2], p[4])


def p_expression_unary(p):
    '''expression : FORALL GLOBALLY expression
                  | FORALL NEXT expression
                  | FORALL EVENTUALLY expression
                  | EXIST GLOBALLY expression
                  | EXIST NEXT expression
                  | EXIST EVENTUALLY expression'''
    p[0] = (p[1] + p[2], p[3])


def p_expression_not(p):
    '''expression : NOT expression'''
    p[0] = (p[1], p[2])


def p_expression_group(p):
    '''expression : LPAREN expression RPAREN'''
    p[0] = p[2]


def p_expression_prop(p):
    '''expression : PROP'''
    p[0] = p[1]

# PCTL grammar rules


def p_expression_probability(p):
    '''expression : PROB COMPARISON NUMBER LPAREN expression RPAREN'''
    # Matches: P>=0.5 (eventually goal)
    # p[1] = 'P', p[2] = '>=', p[3] = '0.5', p[5] = formula
    p[0] = ('P' + p[2] + p[3], p[5])


# def p_expression_probability_path(p):
#     '''expression : PROB COMPARISON NUMBER LBRACKET expression RBRACKET'''
#     # Matches: P>=0.9 [formula]
#     p[0] = ('P' + p[2] + p[3], p[5])


def p_error(p):
    pass


# lexer and parser
lexer = lex.lex()
parser = yacc.yacc()


def get_lexer():
    return lexer

# given a PCTL formula as input, returns a tuple representing the formula divided into subformulas.


def do_parsingPCTL(formula):
    try:
        result = parser.parse(formula)
        print(result)
        return result
    except SyntaxError:  # if parser fails
        return None

# checks whether the input operator corresponds to a given operator defined in the grammar


def verifyPCTL(token_name, string):
    lexer.input(string)
    for token in lexer:
        if token.type == token_name and token.value in string:
            return True
    return False
