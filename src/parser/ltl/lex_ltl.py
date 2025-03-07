
import ply.lex as lex
import warnings
import re

# List of token names.   This is always required
tokens = (

    'OR',
    'AND',
    'NOT',
    'IMPLIES',
    'EQUIVALENT',
    'XOR',

    'NEXT',
    'WEAK_NEXT',

    'UNTIL',
    'RELEASE',
    'FINALLY',
    'GLOBALLY',
    'BOUNDED_UNTIL',
    'BOUNDED_RELEASE',
    'BOUNDED_FINALLY',
    'BOUNDED_GLOBALLY',

    'ATOM',

    'LPAREN',
    'RPAREN',

)

# Regular expression rules for simple tokens
t_OR = r'\|\| | \|'
t_AND = r'\&\& | \&'
t_NOT = r'! | ~'
t_IMPLIES = r'-> | =>'
t_EQUIVALENT = r'<=> | <->'
t_XOR = r'\^'

t_NEXT = r'X\[!\]\s*'
t_WEAK_NEXT = r'X\s*'
t_UNTIL = r'U\s*'
t_RELEASE = r'R\s*'
t_FINALLY = r'F\s*'
t_GLOBALLY = r'G\s*'
t_BOUNDED_UNTIL = r'BU\s*\d+\.\.\d+'
t_BOUNDED_RELEASE = r'BR\s*\d+\.\.\d+'
t_BOUNDED_FINALLY = r'BF\s*\d+\.\.\d+'
t_BOUNDED_GLOBALLY = r'BG\s*\d+\.\.\d+'
t_ATOM = r'\w+'
t_LPAREN = r'\('
t_RPAREN = r'\)'





# A regular expression rule with some action code
# def t_ATOM(t):
#     r'\w+'
#     t.value = str(t.value)
#     return t


# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)


# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t'
t_ignore_COMMENT = r'\#.*'


# Error handling rule
def t_error(t):
    raise Exception("语法错误，非法字符： '%s'" % t.value[0])
    t.lexer.skip(1)


lexer = lex.lex()

def print_token(ltl):
    # Give the lexer some input
    lexer.input(ltl)
    # Tokenize
    while True:
        tok = lexer.token()
        if not tok:
            break  # No more input
        print(tok)


def new_token(type="default", value="default", lexpos=1, lineno=1):
    """创建一个新的token"""
    tok1 = lex.LexToken()
    tok1.type = type
    tok1.value = value
    tok1.lexpos = lexpos
    tok1.lineno = lineno
    return tok1


# print_token("a BF 1..2 c")