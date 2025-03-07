# Yacc examples
import re

import ply.yacc as yacc

from src.parser.ltl import lex_ltl
from src.parser.ltl.lex_ltl import tokens

# Get the token map from the lexer.  This is required.

# 定义二叉树的节点类
class TreeNode:
    def __init__(self, val,left = None,right = None):
        self.val = val
        self.left = left
        self.right = right

'''语法规则: 
expression  : ATOM
            | NOT expression
            | expression OR expression
            | expression AND expression
            | expression IMPLIES expression
            | expression EQUIVALENT expression
            | expression XOR expression
            | NEXT expression
            | WEAK_NEXT expression
            | expression UNTIL expression
            | expression BOUNDED_UNTIL expression
            | expression RELEASE expression
            | expression BOUNDED_RELEASE expression
            | GLOBALLY expression
            | BOUNDED_GLOBALLY expression
            | FINALLY expression
            | BOUNDED_FINALLY expression
            | LPAREN expression RPAREN

              '''

def p_expression_atom(p):
    '''expression : ATOM'''
    token1 = lex_ltl.new_token('ATOM',p[1],p.lineno(1),p.lexpos(1))
    p[0] = TreeNode(token1)

def p_expression_not_expr(p):
    '''expression : NOT expression'''
    token1 = lex_ltl.new_token('NOT', p[1], p.lineno(1), p.lexpos(1))
    p[0] = TreeNode(token1,p[2])

def p_expression_or(p):
    'expression : expression OR expression'
    token1 = lex_ltl.new_token('OR', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1,p[1],p[3])

def p_expression_and(p):
    'expression : expression AND expression'
    token1 = lex_ltl.new_token('AND', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1,p[1],p[3])

def p_expression_implies(p):
    'expression : expression IMPLIES expression'
    token1 = lex_ltl.new_token('IMPLIES', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1,p[1],p[3])

def p_expression_equivalent(p):
    'expression : expression EQUIVALENT expression'
    token1 = lex_ltl.new_token('EQUIVALENT', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1,p[1],p[3])

def p_expression_xor(p):
    'expression : expression XOR expression'
    token1 = lex_ltl.new_token('XOR', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1,p[1],p[3])

def p_expression_next_expr(p):
    '''expression : NEXT expression'''
    token1 = lex_ltl.new_token('NEXT', p[1], p.lineno(1), p.lexpos(1))
    p[0] = TreeNode(token1,p[2])

def p_expression_weak_next_expr(p):
    '''expression : WEAK_NEXT expression'''
    token1 = lex_ltl.new_token('WEAK_NEXT', p[1], p.lineno(1), p.lexpos(1))
    p[0] = TreeNode(token1,p[2])

def p_expression_until(p):
    '''expression : expression UNTIL expression'''
    token1 = lex_ltl.new_token('UNTIL', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1, p[1], p[3])

def p_expression_bounded_until(p):
    '''expression : expression BOUNDED_UNTIL expression'''
    token1 = lex_ltl.new_token('BOUNDED_UNTIL', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1, p[1], p[3])

def p_expression_release(p):
    '''expression : expression RELEASE expression'''
    token1 = lex_ltl.new_token('RELEASE', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1, p[1], p[3])

def p_expression_bounded_release(p):
    '''expression : expression BOUNDED_RELEASE expression'''
    token1 = lex_ltl.new_token('BOUNDED_RELEASE', p[2], p.lineno(2), p.lexpos(2))
    p[0] = TreeNode(token1, p[1], p[3])


def p_expression_globally(p):
    '''expression : GLOBALLY expression'''
    token1 = lex_ltl.new_token('GLOBALLY', p[1], p.lineno(1), p.lexpos(1))
    p[0] = TreeNode(token1, p[2])

def p_expression_bounded_globally(p):
    '''expression : BOUNDED_GLOBALLY expression'''
    token1 = lex_ltl.new_token('BOUNDED_GLOBALLY', p[1], p.lineno(1), p.lexpos(1))
    p[0] = TreeNode(token1, p[2])

def p_expression_finally(p):
    '''expression : FINALLY expression'''
    token1 = lex_ltl.new_token('FINALLY', p[1], p.lineno(1), p.lexpos(1))
    p[0] = TreeNode(token1, p[2])

def p_expression_bounded_finally(p):
    '''expression : BOUNDED_FINALLY expression'''
    token1 = lex_ltl.new_token('BOUNDED_FINALLY', p[1], p.lineno(1), p.lexpos(1))
    p[0] = TreeNode(token1, p[2])



def p_expression_expr(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]



# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input:  ",end="")
    print(p)

precedence = (
    ('left', 'OR'),
    ('left', 'AND', 'XOR'),
    ('left', 'IMPLIES', 'EQUIVALENT'),
    ('left', 'UNTIL','RELEASE','BOUNDED_UNTIL','BOUNDED_RELEASE'),
    ('left', 'FINALLY','GLOBALLY','BOUNDED_FINALLY','BOUNDED_GLOBALLY',),
    ('left', 'NEXT','WEAK_NEXT'),
    ('right', 'NOT')
)


# 定义一个函数，输出二叉树的树形图
def print_tree(root, indent=0):
    # 如果根节点为空，直接返回
    if not root:
        return
    # 打印当前节点的值，用圆括号包围
    print("(" + str(root.val) + ")")
    # 如果节点有左子树，打印一个横线，并向右缩进一个单位，递归地输出左子树
    if root.left:
        print(" " * indent + "----", end="")
        print_tree(root.left, indent + 4)
    # 如果节点有右子树，打印一个横线，并向右缩进一个单位，递归地输出右子树
    if root.right:
        print(" " * indent + "----", end="")
        print_tree(root.right, indent + 4)


def syntaxTreeReconstruction(root):
    """消除作用于时态算子上的NOT"""
    if root:

        if root.val.type == "NOT" and root.left.val.type == "NOT":
            """根据规则：!!expr = expr """
            root = root.left.left
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "AND":
            """根据规则：!(expr&expr) = !expr | !expr """
            l = TreeNode(root.val, root.left.left, None)
            r = TreeNode(root.val, root.left.right, None)
            root = TreeNode(lex_ltl.new_token("OR","|"), l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "OR":
            """根据规则：!(expr|expr) = !expr & !expr """
            l = TreeNode(root.val, root.left.left, None)
            r = TreeNode(root.val, root.left.right, None)
            root = TreeNode(lex_ltl.new_token("AND","&"), l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "IMPLIES":
            """根据规则：expr -> expr = !expr | expr """
            l = TreeNode(lex_ltl.new_token("NOT","!"), root.left, None)
            r = root.right
            root = TreeNode(lex_ltl.new_token("OR","|"), l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "EQUIVALENT":
            """根据规则：!(expr <-> expr) = expr ^ expr """
            l = root.left.left
            r = root.left.right
            root = TreeNode(lex_ltl.new_token("XOR", "^"), l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "XOR":
            """根据规则：!(expr ^ expr) = expr <-> expr """
            l = root.left.left
            r = root.left.right
            root = TreeNode(lex_ltl.new_token("EQUIVALENT", "<->"), l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "NEXT":
            """根据规则：!(NEXT expr) = WEAK_NEXT !expr """
            l = TreeNode(lex_ltl.new_token("NOT","!"), root.left.left, None)
            root = TreeNode(lex_ltl.new_token("WEAK_NEXT", "X"), l, None)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "WEAK_NEXT":
            """根据规则：!(WEAK_NEXT expr) = NEXT !expr """
            l = TreeNode(lex_ltl.new_token("NOT","!"), root.left.left, None)
            root = TreeNode(lex_ltl.new_token("NEXT", "X[!]"), l, None)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type in ["UNTIL", "BOUNDED_UNTIL"]:
            """根据规则：!(expr1 U expr2) = !expr1 R !expr2 """
            l = TreeNode(lex_ltl.new_token("NOT", "!"), root.left.left, None)
            r = TreeNode(lex_ltl.new_token("NOT", "!"), root.left.right, None)
            root = TreeNode(lex_ltl.new_token("RELEASE", root.left.val.value.replace('U','R')), l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type in ["RELEASE", "BOUNDED_RELEASE"]:
            """根据规则：!(expr1 R expr2) = !expr1 U !expr2 """
            l = TreeNode(lex_ltl.new_token("NOT", "!"), root.left.left, None)
            r = TreeNode(lex_ltl.new_token("NOT", "!"), root.left.right, None)
            root = TreeNode(lex_ltl.new_token("UNTIL", root.left.val.value.replace('R','U')), l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type in ["FINALLY", "BOUNDED_FINALLY"]:
            """根据规则：!(F expr) = G !expr """
            l = TreeNode(lex_ltl.new_token("NOT", "!"), root.left.left, None)
            root = TreeNode(lex_ltl.new_token("GLOBALLY", root.left.val.value.replace('F','G')), l, None)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type in ["GLOBALLY", "BOUNDED_GLOBALLY"]:
            """根据规则：!(G expr) = F !expr """
            l = TreeNode(lex_ltl.new_token("NOT", "!"), root.left.left, None)
            root = TreeNode(lex_ltl.new_token("FINALLY", root.left.val.value.replace('G','F')), l, None)
            root = syntaxTreeReconstruction(root)

        root.left = syntaxTreeReconstruction(root.left)
        root.right = syntaxTreeReconstruction(root.right)
    return root


def syntaxTreeReconstruction_total(root):
    """将ltl公式转为仅有X和U的，为构造全时态测试器做准备"""
    if root:
        if root.val.type == "NOT" and root.left.val.type == "NOT":
            """根据规则：!!expr = expr """
            root = root.left.left
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "WEAK_NEXT" :
            """根据规则：X expr = ! X[!] ! expr """
            lll = root.left
            ll = TreeNode(lex_ltl.new_token("NOT","!"), lll)
            l = TreeNode(lex_ltl.new_token("NEXT", "X[!]"), ll)
            root = TreeNode(lex_ltl.new_token("NOT","!"), l)
            root = syntaxTreeReconstruction_total(root)
        elif root.val.type == "FINALLY" :
            """根据规则：F expr = true U expr """
            r = root.left
            l = TreeNode(lex_ltl.new_token("ATOM", "true"))
            root = TreeNode(lex_ltl.new_token("UNTIL","U"), l, r)
            root = syntaxTreeReconstruction_total(root)
        elif root.val.type == "GLOBALLY" :
            """根据规则：G expr = ! F ! expr """
            lll = root.left
            ll = TreeNode(lex_ltl.new_token("NOT","!"), lll)
            l = TreeNode(lex_ltl.new_token("FINALLY", "F"), ll)
            root = TreeNode(lex_ltl.new_token("NOT","!"), l)
            root = syntaxTreeReconstruction_total(root)
        elif root.val.type == "RELEASE" :
            """根据规则：expr1 R expr2 = !(!expr1 U !expr2) """
            lll = root.left
            ll = TreeNode(lex_ltl.new_token("NOT","!"), lll)
            lrl = root.right
            lr = TreeNode(lex_ltl.new_token("NOT","!"), lrl)
            l = TreeNode(lex_ltl.new_token("UNTIL","U"), ll,lr)
            root = TreeNode(lex_ltl.new_token("NOT","!"), l)
            root = syntaxTreeReconstruction_total(root)
        root.left = syntaxTreeReconstruction_total(root.left)
        root.right = syntaxTreeReconstruction_total(root.right)
    return root



global_j = 0
def rename_vars(root, i=1):
    """变量重命名，保证构造测试时变量不同名"""
    global global_j
    if root:
        if root.val.type == "EXPR":
            root.val.lineno = i
            global_j += 1
            root.val.lexpos = global_j
            return
        rename_vars(root.left, i + 1)
        root.val.lineno = i
        global_j += 1
        root.val.lexpos = global_j
        rename_vars(root.right, i + 1)


def toDAG(root, dic=None):
    """字典dic的key对应token的value，字典的值是子树的列表，列表中存了已遍历的value相同但结构不同的子树"""
    if dic is None:
        dic = {}
    if root:

        root.left = toDAG(root.left, dic)
        root.right = toDAG(root.right, dic)

        val = root.val.value.replace(' ','')
        if val not in dic:
            """字符不在字典里"""
            dic[val] = [root]
        elif val in dic:
            """字符在字典里"""
            for subTree in dic[val]:
                if isEqual(subTree, root):
                    # 同字符，且与子树同构
                    root = subTree
                    return root
            # 同字符，但与已有子树不同构，添加root到dic中
            dic[val].append(root)
    return root

def isEqual(t1, t2):
    """判断二叉树是否同构"""
    # 如果两个二叉树都为空，返回True
    if t1 is None and t2 is None:
        return True
    # 如果两个二叉树有一个为空，返回False
    if t1 is None or t2 is None:
        return False
    # 如果两个二叉树的根节点的值不相等，返回False
    val1 = t1.val.value.replace(' ', '')
    val2 = t2.val.value.replace(' ', '')
    if val1 != val2:
        return False
    # 递归地判断两个二叉树的左右子树是否相等
    return isEqual(t1.left, t2.left) and isEqual(t1.right, t2.right)


# Build the parser
parser = yacc.yacc()

def parsing(ltl):
    # print("TOKEN: ")
    # lex_ltl.print_token(ltl)

    root = parser.parse(ltl,lexer=lex_ltl.lexer)
    # print("原始公式的语法树: ")
    # print_tree(root)

    root = syntaxTreeReconstruction(root)
    # print("重构后的语法树: ")
    # print_tree(root)

    rename_vars(root)
    # print("重命名后的语法树: ")
    # print_tree(root)

    root = toDAG(root)
    # print("语法树转化为DAG: ")
    # print_tree(root)

    return root


def parsing_total(ltl):
    # print("TOKEN: ")
    # lex_ltl.print_token(ltl)

    root = parser.parse(ltl)
    # print("原始公式的语法树: ")
    # print_tree(root)

    root = syntaxTreeReconstruction(root)
    # print("重构后的语法树: ")
    # print_tree(root)

    rename_vars(root)
    # print("重命名后的语法树: ")
    # print_tree(root)

    root = toDAG(root)
    # print("语法树转化为DAG: ")
    # print_tree(root)

    return root





# counters1 = "((((X[!] counter_env_0 -> init_counter_0) && (init_counter_0 -> X counter_env_0)) && !counter_sys_0 && !inc_sys) && (G ((inc_env -> !X[!] inc_env)) -> (X[!] G ((X[!] carry_env_0 -> inc_env) && (inc_env -> X carry_env_0) && (carry_sys_0 <-> inc_sys) && ((X[!] counter_env_0 -> !(counter_env_0 <-> X[!] carry_env_0)) && (!(counter_env_0 <-> X carry_env_0) -> X counter_env_0)) && ((X[!] counter_sys_0 -> !(counter_sys_0 <-> X[!] carry_sys_0)) && (!(counter_sys_0 <-> X carry_sys_0) -> X counter_sys_0))) && X[!] F ((counter_env_0 <-> counter_sys_0)))))"
# s = 'a BR 50..60 c'
# parsing(s)
# nim_01_01 = "((turn_sys && !turn_env && (!select_sys_0 -> heap_0_1) && (select_sys_0 -> (change_sys_0))) && (G ((turn_env -> (select_env_0)) && (((!heap_0_0) && heap_0_0 && X[!] select_env_0) -> false) && (((!heap_0_0) && heap_0_1 && X[!] select_env_0) -> (X[!] change_env_0))) -> (G ((turn_sys -> (select_sys_0)) && (((!heap_0_0) && heap_0_0 && X[!] select_sys_0) -> false) && (((!heap_0_0) && heap_0_1 && X[!] select_sys_0) -> (X[!] change_sys_0)) && (turn_sys <-> !turn_env) && (X[!] turn_sys -> turn_env) && (X[!] turn_env -> turn_sys) && (heap_0_1 -> !heap_0_0) && ((turn_env && select_env_0 && change_env_0) -> heap_0_0) && ((turn_sys && select_sys_0 && change_sys_0) -> heap_0_0) && ((X[!] turn_env && X[!] !select_env_0 && heap_0_0) -> X[!] heap_0_0) && ((X[!] turn_env && X[!] !select_env_0 && heap_0_1) -> X[!] heap_0_1) && ((X[!] turn_sys && X[!] !select_sys_0 && heap_0_0) -> X[!] heap_0_0) && ((X[!] turn_sys && X[!] !select_sys_0 && heap_0_1) -> X[!] heap_0_1)) && ((!heap_0_0) U (turn_env && (heap_0_0))))))"
# parsing_total(nim_01_01)
# parsing('(F a) -> false')