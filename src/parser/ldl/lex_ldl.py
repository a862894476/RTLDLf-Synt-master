# ------------------------------------------------------------
# FormulateLex_ldl.py
#
# tokenizer for a simple expression evaluator for
# numbers and +,-,*,/
# ------------------------------------------------------------
import ply.lex as lex
import warnings
import re

class Stack(object):
    def __init__(self):
        """创建一个Stack类"""
        self.stack = []  # 存放元素的栈

    def push(self, data):
        """压入 push ：将新元素放在栈顶"""
        self.stack.append(data)

    def pop(self):
        """ 弹出 pop ：从栈顶移出一个数据"""
        # 判断是否为空栈
        if self.stack:
            return self.stack.pop()
        else:
            raise IndexError("从空栈执行弹栈操作")

    def peek(self):
        """查看栈顶的元素"""
        # 判断栈是否为空
        if self.stack:
            return self.stack[-1]

    def is_empty(self):
        """判断栈是否为空"""
        # 栈为非空时，self.stack为True，再取反，为False
        return not bool(self.stack)

    def size(self):
        """返回栈的大小"""
        return len(self.stack)


class TreeNode:
    def __init__(self, val, left=None, right=None):
        self.val = val
        self.left = left
        self.right = right


# List of token names.   This is always required
tokens = (
    'ATOM',
    'OR',
    'AND',
    'NOT',

    'LEXIST',
    'LFORALL',
    'REXIST',
    'RFORALL',

    'STAR',
    'TEST',
    'CONNECT',
    'PLUS',
    'LPAREN',
    'RPAREN',
    'BOUNDEDSTAR'
)

# Regular expression rules for simple tokens
t_OR = r'\|'
t_AND = r'\&'
t_NOT = r'!'
t_LEXIST = r'\<'
t_LFORALL = r'\['
t_REXIST = r'\>'
t_RFORALL = r'\]'
t_STAR = r'\*'
t_TEST = r'\?'
t_CONNECT = r'\;'
t_PLUS = r'\+'
t_LPAREN = r'\('
t_RPAREN = r'\)'


# A regular expression rule with some action code
def t_ATOM(t):
    r'\w+'
    t.value = str(t.value)
    return t


def t_BOUNDEDSTAR(t):
    r'\*{\d+,\d+}'
    t.value = str(t.value)
    return t


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


def print_token(ldl):
    # Give the lexer some input
    lexer.input(ldl)
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


def reversePolishNotation(ldl):
    """生成ldl公式的逆波兰表示"""
    ldl = ldl.replace('<', '<(')
    ldl = ldl.replace('[', '[(')
    ldl = ldl.replace('>', ')>')
    ldl = ldl.replace(']', ')]')
    lexer.input(ldl)
    stack1 = Stack()
    stack2 = Stack()  # 辅助栈
    while True:
        tok = lexer.token()
        if not tok:
            break  # No more input
        # print(tok)
        if (tok.type == 'LEXIST' or tok.type == 'LFORALL'):
            continue
        elif (tok.type == 'LPAREN'):
            stack2.push(tok)
        elif (tok.type == 'CONNECT'):
            if not stack2.is_empty() and (stack2.peek().type in ["REXIST", "RFORALL"]):
                raise Exception('语法错误：‘;’仅用于路径公式')
            while not stack2.is_empty() and (stack2.peek().type in ['STAR', "BOUNDEDSTAR", 'TEST', 'NOT', 'AND', 'OR']):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == 'PLUS'):
            if not stack2.is_empty() and (stack2.peek().type in ["REXIST", "RFORALL"]):
                raise Exception('语法错误：‘+’仅用于路径公式')
            while (not stack2.is_empty() and (
                    stack2.peek().type in ['STAR', "BOUNDEDSTAR", 'TEST', 'NOT', 'CONNECT', 'AND', 'OR'])):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == 'AND'):
            if not stack2.is_empty() and (stack2.peek().type in ['STAR', "BOUNDEDSTAR"]):
                raise Exception('语法错误：‘*’仅用于路径公式')
            while not stack2.is_empty() and (stack2.peek().type in ['TEST', 'NOT', 'REXIST', 'RFORALL']):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == 'OR'):
            if not stack2.is_empty() and (stack2.peek().type in ['STAR', "BOUNDEDSTAR"]):
                raise Exception('语法错误：‘*’仅用于路径公式')
            while not stack2.is_empty() and (stack2.peek().type in ['TEST', 'NOT', 'REXIST', 'RFORALL', 'AND']):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == 'REXIST'):
            while not stack2.is_empty() and (stack2.peek().type in ['STAR', "BOUNDEDSTAR", 'TEST']):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == 'RFORALL'):
            while not stack2.is_empty() and (stack2.peek().type in ['STAR', "BOUNDEDSTAR", 'TEST']):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == "STAR" or tok.type == "BOUNDEDSTAR"):
            if not stack2.is_empty() and (stack2.peek().type in ["REXIST", "RFORALL"]):
                raise Exception('语法错误：‘*’应作用于路径表达式')
            while not stack2.is_empty() and (stack2.peek().type in ['NOT', 'TEST']):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == "TEST"):
            if not stack2.is_empty() and (stack2.peek().type in ["STAR", "BOUNDEDSTAR"]):
                raise Exception('语法错误：测试的公式应是ldl公式而不是路径表达')
            while not stack2.is_empty() and (stack2.peek().type in ['NOT', 'REXIST', 'RFORALL']):
                stack1.push(stack2.pop())
            stack2.push(tok)
        # elif (tok.type == "NOT"):
        #     if not stack2.is_empty() and (stack2.peek().type in ["STAR", "BOUNDEDSTAR"]):
        #         raise Exception('语法错误：星闭包后面不能带有‘！’')
        #     while not stack2.is_empty() and (stack2.peek().type in ['TEST', 'REXIST', 'RFORALL']):
        #         stack1.push(stack2.pop())
        #     stack2.push(tok)
        elif (tok.type == "NOT"):
            if not stack2.is_empty() and (stack2.peek().type in ["STAR", "BOUNDEDSTAR"]):
                raise Exception('语法错误：星闭包后面不能带有‘！’')
            while not stack2.is_empty() and (stack2.peek().type in ['STAR', "BOUNDEDSTAR"]):
                stack1.push(stack2.pop())
            stack2.push(tok)
        elif (tok.type == "RPAREN"):
            while not (not stack2.is_empty() and stack2.peek().type == 'LPAREN'):
                stack1.push(stack2.pop())
            stack2.pop()
        elif (tok.type == 'ATOM'):
            stack1.push(tok)

    while (not stack2.is_empty()):
        stack1.push(stack2.pop())
    while (not stack1.is_empty()):
        stack2.push(stack1.pop())
    return stack2


def abstractSyntaxTree(ldl):
    """抽象语法树生成"""
    stack1 = reversePolishNotation(ldl)
    stack2 = Stack()  # 辅助子树栈
    while not stack1.is_empty():
        tok = stack1.pop()
        if (tok.type == "ATOM"):
            stack2.push(TreeNode(tok))
        elif (tok.type in ["STAR", "BOUNDEDSTAR", "NOT", "TEST"]):
            stack2.push(TreeNode(tok, stack2.pop(), None))
        else:
            t2 = stack2.pop()
            t1 = stack2.pop()
            stack2.push(TreeNode(tok, t1, t2))
    return stack2.pop()


def is_only_test(root):
    """判断是否是仅测试公式，即(path)*,path步长为0"""
    if root and root.val.type == "TEST":
        return True
    elif root and root.val.type == "CONNECT":
        return is_only_test(root.left) and is_only_test(root.right)
    elif root and root.val.type == "PLUS":
        return is_only_test(root.left) or is_only_test(root.right)
    return False


def eliminate_only_test(root):
    """消除仅测试"""
    if root:
        if root.val.type == "PLUS":
            if root.left.val.type == "TEST":
                root = eliminate_only_test(root.right)
            elif root.right.val.type == "TEST":
                root = eliminate_only_test(root.left)
            elif root.left.val.type in ["ATOM","OR","AND"]:
                # root = root.left
                root.right = eliminate_only_test(root.right)
            elif root.right.val.type in ["ATOM","OR","AND"]:
                # root = root.right
                root.left = eliminate_only_test(root.left)
            else:
                root.right = eliminate_only_test(root.right)
                root.left = eliminate_only_test(root.left)
        elif root.val.type == "CONNECT":
            root.left =  eliminate_only_test(root.left)
            root.right = eliminate_only_test(root.right)

    return root


def syntaxTreeReconstruction(root):
    """语法树重构，构造语义等价化简后的语法树"""
    if root and root.val.type != "EXPR":
        if root.val.type in ["REXIST", "RFORALL"] and root.left.val.type == "PLUS":
            """根据规则：<path1+path2>expr = <path1>expr | <path2>expr """
            l = TreeNode(new_token(root.val.type,root.val.value), root.left.left, root.right)
            r = TreeNode(new_token(root.val.type,root.val.value), root.left.right, root.right)
            if root.val.type == "REXIST""":
                root.left.val.type = "OR"
                root.left.val.value = "|"
            else:
                root.left.val.type = "AND"
                root.left.val.value = "&"
            root = TreeNode(root.left.val, l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type in ["REXIST", "RFORALL"] and root.left.val.type == "CONNECT":
            """根据规则：<path1;path2>expr = <path1><path2>expr """
            l = root.left.left
            r = TreeNode(new_token(root.val.type,root.val.value), root.left.right, root.right)
            root = TreeNode(root.val, l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "NOT":
            """根据规则：!!expr = expr """
            root = root.left.left
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "REXIST":
            """根据规则：!<path>expr = [path]!expr """
            l = root.left.left
            r = TreeNode(root.val, root.left.right, None)
            root.left.val.type = "RFORALL"
            root.left.val.value = "]"
            root = TreeNode(root.left.val, l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "RFORALL":
            """根据规则：![path]expr = <path>!expr """
            l = root.left.left
            r = TreeNode(root.val, root.left.right, None)
            root.left.val.type = "REXIST"
            root.left.val.value = ">"
            root = TreeNode(root.left.val, l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "AND":
            """根据规则：!(expr&expr) = !expr | !expr """
            l = TreeNode(root.val, root.left.left, None)
            r = TreeNode(root.val, root.left.right, None)
            root.left.val.type = "OR"
            root.left.val.value = "|"
            root = TreeNode(root.left.val, l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type == "OR":
            """根据规则：!(expr|expr) = !expr & !expr """
            l = TreeNode(root.val, root.left.left, None)
            r = TreeNode(root.val, root.left.right, None)
            root.left.val.type = "AND"
            root.left.val.value = "&"
            root = TreeNode(root.left.val, l, r)
            root = syntaxTreeReconstruction(root)
        elif root.val.type in ["REXIST","RFORALL"] and root.left.val.type in ["STAR","BOUNDEDSTAR"] and is_only_test(root.left.left):
            warnings.warn("公式的*闭包中中存在仅测试的部分，易造成语义混乱,建议优化公式使*闭包不为仅测试", category=None,
                          stacklevel=1, source=None)
            "消除仅测试,如<(a?+b)*>c = <b*>c"
            root.left.left = eliminate_only_test(root.left.left)
            if root.left.val.type == "BOUNDEDSTAR" and root.left.val.value[2] != '0':
                "有界*闭包的情况下，且下界>0,这样的情况<(a?)*{1,2}>b=<a?>b"
                root.left = root.left.left
            elif is_only_test(root.left.left):
                "消除完仅测试依然是仅测试的,如<(a?+b?)*>c = <true?>c"
                lll = TreeNode(new_token("ATOM", "true"))
                ll = TreeNode(new_token("TEST", "?"), lll)
                root.left = ll
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "REXIST" and root.left.val.type == "STAR":
            "遇见*:按照规则<path*>expr = <path><path*>expr | expr"
            ll = root.left.left
            lr = TreeNode(new_token("EXPR", "EXPR"))
            l = TreeNode(root.val, ll, lr)
            r = root.right
            root = TreeNode(new_token("STAR_OR","|"),l,r)
            root.left.right.left = root
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "RFORALL" and root.left.val.type == "STAR":
            "遇见*:按照规则[path*]expr = [path][path*]expr & expr"
            ll = root.left.left
            lr = TreeNode(new_token("EXPR", "EXPR"))
            l = TreeNode(root.val, ll, lr)
            r = root.right
            root = TreeNode(new_token("STAR_AND","&"),l,r)
            root.left.right.left = root
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "REXIST" and root.left.val.type == "BOUNDEDSTAR":
            "遇见*:按照规则<path*>expr = <path><path*>expr | expr"
            ll = root.left.left
            lr = TreeNode(new_token("EXPR", "EXPR"))
            l = TreeNode(root.val, ll, lr)
            r = root.right
            root = TreeNode(new_token("BOUNDED_OR",root.left.val.value),l,r)
            root.left.right.left = root
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "RFORALL" and root.left.val.type == "BOUNDEDSTAR":
            "遇见*:按照规则[path*]expr = [path][path*]expr & expr"
            ll = root.left.left
            lr = TreeNode(new_token("EXPR", "EXPR"))
            l = TreeNode(root.val, ll, lr)
            r = root.right
            root = TreeNode(new_token("BOUNDED_AND",root.left.val.value),l,r)
            root.left.right.left = root
            root = syntaxTreeReconstruction(root)
        elif root.val.type == "NOT" and root.left.val.type in ["PLUS", "CONNECT", "STAR", "BOUNDEDSTAR", "TEST"]:
            """语法错误：NOT不应该作用在路径公式上"""
            raise Exception('语法错误：NOT不应该作用在路径公式上')
        elif root.val.type == "TEST" and root.left.val.type in ["PLUS", "CONNECT", "STAR", "BOUNDEDSTAR", "TEST"]:
            """语法错误：TEST不应该作用在路径公式上"""
            raise Exception('语法错误：TEST不应该作用在路径公式上')
        elif root.val.type in ["REXIST", "RFORALL"] and root.left.val.type in ["REXIST", "RFORALL"]:
            """语法错误：ldl公式不能做路径公式使用"""
            raise Exception('语法错误：ldl公式不能作为路径公式使用')
        root.left = syntaxTreeReconstruction(root.left)
        root.right = syntaxTreeReconstruction(root.right)
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



def toDAG(root, dic=None, is_star=False):
    """将语法树树优化为DAG有向无环图,并计算子树的公式长度"""
    """字典dic的key对应token的value，字典的值是子树的列表，列表中存了已遍历的value相同但结构不同的子树"""
    if dic is None:
        dic = {}
    if root and root.val.type != "EXPR":
        if root.val.type in ["STAR", "BOUNDEDSTAR"]:
            "判断公式是否处于星号下"
            is_star = True
        elif root.val.type == "TEST":
            is_star = False
        root.left = toDAG(root.left, dic, is_star)
        root.right = toDAG(root.right, dic, is_star)
        if is_star or root.val.type == "EXPR":
            """path*的最后一个元素，不处理EXPR"""
            return root
        if root.val.value not in dic:
            """字符不在字典里"""
            dic[root.val.value] = [root]
        elif root.val.value in dic:
            """字符在字典里"""
            for subTree in dic[root.val.value]:
                if isEqual(subTree, root):
                    # 同字符，且与子树同构
                    root = subTree
                    return root
            # 同字符，但与已有子树不同构，添加root到dic中
            dic[root.val.value].append(root)
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
    if t1.val.value != t2.val.value:
        return False
    if t1.val.type == "EXPR" and t2.val.type == "EXPR" and expr_isEqual(t1.left,t2.left):
        return True
    elif t1.val.type == "EXPR" and t2.val.type == "EXPR" and not expr_isEqual(t1.left,t2.left):
        return False
    # 递归地判断两个二叉树的左右子树是否相等
    return isEqual(t1.left, t2.left) and isEqual(t1.right, t2.right)


def expr_isEqual(t1,t2):
    """判断EXPR是否同构"""
    if t1 is None and t2 is None:
        return True
    if t1 is None or t2 is None:
        return False
    if t1.val.value != t2.val.value:
        return False
    if t1.val.type == "EXPR" and t2.val.type == "EXPR":
        return True
    return expr_isEqual(t1.left, t2.left) and expr_isEqual(t1.right, t2.right)


def print_tree(root, indent=0):
    """打印树"""
    # 如果根节点为空，直接返回
    if not root:
        return
    # 打印当前节点的值，用圆括号包围
    print("(" + str(root.val) + ")")
    # 如果节点有左子树，打印一个横线，并向右缩进一个单位，递归地输出左子树
    if root.val.type == "EXPR":
        print(" " * indent + "          ", end="")
        print("EXPR -> " + str(root.left.val))
        return
    if root.left:
        print(" " * indent + "----", end="")
        print_tree(root.left, indent + 4)
    # 如果节点有右子树，打印一个横线，并向右缩进一个单位，递归地输出右子树
    if root.right:
        print(" " * indent + "----", end="")
        print_tree(root.right, indent + 4)


def parser(ldl):
    # print_token(ldl)
    root = abstractSyntaxTree(ldl)
    # print("原始公式的语法树: ")
    # print_tree(root)

    root = syntaxTreeReconstruction(root)
    # print("重构后的语法树: ")
    # print_tree(root)

    rename_vars(root)
    # print("重命名后的语法树: ")
    # print_tree(root)

    root = toDAG(root)
    # print("语法树转4化为DAG: ")
    # print_tree(root)

    return root


# stack1 = reversePolishNotation('<a;(b*;(c+d);e?;!f?)*{1,2};g>[h]i')
# stack1 = reversePolishNotation('<a;(<b>(c+!d) | <e+f>!g)?>h ')
# stack1 = reversePolishNotation('<a&b|c + a|b&c;(a|b)&c + a&(b|c)>z')#测试符号优先级
# stack1 = reversePolishNotation('<a>b | <c>d & <e>f | <g>h')
# stack1 = reversePolishNotation('<!(a|b)?>b')
# while not stack1.is_empty():
#     print(stack1.pop().value, end="")
# print_tree(abstractSyntaxTree('<a>b'))
# <(((a+b;b);(c;c+d));e)*>d

# ldlf_formula = input("输入RTLDLf公式：\n")
# parser('<(a?+c)*>b')







