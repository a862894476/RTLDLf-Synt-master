import src.parser.ldl.lex_ldl as Parse
from z3 import *
import re


class Tester:
    def __init__(self, vars, init, trans, final=True):
        self.vars = vars
        self.init = init
        self.trans = trans
        self.final = final


class AstRefKey:
    def __init__(self, n):
        self.n = n

    def __hash__(self):
        return self.n.hash()

    def __eq__(self, other):
        return self.n.eq(other.n)

    def __repr__(self):
        return str(self.n)


def askey(n):
    assert isinstance(n, AstRef)
    return AstRefKey(n)


def get_vars(f):
    """返回表达中所有变量"""
    r = set()

    def collect(f):
        if is_const(f):
            if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
                r.add(askey(f))
        else:
            for c in f.children():
                collect(c)

    collect(f)
    return r


def prime(var, num=1):
    """创建加撇的变量"""
    pattern = r"\d+$"
    result = str(var)
    while num:
        result = re.sub(pattern, lambda m: str(int(m.group()) + 1), result)
        num -= 1
    return Bool(result)


def prime_int(var, num=1):
    """创建加撇的变量"""
    pattern = r"\d+$"
    result = str(var)
    while num:
        result = re.sub(pattern, lambda m: str(int(m.group()) + 1), result)
        num -= 1
    return Int(result)

def prime_all_vars_in_list(list1):
    ret = []
    for each in list1:
        if str(each)[0] in ["I", "J"]:
            ret.append(prime_int(each))
        else:
            ret.append(prime(each))
    return ret


def get_submap(expr1):
    """获取变量映射表"""
    ret = []
    for each in get_vars(expr1):
        if str(each)[0] in ["I","J"]:
            ret.append((Int(str(each)), prime_int(each)))
        else:
            ret.append((Bool(str(each)), prime(each)))
    return ret


def prime_expr(expr):
    """表达式所有变量加撇"""
    sub_map = get_submap(expr)
    expr = substitute(expr, sub_map)
    return expr


def is_proposition(root):
    if root and root.val.type in ["AND", "OR"]:
        return is_proposition(root.left) and is_proposition(root.left)
    elif root and root.val.type in ["ATOM"]:
        return True
    elif root:
        return False


def get_name(val):
    """获取变量名字，为token的value+lineno+lexpos+序号"""
    return val.value + str(val.lineno) + str(val.lexpos) + "_0"


interval_variable = []

max_num = 0

def construct(root, constructed_tester=None):
    """自底向上递归构造"""
    if constructed_tester is None:
        constructed_tester = {}
    if root:

        var_name = get_name(root.val)

        if root.val.type in ["BOUNDED_OR", "BOUNDED_AND"]:
            m = re.search(r'\*{(\d+),(\d+)}', root.val.value)
            num1 = int(m.group(1))  # 提取第一个数字
            num2 = int(m.group(2))  # 提取第二个数字
            global max_num
            max_num = num2 if num2>max_num else max_num
            if num2-num1 < 0:
                raise Exception('语法错误：区间上界应该大于下界')
            interval_variable.append((var_name, num1, num2))

        if root.val.type != "EXPR":
            l = construct(root.left, constructed_tester)
            if root.val.type in ["BOUNDED_OR","BOUNDED_AND"]:
                interval_variable.pop()
            r = construct(root.right, constructed_tester)

        if var_name in constructed_tester:
            """已经构造过的测试无需再构造"""
            return constructed_tester[var_name]

        if root.val.type in ["ATOM", "EXPR"]:
            variables = set()
        elif root.val.type in ["STAR", "BOUNDEDSTAR", "TEST", "NOT"]:
            variables = l.vars
        else:
            variables = l.vars.union(r.vars)

        if root.val.type == "BOUNDED_OR":
            "区间星闭包处理"
            init1 = Bool("X_" + var_name)
            i = Int("I_" + var_name)
            j = Int("J_" + var_name)
            variables.add(init1)
            variables.add(i)
            variables.add(j)
            init = And(init1, i == IntVal(num1), j == IntVal(num2))
            trans = And(
                Implies(And(init1, i > IntVal(0), j > IntVal(0)), l.init),
                Implies(And(init1, i <= IntVal(0), j > IntVal(0)), Or(l.init, r.init)),
                Implies(And(init1, i <= IntVal(0), j <= IntVal(0)), r.init),
            )
            trans = And(trans, l.trans, r.trans)
            f = And(Not(init1), l.final, r.final)
        elif root.val.type == "BOUNDED_AND":
            "区间星闭包处理"
            init1 = Bool("X_" + var_name)
            i = Int("I_" + var_name)
            j = Int("J_" + var_name)
            variables.add(init1)
            variables.add(i)
            variables.add(j)
            init = And(init1, i == IntVal(num1), j == IntVal(num2))
            trans = And(
                Implies(And(init1, i > IntVal(0), j > IntVal(0)), l.init),
                Implies(And(init1, i <= IntVal(0), j > IntVal(0)), And(l.init, r.init)),
                Implies(And(init1, i <= IntVal(0), j <= IntVal(0)), r.init),
            )
            trans = And(trans, l.trans, r.trans)
            f = BoolVal(True)
        elif root.val.type == "STAR_AND":
            "是星号指向的EXPR，需要创建变量："
            init = Bool("X_" + var_name)
            variables.add(init)
            trans = Implies(init, And(l.init, r.init))
            trans = And(trans, l.trans, r.trans)
            f = BoolVal(True)
        elif root.val.type == "STAR_OR":
            "是星号指向的EXPR，需要创建变量："
            init = Bool("X_" + var_name)
            variables.add(init)
            trans = Implies(init, Or(l.init, r.init))
            trans = And(trans, l.trans, r.trans)
            f = And(Not(init), l.final, r.final)
        elif root.val.type == "AND":
            "命题逻辑"
            init = And(l.init, r.init)
            trans = And(l.trans, r.trans)
            f = And(l.final, r.final)
        elif root.val.type == "OR":
            "命题逻辑"
            init = Or(l.init, r.init)
            trans = And(l.trans, r.trans)
            f = And(l.final, r.final)
        elif root.val.type == "REXIST" and root.left.val.type in ["AND", "OR", "ATOM", "NOT","TEST"]:
            "REXIST算子："
            init = Bool("X_" + var_name)
            variables.add(init)
            if root.left.val.type == "TEST":
                trans = And(Implies(init, And(l.init, r.init)), l.trans, r.trans)
            else:
                "<prop>expr,需要prime()的"
                if interval_variable and root.right.val.type in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且需要使I'=I-1"
                    vals = interval_variable[-1]  ##这是一个如(var_name, num1, num2)的元组
                    # print(root.right.left.val)
                    # print(vals)
                    if root.right.left.val.type in ["BOUNDED_OR","BOUNDED_AND"]:
                        inter_vals = And(  # I'=I-1 and J'=J-1
                            prime_int(Int("I_" + vals[0])) == Int("I_" + vals[0]) - IntVal(1),
                            prime_int(Int("J_" + vals[0])) == Int("J_" + vals[0]) - IntVal(1)
                        )
                    else:
                        inter_vals = And(  # I'=I and J'=J
                            prime_int(Int("I_" + vals[0])) == Int("I_" + vals[0]),
                            prime_int(Int("J_" + vals[0])) == Int("J_" + vals[0])
                        )
                    for each in interval_variable[0:len(interval_variable)-1]:
                        ""
                        val = And(  # I'=I  and J'=J
                            prime_int(Int("I_" + each[0])) == Int("I_" + each[0]),
                            prime_int(Int("J_" + each[0])) == Int("J_" + each[0])
                        )
                        inter_vals = And(inter_vals, val)
                    trans = And(Implies(init, And(l.init, prime_expr(r.init), inter_vals)), l.trans, r.trans)
                elif interval_variable and root.right.val.type not in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且不需要使I'=I-1，则只要I'=I"
                    inter_vals = True
                    for each in interval_variable:
                        ""
                        val = And(  # I'=I  and J'=J
                            prime_int(Int("I_" + each[0])) == Int("I_" + each[0]),
                            prime_int(Int("J_" + each[0])) == Int("J_" + each[0])
                        )
                        inter_vals = And(inter_vals, val)
                    trans = And(Implies(init, And(l.init, prime_expr(r.init), inter_vals)), l.trans, r.trans)
                else:
                    "interval_variable为空的情况，不存在有界的*，只需正常处理X -> l & X_r' 即可"
                    trans = And(Implies(init, And(l.init, prime_expr(r.init))), l.trans, r.trans)
            f = And(Not(init), l.final, r.final)
        elif root.val.type == "RFORALL" and root.left.val.type in ["AND", "OR", "ATOM", "NOT","TEST"]:
            "RFORALL算子："
            init = Bool("X_" + var_name)
            variables.add(init)
            if root.left.val.type == "TEST":
                trans = And(Implies(init, Implies(l.init, r.init)), l.trans, r.trans)
            else:
                "[prop]expr,需要prime()的"
                if interval_variable and root.right.val.type in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且需要使I'=I-1"
                    vals = interval_variable[-1]  ##这是一个如(var_name, num1, num2)的元组
                    if root.right.left.val.type in ["BOUNDED_OR","BOUNDED_AND"]:
                        inter_vals = And(  # I'=I-1 and J'=J-1
                            prime_int(Int("I_" + vals[0])) == Int("I_" + vals[0]) - IntVal(1),
                            prime_int(Int("J_" + vals[0])) == Int("J_" + vals[0]) - IntVal(1)
                        )
                    else:
                        inter_vals = And(  # I'=I and J'=J
                            prime_int(Int("I_" + vals[0])) == Int("I_" + vals[0]),
                            prime_int(Int("J_" + vals[0])) == Int("J_" + vals[0])
                        )
                    for each in interval_variable[0:len(interval_variable) - 1]:
                        ""
                        val = And(  # I'=I  and J'=J
                            prime_int(Int("I_" + each[0])) == Int("I_" + each[0]),
                            prime_int(Int("J_" + each[0])) == Int("J_" + each[0])
                        )
                        inter_vals = And(inter_vals, val)
                    trans = And(Implies(init, Implies(l.init, And(prime_expr(r.init), inter_vals))), l.trans, r.trans)
                elif interval_variable and root.right.val.type not in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且不需要使I'=I-1，则只要I'=I"
                    inter_vals = True
                    for each in interval_variable:
                        ""
                        val = And(  # I'=I  and J'=J
                            prime_int(Int("I_" + each[0])) == Int("I_" + each[0]),
                            prime_int(Int("J_" + each[0])) == Int("J_" + each[0])
                        )
                        inter_vals = And(inter_vals, val)
                    trans = And(Implies(init, Implies(l.init, And(prime_expr(r.init), inter_vals))), l.trans, r.trans)
                else:
                    "interval_variable为空的情况，不存在有界的*，只需正常处理X_ -> l & X_r' 即可"
                    trans = And(Implies(init, Implies(l.init, prime_expr(r.init))), l.trans, r.trans)
                # trans = And(Implies(init, Implies(l.init, prime(r.init))), l.trans, r.trans)
            f = BoolVal(True)
        elif root.val.type == "ATOM":
            "原子命题,构造Xa==a的"
            if root.val.value in ["TRUE", "True", "true"]:
                init = BoolVal(True)
                trans = BoolVal(True)
                f = BoolVal(True)
            else:
                init = Bool("X_" + root.val.value + "_0")
                a = Bool(root.val.value + "_0")
                variables.add(init)
                variables.add(a)
                trans = init == a
                f = Not(init)
        elif root.val.type == "NOT":
            "原子命题"
            if root.left.val.value in ["TRUE", "True", "true"]:
                init = BoolVal(False)
                trans = BoolVal(False)
                f = BoolVal(True)
            elif root.left.val.value in ["FALSE", "False", "false"]:
                init = BoolVal(True)
                trans = BoolVal(True)
                f = BoolVal(True)
            else:
                init = Not(l.init)
                trans = l.trans
                f = l.final

        # elif root.val.type == "ATOM":
        #     "原子命题,不构造Xa->a的"
        #     if root.val.value in ["TRUE", "True", "true"]:
        #         init = BoolVal(True)
        #     else:
        #         # init = Bool(var_name)
        #         init = Bool(root.val.value + "_0")
        #         variables.add(init)
        #     trans = BoolVal(True)
        #     f = BoolVal(True)
        # elif root.val.type == "NOT":
        #     "原子命题"
        #     if root.left.val.value in ["TRUE", "True", "true"]:
        #         init = BoolVal(False)
        #         trans = BoolVal(False)
        #     else:
        #         init = Not(l.init)
        #         trans = BoolVal(True)
        #     f = BoolVal(True)

        elif root.val.type == "EXPR":
            "标记的原子命题"
            init = Bool("X_" + get_name(root.left.val))
            variables.add(init)
            trans = BoolVal(True)
            f = BoolVal(True)
        elif root.val.type == "TEST":
            "测试"
            init = l.init
            trans = l.trans
            f = l.final
        else:
            print("something wrong!")
            print("正在构造"+var_name)
        # 简化命题公式
        init = simplify(init)
        trans = simplify(trans)
        f = simplify(f)
        tester = Tester(variables, init, trans, f)
        constructed_tester[var_name] = tester
        # printTester(tester)
        return tester


def constructTester(ldl):
    """测试器构造"""
    root = Parse.parser(ldl)
    tester = construct(root)
    # printTester(tester)
    return tester, max_num


def printTester(tester):
    print(str(tester.init) + "的测试器：")
    print("vars:  ", end="")
    print(tester.vars)
    print("init:  ", end="")
    print(tester.init)
    if tester.trans == True:
        print("trans: ", end="")
    else:
        print("trans: ")
    print(tester.trans)
    # print(prime_expr(tester.trans))
    print("final: ", end="")
    print(tester.final)
    # print(prime_expr(tester.final))
    print("")


# a = constructTester("<((a;b)*{1,1};c)*{2,2}>d")
# a = constructTester("[true*;a]<true*>b")
# example1 = "(!cabbage & !goat & !wolf & !man & !carrygoat& !carrycabbage & !carrywolf) & (< true* ; cabbage? ; goat? > wolf)&([ true* ] < (goat? ; man + !goat? ; !man +goat? ; !cabbage? ; !wolf + !goat? ; cabbage? ; wolf) > true)&([ true* ] < (carrygoat? ; !carrycabbage? ; !carrywolf+ !carrygoat? ; carrycabbage? ; !carrywolf+ !carrygoat? ; !carrycabbage? ; carrywolf+ !carrygoat? ; !carrycabbage? ; !carrywolf) > true)&([ true* ] < (goat? ; man ; carrygoat? ; !goat? ; !man+ !goat? ; !man ; carrygoat? ; goat? ; man+ !goat ; !goat? ; !carrygoat + goat ; goat? ; !carrygoat) >true)&([ true* ] < (cabbage? ; man ;carrycabbage? ; !cabbage? ; !man + !cabbage? ; !man ;carrycabbage? ; cabbage? ; man+ !cabbage ; !cabbage? ; !carrycabbage + cabbage ;cabbage? ; !carrycabbage) > true)&([ true* ] < (wolf? ; man ; carrywolf? ; !wolf? ; !man+ !wolf? ; !man ; carrywolf? ; wolf? ; man+ !wolf ; !wolf? ; !carrywolf + wolf ; wolf? ; !carrywolf) >true)"
#
# a = constructTester("[true*;a]b & [true*;a]c")
# print("测试器构造完成：")
# printTester(a)
# a = constructTester("<(a;b*{2,2})*{3,3}>c")
# printTester(a)