import src.parser.ldl.lex_ldl as Parse
import re
import dd.cudd as cudd

bdd = cudd.BDD()


class Tester:
    def __init__(self, vars, init, trans, final=bdd.true , tran_str=bdd.true):
        self.vars = vars
        self.init = init
        self.trans = trans
        self.final = final
        self.tran_str = tran_str


def prime(var):
    "创建加撇的变量,输入为str类型或bdd变量，输出为bdd变量"
    pattern = r"\d+$"
    if type(var) != str:
        result = str(var.var)
    else:
        result = var
    result = re.sub(pattern, lambda m: str(int(m.group()) + 1), result)
    bdd.declare(result)
    return bdd.var(result)



def prime_all_vars_in_list(list1):
    "整个列表加撇，返回str型变量名列表"
    ret = []
    for each in list1:
        ret.append(prime(each).var)
    return ret


def get_submap(expr1, prime=1):
    """获取变量映射表"""
    ret = dict()
    for each in expr1.support:
        if(prime == 1):
            primed_var = re.sub(r"\d+$", lambda m: str(int(m.group()) + 1), each)
        else:
            primed_var = re.sub(r"\d+$", lambda m: str(int(m.group()) - 1), each)
        bdd.declare(primed_var)
        ret[each] = primed_var
    return ret


def prime_expr(expr,prime=1):
    """表达式所有变量加撇"""
    if expr == bdd.true:
        return bdd.true
    elif expr == bdd.false:
        return bdd.false
    sub_map = get_submap(expr,prime)
    expr = bdd.let(sub_map, expr)
    if not sub_map:
        print('submap = [], expr = ',expr.var)
        raise Exception('输入了一个空expr', bdd.to_expr(expr))
    return expr



def is_proposition(root):
    "判断子树是否为命题公式"
    if root and root.val.type in ["AND", "OR"]:
        return is_proposition(root.left) and is_proposition(root.left)
    elif root and root.val.type in ["ATOM"]:
        return True
    elif root:
        return False


def get_name(val):
    """获取变量名字，为token的value+lineno+lexpos+序号"""
    return val.type + str(val.lineno) + str(val.lexpos) + "_0"



def int_to_bdd(num,varname='name',I = 'I'):
    "输入一个int型的数字，输出为BDD表示的布尔命题"
    # 将数字转换为二进制字符串
    bin_str = bin(num)[2:]
    # 获取二进制字符串的长度
    length = len(bin_str)
    # 声明BDD变量，变量名为x0, x1, ..., xn-1
    bdd.declare(*[I + f'{i}_' + varname for i in range(length)])
    # 初始化BDD为True
    ret = bdd.true
    # 遍历二进制字符串，从高位到低位
    for i, bit in enumerate(bin_str):
        i = len(bin_str) - 1 - i
        # 获取对应的BDD变量
        var = bdd.var(I +f'{i}_' + varname)
        # 如果二进制位为1，那么BDD与该变量相与
        if bit == '1':
            ret = ret & var
        # 如果二进制位为0，那么BDD与该变量的否定相与
        else:
            ret = ret & ~var
    # 返回BDD
    return ret


def dict2bdd(dict1):
    """字典转化为bdd表示"""
    output = bdd.true
    for var, value in dict1.items():
        bdd.declare(var)
        if value:
            output &= bdd.var(var)
        else:
            output &= ~bdd.var(var)
    return output

def equ_zero(num,varname='name',I = 'I'):
    "返回 I = 0 的bdd表达式"
    # 将数字转换为二进制字符串
    bin_str = bin(num)[2:]
    # 获取二进制字符串的长度
    length = len(bin_str)
    # 声明BDD变量，变量名为x0, x1, ..., xn-1
    bdd.declare(*[I + f'{i}_' + varname for i in range(length)])
    # 初始化BDD为True
    ret = bdd.true
    # 遍历二进制字符串，从高位到低位
    for i, bit in enumerate(bin_str):
        i = len(bin_str) - 1 - i
        # 获取对应的BDD变量
        var = bdd.var(I +f'{i}_' + varname)
        # 如果二进制位为1，那么BDD与该变量相与
        ret = ret & ~var
    # 返回BDD
    return ret


def i_prime_equ_zero(num,varname='name_0',I = 'I'):
    "返回 I' = 0 的bdd表达式"
    prime_name = prime(varname).var
    ret = equ_zero(num,prime_name,I)
    return ret

# u = i_prime_equ_zero(10,'abc_0','I')
# print(list(bdd.pick_iter(u)))

def get_init_name(init_bdd1):
    """输入init，返回变量名"""
    if init_bdd1 and init_bdd1 != bdd.false and init_bdd1 != bdd.true and bdd.add_expr(init_bdd1.var) != init_bdd1:
        return bdd.to_expr(init_bdd1)
    return str(init_bdd1.var if init_bdd1.var else ('true' if init_bdd1 == bdd.true else 'false'))


def i_prime_euql_i_sub_1(num, varname='name_0', I='I'):
    # 将数字转换为二进制字符串
    bin_str = bin(num)[2:]
    # 获取二进制字符串的长度
    length = len(bin_str)
    # 声明BDD变量，变量名为x0, x1, ..., xn-1
    bdd.declare(*[I + f'{i}_' + varname for i in range(length)])
    # 初始化BDD为True
    ret = bdd.true
    # 遍历二进制字符串，从高位到低位
    for i, bit in enumerate(bin_str):
        var = bdd.var(I + f'{i}_' + varname)
        # print(var.var)
        rrr = bdd.true
        for j in range(0,i):
            rrr = rrr & prime(bdd.var(I + f'{j}_' + varname))
            # print(prime(bdd.var(I + f'{j}_' + varname)).var)
        ret = ret & ( var.equiv(bdd.apply('xor',prime(var),rrr)) )
        # print()
    # 返回BDD
    return ret


# u = i_prime_euql_i_sub_1(15)
# print(bdd.to_expr(u))
# print(u == bdd.add_expr(r'(I0_name_0 <-> I0_name_1 ^ TRUE) & (I1_name_0 <-> I1_name_1 ^ (I0_name_1 & TRUE)) & (I2_name_0 <-> I2_name_1 ^ (I1_name_1 & I0_name_1 & TRUE)) & (I3_name_0 <-> I3_name_1 ^ (I2_name_1 &I1_name_1 & I0_name_1 & TRUE))'))

def i_prime_euql_i(num, varname='name_0', I='I'):
    # 将数字转换为二进制字符串
    bin_str = bin(num)[2:]
    # 获取二进制字符串的长度
    length = len(bin_str)
    # 声明BDD变量，变量名为x0, x1, ..., xn-1
    bdd.declare(*[I + f'{i}_' + varname for i in range(length)])
    # 初始化BDD为True
    ret = bdd.true
    # 遍历二进制字符串，从高位到低位
    for i, bit in enumerate(bin_str):
        var = bdd.var(I + f'{i}_' + varname)
        ret = ret & ( var.equiv(prime(var)) )
    # 返回BDD
    return ret

# u = i_prime_euql_i(15)
# print(bdd.to_expr(u))
# print(u == bdd.add_expr(r'(I0_name_0 <-> I0_name_1)&(I1_name_0 <-> I1_name_1)&(I2_name_0 <-> I2_name_1)&(I3_name_0 <-> I3_name_1)'))




interval_variable = []

def construct_bdd(root, constructed_tester=None):
    """自底向上递归构造(全测试器)"""
    if constructed_tester is None:
        constructed_tester = {}
    if root:
        var_name = get_name(root.val)
        if root.val.type in ["BOUNDED_OR", "BOUNDED_AND"]:
            m = re.search(r'\*{(\d+),(\d+)}', root.val.value)
            num1 = int(m.group(1))  # 提取第一个数字
            num2 = int(m.group(2))  # 提取第二个数字
            if num2 - num1 < 0:
                raise Exception('语法错误：区间上界应该大于下界')
            interval_variable.append((var_name, num1, num2))
            III = int_to_bdd(num1,var_name,'I')
            JJJ = int_to_bdd(num2-num1, var_name,'J')

        if root.val.type != "EXPR":
            l = construct_bdd(root.left, constructed_tester)
            if root.val.type in ["BOUNDED_OR","BOUNDED_AND"]:
                interval_variable.pop()
            r = construct_bdd(root.right, constructed_tester)

        if var_name in constructed_tester:
            """已经构造过的测试无需再构造"""
            return constructed_tester[var_name]

        if root.val.type in ["ATOM", "EXPR"]:
            variables = set()
        elif root.val.type in ["STAR", "BOUNDEDSTAR", "TEST", "NOT"]:
            variables = l.vars
        else:
            variables = l.vars.union(r.vars)

        bdd.declare('X_' + var_name)
        var_name_bdd = bdd.var("X_" + var_name)

        if root.val.type == "BOUNDED_OR":
            "是星号指向的EXPR，需要创建变量："
            init1 = var_name_bdd
            init = init1 & int_to_bdd(num1, var_name, 'I') & int_to_bdd(num2 - num1, var_name, 'J')
            variables.add(var_name_bdd.var)
            variables = variables.union(bdd.support(int_to_bdd(num1, var_name, 'I')))
            variables = variables.union(bdd.support(int_to_bdd(num2 - num1, var_name, 'J')))
            trans = (
                            (init1 & ~equ_zero(num1, var_name, 'I')).implies(l.init) &
                            (init1 & equ_zero(num1, var_name, 'I') & ~equ_zero(num2 - num1, var_name, 'J')).implies(l.init | r.init) &
                            (init1 & equ_zero(num1, var_name, 'I') & equ_zero(num2 - num1, var_name, 'J')).implies(r.init)
                    ) & l.trans & r.trans
            trans_str = ("(" + init1.var + " & I != 0 -> (" + get_init_name(l.init) + ")) " + "&" +
                         "(" + init1.var + " & I = 0 & J != 0" + " -> (" + get_init_name(l.init) + " & " + get_init_name(r.init) + ")) " + "&"
                         "(" + init1.var + " & I = 0 & J = 0" + " -> (" + get_init_name(r.init) + ")) " + "&"
                         + "& " + l.tran_str + " & " + r.tran_str)
            f = ~init1 & l.final & r.final
        elif root.val.type == "BOUNDED_AND":
            "是星号指向的EXPR，需要创建变量："
            init1 = var_name_bdd
            init = init1 & int_to_bdd(num1, var_name, 'I') & int_to_bdd(num2 - num1, var_name, 'J')
            variables.add(var_name_bdd.var)
            variables = variables.union(bdd.support(int_to_bdd(num1, var_name, 'I')))
            variables = variables.union(bdd.support(int_to_bdd(num2 - num1, var_name, 'J')))
            trans = (
                            (init1 & ~equ_zero(num1, var_name, 'I')).implies(l.init) &
                            (init1 & equ_zero(num1, var_name, 'I') & ~equ_zero(num2 - num1, var_name, 'J')).implies(l.init & r.init) &
                            (init1 & equ_zero(num1, var_name, 'I') & equ_zero(num2 - num1, var_name, 'J')).implies(r.init)
                    )& l.trans & r.trans
            trans_str = ("(" + init1.var+ " & I != 0 -> (" + get_init_name(l.init) +  ")) " + "&" +
                         "(" + init1.var + " & I = 0 & J != 0" + " -> (" + get_init_name(l.init) + " & " + get_init_name(r.init) + ")) " + "&"
                         "(" + init1.var + " & I = 0 & J = 0" + " -> (" + get_init_name(r.init) + ")) " + "&"
                         +"& " + l.tran_str + " & " + r.tran_str)
            f = l.final & r.final
            # f = bdd.true
        elif root.val.type == "STAR_AND":
            "是星号指向的EXPR，需要创建变量："
            init = var_name_bdd
            variables.add(var_name_bdd.var)
            trans = init.equiv(l.init & r.init) & l.trans & r.trans
            trans_str = "(" + init.var + "<-> (" + get_init_name(l.init) + " & " + get_init_name(r.init) + ")) & " + l.tran_str + " & " + r.tran_str
            f = l.final & r.final
            # f = bdd.true
        elif root.val.type == "STAR_OR":
            "是星号指向的EXPR，需要创建变量："
            init = var_name_bdd
            variables.add(var_name_bdd.var)
            trans = init.equiv(l.init | r.init) & l.trans & r.trans
            trans_str = "(" + init.var + " <-> (" + get_init_name(l.init) + " | " + get_init_name(r.init) + ")) & " + l.tran_str + " & " + r.tran_str
            f = ~init & l.final & r.final
        elif root.val.type == "AND":
            "命题逻辑"
            init = l.init & r.init
            trans = l.trans & r.trans
            trans_str =  '(' + l.tran_str + " & " + r.tran_str + ')'
            f = l.final & r.final
        elif root.val.type == "OR":
            "命题逻辑"
            init = l.init | r.init
            trans = l.trans & r.trans
            trans_str = '(' + l.tran_str + " & " + r.tran_str + ')'
            f = l.final & r.final
        elif root.val.type == "REXIST" and root.left.val.type in ["AND", "OR", "ATOM", "NOT", "TEST"]:
            "REXIST算子："
            init = var_name_bdd
            variables.add(var_name_bdd.var)
            if root.left.val.type == "TEST":
                trans = init.equiv(l.init & r.init) & l.trans & r.trans
                trans_str = "(" + init.var + " <-> " + get_init_name(l.init) + " & " + get_init_name(r.init) + ") & " + l.tran_str + " & " + r.tran_str
            else:
                "<prop>expr,需要prime()的"
                if interval_variable and root.right.val.type in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且需要使I'=I-1"
                    vals = interval_variable[-1]  ##这是一个如(var_name, num1, num2)的元组
                    if root.right.left.val.type in ["BOUNDED_OR", "BOUNDED_AND"]:
                        inter_vals = (  # I'=I-1 and J'=J-1
                            (~equ_zero(vals[1], vals[0], 'I') & i_prime_euql_i_sub_1(vals[1],vals[0],'I') & i_prime_euql_i(vals[2]-vals[1],vals[0],'J')) |
                            (equ_zero(vals[1], vals[0], 'I') & ~equ_zero(vals[2] - vals[1],vals[0],'J') & i_prime_equ_zero(vals[1],vals[0], 'I')& i_prime_euql_i_sub_1(vals[2]-vals[1],vals[0],'J')) |
                            (equ_zero(vals[1], vals[0], 'I') & equ_zero(vals[2] - vals[1], vals[0], 'J') & i_prime_equ_zero(vals[1],vals[0], 'I') & i_prime_equ_zero(vals[2]-vals[1],vals[0], 'J'))
                        )
                    else:
                        inter_vals = i_prime_euql_i(vals[1],vals[0],'I') & i_prime_euql_i(vals[2]-vals[1],vals[0],'J')  # I'=I and J'=J
                    for each in interval_variable[0:len(interval_variable) - 1]:
                        ""
                        val = i_prime_euql_i(each[1],each[0],'I') & i_prime_euql_i(each[2]-each[1],each[0],'J') # I'=I  and J'=J
                        inter_vals = (inter_vals & val)
                    trans = init.equiv(l.init & prime_expr(r.init) & inter_vals) & l.trans & r.trans
                    trans_str = "("+ init.var+" <-> ("+ get_init_name(l.init) +" & "+get_init_name(r.init)+"' & I' = I-1 & J' = J-1) " + ") & " + l.tran_str + " & " + r.tran_str
                elif interval_variable and root.right.val.type not in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且不需要使I'=I-1，则只要I'=I"
                    inter_vals = bdd.true
                    for each in interval_variable:
                        ""
                        val = i_prime_euql_i(each[1],each[0],'I') & i_prime_euql_i(each[2]-each[1],each[0],'J')# I'=I  and J'=J
                        inter_vals = inter_vals & val
                    trans = init.equiv(l.init & prime_expr(r.init) & inter_vals) & l.trans & r.trans
                    trans_str = "("+ init.var+" <-> ("+ get_init_name(l.init) +" & "+get_init_name(r.init)+"' & I' = I & J' = J) " + ") & " + l.tran_str + " & " + r.tran_str
                else:
                    "interval_variable为空的情况，不存在有界的*，只需正常处理X_ -> l & X_r' 即可"
                    trans = init.equiv(l.init & prime_expr(r.init)) & l.trans & r.trans
                    trans_str = "(" + init.var + " <-> (" + get_init_name(l.init) + " & " + get_init_name(r.init) + "')) & " + l.tran_str + " & " + r.tran_str
                "interval_variable为空的情况，不存在有界的*，只需正常处理X_ -> l & X_r' 即可"
                # trans = init.equiv(l.init & prime_expr(r.init)) & l.trans & r.trans
                # trans_str = "(" + init.var + " <-> (" + get_init_name(l.init) + " & " + get_init_name(r.init) + "')) & " + l.tran_str + " & " + r.tran_str
            f = ~init & l.final & r.final
        elif root.val.type == "RFORALL" and root.left.val.type in ["AND", "OR", "ATOM", "NOT", "TEST"]:
            "RFORALL算子："
            init = var_name_bdd
            variables.add(var_name_bdd.var)
            if root.left.val.type == "TEST":
                trans = init.equiv(l.init.implies(r.init)) & l.trans & r.trans
                trans_str = "(" + init.var + " <-> (" + get_init_name(l.init) + " -> " + get_init_name(r.init) + ")) &" + l.tran_str + " & " + r.tran_str
            else:
                "[prop]expr,需要prime()的"
                if interval_variable and root.right.val.type in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且需要使I'=I-1"
                    vals = interval_variable[-1]  ##这是一个如(var_name, num1, num2)的元组
                    if root.right.left.val.type in ["BOUNDED_OR", "BOUNDED_AND"]:
                        inter_vals = (  # I'=I-1 and J'=J-1
                            (~equ_zero(vals[1], vals[0], 'I') & i_prime_euql_i_sub_1(vals[1],vals[0],'I') & i_prime_euql_i(vals[2]-vals[1],vals[0],'J')) |
                            (equ_zero(vals[1], vals[0], 'I') & ~equ_zero(vals[2] - vals[1],vals[0],'J') & i_prime_equ_zero(vals[1],vals[0], 'I')& i_prime_euql_i_sub_1(vals[2]-vals[1],vals[0],'J')) |
                            (equ_zero(vals[1], vals[0], 'I') & equ_zero(vals[2] - vals[1], vals[0], 'J') & i_prime_equ_zero(vals[1],vals[0], 'I') & i_prime_equ_zero(vals[2]-vals[1],vals[0], 'J'))
                        )
                    else:
                        inter_vals = i_prime_euql_i(vals[1],vals[0],'I') & i_prime_euql_i(vals[2]-vals[1],vals[0],'J')  # I'=I and J'=J
                    for each in interval_variable[0:len(interval_variable) - 1]:
                        ""
                        val = i_prime_euql_i(each[1],each[0],'I') & i_prime_euql_i(each[2]-each[1],each[0],'J') # I'=I  and J'=J
                        inter_vals = (inter_vals & val)

                    trans = init.equiv(l.init.implies(prime_expr(r.init) & inter_vals))  &  l.trans & r.trans
                    trans_str = "("+ init.var+" -> (("+ get_init_name(l.init) +" -> "+get_init_name(r.init)+"') & I' = I-1 & J' = J-1) " + ") & " + l.tran_str + " & " + r.tran_str
                elif interval_variable and root.right.val.type not in ["EXPR"]:
                    "如果interval_variable列表不空，说明上面存在有界*，而且不需要使I'=I-1，则只要I'=I"
                    inter_vals = bdd.true
                    for each in interval_variable:
                        ""
                        val = i_prime_euql_i(each[1],each[0],'I') & i_prime_euql_i(each[2]-each[1],each[0],'J')# I'=I  and J'=J
                        inter_vals = inter_vals & val
                    trans = init.equiv(l.init.implies(prime_expr(r.init) & inter_vals))  & l.trans & r.trans
                    trans_str = "("+ init.var+" <-> (("+ get_init_name(l.init) +" -> "+get_init_name(r.init)+"') & I' = I & J' = J) " + ") & " + l.tran_str + " & " + r.tran_str
                else:
                    "interval_variable为空的情况，不存在有界的*，只需正常处理X_ -> l & X_r' 即可"
                    trans = init.equiv(l.init.implies(prime_expr(r.init))) & l.trans & r.trans
                    trans_str = "(" + init.var + " <-> (" + get_init_name(l.init) + " -> " + get_init_name(r.init) + "')) & " + l.tran_str + " & " + r.tran_str
                "interval_variable为空的情况，不存在有界的*，只需正常处理X_ -> l & X_r' 即可"
                # trans = init.equiv(l.init.implies(prime_expr(r.init))) & l.trans & r.trans
                # trans_str = "(" + init.var + " <-> (" + get_init_name(l.init) + " -> " + get_init_name(r.init) + "'))&" + l.tran_str + "&" + r.tran_str
            # f = bdd.true
            f = l.final & r.final

        elif root.val.type == "ATOM":
            "原子命题,不构造Xa->a的"
            if root.val.value in ["TRUE", "True", "true"]:
                init = bdd.true
            elif   root.val.value in ["False", "FALSE", "false"]:
                init = bdd.false
            else:
                bdd.declare(root.val.value + "_0")
                init = bdd.var(root.val.value + "_0")
                variables.add(init.var)
            trans = bdd.true
            trans_str = "true"
            f = bdd.true
        elif root.val.type == "NOT":
            "原子命题"
            if root.left.val.value in ["TRUE", "True", "true"]:
                init = bdd.false
                trans = bdd.true
            elif root.left.val.value in ["FALSE", "False", "false"]:
                init = bdd.true
                trans = bdd.true
            else:
                init = ~l.init
                trans = bdd.true
            trans_str = "true"
            f = bdd.true


        elif root.val.type == "EXPR":
            "标记的原子命题"
            bdd.declare("X_" + get_name(root.left.val))
            init = bdd.var("X_" + get_name(root.left.val))
            variables.add(init.var)
            trans = bdd.true
            trans_str = "true"
            f = bdd.true

        elif root.val.type == "TEST":
            "测试"
            init = l.init
            trans = l.trans
            trans_str = 'true'
            f = l.final
        else:
            print("something wrong!")
            print("正在构造" + var_name)
        # 简化命题公式

        tester = Tester(variables, init, trans, f , trans_str)
        constructed_tester[var_name] = tester
        # printTester(tester)
        return tester


def constructTester(ldl):
    """测试器构造"""
    root = Parse.parser(ldl)
    tester = construct_bdd(root)
    # printTester(tester)
    # print('Tester:')
    # print('vars',tester.vars)
    # print("Init :", list(bdd.pick_iter(tester.init)))
    # print('Trans:', tester.tran_str.replace(" & true",""))
    # print('Final:', list(bdd.pick_iter(tester.final)))
    return tester


def printTester(tester,mod = 1):
    if mod == 0:
        print(bdd.to_expr(tester.init) + "的测试器：")
        print("support:  ", end="")
        print(tester.trans.support)
        print("vars:  ", end="")
        print(tester.vars)
        print("init:  ", end="")
        print(bdd.to_expr(tester.init))
        print("trans: ", end="")
        print(bdd.to_expr(tester.trans))
        print("final: ", end="")
        print(bdd.to_expr(tester.final))
    else:
        print(bdd.to_expr(tester.init) + "的测试器：")
        print("support:  ", end="")
        print(tester.trans.support)
        print("vars:  ", end="")
        print(tester.vars)
        print("init:  ", end="")
        print(list(bdd.pick_iter(tester.init)))
        print("trans:  ")
        trans = list(bdd.pick_iter(tester.trans))
        for each in trans:
            print(each)
        print("final: ", end="")
        print(list(bdd.pick_iter(tester.final)))
    print("")

# a = constructTester("<((a;b)*{1,1};c)*{2,2}>d")
# a = constructTester("[true*;a]<true*>b")
# example1 = "(!cabbage & !goat & !wolf & !man & !carrygoat& !carrycabbage & !carrywolf) & (< true* ; cabbage? ; goat? > wolf)&([ true* ] < (goat? ; man + !goat? ; !man +goat? ; !cabbage? ; !wolf + !goat? ; cabbage? ; wolf) > true)&([ true* ] < (carrygoat? ; !carrycabbage? ; !carrywolf+ !carrygoat? ; carrycabbage? ; !carrywolf+ !carrygoat? ; !carrycabbage? ; carrywolf+ !carrygoat? ; !carrycabbage? ; !carrywolf) > true)&([ true* ] < (goat? ; man ; carrygoat? ; !goat? ; !man+ !goat? ; !man ; carrygoat? ; goat? ; man+ !goat ; !goat? ; !carrygoat + goat ; goat? ; !carrygoat) >true)&([ true* ] < (cabbage? ; man ;carrycabbage? ; !cabbage? ; !man + !cabbage? ; !man ;carrycabbage? ; cabbage? ; man+ !cabbage ; !cabbage? ; !carrycabbage + cabbage ;cabbage? ; !carrycabbage) > true)&([ true* ] < (wolf? ; man ; carrywolf? ; !wolf? ; !man+ !wolf? ; !man ; carrywolf? ; wolf? ; man+ !wolf ; !wolf? ; !carrywolf + wolf ; wolf? ; !carrywolf) >true)"
#
# a = constructTester("[true*;a]b & [true*;a]c")
# print("测试器构造完成：")
# printTester(a)

# a = constructTester("<true*>a")
# print("测试器构造完成：")
# printTester(a)
# x = prime_expr(bdd.true)
# print(list(bdd.pick_iter(x)))