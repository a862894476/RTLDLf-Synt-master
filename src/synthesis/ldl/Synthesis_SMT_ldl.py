

from src.tester.ldl import Tester_SMT_ldl
from src.synthesis import env_vars_process
import src.util as util
from z3 import *

def env_vars_preprocess_smt(env_vars):
    """环境变量预处理"""
    ret = []
    if env_vars == "":
        return []
    env_vars = env_vars.split(" ")
    for each in env_vars:
        ret.append(Bool(each + "_0"))
    return ret

def print_model(model):
    """输出SAT求解满足的模型"""
    # print(model)
    sorted_model = sorted([(d.name(), model[d]) for d in model], key=lambda x: x[0])
    states = []
    for name, value in sorted_model:
        if name[0:2] not in ["X_", "I_", "J_"] and name not in ["true", "True", "TRUE"]:
            # print(name + " = " + str(value))
            split = name.rsplit("_", 1)
            # print(split)
            while (len(states) <= int(split[1])):
                states.append([])
            if value == BoolVal(False):
                states[int(split[1])].append("!" + split[0])
            else:
                states[int(split[1])].append(split[0])
    for index in range(0, len(states)):
        print("State" + str(index) + " |= ", end="")
        print(states[index])

def smt_solve(TR, i):
    """求解"""
    solver = z3.Solver()
    # solver.add(ForAll(env_vars_k,Exists(ctrl_vars_k,TR)))
    solver.add(TR)

    check_result = solver.check()
    if check_result == sat:
        print("步长为" + str(i) + "时，求解得到" + str(check_result))
        # print(solver.model())
        model = solver.model()
        print_model(model)
        print('Result: Realizable.')
    else:
        print("步长为" + str(i) + "时，求解得到" + str(check_result))

    return check_result

def vars_prime(vars1):
    vars1 = Tester_SMT_ldl.prime_all_vars_in_list(vars1)
    # print(vars1)
    return vars1


def synthesis_bounded(formula, env_vars="", k=100):
    """基于SMT的有界合成"""
    env_vars = env_vars_preprocess_smt(env_vars)  # 环境变量预处理
    env_vars_k = env_vars  # 前k步的所有环境变量
    print("环境变量集合：" + str(env_vars))

    # print(formula)
    tester,max_num = Tester_SMT_ldl.constructTester(formula)
    max_num = 0
    # Tester.printTester(tester)

    ctrl_vars = tester.vars - set(env_vars)
    ctrl_vars = list(ctrl_vars)
    ctrl_vars_k = ctrl_vars
    print("系统变量集合：" + str(ctrl_vars))

    print("测试器变量集合大小：" + str(len(tester.vars)))
    init = tester.init
    trans = tester.trans
    final = tester.final
    trans_k = trans

    for i in range(1, k):

        # print("步长为" + str(i) + "时，环境变量集合：" + str(env_vars_k))
        # all_env_values = get_all_values(env_vars_k) ## 所有环境变量取值的可能，存在一个列表中。比如环境变量集合：[c_0]，可能取值的集合[And(c_0 == True), And(c_0 == False)]
        # # print(all_env_values)
        #
        ctrl_vars = vars_prime(ctrl_vars)
        ctrl_vars_k = ctrl_vars_k + ctrl_vars
        # print("步长为" + str(i) + "时，控制器变量集合：" + str(ctrl_vars_k))

        # k步求解
        final = Tester_SMT_ldl.prime_expr(final)  # 第k步的终止条件
        TR = And(init, trans_k, final)  # 转化为SMT公式

        # result = unknown
        # for each in all_env_values:
        #     TR1 = And(TR,each)
        #     print("当环境变量取值"+str(each)+"时:")
        #     result = smt_solve(TR1,i)
        #     if result == unsat:
        #         print("不可合成")
        #         break
        # if result == sat:
        #     print("可合成")
        #     break
        if max_num < i:
            if env_vars_k == []:
                result = smt_solve(TR, i)
            else:
                result = smt_solve(ForAll(env_vars_k, Exists(ctrl_vars_k, TR)), i)
            if result == sat:
                break

        # solver = z3.Solver()
        # # solver.add(ForAll(env_vars_k,Exists(ctrl_vars_k,TR)))
        # solver.add(TR)
        #
        # check_result = solver.check()
        # if check_result == sat:
        #     print("步长为" + str(i) + "时，求解得到" +str(check_result))
        #     # print(solver.model())
        #     model = solver.model()
        #     print_model(model)
        #     break
        # else:
        #     print("步长为" + str(i) + "时，求解得到" +str(check_result))

        trans = Tester_SMT_ldl.prime_expr(trans)  # 第k步的迁移关系
        trans_k = And(trans, trans_k)  # 前k步的迁移关系

        env_vars = vars_prime(env_vars)  # 第k步的环境变量
        env_vars_k = env_vars_k + env_vars   # 前k步的环境变量

