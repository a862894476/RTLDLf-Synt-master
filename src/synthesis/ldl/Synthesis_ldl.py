
from src.tester.ldl.Tester_BDD_ldl import cudd,bdd
from src.tester.ldl import Tester_BDD_ldl
from src.synthesis import env_vars_process
import src.util as util
from z3 import *

def synthesis_bdd(formula, env_vars="" ,sys_vars=""):
    """基于BDD的不动点计算法（速度快）"""
    # print(formula)
    tester = Tester_BDD_ldl.constructTester(formula)
    # Tester.printTester(tester)
    if type(env_vars) == str:
        # print(env_vars)
        env_vars = env_vars_process.env_vars_preprocess_bdd(env_vars, bdd)  # 环境变量预处理
        sys_vars = env_vars_process.env_vars_preprocess_bdd(sys_vars, bdd)  # 环境变量预处理
    else:
        env_vars = env_vars_process.env_vars_preprocess_bdd_list(env_vars, bdd)
        sys_vars = env_vars_process.env_vars_preprocess_bdd_list(sys_vars, bdd)

    env_vars_k = env_vars  # 前k步的所有环境变量
    print("环境变量集合：" + str(env_vars))
    ctrl_vars = tester.vars - set(env_vars)
    ctrl_vars = list(ctrl_vars)
    print("系统变量集合：" + str(ctrl_vars))


    env_vars_prime = Tester_BDD_ldl.prime_all_vars_in_list(env_vars)
    ctrl_vars_prime = Tester_BDD_ldl.prime_all_vars_in_list(ctrl_vars)
    sys_vars_prime = Tester_BDD_ldl.prime_all_vars_in_list(sys_vars)

    init = tester.init
    trans = tester.trans
    final = tester.final
    win = final
    w = final




    win_set = [final]
    # print(list(bdd.pick_iter(win_set[-1])))

    i = 0
    while (True):
        "不动点计算"
        print("step:"+str(i))
        i += 1
        w = cudd.or_forall(cudd.and_exists(trans, Tester_BDD_ldl.prime_expr(win_set[-1]), ctrl_vars_prime), bdd.false, env_vars_prime)
        # w = bdd.forall(env_vars_prime, bdd.exist(ctrl_vars_prime, trans & Tester_BDD_ldl.prime_expr(win_set[-1]) ))
        if win == (win | w):
            print('到达不动点')
            break
        win_set.append(w)
        win = (win | w)


    if win & init == bdd.false:
        print("Unrealizable.")
        return
    elif cudd.and_exists(win, init, env_vars) == bdd.false:
        print("Unrealizable.")
        return
    else:
        print("Further calculate: \n")


    all_pos_x = list(bdd.pick_iter(bdd.true, env_vars))
    print('len(win_set) = ',len(win_set))
    states = init  & win
    while win_set:
        # print('form ',list(bdd.pick_iter(states)))
        print('to w[', i-1, ']')
        win_i = win_set.pop()
        next_states = bdd.false
        for each_input in all_pos_x:
            print('for input : ',each_input)
            # print('bdd.let(each_input,states & trans) == bdd.false ? :',bdd.let(each_input,states & trans) == bdd.false)
            # print('bdd.let(each_input,states & trans) :',list(bdd.pick_iter(bdd.let(each_input,states))))
            next_state = cudd.and_exists( bdd.let(each_input,states & trans), Tester_BDD_ldl.prime_expr(win_i), ctrl_vars)
            print('next_state',list(bdd.pick_iter(next_state)))
            next_states |= next_state
            if next_state == bdd.false:
                print("Unrealizable1.")
                return
        # next_states = bdd.forall(env_vars, bdd.exist(ctrl_vars, states & trans & Tester_BDD_ldl.prime_expr(win_i)))
        # print('next_states = ', list(bdd.pick_iter(next_states)))
        if next_states == bdd.false:
            print("Unrealizable.")
            return
        states = Tester_BDD_ldl.prime_expr(next_states,-1)
        i -= 1
    print('Realizable.')

# util.ltl2ldl('a <-> X[!] b')


def synthesis_bdd_test(formula, env_vars="" ,sys_vars=""):
    """基于BDD的不动点计算法（速度快）"""
    # print(formula)
    tester = Tester_BDD_ldl.constructTester(formula)
    # Tester.printTester(tester)
    if type(env_vars) == str:
        # print(env_vars)
        env_vars = env_vars_process.env_vars_preprocess_bdd(env_vars, bdd)  # 环境变量预处理
        sys_vars = env_vars_process.env_vars_preprocess_bdd(sys_vars, bdd)  # 环境变量预处理
    else:
        env_vars = env_vars_process.env_vars_preprocess_bdd_list(env_vars, bdd)
        sys_vars = env_vars_process.env_vars_preprocess_bdd_list(sys_vars, bdd)

    env_vars_k = env_vars  # 前k步的所有环境变量
    print("环境变量集合：" + str(env_vars))
    ctrl_vars = tester.vars - set(env_vars)
    ctrl_vars = list(ctrl_vars)
    print("系统变量集合：" + str(ctrl_vars))


    env_vars_prime = Tester_BDD_ldl.prime_all_vars_in_list(env_vars)
    ctrl_vars_prime = Tester_BDD_ldl.prime_all_vars_in_list(ctrl_vars)
    sys_vars_prime = Tester_BDD_ldl.prime_all_vars_in_list(sys_vars)

    init = tester.init
    trans = tester.trans
    final = tester.final
    win = final
    w = final




    win_set = [final]
    # print(list(bdd.pick_iter(win_set[-1])))

    i = 0
    while (True):
        "不动点计算"
        print("step:"+str(i))
        i += 1
        w = cudd.or_forall(cudd.and_exists(trans, Tester_BDD_ldl.prime_expr(win_set[-1]), ctrl_vars_prime), bdd.false, env_vars_prime)
        # w = bdd.forall(env_vars_prime, bdd.exist(ctrl_vars_prime, trans & Tester_BDD_ldl.prime_expr(win_set[-1]) ))
        if win == (win | w):
            print('到达不动点')
            break
        win_set.append(w)
        win = (win | w)


    if win & init == bdd.false:
        print("Unrealizable.")
        return
    elif cudd.and_exists(win, init, env_vars) == bdd.false:
        print("Unrealizable.")
        return
    else:
        print("Further calculate: \n")

    realizable = True
    import queue
    states = queue.Queue()
    steps = queue.Queue()
    counted_states = set()
    n = i - 1
    iterator_input = list(bdd.pick_iter(bdd.true, env_vars))
    for each_x in iterator_input:
        print('for x: ',each_x)
        output = bdd.let(each_x, win_set[n] & init)
        if output == bdd.false:
            realizable = False
            print('Unrealizable')
            return
        iterator_output = bdd.pick_iter(output)
        # iterator_output = [bdd.pick(output)]
        for each_y in iterator_output:
            state = each_y.copy()
            state.update(each_x)
            # print('have y: ', each_y)
            print('state :', state, end=' ')
            state = bdd.cube(state)
            print(state)
            if state not in counted_states:
                states.put(state)
                steps.put(n)
                counted_states.add(state)


    while not states.empty():
        n = steps.get()
        state = states.get()
        print(state,n)
        for each_x in iterator_input:
            print('for x: ', each_x)
            output = bdd.let(each_x,Tester_BDD_ldl.prime_expr(cudd.restrict(trans & Tester_BDD_ldl.prime_expr(win_set[n-1]), state), -1))
            if output == bdd.false:
                realizable = False
            if cudd.restrict(output, final) != bdd.false:
                print('reach_final')
                continue
            # iterator_output = bdd.pick_iter(output)
            iterator_output = [bdd.pick(output)]
            for each_y in iterator_output:
                next_state = each_y.copy()
                next_state.update(each_x)
                # print('have y: ', each_y)
                print('state :', next_state, end=' ')
                next_state = bdd.cube(next_state)
                print(next_state)
                if next_state not in counted_states and n-1>=0:
                    states.put(next_state)
                    steps.put(n-1)
                    counted_states.add(next_state)


    print("Realizable" if realizable else "Unrealizable")