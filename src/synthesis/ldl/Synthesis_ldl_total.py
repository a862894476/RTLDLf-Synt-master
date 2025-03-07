
from src.tester.ldl.Tester_BDD_ldl_total import cudd,bdd
from src.tester.ldl import Tester_BDD_ldl_total
from src.synthesis import env_vars_process
import src.util as util
from z3 import *


def synthesis_bdd_test(formula, env_vars="" , sys_vars="", final_step=0, to_graph = 1):
    """基于BDD的不动点计算法（速度快）"""
    # print(formula)
    tester = Tester_BDD_ldl_total.constructTester(formula)
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


    env_vars_prime = Tester_BDD_ldl_total.prime_all_vars_in_list(env_vars)
    ctrl_vars_prime = Tester_BDD_ldl_total.prime_all_vars_in_list(ctrl_vars)
    sys_vars_prime = Tester_BDD_ldl_total.prime_all_vars_in_list(sys_vars)

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
        w = cudd.or_forall(cudd.and_exists(trans, Tester_BDD_ldl_total.prime_expr(win_set[-1]), ctrl_vars_prime), bdd.false, env_vars_prime)
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

    out_print = open("strategy.dot", "w")
    out_print.write("digraph TESTER {")
    out_print.write("node [shape = box];\n")


    realizable = True
    import queue
    states = queue.Queue()
    xy = queue.Queue()
    steps = queue.Queue()
    counted_states = set()
    n = i - 1
    iterator_input = list(bdd.pick_iter(bdd.true, env_vars))
    for each_x in iterator_input:
        # print('for input: ',each_x)
        output = bdd.let(each_x, win_set[n] & init) if each_x else win_set[n] & init
        output = output & bdd.cube(each_x)
        # print('init_set:',output,list(bdd.pick_iter(output)))
        if output == bdd.false:
            realizable = False
            print('Unrealizable')
            return
        # iterator_output = bdd.pick_iter(output)
        state = output
        # all_states = bdd.pick_iter(state)
        all_states = [bdd.pick(state)]
        for each in all_states:
            output_input = util.print_input_output({key: each[key] for key in sys_vars+env_vars if key in each})
            output_input = output_input if output_input else 'true'
            out_print.write(' "init" -> "' + output_input + '" [label="' +'['+str(n)+']'+ util.print_input_output(each_x) +  '"];\n')
        if state not in counted_states:
            states.put(state)
            steps.put(n)
            xy.put(output_input)
            counted_states.add(state)


    while not states.empty():
        is_final = False
        n = steps.get()
        state = states.get()
        last_xy = xy.get()
        # print('\n处理：states_set',state,n)
        output = Tester_BDD_ldl_total.prime_expr(bdd.exist(env_vars+ctrl_vars,cudd.restrict(trans & Tester_BDD_ldl_total.prime_expr(win_set[n-1]), state)), -1)
        # print('next_states_set',output,list(bdd.pick_iter(output)))
        if output & final != bdd.false:
            is_final = True
        for each_x in iterator_input:
            # print('for input: ', each_x)
            output1 = bdd.let(each_x, output) if each_x else output
            output1 = output1 & bdd.cube(each_x)
            # print('to states_set: ', list(bdd.pick_iter(output1)) , output1)
            if output1 == bdd.false:
                realizable = False
                print('Unrealizable')
                return
            state = output1

            if n == final_step:
                out_print.write(
                    ' "' + last_xy + '" -> "' + 'final' + '" ;\n')
            else:
                all_states = [bdd.pick(state)]
                for each in all_states:
                    output_input = util.print_input_output({key: each[key] for key in sys_vars + env_vars if key in each})
                    output_input = output_input if output_input else 'true'
                    out_print.write(
                        ' "'+last_xy+'" -> "' + output_input + '" [label="' + '[' + str(n-1) + ']' + util.print_input_output(
                            each_x) + '"];\n')

                    if state & final != bdd.false:
                        out_print.write(
                            ' "' + output_input + '" -> "' + 'final' + '" ;\n')

            if state not in counted_states and n-1 > 0:
                states.put(state)
                steps.put(n-1)
                xy.put(output_input)
                counted_states.add(state)

    print("Realizable" if realizable else "Unrealizable")
    out_print.write("}")
    out_print.close()
    util.remove_duplicate_lines('strategy.dot')
    if to_graph == 1:
        os.system("dot -Tsvg strategy.dot > strategy.svg")

