import time
from src.synthesis.ldl import Synthesis_ldl
from src.synthesis.ldl import Synthesis_SMT_ldl
from src.synthesis.ldl import Synthesis_ldl_total
import src.util as util
import argparse
import os

def test():
    """"""
    # tlsf = util.parse_tlsf('examples/TLSF/Two-player-Game/Nim/nim_01/System-first/nim_01_05.tlsf')
    # tlsf = util.parse_tlsf('examples/TLSF/Random/Syft/syft_1/001.tlsf')
    # Synthesis_ldl_total.synthesis_bdd_test(util.ltl2ldl(tlsf[0]), tlsf[1], tlsf[2])
    # Synthesis_ldl.synthesis_bdd('<true*>((!a & !b)|(a & b))', 'a', 'b')
    # Synthesis_ldl.synthesis_bdd('[true*](!a | b) & <true*>(!b)', 'a', ' b ')
    # Synthesis_ldl.synthesis_bdd('!a & [ true* ; b? ] < !c? > !d & [ true* ; (a? ; !e? + !a? ; e?) ] !c & <true* > a','b', ' a c d  ')
    # tlsf = util.parse_tlsf('examples/TLSF/Two-player-Game/Single-Counter/System-first/counter_06.tlsf')
    # tlsf = util.parse_tlsf('examples/TLSF/Two-player-Game/Nim/nim_01/System-first/nim_01_01.tlsf')
    # tlsf = util.parse_tlsf('examples/TLSF/Random/Syft/syft_1/003.tlsf')
    # tlsf = util.parse_tlsf('examples/goat.tlsf')
    # tlsf2 = util.parse_tlsf_ldl('examples/goat2.tlsf')
    # Synthesis_ldl.synthesis_bdd_test(util.ltl2ldl(tlsf[0]), tlsf[1], tlsf[2])
    # Synthesis_ldl.synthesis_bdd(util.ltl2ldl("X[!]a -> b"), "a ", "b")
    # Synthesis_ldl.synthesis_bdd(util.ltl2ldl("F a <-> F a"), "a", "b")  #有问题
    # Synthesis_ldl.synthesis_bdd_test(util.ltl2ldl(" F(a <-> b )"), "a", "b") #有问题
    # Synthesis_ldl.synthesis_bdd(util.ltl2ldl(" G X[!] a"), "a", "b") #有问题
    # Synthesis_ldl.synthesis_bdd(util.ltl2ldl("F a"), "a", "b") #有问题
    # Synthesis_ldl.synthesis_bdd("<b*{5,6}>b", "a", "b") #有问题
    # Synthesis_ldl.synthesis_bdd(util.ltl2ldl("""(turn_sys && !turn_env && (!select_sys_0 -> heap_0_2) && (select_sys_0 -> (change_sys_0 || change_sys_1)))"""), "select_env_0 change_env_0 change_env_1", "select_sys_0 change_sys_0 change_sys_1 turn_sys turn_env heap_0_0 heap_0_1 heap_0_2")


    #全时态测试器
    # Synthesis_ldl_total.synthesis_bdd_test('<b*{100,100}>d','','b d ')
    # Synthesis_ldl_total.synthesis_bdd_test(util.ltl2ldl(tlsf[0]), tlsf[1], tlsf[2],1)
    # Synthesis_ldl_total.synthesis_bdd_test("<a>b", '', 'a b',2)
    # Synthesis_ldl_total.synthesis_bdd_test("[a]<b>c", '', 'a b c',1)
    # Synthesis_SMT_ldl.synthesis_bounded('<b>c','a')

    #过河问题

    # 过河问题SMT
    # tlsf2 = util.parse_tlsf_ldl('examples/goat2.tlsf')
    # Synthesis_SMT_ldl.synthesis_bounded(tlsf2[0], '', 1000)
    # 过河问题BDD
    # tlsf = util.parse_tlsf('examples/goat.tlsf')
    # Synthesis_ldl_total.synthesis_bdd_test(util.ltl2ldl(tlsf[0],0), tlsf[1], tlsf[2], 1, 1)


    #情景1：障碍交替阻止智能体前进方向
    exam1 = " <(true*;(toEast&!toNorth))*{3,3}>true  & <(true*;(toNorth&!toEast))*{3,3}>true & <(barrierN;!barrierN)*{3,3}>true & [true*](!barrierN | (toEast&!toNorth)) & [true*](barrierN | (toNorth&!toEast))"
    # 情景1 BDD
    # Synthesis_ldl_total.synthesis_bdd_test(exam1, '', 'barrierN toNorth toEast', 1)
    # 情景1 SMT
    # Synthesis_SMT_ldl.synthesis_bounded(exam1, '', 1000)

    #情景2：障碍位置完全由环境掌控，此时输出为Unrealizable.
    exam1 = " <(true*;(toEast&!toNorth))*{3,3}>true  & <(true*;(toNorth&!toEast))*{3,3}>true & [true*](!barrierN | (toEast&!toNorth)) & [true*](barrierN | (toNorth&!toEast))"
    # 情景2 BDD
    # Synthesis_ldl_total.synthesis_bdd_test(exam1, 'barrierN', 'toNorth toEast', 1)
    # 情景2 SMT
    # Synthesis_SMT_ldl.synthesis_bounded(exam1, 'barrierN', 1000)

    #环境周期性放置障碍，阻碍智能体前进
    exam1 = " <(true*;(toEast&!toNorth))*{3,3}>true  & <(true*;(toNorth&!toEast))*{3,3}>true & [true*]((!barrier&((toEast&!toNorth)|(!toEast&toNorth))) | (barrier & (!barrierN | (toEast&!toNorth)))) & [true*]((!barrier&((toEast&!toNorth)|(!toEast&toNorth))) | (barrier & (barrierN | (toNorth&!toEast)))) & <(barrier;!barrier)*{3,3}>true"
    # 情景3 BDD
    # Synthesis_ldl_total.synthesis_bdd_test(exam1, 'barrierN', 'barrier  toNorth toEast', 1)
    # 情景3 SMT
    # Synthesis_SMT_ldl.synthesis_bounded(exam1, '', 1000)

    # exam1,固定区间宽度为5，测试不同区间下界m时的性能消耗
    # exam1 BDD
    # m = 32768
    # exam2 = "<(act1;act2;act3;act4)*{%s,%s}>act5"%(m,m+5)
    # Synthesis_ldl_total.synthesis_bdd_test(exam2, '', 'act1 act2 act3 act4 act5', 1,0)
    # exam1 SMT
    # m = 224
    # exam2 = "<(act1;act2;act3;act4)*{%s,%s}>act5" % (m, m + 5)
    # Synthesis_SMT_ldl.synthesis_bounded(exam2,'',1000)

    # exam2，固定区间下界为5，测试不同区间宽度的性能消耗
    # exam2 BDD
    # n = 65536
    # exam2 = "<(act1;act2;act3;act4)*{%s,%s}>act5"%(5,n+5)
    # Synthesis_ldl_total.synthesis_bdd_test(exam2, '', 'act1 act2 act3 act4 act5', 1,0)
    # exam2 SMT
    # n = 2
    # exam2 = "<(act1;act2;act3;act4)*{%s,%s}>act5" % (5, 5 + n)
    # Synthesis_SMT_ldl.synthesis_bounded(exam2,'act4',100)

    # #exam2.5 区间下界为5，区间宽度、区间下界同时变化的性能消耗
    # # 区间下界为5，测试不同区间宽度的性能消耗,BDD
    # n = 200
    # exam2 = "<(act1;act2;act3;act4)*{%s,%s}>act5"%(5+n,2*n+5)
    # Synthesis_ldl_total.synthesis_bdd_test(exam2, 'act5', 'act1 act2 act3 act4 ', 1,0)

    # exam3，循环选择结构，测试循环次数n时的性能消耗
    # exam3，BDD
    # n = 127
    # exam2 = "<(condition?;act1 + (!condition)?;(act5)*;act6)*{%s,%s}>act9"%(n,n)
    # print(exam2)
    # Synthesis_ldl_total.synthesis_bdd_test(exam2, 'condition', 'act1 act2 act3 act4 act5 act6 act7 act8 atc9', 1,1)
    # exam3，SMT
    # n = 6
    # exam2 = "<(condition?;act1 + (!condition)?;(act5)*;act6)*{%s,%s}>act9" % (n, n)
    # print(exam2)
    # Synthesis_SMT_ldl.synthesis_bounded(exam2,'condition',100)

    # test
    # Synthesis_ldl_total.synthesis_bdd_test("<a*>!b", '', 'a b', 2, 1)



def main():
    """命令行方式执行"""
    # 创建 ArgumentParser 对象
    parser = argparse.ArgumentParser(description="Run synthesis methods (BDD or SMT) based on input parameters.")

    # 添加参数
    parser.add_argument("-e", "--method", choices=["bdd", "smt"], required=True,
                        help="Choose the method: 'bdd' for BDD method or 'smt' for SMT method.")
    parser.add_argument("-rtldlf", "--formula", type=str, required=True,
                        help="The formula to be used in the synthesis. Can be a formula string or a path to a .rtldlf file.")
    parser.add_argument("-env", "--env_vars", type=str, default="",
                        help="Environment variables.")
    parser.add_argument("-sys", "--sys_vars", type=str, default="",
                        help="System variables.")
    parser.add_argument("-f", "--final_step", type=int, default=0,
                        help="Final step for synthesis_bdd_test for BDD method.")
    parser.add_argument("-g", "--to_graph", type=int, default=1,
                        help="Whether to generate a graph (1 for yes, 0 for no) for BDD method.")
    parser.add_argument("-k", "--bound", type=int, default=100,
                        help="Bound for SMT method.")

    # 解析参数
    args = parser.parse_args()

    # 判断 formula 是否是文件路径
    if args.formula.endswith(".rtldlf"):
        try:
            args.formula = util.read_formula_from_file(args.formula)
        except FileNotFoundError as e:
            print(e)
            return
    else:
        formula = args.formula

    # 根据方法选择执行逻辑
    if args.method == "bdd":
        Synthesis_ldl_total.synthesis_bdd_test(
            formula=args.formula,
            env_vars=args.env_vars,
            sys_vars=args.sys_vars,
            final_step=args.final_step,
            to_graph=args.to_graph
        )
    elif args.method == "smt":
        Synthesis_SMT_ldl.synthesis_bounded(
            formula=args.formula,
            env_vars=args.env_vars,
            k=args.bound
        )
    else:
        print("Invalid method selected. Use 'bdd' or 'smt'.")


if __name__ == '__main__':
    time_start = time.time_ns()  # 记录开始时间

    # test() #执行测试用例

    main() #命令行输入

    time_end = time.time_ns()  # 记录结束时间
    time_sum = time_end - time_start  # 计算的时间差为程序的执行时间，单位为秒/s
    print("总时间消耗：" + str(time_sum / 1000000) + "ms")
