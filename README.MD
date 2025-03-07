# RTLDLf-Synt-master

这是一个用于 RTLDLf 公式合成的工具，支持 BDD 和 SMT 两种方法。以下是项目的使用说明。

---

## 1. 下载项目

首先，将项目克隆到本地：

```bash
git clone https://github.com/a862894476/RTLDLf-Synt-master.git
cd RTLDLf-Synt-master
```

## 2. 安装依赖

项目依赖的 Python 包列在 requirements.txt 文件中。使用以下命令安装依赖：
```bash
pip install -r requirements.txt
```

## 3. 运行程序

使用 main.py 文件来运行合成工具。

命令行参数说明
以下是 main.py 的命令行参数：
```bash
usage: main.py [-h] -e {bdd,smt} -rtldlf FORMULA [-env ENV_VARS] [-sys SYS_VARS] [-f FINAL_STEP] [-g TO_GRAPH] [-k BOUND]

Run synthesis methods (BDD or SMT) based on input parameters.

options:
  -h, --help            show this help message and exit
  -e {bdd,smt}, --method {bdd,smt}
                        Choose the method: 'bdd' for BDD method or 'smt' for SMT method.
  -rtldlf FORMULA, --formula FORMULA
                        The formula to be used in the synthesis. Can be a formula string or a path to a .rtldlf file.
  -env ENV_VARS, --env_vars ENV_VARS
                        Environment variables.
  -sys SYS_VARS, --sys_vars SYS_VARS
                        System variables.
  -f FINAL_STEP, --final_step FINAL_STEP
                        Final step for synthesis_bdd_test for BDD method.
  -g TO_GRAPH, --to_graph TO_GRAPH
                        Whether to generate a graph (1 for yes, 0 for no) for BDD method.
  -k BOUND, --bound BOUND
                        Bound for SMT method.
```

以下是示例命令：

使用 BDD 方法
```bash
python main.py -e bdd -rtldlf examples/1.rtldlf -env "condition" -sys "act1 act5 act6 act9" -f 1 -g 1 
```
使用 SMT 方法
```bash
python main.py -e smt -rtldlf examples/1.rtldlf -env "condition" -sys "act1 act5 act6 act9"  -k 1000
```


