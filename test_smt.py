from z3 import * # 导入z3库

# 定义变量
x = Int("x")
y = Int("y")

# 定义基本约束
s = Solver()
s.add(x > 0, y > 0)
s.add(x + y < 3)

# 寻找解
while(s.check() == sat):
    # 显示解
    m = s.model()
    print(m)
    # 将解添加到约束条件中
    s.add(Not(And(x == m[x], y == m[y])))
