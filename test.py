import dd.cudd as cudd

bdd = cudd.BDD()

bdd.declare(*["x1","x1'","x2","x2'","xa","xa'","xb","xb'","a","a'","b","b'"])

env_vars_prime = ["a'"]
ctrl_vars_prime = ["x1'","x2'","b'"]

init = bdd.add_expr("x1")
trans = bdd.add_expr("(x1 <-> (x2 | (a))) & (x2 <-> x1')")
final = bdd.add_expr("!x2' & !x1' ")
print('final : ',list(bdd.pick_iter(final)))
print('pre   : ',list(bdd.pick_iter(bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)))))
print('pre =? ',bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)) == bdd.add_expr("(x1 <-> (a) ) & !x2 "))

final = bdd.add_expr("(x1' <-> (a' ) ) & !x2'  ")
print('final : ',list(bdd.pick_iter(final)))
print('pre   : ',list(bdd.pick_iter(bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)))))
print('pre =? ', bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)) == bdd.add_expr("(x1 <-> (x2 | (a)))"))


a = [1]
b = [2]

print(b+a)