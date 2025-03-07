import dd.cudd as cudd

bdd = cudd.BDD()

bdd.declare(*["x22","x22'","x34","x34'","x28","x28'","x310","x310'","a","a'","b","b'","c","c'","d","d'"])

env_vars_prime = ["a'"]
ctrl_vars_prime = ["x22'","x34'","x28'","x310'","c'","b'","d'"]

init = bdd.add_expr("x22 & x28")
trans = bdd.add_expr("(x22 <-> (a -> x34')) & (x34 <-> (c -> d')) & (x28 <-> (a & x310')) & (x310 <-> c)")
final = bdd.add_expr("!x310' & !x28' ")
print('final : ',list(bdd.pick_iter(final)))
print('pre   : ',list(bdd.pick_iter(bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)))))
print('pre =? ',bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)) == bdd.add_expr("(x28 <-> a ) & (x310 <-> c ) & (x22|!x22)&(x34|!x34)&(b|!b)&(d|!d)"))

final = bdd.add_expr("(x28' <-> a' ) & (x310' <-> c' ) & (x22'|!x22')&(x34'|!x34')&(b'|!b')&(d'|!d')   ")
print('final : ',list(bdd.pick_iter(final)))
print('pre   : ',list(bdd.pick_iter(bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)))))
print('pre =? ', bdd.forall(env_vars_prime,bdd.exist(ctrl_vars_prime,trans & final)) == bdd.add_expr("(x28 <-> a ) & (x310 <-> c ) "))



