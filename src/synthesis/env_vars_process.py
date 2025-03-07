




def env_vars_preprocess_bdd(env_vars,bdd):
    """环境变量预处理"""
    ret = []
    if env_vars == "":
        return []
    env_vars = env_vars.split()
    for each in env_vars:
        bdd.declare(each + "_0")
        ret.append(each + "_0")
    return ret

def env_vars_preprocess_bdd_list(env_vars,bdd):
    """环境变量预处理"""
    ret = []
    if env_vars == []:
        return []
    for each in env_vars:
        bdd.declare(each + "_0")
        ret.append(each + "_0")
    return ret