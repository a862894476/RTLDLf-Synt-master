
import os
import examples
import src.parser.ltl.lex_ltl as lex_ltl
import src.parser.ltl.yacc_ltl as yacc_ltl

def read_formula_from_file(file_path):
    """从文件中读取公式内容"""
    if not os.path.exists(file_path):
        raise FileNotFoundError(f"File not found: {file_path}")
    with open(file_path, "r") as file:
        return file.read().strip()


def parse_tlsf(file_path):
    """输入：文件路径  | 返回：guarantees, inputs, outputs"""
    with open(file_path, 'r') as file:
        lines = file.readlines()

    inputs, outputs, guarantees = [], [], ''
    capture = False
    for line in lines:
        if 'INPUTS {' in line:
            capture = 'inputs'
        elif 'OUTPUTS {' in line:
            capture = 'outputs'
        elif 'GUARANTEES {' in line:
            capture = 'guarantees'
        elif '}' in line:
            capture = False

        if capture and ';' in line:
            item = line.strip().replace(';', '')
            if capture == 'inputs':
                inputs.append(item)
            elif capture == 'outputs':
                outputs.append(item)
            elif capture == 'guarantees':
                guarantees = item

    return guarantees, inputs, outputs

def parse_tlsf_ldl(file_path):
    """输入：文件路径  | 返回：guarantees, inputs, outputs"""
    with open(file_path, 'r') as file:
        lines = file.readlines()

    inputs, outputs, guarantees = [], [], ''
    capture = False
    for line in lines:
        if 'INPUTS {' in line:
            capture = 'inputs'
        elif 'OUTPUTS {' in line:
            capture = 'outputs'
        elif 'GUARANTEES {' in line:
            capture = 'guarantees'
        elif '}' in line:
            capture = False

        if capture and ';' in line:
            item = line.strip().replace(';', ';')
            if capture == 'inputs':
                inputs.append(item.replace(';', ''))
            elif capture == 'outputs':
                outputs.append(item.replace(';', ''))
            elif capture == 'guarantees':
                guarantees = item.rstrip(';')

    return guarantees, inputs, outputs


def split_two_parts(file_path):
    """分割为.ltlf文件和.part文件"""
    inputs, outputs, guarantees = parse_tlsf(file_path)

    part = '.inputs'
    for each in inputs:
        part += ' ' + each
    part += '\n.outputs'
    for each in outputs:
        part += ' ' + each
    return guarantees, part



def split_files(src_folder, dest_folder):
    """将examples中的tlsf文件，拆分为ltlf与part文件"""
    for root, dirs, files in os.walk(src_folder):
        # 构建新的目录结构
        dest_root = root.replace(src_folder, dest_folder)
        if not os.path.exists(dest_root):
            os.makedirs(dest_root)

        for file in files:
            if file.endswith('.tlsf'):
                file_path = os.path.join(root, file)
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()

                # 使用parse_tlsf函数分割内容
                part1, part2 = split_two_parts(file_path)

                # 保存分割后的文件
                part1_path = os.path.join(dest_root, f"{os.path.splitext(file)[0]}.ltlf")
                part2_path = os.path.join(dest_root, f"{os.path.splitext(file)[0]}.part")
                with open(part1_path, 'w', encoding='utf-8') as f:
                    f.write(part1)
                with open(part2_path, 'w', encoding='utf-8') as f:
                    f.write(part2)


# 调用函数
# split_files('../examples', '../examples_split')


def ltl2ldl(ltl_formula='',lydia=0):
    """输入为ltlf公式, 返回为ldlf公式"""

    root = yacc_ltl.parsing(ltl_formula)
    # print('ltlf语法树：')
    # yacc_ltl.print_tree(root)

    if lydia:
        #转为lydia的ldlf
        ldl_tree = ltl2ldl_lydia_tree_construct(root)
        # print('lydia的ldlf语法树：')
        # yacc_ltl.print_tree(ldl_tree)
    else:
        ldl_tree = ltl2ldl_tree_construct(root)
        # print('ldlf语法树：')
        # yacc_ltl.print_tree(ldl_tree)

    ldl_formula = tree2str(ldl_tree)
    print('ldlf公式：', tree2str(ldl_tree))

    return ldl_formula


def ltl2ldl_tree_construct(root):
    """输入为ltlf语法树，返回ldlf语法树"""
    if root:
        if root.val.type == 'NEXT':
            l = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            r = root.left
            root = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST','>'), l, r)
        elif root.val.type == 'WEAK_NEXT':
            l = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            r = root.left
            root = yacc_ltl.TreeNode(lex_ltl.new_token('RFORALL',']'), l, r)
        elif root.val.type == 'FINALLY':
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            r = root.left
            root = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST','>'), l, r)
        elif root.val.type == 'GLOBALLY':
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            r = root.left
            root = yacc_ltl.TreeNode(lex_ltl.new_token('RFORALL',']'), l, r)
        elif root.val.type == 'UNTIL':
            llll = root.left
            lll = yacc_ltl.TreeNode(lex_ltl.new_token('TEST','?'),llll)
            llr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('CONNECT',';'),lll,llr)
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            r = root.right
            root = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST','>'), l, r)
        elif root.val.type == 'RELEASE':
            lllll = root.left
            llll = yacc_ltl.TreeNode(lex_ltl.new_token('NOT','!'),lllll)
            lll = yacc_ltl.TreeNode(lex_ltl.new_token('TEST','?'),llll)
            llr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('CONNECT',';'),lll,llr)
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            r = root.right
            root = yacc_ltl.TreeNode(lex_ltl.new_token('RFORALL',']'), l, r)
        root.left = ltl2ldl_tree_construct(root.left)
        root.right = ltl2ldl_tree_construct(root.right)
        return root


def ltl2ldl_lydia_tree_construct(root):
    """输入为ltlf语法树，返回lydia的ldlf语法树"""
    if root :
        if root.val.value == "tt":
            return root
        if root.val.type == 'NEXT':
            l = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            rl = root.left
            rr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','tt'))
            r = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), rl, rr)
            root = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST','>'), l, r)
        elif root.val.type == 'WEAK_NEXT':
            l = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            rl = root.left
            rr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', 'tt'))
            r = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), rl, rr)
            root = yacc_ltl.TreeNode(lex_ltl.new_token('RFORALL',']'), l, r)
        elif root.val.type == 'FINALLY':
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            rl = root.left
            rr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', 'tt'))
            r = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), rl, rr)
            root = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST','>'), l, r)
        elif root.val.type == 'GLOBALLY':
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            rl = root.left
            rr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', 'tt'))
            r = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), rl, rr)
            root = yacc_ltl.TreeNode(lex_ltl.new_token('RFORALL',']'), l, r)
        elif root.val.type == 'UNTIL':
            lllll = root.left
            llllr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', 'tt'))
            llll = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), lllll, llllr)
            lll = yacc_ltl.TreeNode(lex_ltl.new_token('TEST','?'),llll)
            llr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('CONNECT',';'),lll,llr)
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            rl = root.right
            rr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', 'tt'))
            r = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), rl, rr)
            root = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST','>'), l, r)
        elif root.val.type == 'RELEASE':
            llllll = root.left
            lllllr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', 'tt'))
            lllll = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), llllll, lllllr)
            llll = yacc_ltl.TreeNode(lex_ltl.new_token('NOT','!'),lllll)
            lll = yacc_ltl.TreeNode(lex_ltl.new_token('TEST','?'),llll)
            llr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','true'))
            ll = yacc_ltl.TreeNode(lex_ltl.new_token('CONNECT',';'),lll,llr)
            l = yacc_ltl.TreeNode(lex_ltl.new_token('STAR','*'),ll)
            rl = root.right
            rr = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', 'tt'))
            r = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), rl, rr)
            root = yacc_ltl.TreeNode(lex_ltl.new_token('RFORALL',']'), l, r)
        # elif root.val.type == 'ATOM':
        #     l = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM', root.val.value))
        #     r = yacc_ltl.TreeNode(lex_ltl.new_token('ATOM','tt'))
        #     root = yacc_ltl.TreeNode(lex_ltl.new_token('REXIST', '>'), l, r)
        #     return root
        # elif root.val.type == 'AND':
        #     l = ltl2ldl_lydia_tree_construct(root.left)
        #     r = ltl2ldl_lydia_tree_construct(root.right)
        #     root = yacc_ltl.TreeNode(root.val, l, r)
        root.left = ltl2ldl_lydia_tree_construct(root.left)
        root.right = ltl2ldl_lydia_tree_construct(root.right)
        return root



def tree2str(root):
    """输入为ldlf语法树，输出为ldlf公式"""
    if not root.left:
        return root.val.value
    elif root.val.type == "REXIST":
        return '< (' + tree2str(root.left) + ') >(' + tree2str(root.right) + ')'
    elif root.val.type == "RFORALL":
        return '[ (' + tree2str(root.left) + ') ](' + tree2str(root.right) + ')'
    elif root.val.type == "STAR":
        return '(' + tree2str(root.left) + ')*'
    elif root.val.type == "TEST":
        return '(' + tree2str(root.left) + ')?'
    elif root.val.type == "NOT":
        return '!(' + tree2str(root.left) + ')'
    elif root.val.type == "ATOM":
        return  tree2str(root.left)
    elif root.val.type == "CONNECT":
        return '(' + tree2str(root.left) + ');(' + tree2str(root.right) + ')'
    elif root.val.type == "PLUS":
        return '(' + tree2str(root.left) + ')+(' + tree2str(root.right) + ')'
    elif root.val.type == "AND":
        return '((' + tree2str(root.left) + ')&(' + tree2str(root.right) + '))'
    elif root.val.type == "OR":
        return '((' + tree2str(root.left) + ')|(' + tree2str(root.right) + '))'
    elif root.val.type == "EQUIVALENT":
        return '( ((' + tree2str(root.left) + ')&(' + tree2str(root.right) + ')) | (!(' + tree2str(root.left) + ') & !(' + tree2str(root.right) + ')) )'
    elif root.val.type == "XOR":
        return '( (!(' + tree2str(root.left) + ')&(' + tree2str(root.right) + ')) | ((' + tree2str(root.left) + ')&!(' + tree2str(root.right) + ')) )'
    elif root.val.type == "IMPLIES":
        return '(!(' + tree2str(root.left) + ') | (' + tree2str(root.right) + '))'
    else:
        return 'type '+root.val.type+' wrong!'

# ltl2ldl('G a')
# ltlf = "G( (wolf && man && carrywolf && !carrygoat && !carrycabbage && X !wolf && X !man ) || (!wolf && !man && carrywolf && !carrygoat && !carrycabbage && X wolf && X man ) || (wolf&& !carrywolf && X wolf ) || (!wolf&& !carrywolf && X !wolf ))"
# ltlf = "(goat && man && carrygoat && !carrycabbage && !carrywolf && X !goat && X !man )"
# ltl2ldl(ltlf,1)


def remove_duplicate_lines(file_path):
    """去除文件中相同行"""
    with open(file_path, 'r', encoding='utf-8') as file:
        lines = file.readlines()
    # 使用集合去除重复行，保持原有顺序
    unique_lines = list(dict.fromkeys(lines))
    with open(file_path, 'w', encoding='utf-8') as file:
        file.writelines(unique_lines)


def simplify_solutions(solutions):
    """化简pick_iter生成的解集"""
    def can_merge(sol1, sol2):
        # 检查两个解是否可以合并
        diff_count = 0
        # print('sol1:' ,sol1)
        # print('sol2:', sol2)
        var1 = 'default'
        for k in sol1:
            if k not in sol2 or sol1[k] != sol2[k]:
                diff_count += 1
                if diff_count > 2:
                    return False, 'default'
                var1 = k
        for k in sol2:
            if k not in sol1 or sol2[k] != sol1[k]:
                diff_count += 1
                if diff_count > 2:
                    return False, 'default'
                var1 = k
        # print('return: ',(diff_count == 1, var1))
        return diff_count == 2, var1

    changed = True
    while changed:
        changed = False
        for i in range(len(solutions)):
            for j in range(i+1, len(solutions)):
                merge1, var1 = can_merge(solutions[i], solutions[j])
                if merge1:
                    # 合并解并添加到新解集合中
                    del solutions[i][var1]
                    # print('solutions[i]:',solutions[i])
                    solutions.append(solutions[i])
                    solutions.pop(j)
                    solutions.pop(i)
                    # print('solutions',solutions)
                    changed = True
                    break
            if changed:
                break
    return solutions

# print(simplify_solutions([{'a':False},{'a':True, 'b':False}]))


def print_input_output(input={},output={}):
    """输入为字典，返回迁移关系label，形如 !a b """
    input = [key if input[key] == True else '!'+key for key in input.keys()]
    output = [key if output[key] == True else '!'+key for key in output.keys()]
    ret = ''
    for each in input:
        ret += each.rsplit("_", 1)[0] + ' '
    for each in output:
        ret += each.rsplit("_", 1)[0] + ' '
    return ret

# print('p: ',print_input_output({'a':True}))


def to_lydia(m,n):
    "<(act1;act2;act3;act4)*{1024,1029};act5>tt"
    ret = ''
    for i in range (m,n+1):
        s = "<"
        for j in range(0,i):
            s += "(act1;act2;act3;act4);"
        s += "act5>tt || \n"
        ret += s
    return ret[0:-4]

# n = 160
# print(to_lydia(5,n+5))

def to_lydia2(m,n):
    "<(<condition>tt?;act1;act2;act3;act4 + <!condition>tt?;(act5)*;act6;act7;act8)*{%s,%s}><act9>tt"
    ret = ''
    for i in range (m,n+1):
        s = "<"
        for j in range(0,i):
            s += "(<condition>tt?;act1 + <!condition>tt?;(act5)*;act6);"
        s += "act9>tt || \n"
        ret += s
    return ret[0:-4]

# n = 7
# print(to_lydia2(n,n))