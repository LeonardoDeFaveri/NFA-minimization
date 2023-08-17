from FAdo.cfg import REStringRGenerator, reGrammar
from FAdo.fa import NFA, UnionFind
import FAdo.reex as reex
import math

import io, os, sys, time

def generate_eq_rel(nfa: NFA):
    bisimulation = nfa.autobisimulation2()
    eq_sets = UnionFind(auto_create = True)
    for i in range(len(nfa.States)):
        eq_sets.make_set(i)
    for i, j in bisimulation:
        eq_sets.union(i, j)

    rel = set()
    for eq_set in eq_sets.get_sets().values():
        for s1 in eq_set:
            for s2 in eq_set:
                if s1 != s2:
                    rel.add((s1, s2))
                    rel.add((s2, s1))
    return rel

def rel_str(rel):
    res = ''
    for i, j in rel:
        res += f'{i} {j}\n'
    return res

def generate_single_example(regex, file_name):
    regExp: reex.RegExp = reex.str2regexp(regex)
    nfa: NFA = regExp.nfaPosition()

    #nfa: NFA = NFA()
    #nfa.States = range(0, 4)
    #nfa.addFinal(3)
    #nfa.setInitial([0])
    #nfa.setSigma = ['a', 'b']
    #nfa.addTransition(0, 'a', 1)
    #nfa.addTransition(1, 'a', 2)
    #nfa.addTransition(2, 'a', 0)
    #nfa.addTransition(0, 'b', 3)
    #nfa.addTransition(1, 'b', 3)
    #nfa.addTransition(2, 'b', 3)

    right_rel = generate_eq_rel(nfa)
    left_rel = generate_eq_rel(nfa.reversal())
    nfa.display(file_name)
    out = io.open(f'{file_name}.right_rel', 'w')
    out.write(rel_str(right_rel))
    out.close()
    out = io.open(f'{file_name}.left_rel', 'w')
    out.write(rel_str(left_rel))
    out.close()

    r_nfa = nfa.rEquivNFA()
    lr_nfa = r_nfa.lEquivNFA()
    del r_nfa
    lr_nfa.display('RL1')

    l_nfa = nfa.lEquivNFA()
    lr_nfa = l_nfa.rEquivNFA()
    del l_nfa
    lr_nfa.display('LR1')

    min_nfa = nfa.lrEquivNFA()
    min_nfa.display('min')

#generate_single_example('(aaa)*(aab+ab+b)', 'p')
#os.abort()

grammars = {
    'g_finite_base': [
        "Tr -> Tr + Tc | Tc",
        "Tc -> Tc Ts |  Ts",
        "Ts ->  Ti | ( Tr ) "
    ],
    'g_regular_wredund': [
        "Tr -> Trs | Tf ",
        "Trs -> Trs + Tf | Tf + Tf",
        "Tf -> Tc | Te | Ti",
        "Tc -> Ts Ts | Tf Te",
        "Ts -> Te | Ti | ( Trs ) ",
        "Te -> ( Trs ) * | ( Tc ) * | Ti *"
    ],
}

"""
Generates a random NFA. It is first generates a regular expression
and then an NFA is derived using the position automaton construction
algorithm. `alphabet_size` defines the number of symbols of the vocabulary,
`word_size` defines the length of the regular expression. `op_density` is a
value in (0, 1) that defines how many operators there should be in the regular
expression. A value of `0` would produce a regex made of just alphabet symbols,
while a value of `1` would produce a regex made of just operators.
"""
def generate_example(alphabet_size: int, word_size: int, op_density = 0.2):
    if alphabet_size <= 0 or word_size <= 0:
        return None
    
    alphabet = []
    mul = 1
    for i in range(alphabet_size):
        a = chr(ord('a') + i % 26) * mul
        mul = 1 + math.floor(i / 25)
        alphabet.append(a)

    generator = REStringRGenerator(alphabet, word_size, grammars['g_regular_wredund'], None, None)
    
    while True:
        regex = generator.generate()
    
        op_count = 0
        for sym in regex:
            if sym == '+' or sym == '|' or sym == '*' or sym == '(' or sym == ')':
                op_count += 1
    
        if op_count / word_size < op_density:
            continue
    
        regExp: reex.RegExp = reex.str2regexp(regex)
        nfa = regExp.nfaPosition()

        return nfa

def generate_and_save_example(alphabet_size: int, word_size: int, op_density, file_name):
    nfa = generate_example(alphabet_size, word_size, op_density)
    out = io.open(f'{tests_folder}/{file_name}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()

    rel = generate_eq_rel(nfa)
    out = io.open(f'{tests_folder}/{file_name}.right_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    rel = generate_eq_rel(nfa.reversal())
    out = io.open(f'{tests_folder}/{file_name}.left_rel', 'w')
    out.write(rel_str(rel))
    out.close()


# Small:    word_size = 25, op_density = 0.4
# Medium:   word_size = 50, op_density = 0.35
# Large:    word_size = 100, op_density = 0.25
# Huge:     word_size = 500, op_density = 0.1

gen_parameters = ['tests', 60, 1]
for index, value in enumerate(sys.argv):
    if index == 0:
        continue
    gen_parameters[index - 1] = value

tests_folder = gen_parameters[0]
count = int(gen_parameters[1])
alphabet_size = int(gen_parameters[2])

# Makes sure the folder exists
os.makedirs(tests_folder, exist_ok = True)

print(f'Parameters:\n\tNFA count per tipe: {count}\n\tAlphabet size: {alphabet_size}')
print(f'Generating examples (into `{tests_folder}`)...')
start = time.time()

print(f'Generating small nfas:\t 00/{count}', end = '')
sys.stdout.flush()
for i in range(1, count + 1):
    generate_and_save_example(alphabet_size, 25, 0.4, f'small/{alphabet_size}/{i:0>3}')
    print(f"\b\b\b\b\b{i:0>2}/{count}", end = '')
    sys.stdout.flush()

print()
print(f'Generating medium nfas:\t 00/{count}', end = '')
sys.stdout.flush()
for i in range(1, count + 1):
    generate_and_save_example(alphabet_size, 50, 0.35, f'medium/{alphabet_size}/{i:0>3}')
    print(f"\b\b\b\b\b{i:0>2}/{count}", end = '')
    sys.stdout.flush()

print()
print(f'Generating large nfas:\t 00/{count}', end = '')
sys.stdout.flush()
for i in range(1, count + 1):
    generate_and_save_example(alphabet_size, 100, 0.25, f'large/{alphabet_size}/{i:0>3}')
    print(f"\b\b\b\b\b{i:0>2}/{count}", end = '')
    sys.stdout.flush()

print()
print(f'Generating huge nfas:\t 00/{count}', end = '')
sys.stdout.flush()
for i in range(1, count + 1):
    generate_and_save_example(alphabet_size, 500, 0.1, f'huge/{alphabet_size}/{i:0>3}')
    print(f"\b\b\b\b\b{i:0>2}/{count}", end = '')
    sys.stdout.flush()

end = time.time()
print()
print(f'Example generation completed in {end - start:.3f} seconds')