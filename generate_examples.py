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
while a value of `1` would produce a regex made of just operators. `cut_lower_than`
discards all nfas that don't have that minimum number of states
"""
def generate_example(alphabet_size: int, word_size: int, op_density = 0.2, cut_lower_than = 3):
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
    
        if len(nfa.States) < cut_lower_than:
            continue

        return nfa

# Generates:
# 15 small nfas: 10, 25
# 15 medium nfas: 15, 50
# 15 large nfas: 20, 100
# 15 huge nfas: 25, 500

tests_folder = 'tests'
if len(sys.argv) > 1:
    tests_folder = sys.argv[1]
# Makes sure the folder exists
os.makedirs(tests_folder, exist_ok = True)
total_index = 1

print(f"Generating examples (into `{tests_folder}`)...")
start = time.time()

print("Generaing small nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(10, 25, 0.4)
    out = io.open(f'{tests_folder}/{total_index:0>2}-small-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()

    rel = generate_eq_rel(nfa)
    out = io.open(f'{tests_folder}/{total_index:0>2}-small-{i}.right_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    rel = generate_eq_rel(nfa.reversal())
    out = io.open(f'{tests_folder}/{total_index:0>2}-small-{i}.left_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()
    total_index += 1

print()
print("Generaing medium nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(15, 50, 0.35, 10)
    out = io.open(f'{tests_folder}/{total_index:0>2}-medium-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()

    rel = generate_eq_rel(nfa)
    out = io.open(f'{tests_folder}/{total_index:0>2}-medium-{i}.right_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    rel = generate_eq_rel(nfa.reversal())
    out = io.open(f'{tests_folder}/{total_index:0>2}-medium-{i}.left_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()
    total_index += 1

print()
print("Generaing large nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(20, 100, 0.25, 25)
    out = io.open(f'{tests_folder}/{total_index:0>2}-large-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()

    rel = generate_eq_rel(nfa)
    out = io.open(f'{tests_folder}/{total_index:0>2}-large-{i}.right_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    rel = generate_eq_rel(nfa.reversal())
    out = io.open(f'{tests_folder}/{total_index:0>2}-large-{i}.left_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()
    total_index += 1

print()
print("Generaing huge nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(25, 500, 0.1, 40)
    out = io.open(f'{tests_folder}/{total_index:0>2}-huge-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()

    rel = generate_eq_rel(nfa)
    out = io.open(f'{tests_folder}/{total_index:0>2}-huge-{i}.right_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    rel = generate_eq_rel(nfa.reversal())
    out = io.open(f'{tests_folder}/{total_index:0>2}-huge-{i}.left_rel', 'w')
    out.write(rel_str(rel))
    out.close()

    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()
    total_index += 1

end = time.time()
print()
print(f'Example generation completed in {end - start:.3f} secods')