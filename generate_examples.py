from FAdo.cfg import REStringRGenerator, reGrammar
import FAdo.reex as reex
import math

import io, os, sys, time

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

    generator = REStringRGenerator(alphabet, word_size, None, None, reGrammar['g_regular_wredund'])
    
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
# 15 small nfas: 25, 100
# 15 medium nfas: 50, 100
# 15 large nfas: 100, 100
# 15 huge nfas: 1000, 100

tests_folder = 'tests'
if len(sys.argv) > 1:
    tests_folder = sys.argv[1]
# Makes sure the folder exists
os.makedirs(tests_folder, exist_ok = True)

print(f"Generating examples (into `{tests_folder}`)...")
start = time.time()

print("Generaing small nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(10, 25, 0.4)
    out = io.open(f'tests/small-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()
    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()

print()
print("Generaing medium nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(10, 50, 0.35, 10)
    out = io.open(f'tests/medium-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()
    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()

print()
print("Generaing large nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(10, 100, 0.25, 25)
    out = io.open(f'tests/large-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()
    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()

print()
print("Generaing huge nfas:\t 00/15", end = '')
sys.stdout.flush()
for i in range(1, 15 + 1):
    nfa = generate_example(10, 500, 0.1, 40)
    out = io.open(f'tests/huge-{i}.gv', 'w')
    out.write(nfa.dotFormat())
    out.close()
    print(f"\b\b\b\b\b{i:0>2}/15", end = '')
    sys.stdout.flush()

end = time.time()
print()
print(f'Example generation completed in {end - start:.3f} secods')