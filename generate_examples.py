from FAdo.cfg import REStringRGenerator, reGrammar
import FAdo.reex as reex
import math

"""
Generates a random NFA. It is first generates a regular expression
and then an NFA is derived using the position automaton construction
algorithm. `alphabet_size` defines the number of symbols of the vocabulary,
`word_size` defines the length of the regular expression.
"""
def generate_example(alphabet_size: int, word_size: int):
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
            if sym == '+' or sym == '|' or sym == '*':
                op_count += 1

        if op_count / word_size < 0.2:
            continue

        regExp: reex.RegExp = reex.str2regexp(regex)
        nfa = regExp.nfaPosition()
        return nfa

nfa = generate_example(10, 100)
nfa.display('generated_examples/1')
