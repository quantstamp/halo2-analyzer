from z3 import *

a = Int('a')
b = Int('b')
h = Int('h')
o = Int('o')

func = h * (a + b) + (1 - h) * (a * b) - o
context = Or(h == 0, h == 1)

stmt = Implies(func == 0, Or(h == 0, h == 1))
z3.prove(stmt) 
# Returns:
# counterexample
# [h = -8, o = -8, a = 1, b = 0]

stmt2 = Implies(context, stmt)
z3.prove(stmt2)
# Returns: proved
