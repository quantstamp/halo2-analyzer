from z3 import *


def prove(f):
    s = Solver()
    s.add(Not(f))
    # print("H", h, type(h))
    if s.check() == unsat:
        print("proved")
    else:
        print("failed to prove")
        model = s.model()
        for x in model:
            print(x, model[x])
        # print(f"H value {model[h]}", type(model[h]), type(h))


def prove2(f, x):
    s = Solver()
    s.add(x)
    s.add(Not(f))
    if s.check() == unsat:
        print("proved")
    else:
        print("failed to prove", s.model())


a = Int('a')
b = Int('b')
h = Int('h')
o = Int('o')
f = h * (a + b) + (1 - h) * (a * b) - o
i = Or(h == 0, h == 1)
# print(f)
# print(i)


g = ForAll([a, b, h, o], Implies(f == 0, Or(h == 0, h == 1)))
g2 = ForAll([a, b, o], Implies(f == 0, Or(h == 0, h == 1)))

g3 = Implies(f == 0, Or(h == 0, h == 1))

z3.prove(g3)

g4 = Implies(i, g3)
z3.prove(g4)

### This is unsat
# s.add(ForAll([a, b, h, o], Implies(f == 0, Or(h == 0, h == 1))))
### These are sat
# s.add(Or(h == 0, h==1))
# s.add(ForAll([a, b, o], Implies(f == 0, Or(h == 0, h == 1)))) #

# print(s.check())


# prove(g, h) # "failed to prove"
# prove(And(g, i),h) # "failed to prove"
# prove(g2,h) # "failed to prove"
# prove(And(g2, i),h) # "failed to prove"
# prove2(g2, i)