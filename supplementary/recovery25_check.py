"""Exact check of the manuscript's conductor-25 generator recovery table."""
from example25 import K, L

alpha = L([0, 1, 0, 0, 0])
gamma = (-4 - 2*alpha + 19*alpha**2 - 5*alpha**4)/4
coefficients = [
    (-82999543578141, -58480846421497),
    (-13850695515680, -108800134011388),
    (35174826943120, 51032088536896),
    (-11192002202560, 42345158096896),
    (3353265729280, -15629538309120),
]
numerator = sum((L(K(a, b))*gamma**j
                 for j, (a, b) in enumerate(coefficients)), L())
assert numerator/45170808970351 == alpha
print('Conductor-25 recovery table: PASS (exact quotient-field arithmetic)')
