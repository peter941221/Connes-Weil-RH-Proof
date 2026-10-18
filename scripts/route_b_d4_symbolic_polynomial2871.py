"""Emit the explicit logistic D4 numerator for the D4 sign bridge."""
import sympy as s
u, q = s.symbols('u q')
phi = 1/u - 1/(1-u)
v = -s.diff(phi, u) * q * (1-q)
p = q
for _ in range(4):
    p = s.factor(s.diff(p, u) + s.diff(p, q) * v)
num, den = s.fraction(p)
print('D4 =')
print(s.factor(p))
print('numerator degree in q:', s.degree(num, q))
print('numerator degree in u:', s.degree(num, u))
