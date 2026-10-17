"""Exact rational-polynomial cross-checks for the geometric audit.

Uses the existing standard-library sparse rational-polynomial implementation.
These checks supplement the written argument; they are not another proof kernel.
"""
from audit import Poly
import json


class Rat:
    def __init__(self, n, d=1):
        if isinstance(n, Rat):
            self.n, self.d = n.n, n.d
        else:
            self.n = n
            self.d = n.cast(d)

    def cast(self, x):
        return x if isinstance(x, Rat) else Rat(self.n.cast(x))

    def __add__(self, x):
        x = self.cast(x)
        return Rat(self.n*x.d + x.n*self.d, self.d*x.d)

    __radd__ = __add__

    def __neg__(self):
        return Rat(-self.n, self.d)

    def __sub__(self, x):
        return self + -self.cast(x)

    def __rsub__(self, x):
        return self.cast(x) + -self

    def __mul__(self, x):
        x = self.cast(x)
        return Rat(self.n*x.n, self.d*x.d)

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = self.cast(x)
        return Rat(self.n*x.d, self.d*x.n)

    def __rtruediv__(self, x):
        return self.cast(x) / self

    def __pow__(self, k):
        return Rat(self.n**k, self.d**k)


checks = []


def check(name, expression):
    numerator = expression.n if isinstance(expression, Rat) else expression
    assert numerator.is_zero(), name
    checks.append({'name': name, 'result': 'exact zero polynomial'})


a, b, c, h, z = [Rat(p) for p in Poly.variables(5)]
d = z-1
G = ((z*z-h)*d-2*a*b*z)**2 + 4*a*a*c*c*z*z - 4*c*c*z*z*d*d
v2 = 1-4*a*b-2*h-4*c*c
v3 = 4*a*b+4*h+8*c*c
v4 = (h+2*a*b)**2-2*h-4*c*c+4*a*a*c*c
v5 = -4*a*b*h-2*h*h
f = z**6-2*z**5+v2*z**4+v3*z**3+v4*z*z+v5*z+h*h
check('sextic coefficient expansion', G-f)
m = 2-2*v2-v3
q = (v3-m-4*h)/8
A = (v4-(h+m/2)**2+2*h+4*q)/(4*q)
check('reconstructed m equals 4ab', m-4*a*b)
check('reconstructed q equals c squared', q-c*c)
check('reconstructed A equals a squared', A-a*a)
check('reconstructed radius squared', h+m*m/(16*a*a)+q-(b*b+c*c+h))
X = a*z/d
Y = (z*z-h-2*b*X)/(2*c)
check('norm residual equals sextic residual', X*X+Y*Y-z*z-G/(4*c*c*d*d))
check('circle residual equals sextic residual', (X-b)**2+(Y-c)**2-(b*b+c*c+h)-G/(4*c*c*d*d))
V = d*X/z
W = d*Y/z
check('second mark lies on vertical line', V-a)
check('ruler goes through origin', X*W-Y*V)
check('distance residual equals sextic residual', (X-V)**2+(Y-W)**2-1-G/(4*c*c*d*d*z*z))
check('signed root recovery', X/(X-a)-z)
check('root one strictly positive expression', 1-2+v2+v3+v4+v5+h*h-4*a*a*(b*b+c*c))

p, q, v = [Rat(t) for t in Poly.variables(3)]
a = 2*q/p
b = -a/p
h = 1+2*a*a/p
X = v+a
F = v**3+p*v+q
check('cubic conchoid identity', v*v*(h+2*b*X)-X*X-(-2*a/p)*F)
check('cubic circle residual', X*X/(v*v)-2*b*X-h-(2*a/p)*F/(v*v))
check('cubic radius positivity identity', b*b+h-(1+a*a*(1+2*p)/(p*p)))
check('cubic mark separation', (1-a/X)**2*(X*X/(v*v))-1)

u, q = [Rat(t) for t in Poly.variables(2)]
y = u*u+u
check('pure cubic auxiliary equation', y**3+3*q*y+q-q*q-(u**3+q)*(u**3+3*u*u+3*u+1-q))
check('pure cubic recovery', u*(y+1)-(y-q)-(u**3+q))

print(json.dumps({'arithmetic': 'exact rational polynomial coefficients',
                  'checks_passed': len(checks), 'checks': checks}, indent=2))
