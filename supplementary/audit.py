#!/usr/bin/env python3
"""Exact cyclic-quintic audit. Python standard library only; no floating point.

Run: python3 audit.py --output certificate.json --expanded expanded-residual.txt
The sparse polynomial implementation compares every rational coefficient.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from itertools import combinations
from math import prod
from pathlib import Path


class Poly:
    """Sparse multivariate polynomial over Q in a fixed number of variables."""
    def __init__(self, n, data=0):
        self.n = n
        if isinstance(data, dict):
            self.d = {e: Q(c) for e, c in data.items() if c}
        else:
            self.d = {(0,) * n: Q(data)} if data else {}

    @classmethod
    def variables(cls, n):
        return [cls(n, {tuple(int(i == j) for i in range(n)): 1}) for j in range(n)]

    def cast(self, other):
        if isinstance(other, Poly):
            assert self.n == other.n
            return other
        return Poly(self.n, other)

    def __add__(self, other):
        other = self.cast(other)
        d = dict(self.d)
        for e, c in other.d.items():
            d[e] = d.get(e, Q(0)) + c
        return Poly(self.n, d)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.n, {e: -c for e, c in self.d.items()})

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        d = {}
        for e, c in self.d.items():
            for f, b in other.d.items():
                h = tuple(i + j for i, j in zip(e, f))
                d[h] = d.get(h, Q(0)) + c * b
        return Poly(self.n, d)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        scalar = Q(scalar)
        if not scalar:
            raise ZeroDivisionError
        return Poly(self.n, {e: c / scalar for e, c in self.d.items()})

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        ans, base = Poly(self.n, 1), self
        while n:
            if n & 1:
                ans = ans * base
            base = base * base
            n //= 2
        return ans

    def is_zero(self):
        return not self.d

    def evaluate(self, values):
        assert len(values) == self.n
        return sum(c * prod(Q(v)**p for v, p in zip(values, e)) for e, c in self.d.items())

    def rotate_first_five(self):
        d = {}
        for e, c in self.d.items():
            f = (e[4], e[0], e[1], e[2], e[3], *e[5:])
            d[f] = d.get(f, Q(0)) + c
        return Poly(self.n, d)

    def coefficient_last(self, k):
        return {e[:-1]: c for e, c in self.d.items() if e[-1] == k}

    def text(self, names):
        if not self.d:
            return '0'
        terms = []
        for e, c in sorted(self.d.items(), reverse=True):
            monomial = '*'.join(name if p == 1 else f'{name}^{p}' for name, p in zip(names, e) if p)
            terms.append(str(c) + ('*' + monomial if monomial else ''))
        return ' + '.join(terms).replace('+ -', '- ')


class Interval:
    """Closed rational interval with inclusion-preserving elementary operations."""
    def __init__(self, lo, hi=None):
        self.lo, self.hi = Q(lo), Q(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def cast(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, other):
        other = self.cast(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        candidates = [self.lo*other.lo, self.lo*other.hi, self.hi*other.lo, self.hi*other.hi]
        return Interval(min(candidates), max(candidates))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError('Interval denominator contains zero')
        return Interval(1/self.hi, 1/self.lo)

    def __truediv__(self, other):
        return self * self.cast(other).reciprocal()

    def __rtruediv__(self, other):
        return self.cast(other) * self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        if n == 0:
            return Interval(1)
        if n % 2:
            return Interval(self.lo**n, self.hi**n)
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**n, self.hi**n)
        return Interval(low, max(self.lo**n, self.hi**n))

    def coarsen(self, scale=10000):
        lo = self.lo.numerator * scale // self.lo.denominator
        hi = -((-self.hi.numerator * scale) // self.hi.denominator)
        return [str(Q(lo, scale)), str(Q(hi, scale))]

    def rounded(self, scale=10**30):
        lo = self.lo.numerator * scale // self.lo.denominator
        hi = -((-self.hi.numerator * scale) // self.hi.denominator)
        return Interval(Q(lo,scale),Q(hi,scale))


def elementary(values):
    return [1] + [sum(prod(group) for group in combinations(values, k)) for k in range(1, len(values)+1)]


def residual_coefficients(x):
    ex = elementary(x)
    S = sum(x)
    t = sum(x[i]*x[(i+1)%5] for i in range(5))
    v = sum(x[i]*x[(i+1)%5]**2*x[(i+2)%5] for i in range(5))
    c = sum(x[i]*x[(i+1)%5]*x[(i+2)%5] for i in range(5))
    A32 = sum(x[i]**3*x[(i+1)%5]**2 + x[i]**2*x[(i+1)%5]**3 for i in range(5))
    A33 = sum(x[i]**3*x[(i+1)%5]**3 for i in range(5))
    return [4*(t**2 - 4*v),
            4*A32 - 2*S*t**2 + 2*t*(c+ex[3]) + 4*S*ex[4] + 4*ex[5],
            (4*A33-t**3)/3 + 2*t*ex[4] + 4*S*ex[5],
            2*t*ex[5]]


def reconstruction_values(x, u):
    g = [1+u*t for t in x]
    beta = [g[i]*g[(i+1)%5] for i in range(5)]
    e = elementary(beta)
    P = prod(g)
    D = 1+e[1]
    lam = 2/D
    a = [1,-2] + [(-lam)**k*(e[k]+e[k-1]) for k in range(2,6)] + [lam**6*P**2]
    h = -lam**3*P
    m = 2-2*a[2]-a[3]
    q = (a[3]-m-4*h)/8
    A = (a[4]-(h+m/2)**2+2*h+4*q)/(4*q)
    b2 = m**2/(16*A)
    rho2 = h+b2+q
    return {'D':D,'P':P,'lambda':lam,'h':h,'m':m,'m+4h':m+4*h,
            'c_squared':q,'a_squared':A,'b_squared':b2,'rho_squared':rho2}, beta


def universal_audit():
    *x, U = Poly.variables(6)
    g = [1 + U*t for t in x]
    beta = [g[i]*g[(i+1)%5] for i in range(5)]
    e = elementary(beta)
    P = prod(g)
    R = sum(g[i]*g[(i+1)%5]*g[(i+2)%5] for i in range(5))
    T = e[1]
    D = T + 1
    assert (e[5] - P**2).is_zero()
    assert (e[4] - P*R).is_zero()

    # Explicit compact residual coefficients in the ORIGINAL x variables.
    C = residual_coefficients(x)
    H = sum(C[k]*U**k for k in range(4))
    B = D**3 - 4*(e[2]+T)*D + 4*(e[3]+e[2]) + 2*(P+R)*D - 8*P
    assert (B - U**4*H).is_zero(), 'Universal cubic identity failed'

    # D^6 times (a5 + m*h + 2*h^2), with lambda=2/D, h=-lambda^3*P.
    N = -32*(P**2+e[4])*D - 16*P*D**3 + 64*P*(e[2]+T)*D - 64*P*(e[3]+e[2]) + 128*P**2
    assert (N + 16*P*U**4*H).is_zero(), 'Signed obstruction identity failed'
    for coefficient in C:
        assert (coefficient.rotate_first_five() - coefficient).is_zero()

    template = [-3,-1,1,4,2]
    values = [c.evaluate(template+[0]) for c in C]
    assert values == [912,792,792,384]
    assert values[3] != 0
    return C, {'residual_coefficients_ascending': list(map(str, values)),
               'universal_coefficient_monomial_counts': [len(c.d) for c in C],
               'universal_factorization': 'PASS', 'cyclic_invariance': 'PASS'}


def reconstruction_audit():
    # A=a^2, q=c^2, R=rho^2, and ab=m/4. No square roots in this comparison.
    a2,a3,a4,h = Poly.variables(4)
    m = 2-2*a2-a3
    q = (a3-m-4*h)/8
    numerator = a4-(h+m/2)**2+2*h+4*q  # 4*A*q
    K = h+m/2
    geometric = [1,-2,1-2*K-4*q,2*h+2*K+8*q,
                 K**2-2*h+numerator-4*q,-2*h*K,h**2]
    expected = [1,-2,a2,a3,a4,-m*h-2*h**2,h**2]
    for actual, target in zip(geometric, expected):
        if isinstance(actual, Poly) or isinstance(target, Poly):
            assert (Poly(4, actual) - target).is_zero() if not isinstance(actual,Poly) else (actual-target).is_zero()
        else:
            assert actual == target

    z,a,b,c,rho = Poly.variables(5)
    h = rho**2-b**2-c**2
    compact = ((z**2-h)*(z-1)-2*a*b*z)**2 + 4*a**2*c**2*z**2 - 4*c**2*z**2*(z-1)**2
    co = [1,-2,
          1-2*(rho**2-b**2+c**2+2*a*b),
          4*(rho**2-b**2+c**2+a*b),
          (rho**2-b**2+c**2+2*a*b)**2-2*(rho**2-b**2+c**2)-4*c**2*(rho**2-(a-b)**2),
          2*(a*b)**2-2*(rho**2-b**2-c**2+a*b)**2,h**2]
    assert (compact-sum(co[k]*z**(6-k) for k in range(7))).is_zero()
    return 'PASS'


def template_audit():
    lo, hi = Q(-167710,100000), Q(-167709,100000)
    f = lambda u:16*u**3+33*u**2+33*u+38
    assert f(lo)<0<f(hi)
    # f'(u) = 48*(u+11/16)^2+165/16 > 0, an exact polynomial identity.
    u = Poly.variables(1)[0]
    assert (48*u**2+66*u+33 - (48*(u+Q(11,16))**2+Q(165,16))).is_zero()
    interval = Interval(lo,hi)
    x = [-3,-1,1,4,2]
    g = [1+interval*t for t in x]
    beta = [g[i]*g[(i+1)%5] for i in range(5)]
    e = elementary(beta)
    P = prod(g)
    D = 1+e[1]
    lam = 2/D
    a = [Interval(1),Interval(-2)] + [(-lam)**k*(e[k]+e[k-1]) for k in range(2,6)] + [lam**6*P**2]
    h = -lam**3*P
    m = 2-2*a[2]-a[3]
    q = (a[3]-m-4*h)/8
    A = (a[4]-(h+m/2)**2+2*h+4*q)/(4*q)
    b2 = m**2/(16*A)
    rho2 = h+b2+q
    vals = {'D':D,'P':P,'lambda':lam,'h':h,'m':m,'m+4h':m+4*h,
            'c_squared':q,'a_squared':A,'b_squared':b2,'rho_squared':rho2}
    for name in ['D','lambda','h','m','m+4h','c_squared','a_squared','rho_squared']:
        assert vals[name].lo>0, (name,vals[name].coarsen())
    assert P.hi<0
    # Leading residual coefficient C3=384 and every selected root is in (-2,-1).
    # Exact beta ordering, valid on the ENTIRE larger interval (-2,-1).
    B = [1-4*u+3*u**2,1-u**2,1+5*u+4*u**2,1+6*u+8*u**2,1-u-6*u**2]
    factors=[u*(5*u+1),5*u*(u+1),u*(4*u+1),-5*u*(u+2)]
    for (i,j),factored in zip([(4,1),(1,2),(2,3),(3,0)],factors):
        assert (B[j]-B[i]-factored).is_zero()
    assert -2<lo<hi<-1
    # Each g_i excludes zero. Hence every beta_i and every z_i=lambda*beta_i exclude zero.
    assert all(not (gi.lo<=0<=gi.hi) for gi in g)
    return {'interval':[str(lo),str(hi)],'cubic_endpoint_values':[str(f(lo)),str(f(hi))],
            'rational_interval_enclosures':{name:v.coarsen() for name,v in vals.items()},
            'beta_order':[4,1,2,3,0], 'template_positivity':'PASS',
            'note':'Enclosures hold throughout the closed rational interval, not just at its root.'}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output', default='certificate.json')
    parser.add_argument('--expanded', default='expanded-residual.txt')
    args=parser.parse_args()
    C,universal=universal_audit()
    print('Universal identity and cyclic descent invariance: PASS',flush=True)
    geometry=reconstruction_audit()
    print('Geometric coefficient reconstruction: PASS',flush=True)
    template=template_audit()
    print('Exact template signs, positivity and distinctness: PASS',flush=True)
    output={'arithmetic':'Exact integers and fractions; no floating point',
            'universal':universal,'geometry':geometry,'template':template,
            'scope':'Finite algebraic and inequality certificates only. Analytic and field-theoretic proofs are in proof-draft.md.'}
    Path(args.output).write_text(json.dumps(output,indent=2)+'\n')
    names=['x0','x1','x2','x3','x4','U']
    Path(args.expanded).write_text('\n\n'.join(f'C{k} = '+p.text(names) for k,p in enumerate(C))+'\n')
    print(json.dumps(template['rational_interval_enclosures'],indent=2))


if __name__=='__main__':
    main()
