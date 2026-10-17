#!/usr/bin/env python3
"""Exact 25-gon example, using only Python's standard library and audit.py.

K=Q(t), t^2+t-1=0, t>0; alpha^5-5alpha^3+5alpha-t=0.
All field arithmetic is exact; all real inequalities use rational intervals.
"""
import json
from fractions import Fraction as Q
from pathlib import Path
from audit import Interval, residual_coefficients, reconstruction_values
from itertools import combinations


class K:
    def __init__(self, a=0, b=0):
        self.a,self.b=Q(a),Q(b)
    @staticmethod
    def cast(x):return x if isinstance(x,K) else K(x)
    def __add__(self,o):
        o=self.cast(o);return K(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self):return K(-self.a,-self.b)
    def __sub__(self,o):return self+-self.cast(o)
    def __rsub__(self,o):return self.cast(o)+-self
    def __mul__(self,o):
        o=self.cast(o)
        return K(self.a*o.a+self.b*o.b,self.a*o.b+self.b*o.a-self.b*o.b)
    __rmul__=__mul__
    def __truediv__(self,o):return K(self.a/Q(o),self.b/Q(o))
    def __eq__(self,o):
        o=self.cast(o);return self.a==o.a and self.b==o.b
    def at(self,t):return self.a+self.b*t
    def pair(self):return [str(self.a),str(self.b)]


class L:
    def __init__(self,c=0):
        self.c=tuple(K.cast(v) for v in c) if isinstance(c,(list,tuple)) else (K.cast(c),K(),K(),K(),K())
        assert len(self.c)==5
    @staticmethod
    def cast(x):return x if isinstance(x,L) else L(x)
    def __add__(self,o):
        o=self.cast(o);return L([a+b for a,b in zip(self.c,o.c)])
    __radd__=__add__
    def __neg__(self):return L([-a for a in self.c])
    def __sub__(self,o):return self+-self.cast(o)
    def __rsub__(self,o):return self.cast(o)+-self
    def __mul__(self,o):
        o=self.cast(o);d=[K() for _ in range(9)]
        for i,a in enumerate(self.c):
            for j,b in enumerate(o.c):d[i+j]=d[i+j]+a*b
        for k in range(8,4,-1):
            v=d[k];d[k]=K()
            d[k-2]=d[k-2]+5*v
            d[k-4]=d[k-4]-5*v
            d[k-5]=d[k-5]+K(0,1)*v
        return L(d[:5])
    __rmul__=__mul__
    def __truediv__(self,o):return L([v/o for v in self.c])
    def __pow__(self,n):
        ans=L(1)
        for _ in range(n):ans=ans*self
        return ans
    def __eq__(self,o):return self.c==self.cast(o).c
    def at(self,alpha,t):
        ans=0
        for v in reversed(self.c):ans=ans*alpha+v.at(t)
        return ans


def horner(c,x):
    ans=0
    for a in reversed(c):ans=ans*x+a
    return ans


def polyadd(p,q):
    return [(p[i] if i<len(p) else L())+(q[i] if i<len(q) else L()) for i in range(max(len(p),len(q)))]


def polymul(p,q):
    out=[L() for _ in range(len(p)+len(q)-1)]
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]=out[i+j]+a*b
    return out


def product_polynomials(items):
    out=[L(1)]
    for item in items:out=polymul(out,item)
    return out


def descend_poly(p):
    assert all(all(c==0 for c in v.c[1:]) for v in p)
    return [v.c[0].pair() for v in p]


def main():
    alpha=L([0,1,0,0,0]);t=L(K(0,1))
    image=-alpha**4+4*alpha**2+t*alpha-2
    assert image**5-5*image**3+5*image-t==0
    orbit=[alpha]
    for _ in range(5):
        previous=orbit[-1]
        v=L()
        for coefficient in reversed(previous.c):v=v*image+L(coefficient)
        orbit.append(v)
    assert orbit[5]==alpha
    assert all(orbit[i]!=orbit[j] for i in range(5) for j in range(i))
    gamma=lambda a:(-4-2*a+19*a**2-5*a**4)/4
    x=[gamma(a) for a in orbit[:5]]
    C=residual_coefficients(x)
    assert all(all(c==0 for c in v.c[1:]) for v in C), 'Residual coefficients did not descend to K'
    coeff=[v.c[0] for v in C]
    # Export ALL data needed to build the geometry without constructing gamma first.
    beta_polys=[[L(1),x[i]+x[(i+1)%5],x[i]*x[(i+1)%5]] for i in range(5)]
    invariant_data={}
    for k in range(1,5):
        ek=[L()]
        for group in combinations(beta_polys,k):ek=polyadd(ek,product_polynomials(group))
        invariant_data[f'e{k}']=descend_poly(ek)
    invariant_data['P']=descend_poly(product_polynomials([[L(1),v] for v in x]))
    # Column j is beta_0(U)^j in the alpha basis; solve this matrix against e_1
    # after U=u to express alpha as a degree-at-most-four polynomial in beta.
    powers=[[L(1)]]
    for _ in range(4):powers.append(polymul(powers[-1],beta_polys[0]))
    recovery_matrix=[[[v.c[i].pair() for v in col] for col in powers] for i in range(5)]
    Path('example25-invariants.json').write_text(json.dumps({
        'coefficient_order':'ascending powers of U; each field coefficient is [a,b] for a+b*t',
        't_relation':'t^2=1-t, t>0',
        'invariants':invariant_data,
        'recovery_matrix':recovery_matrix,
        'recovery':'At U=u solve M*r=(0,1,0,0,0). Then alpha=sum(r[j]*beta^j,j=0..4).'
    },indent=2)+'\n')

    den=10**30
    sqlo=Q(2236067977499789696409173668731,den)
    sqhi=sqlo+Q(1,den)
    assert sqlo**2<5<sqhi**2
    ti=(Interval(sqlo,sqhi)-1)/2
    alo=Q(1937166322257262238980336750929,den)
    ahi=alo+Q(1,den)
    f=lambda a:a**5-5*a**3+5*a-ti
    assert f(alo).hi<0<f(ahi).lo
    ai=Interval(alo,ahi)
    assert (5*ai**4-15*ai**2+5).lo>0
    a_orbit=[ai]
    for _ in range(4):
        v=a_orbit[-1]
        a_orbit.append((-v**4+4*v**2+ti*v-2).rounded())
    xi=[gamma(a).rounded() for a in a_orbit]
    # gamma has small rational coefficients, rather than an opaque large search output.
    u=Interval(Q(-119356,100000),Q(-119355,100000))
    ci=[v.at(ti) for v in coeff]
    vlo,vhi=horner(ci,u.lo),horner(ci,u.hi)
    assert vlo.hi<0<vhi.lo, (vlo.coarsen(),vhi.coarsen())
    assert ci[3].lo>0
    vals,beta=reconstruction_values(xi,u)
    for name in ['D','lambda','h','m+4h','c_squared','a_squared','rho_squared']:
        assert vals[name].lo>0,(name,vals[name].coarsen())
    assert vals['P'].hi<0
    for i in range(5):
        assert not (beta[i].lo<=0<=beta[i].hi)
        for j in range(i):
            diff=beta[i]-beta[j]
            assert diff.lo>0 or diff.hi<0
    result={'field':'K=Q(t), t^2+t-1=0, t>0; L=K(alpha), alpha^5-5alpha^3+5alpha-t=0',
            'sigma_alpha':'-alpha^4+4alpha^2+t*alpha-2',
            'gamma':'(-4-2alpha+19alpha^2-5alpha^4)/4',
            'residual_coefficients_ascending_as_a_plus_b_t':[c.pair() for c in coeff],
            'auxiliary_interval':[str(u.lo),str(u.hi)],
            'endpoint_signs':['negative','positive'],
            'endpoint_value_enclosures':[vlo.coarsen(),vhi.coarsen()],
            'rational_geometry_enclosures':{name:v.coarsen() for name,v in vals.items()},
            'note':'All arithmetic and interval checks exact. Cyclotomic identification and primitivity are proved in the text.'}
    Path('example25-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
