"""Greedy rotation zigzag: alternate B-right (to contact) and F-left (to contact), escape when possible.
For each L, best over start x0 grid and first move; returns minimal number of manoeuvres (or None)."""
import numpy as np, sys
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
def try_escape(q,L):
    V,_,_=car.V(q[None]); return V[0]<=L and car.escapes(q,L+1e-9)
def run(L,x0,first,maxn=60):
    q=np.array([x0,car.H-car.w/2,0.0])
    if not car.fits(q[None],L)[0]: return None
    d=first; n=0
    while n<maxn:
        if try_escape(q,L): return n+1
        k=1/R if d==+1 else -1/R
        s=car.max_free(q,d,k,L,smax=10.0,ds=2e-3)
        if s<1e-6 and n>0: return None
        q=arc_states(q,d,k,np.array([s*0.999999]))[0]; n+=1; d=-d
    return None
for L in [float(a) for a in sys.argv[1:]]:
    best=None
    for x0 in np.linspace(car.db, car.db+(L-car.ell), 15):
        for first in (+1,-1):
            r=run(L,x0,first)
            if r is not None and (best is None or r<best): best=r
    print("L",L,"g",round(L-car.ell,3),"greedy zigzag manoeuvres",best,flush=True)
