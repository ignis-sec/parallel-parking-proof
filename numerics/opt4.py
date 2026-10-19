"""Differential-evolution search over alternating full-lock strategies (exit time).
Params: start x0 offset, first direction, fractions of max free length for each maneuver (last = escape)."""
import numpy as np, sys
from scipy.optimize import differential_evolution
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
def run(L, z, n, first):
    x0=car.db+z[0]*(L-car.ell); q=np.array([x0,car.H-car.w/2,0.0])
    if not car.fits(q[None],L)[0]: return -9.0, q
    d=first
    for t in z[1:n]:
        k=1/R if d==+1 else -1/R
        smax=car.max_free(q,d,k,L,smax=12.0,ds=3e-3)
        q=arc_states(q,d,k,np.array([t*smax*0.999999]))[0]; d=-d
    V,_,_=car.V(q[None]); return L-V[0], q
def slack(L,n,first,seed=0):
    f=lambda z: -run(L,z,n,first)[0]
    res=differential_evolution(f,[(0,1)]*n,seed=seed,maxiter=60,popsize=12,tol=1e-7,polish=True)
    return -res.fun,res.x
n=int(sys.argv[1]); first=int(sys.argv[2])  # number of maneuvers incl. escape; first = +1 or -1
# the escape is forward: sequence of n-1 maneuvers then escape; parity: (n-1) maneuvers alternate starting at 'first' and must end with backward
lo,hi=car.ell,5.9
best=None
for _ in range(12):
    mid=(lo+hi)/2; s,z=slack(mid,n,first)
    if s>=0:
        ok=car.escapes(run(mid,z,n,first)[1],mid+1e-6)
    else: ok=False
    if ok: hi=mid; best=z
    else: lo=mid
print(n,first,"L~",round(hi,4),"z",np.round(best,3) if best is not None else None,flush=True)
