"""2-manoeuvre exits: level start at top at x0; reverse = B-left by a0, then B-right by a1 (<= contact),
then optional reverse piece with curvature k2 and length s2; then forward full-left escape."""
import numpy as np
from scipy.optimize import differential_evolution, minimize
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
def path(L,z):
    a,a0,t1,k2,s2=z
    q=np.array([car.db+a*(L-car.ell), car.H-car.w/2, 0.0])
    if not car.fits(q[None],L)[0]: return None
    segs=[(-1, 1/R, a0*R)]
    out=[]
    for (d,k,s) in segs:
        S=np.linspace(0,s,200); Q=arc_states(q,d,k,S)
        if car.collide(Q,L).any(): return None
        q=Q[-1]
    smax=car.max_free(q,-1,-1/R,L,smax=8.0,ds=2e-3); q=arc_states(q,-1,-1/R,np.array([t1*smax*0.999999]))[0]
    if s2>1e-9:
        kk=(2*k2-1)/R; smax2=car.max_free(q,-1,kk,L,smax=s2,ds=2e-3); q=arc_states(q,-1,kk,np.array([smax2*0.999999]))[0]
    return q
def slack(L,z):
    q=path(L,z)
    if q is None: return -5.0
    V,_,_=car.V(q[None]); return L-V[0]
def best(L,seed=0):
    r=differential_evolution(lambda z:-slack(L,z),[(0,1),(0,0.08),(0,1),(0,1),(0,1.0)],seed=seed,maxiter=120,popsize=25,tol=1e-9,polish=True)
    return -r.fun,r.x
lo,hi=5.2,5.4247
for it in range(14):
    mid=(lo+hi)/2; s,z=best(mid)
    q=path(mid,z) if s>=0 else None
    ok = (q is not None) and car.escapes(q,mid+1e-6)
    if ok: hi=mid; zb=z
    else: lo=mid
    print(it,round(mid,5),round(s,5),ok,np.round(z,4),flush=True)
print("RESULT L2' ~",hi,"z",zb)
