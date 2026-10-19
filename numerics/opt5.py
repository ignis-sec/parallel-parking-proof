"""Richer zigzag family: reverse manoeuvre = B-left by a (<=0.1 rad, truncated at contact) then B-right (fraction t of max);
forward manoeuvre = F-left fraction t. Start level at top at x0. Last = forward escape (V<=L & escape check)."""
import numpy as np, sys
from scipy.optimize import differential_evolution
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
def seq(n):
    # n-1 manoeuvres before escape, last of them reverse
    d=-1; out=[]
    for i in range(n-1): out.append(d); d=-d
    return out[::-1]
def run(L,z,n):
    x0=car.db+z[0]*(L-car.ell); q=np.array([x0,car.H-car.w/2,0.0])
    if not car.fits(q[None],L)[0]: return -9.0,q
    i=1
    for d in seq(n):
        if d==-1:
            a=z[i]*0.1; t=z[i+1]; i+=2
            sm=car.max_free(q,-1,1/R,L,smax=a*R+1e-9,ds=2e-3); q=arc_states(q,-1,1/R,np.array([min(sm,a*R)*0.999999]))[0]
            sm=car.max_free(q,-1,-1/R,L,smax=10.0,ds=2e-3); q=arc_states(q,-1,-1/R,np.array([t*sm*0.999999]))[0]
        else:
            t=z[i]; i+=1
            sm=car.max_free(q,+1,1/R,L,smax=10.0,ds=2e-3); q=arc_states(q,+1,1/R,np.array([t*sm*0.999999]))[0]
    V,_,_=car.V(q[None]); return L-V[0],q
def npar(n): return 1+sum(2 if d==-1 else 1 for d in seq(n))
n=int(sys.argv[1]); hi=float(sys.argv[2]); lo=car.ell
best=None
for it in range(12):
    mid=(lo+hi)/2
    r=differential_evolution(lambda z:-run(mid,z,n)[0],[(0,1)]*npar(n),seed=it,maxiter=80,popsize=15,tol=1e-9,polish=True)
    s=-r.fun; ok=False
    if s>=0: ok=car.escapes(run(mid,r.x,n)[1],mid+1e-6)
    if ok: hi=mid; best=r.x
    else: lo=mid
    print(n,it,round(mid,5),round(s,5),ok,flush=True)
print("RESULT n",n,"L~",round(hi,5),"z",np.round(best,4) if best is not None else None,flush=True)
