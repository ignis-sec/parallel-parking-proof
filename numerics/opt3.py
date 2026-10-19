"""Faster search: start parallel at top (bottom at m) at x0; maneuver fractions t_i of max free length.
Objective for given L: max slack = L - V(final) subject to escape check."""
import numpy as np, sys, itertools
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
def run(L, x0, ts, pattern):
    q=np.array([x0, car.H-car.w/2, 0.0])
    if not car.fits(q[None],L)[0]: return -9, q
    for (d,k),t in zip(pattern,ts):
        smax=car.max_free(q,d,k,L,smax=12.0,ds=3e-3)
        q=arc_states(q,d,k,np.array([min(max(t,0),1)*smax*0.999999]))[0]
    V,_,_=car.V(q[None]); return L-V[0], q
def best(L, pattern, grid):
    bs=-9; bz=None
    xs=np.linspace(car.db, car.db+(L-car.ell), 41)
    for x0 in xs:
        for ts in itertools.product(*grid):
            s,q=run(L,x0,ts,pattern)
            if s>bs: bs,bz=s,(x0,ts,q)
    return bs,bz
pats={3:[(+1,1/R),(-1,-1/R)], 4:[(-1,-1/R),(+1,1/R),(-1,-1/R)], 5:[(+1,1/R),(-1,-1/R),(+1,1/R),(-1,-1/R)],
      6:[(-1,-1/R),(+1,1/R),(-1,-1/R),(+1,1/R),(-1,-1/R)]}
n=int(sys.argv[1]); pat=pats[n]
fr=np.linspace(0,1,11)
grid=[fr if d==+1 else [1.0] for (d,k) in pat]   # backward moves greedy (to contact), forward moves fractional
lo,hi=car.ell,5.6
for _ in range(13):
    mid=(lo+hi)/2; s,z=best(mid,pat,grid)
    if s>=0 and car.escapes(z[2],mid+1e-6): hi=mid; zb=z
    else: lo=mid
print(n,"L~",round(hi,4),"x0",round(zb[0],4),"ts",zb[1],"q",np.round(zb[2],4),flush=True)
