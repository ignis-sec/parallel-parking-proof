"""Simulate many-maneuver exits for small slack g: S-curve wiggle and tilted loops (margin model)."""
import numpy as np, sys
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R; w=car.w; m=car.m; H=car.H
def path_ok(q, segs, L, ns=40):
    for (d,k,s) in segs:
        S=np.linspace(0,s,ns); Q=arc_states(q,d,k,S)
        if car.collide(Q,L).any(): return False, None
        q=Q[-1]
    return True, q
def scurve(q, d, a1, a2):
    """direction d; first arc rotates by +a1*(sign) then second by a2 back. fwd: left then right."""
    if d==+1: return [(+1, 1/R, a1*R), (+1, -1/R, a2*R)]
    else:     return [(-1, 1/R, a1*R), (-1, -1/R, a2*R)]   # bwd: B-left (heading down) then B-right
def run(g, mode='S', maxn=200000):
    L=car.ell+g; q=np.array([car.db+1e-9, H-w/2, 0.0]); n=0; d=+1
    while n<maxn:
        X,Y=car.corners(q[None])
        if Y.min()>=H: return n
        k=max(0.0,(q[1]-w/2-m)-w/2)
        tilt=(k/(R**2-k**2))*g if mode=='T' else 0.0
        # target end heading: fwd ends at -tilt/2, bwd ends at +tilt/2 ; start heading is q[2]
        h_end = -tilt/2 if d==+1 else tilt/2
        lo,hi=0.0,0.5; best=None
        for _ in range(30):
            a=(lo+hi)/2
            if d==+1: a1=a; a2=a1+(q[2]-h_end)      # heading: q2 -> q2+a1 -> h_end
            else:     a1=a; a2=a1+(h_end-q[2])      # bwd: B-left decreases heading by a1, B-right increases by a2
            if a2<0: lo=a; continue
            ok,qn=path_ok(q, scurve(q,d,a1,a2), L)
            if ok: lo=a; best=qn
            else: hi=a
        if best is None: return -n
        q=best; n+=1; d=-d
    return n
if __name__=="__main__":
    mode=sys.argv[1]
    K2=4*R*w-w**3/(6*R)
    for g in [float(x) for x in sys.argv[2:]]:
        n=run(g,mode); print(mode,"g",g,"n",n,"n g^2",n*g*g,"K^2",K2,"4Rw",4*R*w,flush=True)
