"""Monte-Carlo test of the calibration inequality: for random feasible manoeuvres at height u,
Delta u / g^2 - Delta G_k <= r_k + O(g)."""
import numpy as np
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R; w=car.w; m=car.m; H=car.H
rng=np.random.default_rng(1)
def G(q,g,k):
    xi=(q[0]-car.db)/g; ph=q[2]/g; return (xi-0.5)*ph+0.5*k*ph**2
worst=-1e9
for g in [0.05,0.1]:
    L=car.ell+g
    for u in [0.3*w,0.6*w,0.85*w]:
        k=max(0.0,u-w/2); rk=R/(4*(R*R-k*k))
        cnt=0; tries=0
        while cnt<400 and tries<40000:
            tries+=1
            # random start inside window (rough), random heading small
            ph=rng.uniform(-0.3,0.3); xi=rng.uniform(-0.2,1.2)
            q=np.array([car.db+g*xi, m+w/2+u, g*ph])
            if car.collide(q[None],L)[0]: continue
            d=rng.choice([1,-1]); q0=q.copy(); ok=True
            # random piecewise curvature, up to 4 pieces
            for _ in range(rng.integers(1,5)):
                kap=rng.choice([1/R,-1/R,0.0,rng.uniform(-1/R,1/R)]); s=rng.uniform(0,0.6*g)
                S=np.linspace(0,s,25); Q=arc_states(q,d,kap,S)
                bad=car.collide(Q,L)
                if bad.any():
                    j=np.argmax(bad); q=Q[max(j-1,0)]; break
                q=Q[-1]
            du=q[1]-q0[1]
            val=du/g**2-(G(q,g,k)-G(q0,g,k))
            worst=max(worst,val-rk); cnt+=1
        print("g",g,"u/w",round(u/w,2),"r_k",round(rk,5),"max(du/g^2 - dG) - r_k over samples:",round(worst,5),flush=True)
