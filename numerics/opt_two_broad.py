"""Broad search for 2-manoeuvre exits (reverse, then forward escape) in the margin model.
Reverse manoeuvre = 3 pieces with free curvature in [-1/R,1/R] and free lengths; start: free (x0 offset, height drop, tilt).
Feasibility: whole reverse path collision-free; then V(q1) <= L and escape check (full-left-lock arc)."""
import numpy as np, sys
from scipy.optimize import differential_evolution
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
PFIT=0.042
def start(L,a,dy,p):
    top=car.H-max(car.b*np.sin(p),-car.db*np.sin(p))-(car.w/2)*np.cos(p)
    y=top-dy; x=car.db+a*(L-car.ell)
    return np.array([x,y,p])
def run(L,z):
    a,dy,p=z[0],z[1]*0.15,(z[2]*2-1)*PFIT
    q=start(L,a,dy,p)
    if not car.fits(q[None],L)[0]: return -5.0,q,False
    for i in range(3):
        k=(z[3+2*i]*2-1)/R; s=z[4+2*i]*1.5
        S=np.linspace(0,s,60); Q=arc_states(q,-1,k,S)
        bad=car.collide(Q,L)
        if bad.any():
            j=np.argmax(bad); q=Q[max(j-1,0)]; break
        q=Q[-1]
    V,_,_=car.V(q[None]); return L-V[0],q,True
def best(L,seed):
    f=lambda z: -run(L,z)[0]
    r=differential_evolution(f,[(0,1)]*9,seed=seed,maxiter=150,popsize=20,tol=1e-8,polish=True)
    return -r.fun,r.x
L=float(sys.argv[1]) if len(sys.argv)>1 else 5.40
for seed in range(3):
    s,z=best(L,seed); sl,q,_=run(L,z)
    print("L",L,"seed",seed,"best slack",round(s,5),"escape?",car.escapes(q,L) if s>=0 else False,"z",np.round(z,3),flush=True)
