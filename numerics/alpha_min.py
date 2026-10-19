import numpy as np
from fast import FastCar, arc_states
from assumptions import check
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
o,i=check(0.9,2.6,0.8,1.8,np.radians(35)); pd=i['pd']; L=i['Lam1']+1e-6
q0=np.array([car.db*np.cos(pd)+(car.w/2)*np.sin(pd), car.H-car.b*np.sin(pd)-(car.w/2)*np.cos(pd), pd])
assert car.fits(q0[None],L)[0]
def ok(alpha):
    S1=np.linspace(0,(alpha-pd)*R,800); Q1=arc_states(q0,+1,1/R,S1)
    if car.collide(Q1,L).any(): return False
    q1=Q1[-1]; S2=np.linspace(0,alpha*R,800); Q2=arc_states(q1,+1,-1/R,S2)
    if car.collide(Q2,L).any(): return False
    X,Y=car.corners(Q2[-1][None]); return Y.min()>=car.H
lo,hi=pd,np.pi/2
assert ok(hi)
for _ in range(40):
    mid=(lo+hi)/2
    if ok(mid): hi=mid
    else: lo=mid
print("alpha_min",hi,"deg",np.degrees(hi))
