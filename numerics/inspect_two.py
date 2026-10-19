import numpy as np
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
def final(L,a0):
    q=np.array([L-car.b, car.H-car.w/2, 0.0])
    q=arc_states(q,-1,1/R,np.array([a0*R]))[0]
    s=car.max_free(q,-1,-1/R,L,smax=8,ds=1e-3); q1=arc_states(q,-1,-1/R,np.array([s*0.9999999]))[0]
    V,Cx,Cy=car.V(q1[None]); return q1,V[0],Cx[0],Cy[0]
# find best a0 for each L by scanning, and min L with V<=L
for L in [5.405,5.4105,5.415]:
    best=None
    for a0 in np.linspace(0,0.06,121):
        q1,V,Cx,Cy=final(L,a0)
        if best is None or L-V>best[0]: best=(L-V,a0,q1,V,Cy)
    s,a0,q1,V,Cy=best
    X,Y=car.corners(q1[None])
    print("L",L,"slack",round(s,5),"a0",round(a0,4),"psi1",round(q1[2],4),"RC",np.round([X[0,0],Y[0,0]],4),"RL",np.round([X[0,3],Y[0,3]],4),"Cy-r",round(Cy-car.rb,5),"beta",round(np.arcsin(car.db/car.rb),4))
