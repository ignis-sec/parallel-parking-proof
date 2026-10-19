import numpy as np
from car import Car, collides
from sim import step, max_free
from zigzag import escapes
car = Car(df=0.9, dw=2.6, db=0.8, w=1.8, theta=np.radians(35)); R = car.R
def run(L, x0, model='W'):
    q0 = np.array([x0, car.w/2, 0.0])
    s1 = max_free(car, q0, +1, 1/R, L, model, smax=20, ds=2e-3); q1 = step(q0, +1, 1/R, s1*0.999999)
    s2 = max_free(car, q1, -1, -1/R, L, model, smax=20, ds=2e-3); q2 = step(q1, -1, -1/R, s2*0.999999)
    return q1, q2, s1, s2, escapes(car, q2, L, model)
L = 5.1127
best=None
for x0 in np.linspace(car.db, car.db+(L-car.ell), 81):
    q1,q2,s1,s2,ok = run(L,x0)
    if ok: print("x0",round(x0,4),"a1",round(s1/R,4),"a2",round(s2/R,4),"q1",q1.round(4),"q2",q2.round(4)); break
# identify binding contacts at end of B2
from car import Car as C
q = q2
print("corners", C.to_world(car.corners_body(), q).round(4))
print("wheels", C.to_world(car.wheels_body(), q).round(4))
