import numpy as np
from car import Car, collides
from sim import step, max_free, in_lane
from escape2 import escape_any
car = Car(df=0.9, dw=2.6, db=0.8, w=1.8, theta=np.radians(35)); R = car.R
L = car.L1() - 0.002
for x0 in np.linspace(car.db, car.db+(L-car.ell), 21):
    q0 = np.array([x0, car.w/2, 0.0])
    smax = max_free(car, q0, +1, 1/R, L, 'W', smax=20)
    for s in np.linspace(0, smax*0.9999, 41):
        q1 = step(q0, +1, 1/R, s)
        ok, how = escape_any(car, q1, L, 'W')
        if ok and how[0] == -1:
            print("x0", x0, "s", s, "smax", smax, "q1", q1, "how", how); raise SystemExit
print("none")
