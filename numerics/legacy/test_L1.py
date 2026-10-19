import numpy as np
from car import Car, collides
from sim import step, max_free
car = Car(df=0.9, dw=2.6, db=0.8, w=1.8, theta=np.radians(35))
print("R",car.R,"ell",car.ell,"L1",car.L1())
for L in [car.L1()-0.01, car.L1()+0.01]:
    q0 = np.array([car.db, car.w/2, 0.0])
    s = max_free(car, q0, +1, 1/car.R, L, smax=car.R*np.pi/2)
    q = step(q0, +1, 1/car.R, s)
    print(L, "free arclength", s, "of", car.R*np.pi/2, "end", q)
