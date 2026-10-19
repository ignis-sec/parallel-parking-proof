import numpy as np
from car import Car, collides
from sim import step, max_free, free_along, in_lane

def escapes(car, q, L, model='W'):
    """forward full-left-lock arc from q until heading pi/2: collision-free and ends in lane"""
    ang = np.pi/2 - q[2]
    if ang <= 0: return in_lane(car, q)
    s = ang*car.R
    if not free_along(car, q, +1, 1/car.R, s, L, model, ds=5e-3): return False
    return in_lane(car, step(q, +1, 1/car.R, s))

def greedy(car, L, x0, pattern, model='W'):
    """pattern: list of (d, kappa) maneuvers, each run until contact; then test escape"""
    q = np.array([x0, car.w/2, 0.0])
    if collides(car, q, L, model): return False, q
    for (d, k) in pattern:
        if escapes(car, q, L, model): return True, q
        s = max_free(car, q, d, k, L, model, smax=20.0, ds=4e-3)
        q = step(q, d, k, s*0.999999)
    return escapes(car, q, L, model), q

def min_L(car, pattern, model='W', lo=None, hi=None, nx=25):
    lo = car.ell if lo is None else lo; hi = car.L1()+0.01 if hi is None else hi
    def feas(L):
        for x0 in np.linspace(car.db, car.db + (L-car.ell), nx):
            if greedy(car, L, x0, pattern, model)[0]: return True
        return False
    if not feas(hi): return None
    for _ in range(22):
        mid = (lo+hi)/2
        if feas(mid): hi = mid
        else: lo = mid
    return hi

if __name__ == "__main__":
    car = Car(df=0.9, dw=2.6, db=0.8, w=1.8, theta=np.radians(35))
    R = car.R
    print("L1", car.L1(), "ell", car.ell)
    for model in ['W','M0']:
        for name, pat in [("F",[]),
                          ("F,B-right,F", [(+1,1/R),(-1,-1/R)]),
                          ("F,B-str,F", [(+1,1/R),(-1,0.0)]),
                          ("B-right,F", [(-1,-1/R)]),
                          ("F,B,F,B,F", [(+1,1/R),(-1,-1/R),(+1,1/R),(-1,-1/R)])]:
            print(model, name, min_L(car, pat, model))
