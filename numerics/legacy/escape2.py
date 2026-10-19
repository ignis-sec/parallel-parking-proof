import numpy as np
from car import Car, collides
from sim import step, max_free, in_lane
from zigzag import escapes

def escape_any(car, q, L, model='W', ds=5e-3):
    """try arcs (d,kappa), d in {+1,-1}, kappa in {+-1/R, 0}: success if reaches lane moving up"""
    for d in (+1, -1):
        for k in (1/car.R, -1/car.R, 0.0):
            s = 0.0; ok = False
            while s < 2*np.pi*car.R:
                s += ds; qq = step(q, d, k, s)
                if collides(car, qq, L, model): break
                vy = d*np.sin(qq[2])
                if in_lane(car, qq) and vy > 0: ok = True; break
            if ok: return True, (d, k)
    return False, None

def best_FB(car, model='W', nx=21, na=41):
    """exit: F-left by angle a (<= contact) from x0, then any single-arc escape"""
    R = car.R
    def feas(L):
        for x0 in np.linspace(car.db, car.db+(L-car.ell), nx):
            q0 = np.array([x0, car.w/2, 0.0])
            smax = max_free(car, q0, +1, 1/R, L, model, smax=20)
            for s in np.linspace(0, smax*0.9999, na):
                q1 = step(q0, +1, 1/R, s)
                ok, how = escape_any(car, q1, L, model)
                if ok and how[0] == -1: return True
        return False
    lo, hi = car.ell, car.L1() + 0.3
    if not feas(hi): return None
    for _ in range(14):
        mid = (lo+hi)/2
        if feas(mid): hi = mid
        else: lo = mid
    return hi

if __name__ == "__main__":
    car = Car(df=0.9, dw=2.6, db=0.8, w=1.8, theta=np.radians(35))
    print("L1", car.L1(), " back-1 formula", car.b + np.sqrt(car.db**2 + 2*car.R*car.w))
    print("W  F-then-backward-escape:", best_FB(car, 'W'))
