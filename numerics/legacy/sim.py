import numpy as np
from car import Car, collides

def step(q, d, kappa, s):
    """move state q along an arc: direction d=+1 fwd/-1 bwd, curvature kappa, arclength s>=0"""
    x,y,p = q
    if abs(kappa) < 1e-14:
        return np.array([x + d*s*np.cos(p), y + d*s*np.sin(p), p])
    p2 = p + d*kappa*s
    return np.array([x + (np.sin(p2)-np.sin(p))/kappa, y - (np.cos(p2)-np.cos(p))/kappa, p2])

def free_along(car, q, d, kappa, s, L, model='W', ds=2e-3):
    n = max(2, int(np.ceil(s/ds)))
    for t in np.linspace(0, s, n+1)[1:]:
        if collides(car, step(q, d, kappa, t), L, model): return False
    return True

def max_free(car, q, d, kappa, L, model='W', smax=50.0, ds=2e-3):
    """largest s such that the arc is collision-free on [0,s] (sampled), bisection refine"""
    s = 0.0
    while s < smax:
        if collides(car, step(q, d, kappa, s+ds), L, model):
            lo, hi = s, s+ds
            for _ in range(40):
                mid = (lo+hi)/2
                if collides(car, step(q, d, kappa, mid), L, model): hi = mid
                else: lo = mid
            return lo
        s += ds
    return smax

def in_lane(car, q):
    from car import Car as C
    pts = C.to_world(car.corners_body(), q)
    return pts[:,1].min() >= car.w - 1e-12
