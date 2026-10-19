import numpy as np, itertools, sys
from car2 import Car, to_world, collides, fits, step, escapes, max_free
car = Car(df=0.9, dw=2.6, db=0.8, w=1.8, theta=np.radians(35)); R = car.R

def starts(L, nx=9, npsi=7):
    out = []
    pfit = 0.042
    for p in np.linspace(-pfit*0.5, pfit, npsi):
        top = car.H - max(car.b*np.sin(p), -car.db*np.sin(p)) - (car.w/2)*np.cos(p)
        for x in np.linspace(car.db*0.95, car.db + (L-car.ell) + 0.05, nx):
            for dy in (0.0, 0.03, 0.08):
                q = np.array([x, top-dy, p])
                if fits(car, q, L): out.append(q)
    return out

def greedy(L, q, pattern):
    for (d, k) in pattern:
        if escapes(car, q, L): return True
        s = max_free(car, q, d, k, L, smax=15.0, ds=4e-3)
        q = step(q, d, k, s*0.999999)
    return escapes(car, q, L)

def feas(L, pattern):
    return any(greedy(L, q, pattern) for q in starts(L))

def min_L(pattern, lo=None, hi=5.9, it=16):
    lo = car.ell if lo is None else lo
    if not feas(hi, pattern): return None
    for _ in range(it):
        mid = (lo+hi)/2
        (hi, lo) = (mid, lo) if feas(mid, pattern) else (hi, mid)
    return hi

pats = {1: [], 2: [(-1,-1/R)], 3: [(+1,1/R),(-1,-1/R)], 4: [(-1,-1/R),(+1,1/R),(-1,-1/R)],
        5: [(+1,1/R),(-1,-1/R),(+1,1/R),(-1,-1/R)]}
for n in [int(a) for a in sys.argv[1:]]:
    print(n, min_L(pats[n]), flush=True)
