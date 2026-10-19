"""Shortest slot for the typical car with at most 20 manoeuvres, in the contact-zigzag family.

Exit manoeuvres alternate: forward = full left lock until contact; reverse = full left lock
through a small angle a (until contact if earlier), then full right lock until contact.
The escape (forward left lock into the lane) is tried before every manoeuvre.
Parameters: start position (fraction of the slack), direction of the first manoeuvre, a.
Light-weight: single process, single thread.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json, sys, time
import numpy as np
from fast import FastCar, arc_states
from car_table import max_free

car = FastCar(0.9, 2.6, 0.8, 1.8, np.radians(35))
R = car.R
NMAX = 20


def run(L, xf, first, a, nmax=NMAX, car=car):
    """Returns (number of manoeuvres incl. escape, list of manoeuvres) or (None, None)."""
    q = np.array([car.db + xf * (L - car.ell), car.H - car.w / 2, 0.0])
    if not car.fits(q[None], L)[0]:
        return None, None
    mans, d = [], first
    while len(mans) < nmax:
        V, _, _ = car.V(q[None])
        if V[0] <= L and car.escapes(q, L):
            return len(mans) + 1, mans
        if len(mans) == nmax - 1:
            return None, None
        man = []
        if d == +1:
            s = max_free(car, q, +1, 1 / R, L, smax=10.0)
            man.append((+1, 1 / R, s * 0.999999))
        else:
            if a > 0:
                s = max_free(car, q, -1, 1 / R, L, smax=a * R + 1e-9)
                s = min(s, a * R) * 0.999999
                man.append((-1, 1 / R, s))
                q = arc_states(q, -1, 1 / R, np.array([s]))[0]
            s = max_free(car, q, -1, -1 / R, L, smax=10.0)
            man.append((-1, -1 / R, s * 0.999999))
        q = arc_states(q, man[-1][0], man[-1][1], np.array([man[-1][2]]))[0]
        if sum(x[2] for x in man) < 1e-5:
            return None, None          # stalled
        mans.append(man)
        d = -d
    return None, None


def feasible(L, car=car):
    best = None
    for a in (0.0, 0.02, 0.04, 0.06, 0.08):
        for first in (+1, -1):
            for xf in np.linspace(0, 1, 11):
                n, mans = run(L, xf, first, a, car=car)
                if n is not None and (best is None or n < best[0]):
                    best = (n, dict(xf=float(xf), first=first, a=a))
    return best


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "time":
        t = time.time()
        print(feasible(4.9), round(time.time() - t, 1), "s")
        sys.exit()
    lo, hi = 4.70, 4.95
    res_hi = feasible(hi)
    assert res_hi is not None, "upper end not feasible"
    for it in range(9):
        mid = (lo + hi) / 2
        r = feasible(mid)
        print(f"L={mid:.4f}", r, flush=True)
        if r is not None:
            hi, res_hi = mid, r
        else:
            lo = mid
    # stage 2: finer grid near the optimum (start positions 0.2..0.6, small left-lock angles)
    def feasible_fine(L):
        best = None
        for a in (0.0, 0.01, 0.02, 0.03):
            for first in (-1, +1):
                for xf in np.linspace(0.2, 0.6, 41):
                    n, mans = run(L, xf, first, a)
                    if n is not None and (best is None or n < best[0]):
                        best = (n, dict(xf=float(xf), first=first, a=a))
        return best
    lo = 4.835
    for it in range(7):
        mid = (lo + hi) / 2
        r = feasible_fine(mid)
        print(f"fine L={mid:.5f}", r, flush=True)
        if r is not None:
            hi, res_hi = mid, r
        else:
            lo = mid
    out = dict(L=hi, n=res_hi[0], **res_hi[1])
    json.dump(out, open("out_twenty.json", "w"), indent=1)
    print("RESULT", out, flush=True)
