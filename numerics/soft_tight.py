"""Full zigzag search for the soft-curb typical car, as for the rigid curb (tab:zigzag):
differential evolution with polishing that maximises L - V at the end, warm-started from the best
known motion, and bisection on L. Usage: soft_tight.py n [bracket width]. Writes out_soft_tight{n}.json.
Light-weight: one process, one thread."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json, sys
import numpy as np
from scipy.optimize import differential_evolution
from soft import SoftCar
from car_table import run, npar

car = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35), half_track=0.77, tyre_w=0.205, tyre_l=0.50)
n = int(sys.argv[1])
width = float(sys.argv[2]) if len(sys.argv) > 2 else 0.08
fn = f'out_soft_tight{n}.json'
if os.path.exists(fn):
    d = json.load(open(fn)); hi, zhi = d[f'L{n}'], np.array(d[f'z{n}'])
else:
    r = json.load(open('out_soft_table.json'))['Typical']; hi, zhi = r[f'L{n}'], np.array(r[f'z{n}'])
lo = hi - width


def solve(L, x0, seed):
    r = differential_evolution(lambda z: -run(car, L, z, n)[0], [(0, 1)] * npar(n), seed=seed,
                               maxiter=60, popsize=12, tol=1e-10, polish=True, x0=x0)
    s, q = run(car, L, r.x, n)
    return r.x, s, (s >= 0 and car.escapes(q, L + 1e-6))


warm = zhi
for it in range(8):
    mid = (lo + hi) / 2
    z, s, ok = solve(mid, warm, it + 1)
    print(f"n={n} L={mid:.5f}: slack {s:.5f} ok {ok}", flush=True)
    if ok:
        hi, zhi, warm = mid, z, z
        json.dump({f'L{n}': float(hi), f'z{n}': [float(x) for x in zhi]}, open(fn, 'w'), indent=1)
    else:
        lo = mid
print("RESULT", n, hi, list(np.round(zhi, 5)), flush=True)
