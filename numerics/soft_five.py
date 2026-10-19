"""Tightening search for the soft-curb five-manoeuvre zigzag of the typical car (for the appendix
figure): differential evolution with polishing that maximises L - V at the end (as for the rigid
curb), warm-started from the motion of soft_table.py / soft_polish.py, and bisection on L.
Light-weight: one process, one thread."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json
import numpy as np
from scipy.optimize import differential_evolution
from soft import SoftCar
from car_table import run, npar

car = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35), half_track=0.77, tyre_w=0.205, tyre_l=0.50)
n = 5
rows = json.load(open('out_soft_table.json'))
hi, zhi = rows['Typical']['L5'], np.array(rows['Typical']['z5'])
lo = hi - 0.04
warm = zhi


def solve(L, x0, seed):
    r = differential_evolution(lambda z: -run(car, L, z, n)[0], [(0, 1)] * npar(n), seed=seed,
                               maxiter=60, popsize=12, tol=1e-10, polish=True, x0=x0)
    s, q = run(car, L, r.x, n)
    return r.x, s, (s >= 0 and car.escapes(q, L + 1e-6))


z, s, ok = solve(hi, warm, 0)
print(f"L={hi:.5f}: slack {s:.5f} ok {ok}", flush=True)
if ok:
    zhi, warm = z, z
for it in range(6):
    mid = (lo + hi) / 2
    z, s, ok = solve(mid, warm, it + 1)
    print(f"L={mid:.5f}: slack {s:.5f} ok {ok}", flush=True)
    if ok:
        hi, zhi, warm = mid, z, z
    else:
        lo = mid
json.dump({'L5': float(hi), 'z5': [float(x) for x in zhi]}, open('out_soft_five.json', 'w'), indent=1)
print("RESULT", hi, list(np.round(zhi, 5)), flush=True)
