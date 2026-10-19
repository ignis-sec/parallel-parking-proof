"""Shortest slots for the typical car in the soft-curb model (tyres only), n = 2..5 and 20.
Same strategy families and searches as for the rigid curb (car_table.py, twenty_search.py)."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json
import numpy as np
from soft import SoftCar, one_manoeuvre
from car_table import zigzag_min
import twenty_search

car = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35))
out = {}
L1, psi1, q1 = one_manoeuvre(car, np.linspace(-0.05, 0.12, 341))
out["L1"] = float(L1)
print("n=1", round(L1, 4), flush=True)
hi = L1 + 0.3
for n in (2, 3, 4, 5):
    val, z = zigzag_min(car, n, hi, steps=11 if n == 2 else 10)
    out[f"L{n}"] = None if val is None else float(val)
    out[f"z{n}"] = None if z is None else [float(x) for x in z]
    print(f"n={n}", val, flush=True)
    if val is not None:
        hi = val
    json.dump(out, open("out_soft.json", "w"), indent=1)

# twenty manoeuvres: contact zigzags, bisection between ell and the rigid-curb value
lo, hi = car.ell, 4.8545
res = twenty_search.feasible(hi, car=car)
assert res is not None
for it in range(10):
    mid = (lo + hi) / 2
    r = twenty_search.feasible(mid, car=car)
    print(f"n=20 L={mid:.4f}", r, flush=True)
    if r is not None:
        hi, res = mid, r
    else:
        lo = mid
out["L20"] = float(hi)
out["p20"] = dict(n=res[0], **res[1])
json.dump(out, open("out_soft.json", "w"), indent=1)
print("RESULT", out, flush=True)
