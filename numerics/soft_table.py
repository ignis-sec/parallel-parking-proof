"""Soft-curb (tyres only) slot lengths for the six cars of the appendix table, n = 1..5,
and n = 20 for the typical car. Body-aligned tyres: outer sidewall 2.75 cm inside the body
side, tyre width 0.205 m, plan-view length 0.50 m. Light-weight: one process, one thread."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json
import numpy as np
from soft import SoftCar, one_manoeuvre
from soft_theory import quantities, CARS
from car_table import zigzag_min
import twenty_search

out = json.load(open("out_soft_table.json")) if os.path.exists("out_soft_table.json") else {}
for name, df, dw, db, w, thd in CARS:
    if name in out:
        continue
    th = np.radians(thd)
    car = SoftCar(df, dw, db, w, th, half_track=w / 2 - 0.0275 - 0.1025, tyre_w=0.205, tyre_l=0.50)
    q, ck = quantities(df, dw, db, w, th)
    row = dict(L1s_closed=float(q['L1s']), L2s_closed=float(q['L2s']),
               thm_hyp=all(v for k, v in ck.items() if k.startswith('S')),
               two_hyp=all(v for k, v in ck.items() if k.startswith('T2') and 'X(alpha)' not in k))
    L1, psi1, q1 = one_manoeuvre(car, np.linspace(-0.05, 0.12, 681))
    row['L1'] = float(L1)
    hi = L1 + 0.3
    for n in (2, 3, 4, 5):
        val, z = zigzag_min(car, n, hi, steps=11 if n == 2 else 10)
        row[f'L{n}'] = None if val is None else float(val)
        row[f'z{n}'] = None if z is None else [float(x) for x in z]
        if val is not None:
            hi = val
    out[name] = row
    json.dump(out, open("out_soft_table.json", "w"), indent=1)
    print("done", name, {k: (round(v, 4) if isinstance(v, float) else v) for k, v in row.items() if not k.startswith('z')}, flush=True)

if "twenty" not in out:
    car = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35), half_track=0.9 - 0.0275 - 0.1025, tyre_w=0.205, tyre_l=0.50)
    lo, hi = car.ell, 4.8545
    res = twenty_search.feasible(hi, car=car)
    for it in range(11):
        mid = (lo + hi) / 2
        r = twenty_search.feasible(mid, car=car)
        print(f"   n=20 L={mid:.4f}", r, flush=True)
        if r is not None:
            hi, res = mid, r
        else:
            lo = mid
    out["twenty"] = dict(L=float(hi), n=res[0], **res[1])
    json.dump(out, open("out_soft_table.json", "w"), indent=1)
    print("done twenty", out["twenty"], flush=True)
