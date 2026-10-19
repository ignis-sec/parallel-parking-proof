"""Sensitivity of the soft-curb one-manoeuvre length of the typical car to the tyre data:
delta_s in {0, 2.75, 5} cm and lambda in {0.20, 0.25, 0.30} m. Closed form phi_0(psi_t) and the
numerical optimum over parked starts (as for the city car). Light-weight: one thread."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np
from soft import SoftCar, one_manoeuvre
from soft_theory import quantities

df, dw, db, w, th = 0.9, 2.6, 0.8, 1.8, np.radians(35)
TW = 0.205
vals = []
for ds in (0.0, 0.0275, 0.05):
    for lam in (0.20, 0.25, 0.30):
        q, ck = quantities(df, dw, db, w, th, ds=ds, lam=lam)
        hyp = all(v for k, v in ck.items() if k.startswith('S'))
        car = SoftCar(df, dw, db, w, th, half_track=w / 2 - ds - TW / 2, tyre_w=TW, tyre_l=2 * lam)
        pt = q['psi_t']
        L, psi, _ = one_manoeuvre(car, np.linspace(pt - 0.012, pt, 241))
        vals.append(L)
        print(f"ds={100 * ds:4.2f} cm lam={lam:.2f}: closed {q['L1s']:.4f} (hyp {hyp}), numerical {L:.4f} "
              f"at psi={psi:.4f} (psi_t={pt:.4f})", flush=True)
print(f"range of the numerical values: {min(vals):.4f} - {max(vals):.4f}, spread {100 * (max(vals) - min(vals)):.2f} cm")
