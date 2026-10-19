"""Exact-simulation checks of the soft-curb closed forms (body-aligned tyres)."""
import numpy as np
from fast import arc_states
from soft import SoftCar, arcs_free, level_out, one_manoeuvre
from soft_theory import quantities, CARS

for name, df, dw, db, w, thd in CARS:
    th = np.radians(thd)
    car = SoftCar(df, dw, db, w, th, half_track=w / 2 - 0.0275 - 0.1025, tyre_w=0.205, tyre_l=0.50)
    q, ck = quantities(df, dw, db, w, th)
    R, b, m, H = car.R, car.b, car.m, car.H
    # one manoeuvre: numerical optimum over parked starts (grid) vs closed form
    L1, psi1, q1 = one_manoeuvre(car, np.linspace(-0.05, 0.12, 681))
    # two manoeuvres: double-contact construction at L = L2s (+1e-6)
    L = q['L2s'] + 1e-6
    q0 = np.array([L - b, m + w / 2, 0.0])
    ok0 = car.fits(q0[None], L)[0]
    ok1, qe = arcs_free(car, q0, [(-1, -1 / R, R * q['alpha_s'] * (1 - 1e-7))], L)
    ok2 = car.escapes(qe, L + 1e-6) and level_out(car, qe, L + 1e-6) is not None
    print(f"{name:15s} L1 numeric {L1:.4f} (tilt {psi1:.4f}) closed {q['L1s']:.4f} | "
          f"two: start parked {ok0}, reverse arc free {ok1}, exit {ok2}, L2s {q['L2s']:.4f}", flush=True)
