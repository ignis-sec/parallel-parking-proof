"""Soft-curb model: the bodywork may overhang the curb, only the tyres must stay on the road.

The parked cars are obstacles for the whole body as before (margin m = w/10).
Tyre geometry (not part of the paper's car data; typical compact-car values):
half track 0.77 m, tyre width 0.205 m, plan-view tyre length at curb height 0.50 m.
By default the tyre rectangles are aligned with the body, as in the paper; with steer_front=True
the front tyres are turned to the Ackermann angles of the current full-lock arc (straight if k = 0).
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json, sys
import numpy as np
from fast import FastCar, arc_states

HALF_TRACK, TYRE_W, TYRE_L = 0.77, 0.205, 0.50


class SoftCar(FastCar):
    def __init__(s, *a, half_track=HALF_TRACK, tyre_w=TYRE_W, tyre_l=TYRE_L, steer_front=False, **kw):
        super().__init__(*a, **kw)
        s.T, s.tw, s.tl = half_track, tyre_w, tyre_l
        s.steer_front = steer_front
        s._tp = {}

    def tyre_points(s, k):
        """Body coordinates of the 16 tyre corners. By default (the model of the paper) the
        tyre rectangles are aligned with the car; with steer_front=True the front tyres are
        turned to the Ackermann angles of the full-lock steering k."""
        key = None if (not k or not s.steer_front) else (1 if k > 0 else -1)
        if key not in s._tp:
            pts = []
            for u in (0.0, s.dw):
                for v in (-s.T, s.T):
                    if u == 0.0 or key is None:
                        a = 0.0
                    elif key > 0:
                        a = np.arctan2(s.dw, s.R - v)
                    else:
                        a = -np.arctan2(s.dw, s.R + v)
                    ca, sa = np.cos(a), np.sin(a)
                    for du, dv in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                        x, y = du * s.tl / 2, dv * s.tw / 2
                        pts.append((u + ca * x - sa * y, v + sa * x + ca * y))
            s._tp[key] = np.array(pts)
        return s._tp[key]

    def collide(s, Q, L, eps=1e-12, k=None):
        Q = np.atleast_2d(Q)
        P = s.tyre_points(k)
        c, sn = np.cos(Q[:, 2]), np.sin(Q[:, 2])
        Yt = Q[:, 1, None] + sn[:, None] * P[None, :, 0] + c[:, None] * P[None, :, 1]
        return (Yt.min(1) < -eps) | s.strips(Q, L, eps)


def arcs_free(car, q, man, L, ns=400):
    """Collision check of a manoeuvre given as arcs (d, k, s); returns (free, end state)."""
    for d, k, s in man:
        Q = arc_states(q, d, k, np.linspace(0, s, ns))
        if car.collide(Q, L, k=k).any():
            return False, q
        q = Q[-1]
    return True, q


def level_out(car, q, L, gap=0.0):
    """Forward full left lock to psi*, then full right lock to level in the lane (smallest psi*)."""
    R = car.R
    for psi in np.arange(q[2] + 0.01, 1.4, 0.005):
        man = [(+1, 1 / R, (psi - q[2]) * R), (+1, -1 / R, psi * R)]
        ok, qe = arcs_free(car, q, man, L)
        if ok:
            X, Y = car.corners(qe[None])
            if Y.min() >= car.H + gap - 1e-9:
                return man
    return None


def one_manoeuvre(car, psis):
    """Best forward one-manoeuvre exit over parked starts with heading in `psis`:
    each start is as high (top at H) and as far back (touching the car behind) as possible."""
    best = None
    for psi in psis:
        c, s = np.cos(psi), np.sin(psi)
        top = max(u * s + v * c for u in (-car.db, car.b) for v in (-car.w / 2, car.w / 2))
        y = car.H - top
        lo, hi = -1.0, 3.0
        if car.collide(np.array([[hi, y, psi]]), 100.0)[0]:
            continue                                  # tyres below the curb at this tilt
        for _ in range(50):
            mid = (lo + hi) / 2
            if car.collide(np.array([[mid, y, psi]]), 100.0)[0]:
                lo = mid
            else:
                hi = mid
        q = np.array([hi, y, psi])
        L = car.V(q[None])[0][0] + 1e-6
        L = max(L, (car.corners(q[None])[0].max()) + 1e-6)
        if not car.fits(q[None], L)[0] or not car.escapes(q, L):
            continue
        man = level_out(car, q, L)
        if man is None:
            continue
        if best is None or L < best[0]:
            best = (L, psi, q)
    return best


if __name__ == "__main__":
    hard = FastCar(0.9, 2.6, 0.8, 1.8, np.radians(35))
    soft = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35))
    psis = np.linspace(-0.05, 0.12, 341)
    for name, car in (("rigid curb", hard), ("tyres only", soft)):
        L, psi, q = one_manoeuvre(car, psis)
        X, Y = car.corners(q[None])
        print(f"{name:11s}: L1 = {L:.4f} m  parked tilt {np.degrees(psi):.2f} deg,"
              f" lowest body point y = {100 * Y.min():.1f} cm", flush=True)
