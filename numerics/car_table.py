"""Minimal slot lengths for several car configurations (appendix table).

n = 1 : exact value Lambda_1 (Theorem one), after checking Assumption (A1)-(A7).
n = 2 : Lambda_2^* (Proposition two-better), after checking its hypotheses, confirmed by an
        exact simulation of the exit.
n >= 3: best rotation zigzag found by a warm-started differential-evolution search
        (same family as opt5.py), every reported value confirmed by simulating the escape.
All values for n >= 2 are upper bounds for L_min(n).

Light-weight by design: single process, single thread, chunked collision sweeps.
Usage: nice -n 19 python3 car_table.py [time]
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import sys, json, time
import numpy as np
from scipy.optimize import brentq, differential_evolution
from fast import FastCar, arc_states
from assumptions import check

CARS = [
    # name,            df,   dw,   db,   w,    theta [deg]
    ("City car",       0.65, 2.35, 0.55, 1.65, 37),
    ("Compact",        0.85, 2.60, 0.75, 1.78, 36),
    ("Typical",        0.90, 2.60, 0.80, 1.80, 35),
    ("Mid-size sedan", 0.95, 2.85, 1.00, 1.84, 34),
    ("Large SUV",      1.00, 3.00, 1.05, 1.98, 33),
    ("Van",            1.00, 3.40, 1.10, 2.00, 31),
]
NS = [3, 4, 5]
# optimal parameters of the typical car (opt5.py), used as warm starts
WARM = {2: [1.0, 0.4117, 1.0], 3: [0.0, 0.8121, 0.5519, 1.0],
        4: [1.0, 0.7598, 1.0, 1.0, 0.0, 1.0], 5: [0.0, 0.9954, 0.3825, 1.0, 1.0, 0.0, 1.0]}


def max_free(car, q, d, k, L, smax, ds=2e-3, chunk=200):
    """Largest s <= smax such that the arc from q is collision free on [0, s]."""
    s0 = 0.0
    while s0 < smax:
        S = s0 + ds * np.arange(1, chunk + 1)
        S = np.minimum(S, smax)
        bad = car.collide(arc_states(q, d, k, S), L, k=k)
        if bad.any():
            i = int(np.argmax(bad))
            lo = S[i - 1] if i > 0 else s0
            hi = S[i]
            for _ in range(30):
                mid = (lo + hi) / 2
                if car.collide(arc_states(q, d, k, np.array([mid])), L, k=k)[0]:
                    hi = mid
                else:
                    lo = mid
            return lo
        s0 = S[-1]
    return smax


def seq(n):
    d, out = -1, []
    for _ in range(n - 1):
        out.append(d)
        d = -d
    return out[::-1]


def npar(n):
    return 1 + sum(2 if d == -1 else 1 for d in seq(n))


def run(car, L, z, n):
    """Zigzag exit; returns (L - V(final), final configuration)."""
    R = car.R
    x0 = car.db + z[0] * (L - car.ell)
    q = np.array([x0, car.H - car.w / 2, 0.0])
    if not car.fits(q[None], L)[0]:
        return -9.0, q
    i = 1
    for d in seq(n):
        if d == -1:
            a = z[i] * 0.1
            t = z[i + 1]
            i += 2
            sm = max_free(car, q, -1, 1 / R, L, smax=a * R + 1e-9)
            q = arc_states(q, -1, 1 / R, np.array([min(sm, a * R) * 0.999999]))[0]
            sm = max_free(car, q, -1, -1 / R, L, smax=10.0)
            q = arc_states(q, -1, -1 / R, np.array([t * sm * 0.999999]))[0]
        else:
            t = z[i]
            i += 1
            sm = max_free(car, q, +1, 1 / R, L, smax=10.0)
            q = arc_states(q, +1, 1 / R, np.array([t * sm * 0.999999]))[0]
    V, _, _ = car.V(q[None])
    return L - V[0], q


def feasible(car, L, n, seed, maxiter=40, popsize=10):
    """Search the zigzag family at slot length L; returns parameters of a verified exit or None."""
    found = {}

    def cb(xk, convergence=None):
        s, q = run(car, L, xk, n)
        if s >= 0 and car.escapes(q, L + 1e-6):
            found["z"] = np.array(xk)
            return True
        return False

    warm = np.clip(np.array(WARM[n], float), 0, 1)
    if cb(warm):
        return found["z"]
    differential_evolution(lambda z: -run(car, L, z, n)[0], [(0, 1)] * npar(n), seed=seed,
                           maxiter=maxiter, popsize=popsize, tol=1e-9, polish=False,
                           x0=warm, callback=cb)
    return found.get("z")


def zigzag_min(car, n, hi, steps=10):
    """Bisection between ell (infeasible) and hi (assumed feasible); returns a verified value."""
    lo, best, zbest = car.ell, None, None
    for it in range(steps):
        mid = (lo + hi) / 2
        z = feasible(car, mid, n, seed=it)
        if z is not None:
            hi, best, zbest = mid, mid, z
        else:
            lo = mid
        print(f"   n={n} it={it} L={mid:.4f} {'ok' if z is not None else '--'}", flush=True)
    return best, zbest


def lambda2_star(df, dw, db, w, th, mfrac=0.1):
    """Proposition two-better: returns (Lambda2*, a0, alpha1, hypotheses_ok)."""
    R = dw / np.tan(th); b = dw + df; Rm, Rp = R - w / 2, R + w / 2
    rho = np.hypot(b, Rp); r = np.hypot(db, Rp); m = mfrac * w; H = m + w
    beta = np.arctan2(db, Rp); gam = np.arctan2(Rp, b)

    def a0_of(a1):
        c = (H + Rm * (1 + np.cos(a1)) - db * np.sin(a1)) / (2 * R)
        return np.arccos(np.clip(c, -1, 1))

    def f(a1):
        a0 = a0_of(a1)
        return b + 2 * R * (np.sin(a0) + np.sin(a1)) - np.sqrt(max(rho**2 - (r * np.cos(a1 - beta) - H)**2, 0))

    grid = np.linspace(beta, np.pi / 2 - 1e-6, 400)
    vals = [f(a) for a in grid]
    a1 = None
    for i in range(len(grid) - 1):
        if vals[i] <= 0 <= vals[i + 1] or vals[i] >= 0 >= vals[i + 1]:
            a1 = brentq(f, grid[i], grid[i + 1], xtol=1e-14)
            break
    if a1 is None:
        return None
    a0 = a0_of(a1)
    L2 = b + 2 * R * np.sin(a0) + db * np.cos(a1) + Rp * np.sin(a1)
    M = max(b, db)
    ok = (beta <= a1 < np.pi / 2 and 0 < a0 < np.pi / 2 and db < b
          and H + Rm >= rho * np.sin(gam + a0) and db * np.cos(a1) >= Rm * np.sin(a1)
          and r * np.cos(a1 - beta) - db >= H and Rp >= db * np.tan(a1 / 2)
          and M * np.tan(a0) < Rm and Rm * np.tan(a0) < db and M * np.tan(a1) < Rm)
    return L2, a0, a1, ok


def simulate_two(car, L, a0, a1):
    """Exact simulation of the exit of Proposition two-better at slot length L."""
    R = car.R
    q = np.array([L - car.b, car.m + car.w / 2, 0.0])
    if not car.fits(q[None], L)[0]:
        return False
    s1 = R * a0
    if max_free(car, q, -1, 1 / R, L, smax=s1) < s1 * (1 - 1e-9):
        return False
    q = arc_states(q, -1, 1 / R, np.array([s1]))[0]
    s2 = R * (a0 + a1) * 0.999999
    if max_free(car, q, -1, -1 / R, L, smax=s2) < s2 * (1 - 1e-9):
        return False
    q = arc_states(q, -1, -1 / R, np.array([s2]))[0]
    return car.escapes(q, L)


def main():
    timing = len(sys.argv) > 1 and sys.argv[1] == "time"
    results = []
    if os.path.exists("out_car_table.json"):
        results = json.load(open("out_car_table.json"))
    done = {r["name"] for r in results}
    for name, df, dw, db, w, thd in CARS:
        if name in done:
            continue
        th = np.radians(thd)
        t0 = time.time()
        car = FastCar(df, dw, db, w, th)
        ok, info = check(df, dw, db, w, th)
        row = dict(name=name, df=df, dw=dw, db=db, w=w, theta=thd, ell=car.ell, R=car.R,
                   m=car.m, K=float(np.sqrt(4 * car.R * w - w**3 / (6 * car.R))),
                   assumptions={k: bool(v) for k, v in ok.items()}, L1=float(info["Lam1"]) if info else None,
                   classical=float(info["L1"]) if info else None)
        print(name, {k: bool(v) for k, v in ok.items()}, "Lam1", row["L1"], flush=True)
        two = lambda2_star(df, dw, db, w, th)
        if two is not None:
            L2, a0, a1, ok2 = two
            sim = simulate_two(car, L2 * (1 + 1e-7) + 1e-6, a0, a1)
            row.update(L2=float(L2), a0=float(a0), a1=float(a1), L2_hyp=bool(ok2), L2_sim=bool(sim))
            print(f"   Lambda2*={L2:.4f} a0={a0:.4f} a1={a1:.4f} hyp={ok2} sim={sim}", flush=True)
        else:
            ok2, sim = False, False
            row.update(L2=None, L2_hyp=False, L2_sim=False)
            print("   Lambda2*: no triple-contact solution with alpha1 >= beta", flush=True)
        row["L2_closed"] = bool(ok2 and sim)
        if not row["L2_closed"]:
            val, z = zigzag_min(car, 2, row["L1"] + 0.3, steps=11)
            row["L2"] = None if val is None else float(val)
            row["z2"] = None if z is None else [float(x) for x in z]
            L2 = row["L2"]
        if timing:
            t1 = time.time()
            z = feasible(car, 0.5 * (car.ell + L2) + 0.3, 3, seed=0)
            print("   one feasibility search:", round(time.time() - t1, 1), "s", z is not None)
            return
        hi = L2
        for n in NS:
            val, z = zigzag_min(car, n, hi)
            row[f"L{n}"] = None if val is None else float(val)
            row[f"z{n}"] = None if z is None else [float(x) for x in z]
            if val is not None:
                hi = val
        row["seconds"] = round(time.time() - t0)
        results.append(row)
        with open("out_car_table.json", "w") as fh:
            json.dump(results, fh, indent=1)
        print("  done", name, {k: row.get(k) for k in ("L1", "L2", "L3", "L4", "L5")},
              row["seconds"], "s", flush=True)


if __name__ == "__main__":
    main()
