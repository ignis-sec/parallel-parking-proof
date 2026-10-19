"""Second pass for the soft-curb table: re-run the zigzag searches seeded with the car's own
rigid-curb motion, converted to soft-curb parameters. A rigid-curb motion is admissible with a
soft curb, so the seed is feasible at the rigid-curb length, and the bisection can only improve.
Light-weight: one process, one thread."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json, sys
import numpy as np
from scipy.optimize import differential_evolution
from fast import FastCar, arc_states
from soft import SoftCar
from soft_theory import CARS
from car_table import run, seq, npar, max_free


def convert(rig, soft, L, z, n):
    """Soft-curb parameters reproducing the rigid-curb zigzag with parameters z at length L."""
    R = rig.R
    q = np.array([rig.db + z[0] * (L - rig.ell), rig.H - rig.w / 2, 0.0])
    out = [z[0]]
    i = 1
    for d in seq(n):
        if d == -1:
            a, t = z[i] * 0.1, z[i + 1]
            i += 2
            sm = max_free(rig, q, -1, 1 / R, L, smax=a * R + 1e-9)
            s1 = min(sm, a * R) * 0.999999
            q = arc_states(q, -1, 1 / R, np.array([s1]))[0]
            sm = max_free(rig, q, -1, -1 / R, L, smax=10.0)
            s2 = t * sm * 0.999999
            sm_soft = max_free(soft, q, -1, -1 / R, L, smax=10.0)
            out += [s1 / R / 0.1 / 0.999999, min(1.0, s2 / (sm_soft * 0.999999))]
            q = arc_states(q, -1, -1 / R, np.array([s2]))[0]
        else:
            t = z[i]
            i += 1
            sm = max_free(rig, q, +1, 1 / R, L, smax=10.0)
            s = t * sm * 0.999999
            sm_soft = max_free(soft, q, +1, 1 / R, L, smax=10.0)
            out.append(min(1.0, s / (sm_soft * 0.999999)))
            q = arc_states(q, +1, 1 / R, np.array([s]))[0]
    return np.clip(np.array(out), 0, 1)


def feasible(car, L, n, warms, seed, maxiter=40, popsize=10):
    found = {}

    def ok(z):
        s, q = run(car, L, z, n)
        return s >= 0 and car.escapes(q, L + 1e-6)

    for wz in warms:
        if ok(wz):
            return np.array(wz)

    def cb(xk, convergence=None):
        if ok(xk):
            found["z"] = np.array(xk)
            return True
        return False

    differential_evolution(lambda z: -run(car, L, z, n)[0], [(0, 1)] * npar(n), seed=seed, maxiter=maxiter,
                           popsize=popsize, tol=1e-9, polish=False, x0=warms[0], callback=cb)
    return found.get("z")


rig_rows = {r['name']: r for r in json.load(open('out_car_table.json'))}
soft_rows = json.load(open('out_soft_table.json'))
# arguments: entries "Car name:n" (default: all cars, n = 3, 4, 5)
todo = {}
for arg in sys.argv[1:]:
    nm, nn = arg.rsplit(':', 1)
    todo.setdefault(nm, []).append(int(nn))
if not todo:
    todo = {c[0]: [3, 4, 5] for c in CARS}
for name, df, dw, db, w, thd in CARS:
    if name not in todo:
        continue
    th = np.radians(thd)
    rig = FastCar(df, dw, db, w, th)
    soft = SoftCar(df, dw, db, w, th, half_track=w / 2 - 0.0275 - 0.1025, tyre_w=0.205, tyre_l=0.50)
    for n in todo[name]:
        Lr, zr = rig_rows[name][f'L{n}'], rig_rows[name][f'z{n}']
        Ls, zs = soft_rows[name][f'L{n}'], soft_rows[name].get(f'z{n}')
        zc = convert(rig, soft, Lr, zr, n)
        s, q = run(soft, Lr, zc, n)
        seed_ok = s >= 0 and soft.escapes(q, Lr + 1e-6)
        warms = [zc] + ([np.array(zs)] if zs is not None else [])
        if name == 'Typical' and os.path.exists('out_soft.json'):
            zold = json.load(open('out_soft.json')).get(f'z{n}')     # earlier run (steered front tyres)
            if zold is not None:
                warms.append(np.array(zold))
        hi = min(Lr, Ls) if seed_ok else Ls
        best, zbest = hi, (zc if (seed_ok and Lr <= Ls) else (np.array(zs) if zs is not None else None))
        lo = rig.ell
        for it in range(9):
            mid = (lo + hi) / 2
            zf = feasible(soft, mid, n, warms, seed=it)
            if zf is not None:
                hi, best, zbest = mid, mid, zf
                warms = [zf] + warms
            else:
                lo = mid
        print(f"{name} n={n}: soft {Ls:.4f} rigid {Lr:.4f} seed ok {seed_ok} -> {best:.4f}", flush=True)
        if best < Ls - 1e-9:
            soft_rows[name][f'L{n}'] = float(best)
            soft_rows[name][f'z{n}'] = [float(x) for x in zbest]
            soft_rows[name][f'polished{n}'] = True
        json.dump(soft_rows, open('out_soft_table.json', 'w'), indent=1)
print("polish done", flush=True)
