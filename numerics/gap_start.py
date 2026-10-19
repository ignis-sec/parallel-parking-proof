"""Does a 10 cm lateral gap at the start (car level in the lane, its curb-side edge 10 cm
outside the parked cars) change the minimal slot lengths of the 1-, 5- and 20-manoeuvre motions?"""
import json, sys
import numpy as np
from fast import arc_states
from car_table import max_free
from assumptions import check
from twenty_search import run
from figtools import car, R, w, H, states, escape, escape_gap

GAP = float(sys.argv[1]) if len(sys.argv) > 1 else 0.10
cases = {}

# one manoeuvre: start of the exit is the parked configuration q_d, L = Lambda_1
_, info = check(0.9, 2.6, 0.8, 1.8, np.radians(35))
pd = info['pd']
qd = np.array([car.db * np.cos(pd) + (w / 2) * np.sin(pd), H - car.b * np.sin(pd) - (w / 2) * np.cos(pd), pd])
cases[1] = (info['Lam1'] + 1e-6, qd)

# five manoeuvres (car_table.py parameters)
row = [r for r in json.load(open('out_car_table.json')) if r['name'] == 'Typical'][0]
L5, z = row['L5'] + 1e-6, row['z5']
q = np.array([car.db + z[0] * (L5 - car.ell), H - w / 2, 0.0])
i = 1
for d in [+1, -1, +1, -1]:
    if d == -1:
        a, t = z[i] * 0.1, z[i + 1]
        i += 2
        if a > 0:
            sm = max_free(car, q, -1, 1 / R, L5, smax=a * R + 1e-9)
            q = arc_states(q, -1, 1 / R, np.array([min(sm, a * R) * 0.999999]))[0]
        sm = max_free(car, q, -1, -1 / R, L5, smax=10.0)
        q = arc_states(q, -1, -1 / R, np.array([t * sm * 0.999999]))[0]
    else:
        t = z[i]
        i += 1
        sm = max_free(car, q, +1, 1 / R, L5, smax=10.0)
        q = arc_states(q, +1, 1 / R, np.array([t * sm * 0.999999]))[0]
cases[5] = (L5, q)

# twenty manoeuvres (twenty_search.py result)
P = json.load(open('out_twenty.json'))
L20 = P['L']
n, mans = run(L20, P['xf'], P['first'], P['a'])
q = np.array([car.db + P['xf'] * (L20 - car.ell), H - w / 2, 0.0])
for man in mans:
    q = states(q, man)[-1]
cases[20] = (L20, q)

for n, (L, q1) in cases.items():
    psi0, man0 = escape(q1, L)
    Q0 = states(q1, man0)
    gap0 = car.corners(Q0[-1:])[1].min() - H
    psi, man, ok = escape_gap(q1, L, GAP)
    Q = states(q1, man)
    print(f"n={n:2d}  L={L:.4f}  old start gap {100 * gap0:5.1f} cm (psi*={np.degrees(psi0):.1f} deg)"
          f"  ->  {100 * GAP:.0f} cm gap: psi*={np.degrees(psi):.1f} deg, collision free: {ok},"
          f" start x={Q[-1][0]:.2f}")
