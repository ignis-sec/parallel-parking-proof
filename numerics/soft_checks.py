"""Checks of the final soft-curb motions (six cars, n = 1..5, and n = 20 for the typical car):
(1) they are free in the model of the paper (tyres aligned with the body), also when the front
    tyres are turned to the Ackermann angles of full lock, and (n >= 2) also for the largest
    tyres considered in the paper (delta_s = 0, lambda = 0.30 m), which covers delta_s in [0, 5] cm
    and lambda in [0.20, 0.30] m because the lowest tyre point is monotone in both;
(2) minimal tyre clearance and maximal overhang of the body over the curb;
(3) contacts at the end of each manoeuvre of the 20-manoeuvre motion.
Light-weight: one process, one thread."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json
import numpy as np
from fast import arc_states
from soft import SoftCar, level_out, one_manoeuvre
from soft_theory import quantities, CARS
from car_table import seq, max_free
import twenty_search

DS, TW, LAM = 0.0275, 0.205, 0.25
rows = json.load(open('out_soft_table.json'))


def cars(df, dw, db, w, th):
    nom = dict(half_track=w / 2 - DS - TW / 2, tyre_w=TW, tyre_l=2 * LAM)
    big = dict(half_track=w / 2 - TW / 2, tyre_w=TW, tyre_l=0.60)
    return (SoftCar(df, dw, db, w, th, **nom), SoftCar(df, dw, db, w, th, steer_front=True, **nom),
            SoftCar(df, dw, db, w, th, **big))


def zig_arcs(car, L, z, n):
    """The arcs of the zigzag with parameters z, exactly as car_table.run builds them."""
    R = car.R
    q = np.array([car.db + z[0] * (L - car.ell), car.H - car.w / 2, 0.0])
    q0, mans, i = q.copy(), [], 1
    for d in seq(n):
        man = []
        if d == -1:
            a, t = z[i] * 0.1, z[i + 1]; i += 2
            sm = max_free(car, q, -1, 1 / R, L, smax=a * R + 1e-9); s1 = min(sm, a * R) * 0.999999
            man.append((-1, 1 / R, s1)); q = arc_states(q, -1, 1 / R, np.array([s1]))[0]
            sm = max_free(car, q, -1, -1 / R, L, smax=10.0); s2 = t * sm * 0.999999
            man.append((-1, -1 / R, s2)); q = arc_states(q, -1, -1 / R, np.array([s2]))[0]
        else:
            t = z[i]; i += 1
            sm = max_free(car, q, +1, 1 / R, L, smax=10.0); s = t * sm * 0.999999
            man.append((+1, 1 / R, s)); q = arc_states(q, +1, 1 / R, np.array([s]))[0]
        mans.append(man)
    return q0, mans, q


def check(label, trio, L, q0, mans, big=True):
    car, steer, large = trio
    q = q0.copy()
    tyre_min, body_min, ok = 9.0, 9.0, [True, True, True]
    for man in mans:
        for d, k, s in man:
            Q = arc_states(q, d, k, np.linspace(0, s, 400))
            for j, c in enumerate(trio):
                if j < 2 or big:
                    ok[j] &= not c.collide(Q, L, k=k).any()
            P = car.tyre_points(k)
            c, sn = np.cos(Q[:, 2]), np.sin(Q[:, 2])
            Yt = Q[:, 1, None] + sn[:, None] * P[None, :, 0] + c[:, None] * P[None, :, 1]
            tyre_min = min(tyre_min, Yt.min())
            body_min = min(body_min, car.corners(Q)[1].min())
            q = Q[-1]
    print(f"{label:22s} L={L:.4f}: free {ok[0]}, steered front tyres {ok[1]}, "
          f"large tyres {ok[2] if big else '  - '}, lowest tyre point {100 * tyre_min:5.1f} cm, "
          f"lowest body point {100 * body_min:5.1f} cm", flush=True)
    return all(ok[:2]) and (ok[2] or not big)


allok = True
for name, df, dw, db, w, thd in CARS:
    th = np.radians(thd)
    trio = cars(df, dw, db, w, th)
    car = trio[0]
    R, H, m = car.R, car.H, car.m
    qd, ck = quantities(df, dw, db, w, th)
    r = rows[name]
    # n = 1: from q_t (theorem) or the numerical optimum (city car)
    if r['thm_hyp']:
        L = qd['L1s'] + 1e-6; pt = qd['psi_t']
        q0 = np.array([db * np.cos(pt) + (w / 2) * np.sin(pt), H - car.b * np.sin(pt) - (w / 2) * np.cos(pt), pt])
    else:
        L, pt, q0 = one_manoeuvre(car, np.linspace(qd['psi_t'] - 0.01, qd['psi_t'], 201))
    man = level_out(car, q0, L)
    allok &= man is not None and check(f"{name} n=1", trio, L, q0, [man], big=False)
    # n = 2: reverse with full right lock to the double contact, then exit
    L = qd['L2s'] + 1e-6; q0 = np.array([L - car.b, m + w / 2, 0.0])
    rev = [(-1, -1 / R, R * qd['alpha_s'] * (1 - 1e-7))]
    q1 = arc_states(q0, -1, -1 / R, np.array([rev[0][2]]))[0]
    man = level_out(car, q1, L)
    allok &= man is not None and check(f"{name} n=2", trio, L, q0, [rev, man])
    # n = 3..5: zigzags
    for n in (3, 4, 5):
        L = r[f'L{n}']; z = r[f'z{n}']
        q0, mans, qe = zig_arcs(car, L, z, n)
        man = level_out(car, qe, L + 1e-6)
        allok &= man is not None and check(f"{name} n={n}", trio, L + 1e-6, q0, mans + [man])

# n = 20, typical car
trio = cars(0.9, 2.6, 0.8, 1.8, np.radians(35))
car = trio[0]
H, w, m = car.H, car.w, car.m
tw = rows['twenty']; L = tw['L']
nn, mans = twenty_search.run(L, tw['xf'], tw['first'], tw['a'], car=car)
q0 = np.array([car.db + tw['xf'] * (L - car.ell), H - w / 2, 0.0])
q = q0.copy()
for man in mans:
    for d, k, s in man:
        q = arc_states(q, d, k, np.array([s]))[0]
man = level_out(car, q, L + 1e-6)
allok &= man is not None and check(f"Typical n={nn}", trio, L + 1e-6, q0, mans + [man])
print("all checks passed" if allok else "SOME CHECK FAILED", flush=True)
# contacts at the end of each exit manoeuvre of the 20-manoeuvre motion (exit time)
q = q0.copy()
names = ['RC', 'FC', 'FL', 'RL']
for j, man in enumerate(mans):
    for d, k, s in man:
        q = arc_states(q, d, k, np.array([s]))[0]
    X, Y = car.corners(q[None]); P = np.c_[X[0], Y[0]]
    tags = []
    for i, p in enumerate(P):
        if abs(p[0]) < 3e-3 and m - 3e-3 <= p[1] <= H + 3e-3: tags.append(names[i] + '@rear car')
        if abs(p[0] - L) < 3e-3 and m - 3e-3 <= p[1] <= H + 3e-3: tags.append(names[i] + '@front car')
    for cpt, lab in (((0, m), 'rear-car corner'), ((0, H), 'rear-car top corner'), ((L, m), 'front-car corner'), ((L, H), 'front-car top corner')):
        for i in range(4):
            a, b = P[i], P[(i + 1) % 4]; ab = b - a; t = np.clip(np.dot(np.array(cpt) - a, ab) / np.dot(ab, ab), 0, 1)
            if np.linalg.norm(a + t * ab - np.array(cpt)) < 3e-3: tags.append(lab)
    Yt = q[1] + np.sin(q[2]) * car.tyre_points(None)[:, 0] + np.cos(q[2]) * car.tyre_points(None)[:, 1]
    if Yt.min() < 3e-3: tags.append('tyre@curb')
    print(f"  exit manoeuvre {j + 1:2d} ({'fwd' if man[0][0] > 0 else 'rev'}): heading {np.degrees(q[2]):5.1f} deg, "
          f"contacts {sorted(set(tags))}")
