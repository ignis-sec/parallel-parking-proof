"""Figure: the best five-manoeuvre parking motion found for the typical car (appendix).

The exit is rebuilt from the parameters found by car_table.py (L = 5.050 m), checked with exact
collision tests, completed by a final left/right-lock escape to a level lane configuration,
and drawn in parking (forward) time: panel j shows parking manoeuvre j.
With the argument `soft`: the soft-curb motion of soft_table.py (L = 4.923 m), fig_five_soft.pdf.
"""
import os
import json, sys
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from fast import arc_states
from car_table import max_free
import figtools
SOFT = 'soft' in sys.argv[1:]
if SOFT:
    figtools.set_soft()
from figtools import (car, R, w, H, states, escape, draw_scene, labels_for, draw_manoeuvre,
                      contacts)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'figures', '')
NAME = 'fig_five_soft' if SOFT else 'fig_five'
plt.rcParams.update({'font.size': 9, 'font.family': 'serif'})
if SOFT:
    row = json.load(open('out_soft_table.json'))['Typical']
else:
    row = [r for r in json.load(open('out_car_table.json')) if r['name'] == 'Typical'][0]
L0, z = row['L5'], row['z5']
L = L0 + 1e-6

# ---- rebuild the exit (same steps as car_table.run) -------------------------------------
arcs = []          # exit manoeuvres, each a list of arcs (d, k, s)


def go(q, d, k, s, man):
    man.append((d, k, s))
    return arc_states(q, d, k, np.array([s]))[0]


q = np.array([car.db + z[0] * (L - car.ell), H - w / 2, 0.0])
qstart = q.copy()
assert car.fits(q[None], L)[0]
i = 1
for d in [+1, -1, +1, -1]:
    man = []
    if d == -1:
        a, t = z[i] * 0.1, z[i + 1]
        i += 2
        if a > 0:
            sm = max_free(car, q, -1, 1 / R, L, smax=a * R + 1e-9)
            q = go(q, -1, 1 / R, min(sm, a * R) * 0.999999, man)
        sm = max_free(car, q, -1, -1 / R, L, smax=10.0)
        q = go(q, -1, -1 / R, t * sm * 0.999999, man)
    else:
        t = z[i]
        i += 1
        sm = max_free(car, q, +1, 1 / R, L, smax=10.0)
        q = go(q, +1, 1 / R, t * sm * 0.999999, man)
    arcs.append(man)
V, _, _ = car.V(q[None])
print('L - V after four manoeuvres:', L - V[0])
if SOFT:
    from soft import SoftCar
    car_s = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35), half_track=0.77, tyre_w=0.205, tyre_l=0.50,
                    steer_front=True)
psi, man = escape(q, L)
arcs.append(man)
print('escape psi* =', round(psi, 3))

# ---- verify and convert to parking time --------------------------------------------------
exitQ, exitK = [], []
q = qstart
for man in arcs:
    Q, K = states(q, man, steer=True)
    assert not car.collide(Q, L).any()
    if SOFT:                                          # also with steered front tyres
        assert not any(car_s.collide(Q[K == k], L, k=k).any() for k in set(K))
    exitQ.append(Q)
    exitK.append(K)
    q = Q[-1]
X, Y = car.corners(exitQ[-1][-1:])
assert Y.min() >= H - 1e-9 and abs(exitQ[-1][-1][2]) < 1e-9
print('exit verified; final config', np.round(exitQ[-1][-1], 3))
park = [Q[::-1] for Q in exitQ[::-1]]
parkK = [K[::-1] for K in exitK[::-1]]
park_arcs = [[(-d, k, s) for (d, k, s) in man[::-1]] for man in arcs[::-1]]
labels = labels_for(park_arcs)


def bounds(Qs):
    X, Y = car.corners(np.vstack(Qs))
    return X.min(), X.max(), Y.max()


x1a, x1b, y1 = bounds(park[:1])
x2a, x2b, y2 = bounds(park[1:])
big = ((min(-0.4, x1a - 0.2), max(L + 0.4, x1b + 0.2)), (-0.35, y1 + 0.25))
small = ((min(-0.3, x2a - 0.1), max(L + 0.3, x2b + 0.1)), (-0.3, y2 + 0.15))
hb = (big[0][1] - big[0][0]) / (big[1][1] - big[1][0])
hs = (small[0][1] - small[0][0]) / (small[1][1] - small[1][0])
fig = plt.figure(figsize=(6.6, 6.6 / hb + 2 * 3.3 / hs + 0.9))
gs = fig.add_gridspec(3, 2, height_ratios=[2 / hb, 1 / hs, 1 / hs], hspace=0.22, wspace=0.05)
axes = [fig.add_subplot(gs[0, :])] + [fig.add_subplot(gs[r, c]) for r in (1, 2) for c in (0, 1)]
for j, (ax, Q, K) in enumerate(zip(axes, park, parkK)):
    xl, yl = big if j == 0 else small
    draw_scene(ax, L, xl, yl)
    draw_manoeuvre(ax, Q, K, L, ghost=4, ghost_wheels=(j == 0))
    ax.set_title(f'({j + 1}) {labels[j]}', fontsize=8)
axes[0].annotate('', xy=(0, -0.2), xytext=(L, -0.2), arrowprops=dict(arrowstyle='<->', lw=0.7))
axes[0].text(L / 2, -0.17, rf'$L={np.ceil(L0 * 1000 - 1e-9) / 1000:.3f}$ m', ha='center', va='bottom', fontsize=8,
             bbox=dict(fc='w', ec='none', pad=0.6))
fig.savefig(OUT + NAME + '.pdf', bbox_inches='tight')
for j, Q in enumerate(park):
    X, Y = car.corners(Q)
    print(j + 1, labels[j], 'heading', round(Q[0][2], 4), '->', round(Q[-1][2], 4),
          'length', round(sum(s for _, _, s in park_arcs[j]), 3),
          'arcs', [round(s, 3) for _, _, s in park_arcs[j]],
          'contacts', [tuple(np.round(p, 3)) for p in contacts(Q[-1], L)],
          'lowest body point', round(Y.min(), 3))
