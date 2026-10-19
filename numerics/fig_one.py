"""Figure 2 of the paper (optimal one-manoeuvre exit), regenerated with axes that show the
final lane position. Same construction as in figures.py."""
import os
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Rectangle
from fast import FastCar, arc_states
from assumptions import check
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'figures', '')
car = FastCar(0.9, 2.6, 0.8, 1.8, np.radians(35)); R = car.R; w = car.w; m = car.m; H = car.H
o, info = check(0.9, 2.6, 0.8, 1.8, np.radians(35)); pd = info['pd']; L1 = info['Lam1']
plt.rcParams.update({'font.size': 9, 'font.family': 'serif'})


def draw_scene(ax, L, xl, yl):
    ax.add_patch(Rectangle((-4, m), 4, w, fc='0.85', ec='0.4', lw=0.8))
    ax.add_patch(Rectangle((L, m), 8, w, fc='0.85', ec='0.4', lw=0.8))
    ax.add_patch(Rectangle((-4, -1), L + 12, 1, fc='none', ec='0.3', hatch='////', lw=0))
    ax.plot([-4, L + 8], [0, 0], 'k', lw=1.0)
    ax.plot([-4, L + 8], [H, H], ':', color='0.5', lw=0.7)
    ax.set_aspect('equal'); ax.set_xlim(*xl); ax.set_ylim(*yl); ax.set_xticks([]); ax.set_yticks([])


def car_poly(q, **kw):
    X, Y = car.corners(np.array(q)[None]); return Polygon(np.c_[X[0], Y[0]], closed=True, **kw)


L = L1 + 1e-6
q0 = np.array([car.db * np.cos(pd) + (w / 2) * np.sin(pd), H - car.b * np.sin(pd) - (w / 2) * np.cos(pd), pd])
alpha = 0.76
Q1 = arc_states(q0, +1, 1 / R, np.linspace(0, (alpha - pd) * R, 40))
Q2 = arc_states(Q1[-1], +1, -1 / R, np.linspace(0, alpha * R, 40))
Q = np.vstack([Q1, Q2[1:]])
assert not car.collide(Q, L).any()
X, Y = car.corners(Q)
fig, ax = plt.subplots(figsize=(6.4, 3.3))
draw_scene(ax, L, (-0.8, X.max() + 0.4), (-0.5, Y.max() + 0.3))
for i in range(0, len(Q), 8):
    ax.add_patch(car_poly(Q[i], fc='none', ec=(0.2, 0.3, 0.9, 0.35 + 0.65 * i / len(Q)), lw=0.8))
ax.add_patch(car_poly(Q[-1], fc='none', ec='b', lw=1.0, ls='--'))
ax.add_patch(car_poly(q0, fc=(0.75, 0.85, 1.0), ec='b', lw=1.0))
ax.plot(X[:, 1], Y[:, 1], 'r-', lw=0.8, label=r'$\mathsf{FC}$ trace')
ax.plot(X[:, 0], Y[:, 0], 'g-', lw=0.8, label=r'$\mathsf{RC}$ trace')
ax.plot(Q[:, 0], Q[:, 1], 'k-', lw=0.6, label='rear axle')
ax.plot([L], [H], 'ro', ms=3)
ax.legend(loc='upper left', fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig(OUT + 'fig_one.pdf')
print('final config', np.round(Q[-1], 3), 'lowest final', round(car.corners(Q[-1:])[1].min(), 3))
