"""Figure: the soft-curb two-manoeuvre exit (Proposition two-soft) for the typical car."""
import os
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Rectangle
from fast import arc_states
from soft import SoftCar, arcs_free, level_out
from soft_theory import quantities

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'figures', '')
plt.rcParams.update({'font.size': 9, 'font.family': 'serif'})
car = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35), half_track=0.9 - 0.0275 - 0.1025, tyre_w=0.205, tyre_l=0.50)
q, ck = quantities(0.9, 2.6, 0.8, 1.8, np.radians(35))
R, b, m, w, H = car.R, car.b, car.m, car.w, car.H
L = q['L2s'] + 1e-6
al = q['alpha_s']
q0 = np.array([L - b, m + w / 2, 0.0])
ok1, q1 = arcs_free(car, q0, [(-1, -1 / R, R * al * (1 - 1e-7))], L)
assert ok1 and car.fits(q0[None], L)[0] and car.escapes(q1, L + 1e-6)


def scene(ax, xl, yl):
    ax.add_patch(Rectangle((-4, m), 4, w, fc='0.85', ec='0.4', lw=0.8))
    ax.add_patch(Rectangle((L, m), 6, w, fc='0.85', ec='0.4', lw=0.8))
    ax.add_patch(Rectangle((-4, -1), L + 10, 1, fc='none', ec='0.3', hatch='////', lw=0))
    ax.plot([-4, L + 6], [0, 0], 'k', lw=1.0)
    ax.plot([-4, L + 6], [H, H], ':', color='0.5', lw=0.7)
    ax.set_aspect('equal'); ax.set_xlim(*xl); ax.set_ylim(*yl); ax.set_xticks([]); ax.set_yticks([])


def body(qq, **kw):
    X, Y = car.corners(np.array(qq)[None])
    return Polygon(np.c_[X[0], Y[0]], closed=True, **kw)


def tyres(qq, **kw):
    P = car.tyre_points(None).reshape(4, 4, 2)
    x, y, p = qq
    c, s = np.cos(p), np.sin(p)
    out = []
    for t in P:
        pts = np.array([[x + c * u - s * v, y + s * u + c * v] for u, v in t])
        order = np.argsort(np.arctan2(pts[:, 1] - pts[:, 1].mean(), pts[:, 0] - pts[:, 0].mean()))
        out.append(Polygon(pts[order], closed=True, **kw))
    return out


fig, axs = plt.subplots(1, 2, figsize=(6.8, 2.8))
Q1 = arc_states(q0, -1, -1 / R, np.linspace(0, al * R, 20))
ax = axs[0]
scene(ax, (-0.5, L + 0.5), (-0.45, H + 0.9))
for i in range(4, 20, 4):
    ax.add_patch(body(Q1[i], fc='none', ec=(0.2, 0.3, 0.9, 0.4), lw=0.7))
ax.add_patch(body(q0, fc='none', ec='b', lw=1.0, ls='--'))
ax.add_patch(body(Q1[-1], fc=(0.75, 0.85, 1.0, 0.9), ec='b', lw=1.0))
for t in tyres(Q1[-1], fc='0.2', ec='none'):
    ax.add_patch(t)
X, Y = car.corners(Q1)
ax.plot(X[:, 0], Y[:, 0], 'g-', lw=0.8)
ax.plot([0], [Y[-1, 3]], 'o', color='tab:red', ms=3)
ax.set_title('(a) reverse, full right lock', fontsize=8)
ax = axs[1]
scene(ax, (-0.5, L + 2.2), (-0.45, 4.6))
Qe = arc_states(q1, +1, 1 / R, np.linspace(0, (0.8 - al) * R, 30))
for i in range(0, 30, 5):
    ax.add_patch(body(Qe[i], fc='none', ec=(0.2, 0.3, 0.9, 0.45), lw=0.7))
ax.add_patch(body(q1, fc=(0.75, 0.85, 1.0, 0.9), ec='b', lw=1.0))
for t in tyres(q1, fc='0.2', ec='none'):
    ax.add_patch(t)
X, Y = car.corners(Qe)
ax.plot(X[:, 1], Y[:, 1], 'r-', lw=0.8)
ax.plot([L], [H], 'ro', ms=3)
ax.set_title('(b) forward, full left lock', fontsize=8)
fig.tight_layout()
fig.savefig(OUT + 'fig_two_soft.pdf')
print('ok; RC lowest during reverse arc [cm]:', round(100 * car.corners(Q1)[1][:, 0].min(), 1))
