"""Figure: the best twenty-manoeuvre parking motion found for the typical car (appendix).

The exit found by twenty_search.py (contact zigzag, L = 4.8545 m) is rebuilt, checked with exact
collision tests, completed by a left/right-lock escape to a level lane configuration, and drawn
in parking time on a single page.
With the argument `soft`: the soft-curb motion (soft_table.py, L = 4.7032 m), fig_twenty_soft.pdf.
"""
import os
import json, sys
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from twenty_search import run
import figtools
SOFT = 'soft' in sys.argv[1:]
ARGS = [a for a in sys.argv[1:] if a != 'soft']
if SOFT:
    figtools.set_soft()
from figtools import car, w, H, states, escape, escape_gap, draw_scene, labels_for, draw_manoeuvre

# optional: lateral gap [m] between the starting car and the parked cars, and output file
GAP = float(ARGS[0]) if len(ARGS) > 0 else None
PDF = ARGS[1] if len(ARGS) > 1 else None

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'figures', '')
NAME = 'fig_twenty_soft' if SOFT else 'fig_twenty'
plt.rcParams.update({'font.size': 7, 'font.family': 'serif'})
P = json.load(open('out_soft_table.json'))['twenty'] if SOFT else json.load(open('out_twenty.json'))
L = P['L']
n, mans = run(L, P['xf'], P['first'], P['a'], car=car)
assert n == 20
if SOFT:
    from soft import SoftCar
    car_s = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35), half_track=0.77, tyre_w=0.205, tyre_l=0.50,
                    steer_front=True)

# ---- verify and convert to parking time --------------------------------------------------
q = np.array([car.db + P['xf'] * (L - car.ell), H - w / 2, 0.0])
exitQ, exitK = [], []
for man in mans:
    Q, K = states(q, man, steer=True)
    assert not car.collide(Q, L).any()
    if SOFT:                                          # also with steered front tyres
        assert not any(car_s.collide(Q[K == k], L, k=k).any() for k in set(K))
    exitQ.append(Q)
    exitK.append(K)
    q = Q[-1]
if GAP is None:
    psi, man = escape(q, L)
else:
    psi, man, ok = escape_gap(q, L, GAP)
    assert ok, "start with the requested gap collides"
mans.append(man)
Q, K = states(q, man, steer=True)
assert not car.collide(Q, L).any()
exitQ.append(Q)
exitK.append(K)
X, Y = car.corners(Q[-1:])
assert Y.min() >= H - 1e-9 and abs(Q[-1][2]) < 1e-9
park = [Q[::-1] for Q in exitQ[::-1]]
parkK = [K[::-1] for K in exitK[::-1]]
park_arcs = [[(-d, k, s) for (d, k, s) in m[::-1]] for m in mans[::-1]]
lengths = [sum(s for _, _, s in a) for a in park_arcs]
short = {'forward': 'fwd.', 'reverse': 'rev.'}
titles = []
for j, lab in enumerate(labels_for(park_arcs)):
    d, locks = lab.split(', ')
    locks = locks.replace(' lock', '').replace(' then ', r'$\to$')
    s = lengths[j]
    ls = f'{s:.2f} m' if s >= 1 else f'{100 * s:.1f} cm'
    titles.append(f'({j + 1}) {short[d]} {locks}, {ls}')
print('verified; L =', L)

# ---- layout: 6 rows x 4 columns on one page ------------------------------------------------
X, Y = car.corners(np.vstack(park[:1]))
big = ((min(-0.4, X.min() - 0.2), max(L + 0.4, X.max() + 0.2)), (-0.35, Y.max() + 0.2))
X, Y = car.corners(np.vstack(park[1:]))
small = ((-0.25, L + 0.25), (-0.25, Y.max() + 0.12))
hb = (big[0][1] - big[0][0]) / (big[1][1] - big[1][0])
hs = (small[0][1] - small[0][0]) / (small[1][1] - small[1][0])
fig = plt.figure(figsize=(6.3, 8.6))
gs = fig.add_gridspec(6, 4, hspace=0.34, wspace=0.06,
                      height_ratios=[2.03 * hs / hb, 1, 1, 1, 1, 1.05])
gb = gs[5, :].subgridspec(1, 3, width_ratios=[1, 1.05, 1.95], wspace=0.42)
axes = [fig.add_subplot(gs[0, 0:2]), fig.add_subplot(gs[0, 2]), fig.add_subplot(gs[0, 3])]
axes += [fig.add_subplot(gs[r, c]) for r in range(1, 5) for c in range(4)]
axes += [fig.add_subplot(gb[0])]
for j, (ax, Q, K) in enumerate(zip(axes, park, parkK)):
    draw_scene(ax, L, *(big if j == 0 else small), lw=0.6)
    draw_manoeuvre(ax, Q, K, L, ghost=4 if j == 0 else 2, ghost_wheels=(j == 0), lw=0.75,
                   arrow_scale=5, dot=2.2)
    ax.set_title(titles[j], fontsize=6.3, pad=2)
    ax.text(0.03, 0.95, rf'{np.degrees(Q[-1][2]):.1f}$^\circ$', transform=ax.transAxes,
            fontsize=5.8, va='top', ha='left', color='0.25')
axes[0].annotate('', xy=(0, -0.2), xytext=(L, -0.2), arrowprops=dict(arrowstyle='<->', lw=0.6))
axes[0].text(L / 2, -0.17, rf'$L={np.ceil(L * 1000) / 1000:.3f}$ m', ha='center', va='bottom',
             fontsize=6.5, bbox=dict(fc='w', ec='none', pad=0.5))

# heading after each manoeuvre
ax = fig.add_subplot(gb[1])
heads = [np.degrees(park[0][0][2])] + [np.degrees(Q[-1][2]) for Q in park]
ax.plot(range(21), heads, 'o-', color='b', ms=2, lw=0.7)
ax.set_xlim(-0.5, 20.5)
ax.set_ylim(-1.5, 29)
ax.set_xticks([0, 5, 10, 15, 20])
ax.set_yticks([0, 10, 20])
ax.tick_params(labelsize=5.8, length=2, pad=1)
ax.set_xlabel('manoeuvre', fontsize=6, labelpad=1)
ax.set_ylabel(r'heading [$^\circ$]', fontsize=6, labelpad=1)
ax.set_title('heading after each manoeuvre', fontsize=6.3, pad=2)

# rear-axle path after the entry, magnified
ax = fig.add_subplot(gb[2])
Pth = np.vstack(park[1:])[:, :2]
ax.plot(Pth[:, 0] * 100, Pth[:, 1] * 100, '-', color='k', lw=0.6)
ends = np.array([Q[-1][:2] for Q in park])
ax.plot(ends[1:, 0] * 100, ends[1:, 1] * 100, 'o', color='b', ms=1.8)
ax.plot(ends[0, 0] * 100, ends[0, 1] * 100, 's', color='tab:green', ms=2.5)
ax.plot(ends[-1, 0] * 100, ends[-1, 1] * 100, '*', color='tab:red', ms=4)
for j in ((15, 19, 20) if SOFT else (17, 19, 20)):
    ax.annotate(str(j), ends[j - 1] * 100, textcoords='offset points', xytext=(0, 3),
                fontsize=5.5, ha='center')
ax.set_aspect('equal')
ax.tick_params(labelsize=5.8, length=2, pad=1)
ax.set_xlabel('x [cm]', fontsize=6, labelpad=1)
ax.set_ylabel('y [cm]', fontsize=6, labelpad=1)
ax.set_title('rear-axle midpoint, manoeuvres 2–20', fontsize=6.3, pad=2)

if GAP is not None:
    # magnified inset: the starting car above the car in front
    from figtools import car_poly
    q0 = park[0][0]
    X0, Y0 = car.corners(q0[None])
    xc = min(X0[0].max() - 0.5, L + 1.6)
    zx, zy = (xc - 0.45, xc + 0.45), (H - 0.22, H + GAP + 0.22)
    ins = axes[0].inset_axes([0.70, 0.04, 0.29, 0.40])
    draw_scene(ins, L, zx, zy, lw=0.6)
    ins.set_aspect('auto')
    ins.add_patch(car_poly(q0, fc='none', ec='b', lw=0.9, ls='--'))
    ins.annotate('', xy=(xc, H), xytext=(xc, H + GAP),
                 arrowprops=dict(arrowstyle='<->', lw=0.6, shrinkA=0, shrinkB=0))
    ins.text(xc + 0.05, H + GAP / 2, f'{100 * GAP:.0f} cm', fontsize=6, va='center')
    ins.set_title('start (magnified)', fontsize=5.5, pad=1)
    axes[0].indicate_inset_zoom(ins, edgecolor='0.3', lw=0.5)
if PDF is None:
    fig.savefig(OUT + NAME + '.pdf', bbox_inches='tight')
else:
    fig.savefig(PDF, bbox_inches='tight')
    fig.savefig(PDF.replace('.pdf', '.png'), dpi=130, bbox_inches='tight')
print('saved')
from figtools import contacts
for j, Q in enumerate(park):
    X, Y = car.corners(Q)
    print(f"{j + 1:2d} {titles[j]:40s} heading {np.degrees(Q[0][2]):5.1f} -> {np.degrees(Q[-1][2]):5.1f} deg, "
          f"contacts {[tuple(np.round(p, 3)) for p in contacts(Q[-1], L)]}, lowest body point {100 * Y.min():.1f} cm")
