"""Shared drawing and path tools for the multi-manoeuvre figures (fig_five.py, fig_twenty.py)."""
import numpy as np
from matplotlib.patches import Polygon, Rectangle
from fast import FastCar, arc_states

car = FastCar(0.9, 2.6, 0.8, 1.8, np.radians(35))
R, w, m, H = car.R, car.w, car.m, car.H
TW, WL, WW = car.w / 2 - 0.17, 0.62, 0.20     # half track, wheel length and width [m]
SOFT = False


def set_soft():
    """Switch to the soft-curb model (only the tyres must avoid the curb). The wheels are then
    drawn with the model's tyre data: half track 0.77 m, plan-view length 0.50 m, width 0.205 m.
    Call before importing names such as `car` from this module."""
    global car, TW, WL, WW, SOFT
    from soft import SoftCar
    car = SoftCar(0.9, 2.6, 0.8, 1.8, np.radians(35), half_track=0.77, tyre_w=0.205, tyre_l=0.50)
    TW, WL, WW, SOFT = 0.77, 0.50, 0.205, True


def states(q, man, ns=400, steer=False):
    """Dense states along a manoeuvre given as a list of arcs (d, k, s)."""
    out, ks = [q[None]], [man[0][1]]
    for d, k, s in man:
        S = np.linspace(0, s, ns)
        Q = arc_states(out[-1][-1], d, k, S)
        out.append(Q[1:])
        ks += [k] * (ns - 1)
    return (np.vstack(out), np.array(ks)) if steer else np.vstack(out)


def escape(q4, L, psi_max=1.4):
    """Final exit: full left lock up to the smallest heading psi* such that full right lock
    then brings the car level and entirely into the lane, without collisions."""
    for psi in np.arange(q4[2] + 0.01, psi_max, 0.005):
        man = [(+1, 1 / R, (psi - q4[2]) * R), (+1, -1 / R, psi * R)]
        Q = states(q4, man)
        X, Y = car.corners(Q[-1:])
        if (not car.collide(Q, L).any()) and Y.min() >= H - 1e-9:
            return psi, man
    raise RuntimeError("no escape found")


def escape_gap(q1, L, gap):
    """Final exit ending level with its curb-side edge exactly `gap` above the parked cars:
    full left lock up to psi*, then full right lock to heading 0 (psi* solved exactly).
    Returns (psi*, manoeuvre, collision_free)."""
    c = (q1[1] + R * (np.cos(q1[2]) + 1) - (H + gap + w / 2)) / (2 * R)
    if not -1 <= c <= np.cos(q1[2]):
        return None, None, False
    psi = np.arccos(c)
    man = [(+1, 1 / R, (psi - q1[2]) * R), (+1, -1 / R, psi * R)]
    Q = states(q1, man)
    X, Y = car.corners(Q[-1:])
    assert abs(Y.min() - (H + gap)) < 1e-9 and abs(Q[-1][2]) < 1e-12
    return psi, man, not car.collide(Q, L).any()


def draw_scene(ax, L, xl, yl, lw=0.8):
    ax.add_patch(Rectangle((-6, m), 6, w, fc='0.85', ec='0.4', lw=lw))
    ax.add_patch(Rectangle((L, m), 8, w, fc='0.85', ec='0.4', lw=lw))
    ax.add_patch(Rectangle((-6, -1), L + 14, 1, fc='none', ec='0.3', hatch='////', lw=0))
    ax.plot([-6, L + 8], [0, 0], 'k', lw=1.25 * lw)
    ax.plot([-6, L + 8], [H, H], ':', color='0.5', lw=0.9 * lw)
    ax.set_aspect('equal')
    ax.set_xlim(*xl)
    ax.set_ylim(*yl)
    ax.set_xticks([])
    ax.set_yticks([])


def car_poly(q, **kw):
    X, Y = car.corners(np.array(q)[None])
    return Polygon(np.c_[X[0], Y[0]], closed=True, **kw)


def wheels(q, k, **kw):
    """The four wheels; front wheels at the Ackermann angles of full lock k = +-1/R."""
    x, y, p = q
    e, nrm = np.array([np.cos(p), np.sin(p)]), np.array([-np.sin(p), np.cos(p)])
    polys = []
    for u in (0.0, car.dw):
        for v in (-TW, TW):
            if u == 0.0:
                a = 0.0
            elif k > 0:
                a = np.arctan2(car.dw, R - v)
            else:
                a = -np.arctan2(car.dw, R + v)
            c = np.array([x, y]) + u * e + v * nrm
            ea = np.cos(a) * e + np.sin(a) * nrm
            na = -np.sin(a) * e + np.cos(a) * nrm
            pts = [c + sx * WL / 2 * ea + sy * WW / 2 * na
                   for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1))]
            polys.append(Polygon(pts, closed=True, **kw))
    return polys


def rear_wheel_paths(Q):
    nrm = np.c_[-np.sin(Q[:, 2]), np.cos(Q[:, 2])]
    return Q[:, :2] - TW * nrm, Q[:, :2] + TW * nrm


def seg_point_dist(p, a, b):
    ab = b - a
    t = np.clip(np.dot(p - a, ab) / np.dot(ab, ab), 0, 1)
    c = a + t * ab
    return np.linalg.norm(p - c), c


def contacts(q, L, tol=3e-3):
    """Distinct contact points of configuration q with the curb and the parked cars."""
    X, Y = car.corners(q[None])
    P = np.c_[X[0], Y[0]]
    pts = []
    if SOFT:                       # curb contacts are tyre corners
        T = car.tyre_points(None)
        c, sn = np.cos(q[2]), np.sin(q[2])
        for u, v in T:
            p = np.array([q[0] + c * u - sn * v, q[1] + sn * u + c * v])
            if abs(p[1]) < tol:
                pts.append(p)
    for p in P:
        if abs(p[1]) < tol and not SOFT:
            pts.append(p)
        if m - tol <= p[1] <= H + tol and (abs(p[0]) < tol or abs(p[0] - L) < tol):
            pts.append(p)
    for c in ([0, m], [0, H], [L, m], [L, H]):
        c = np.array(c, float)
        for j in range(4):
            if seg_point_dist(c, P[j], P[(j + 1) % 4])[0] < tol:
                pts.append(c)
    out = []
    for p in pts:
        if all(np.linalg.norm(p - r) > 1e-2 for r in out):
            out.append(p)
    return out


def labels_for(arcs_park):
    """Driving description of parking manoeuvres given as lists of arcs in parking time."""
    steer = {1 / R: 'left', -1 / R: 'right'}
    out = []
    for man in arcs_park:
        d = man[0][0]
        locks = [steer[k] for (_, k, _) in man]
        out.append(('forward' if d > 0 else 'reverse') + ', ' + ' then '.join(locks) + ' lock')
    return out


def draw_manoeuvre(ax, Q, K, L, ghost=4, ghost_wheels=False, lw=1.0, arrow_scale=7, dot=3.2):
    """One panel: start (dashed), ghosts, end (filled), wheels, rear-wheel paths, contacts."""
    n = len(Q)
    sc = np.r_[0, np.cumsum(np.linalg.norm(np.diff(Q[:, :2], axis=0), axis=1))]
    for t in np.linspace(0, sc[-1], ghost + 2)[1:-1]:
        f = int(np.argmin(np.abs(sc - t)))
        ax.add_patch(car_poly(Q[f], fc='none', ec=(0.2, 0.3, 0.9, 0.35), lw=0.6 * lw))
        if ghost_wheels:
            for wp in wheels(Q[f], K[f], fc=(0.25, 0.25, 0.25, 0.35), ec='none'):
                ax.add_patch(wp)
    ax.add_patch(car_poly(Q[0], fc='none', ec='b', lw=0.9 * lw, ls='--'))
    for wp in wheels(Q[0], K[0], fc='none', ec='0.3', lw=0.5 * lw, ls='--'):
        ax.add_patch(wp)
    ax.add_patch(car_poly(Q[-1], fc=(0.75, 0.85, 1.0, 0.9), ec='b', lw=lw))
    for wp in wheels(Q[-1], K[-1], fc='0.2', ec='none'):
        ax.add_patch(wp)
    paths = rear_wheel_paths(Q)
    for path in paths:
        ax.plot(path[:, 0], path[:, 1], '-', color='k', lw=0.6 * lw)
    k = max(2, n // 12)
    ax.annotate('', xy=paths[1][-1], xytext=paths[1][-k],
                arrowprops=dict(arrowstyle='-|>', color='k', lw=0.8 * lw, mutation_scale=arrow_scale))
    for p in contacts(Q[-1], L):
        ax.plot(p[0], p[1], 'o', color='tab:red', ms=dot, zorder=5)
