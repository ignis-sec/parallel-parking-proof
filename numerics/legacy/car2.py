"""Margin model: curb y>=0 hard; parked cars occupy open strips x<0 or x>L, m<y<H (H=m+w)."""
import numpy as np
class Car:
    def __init__(s, df, dw, db, w, theta, mfrac=0.1):
        s.df, s.dw, s.db, s.w, s.theta = df, dw, db, w, theta
        s.R = dw/np.tan(theta); s.b = dw+df; s.ell = df+dw+db
        s.Ri, s.Ro = s.R-w/2, s.R+w/2; s.rho = np.hypot(s.b, s.Ro); s.rb = np.hypot(s.db, s.Ro)
        s.m = mfrac*w; s.H = s.m + w
    def L1(s): return s.db + np.sqrt(s.b**2 + 2*s.R*s.w)
    def corners_body(s):
        return np.array([[-s.db,-s.w/2],[s.b,-s.w/2],[s.b,s.w/2],[-s.db,s.w/2]])
def to_world(pts, q):
    x,y,p = q; c,sn = np.cos(p), np.sin(p)
    return np.stack([x + c*pts[:,0] - sn*pts[:,1], y + sn*pts[:,0] + c*pts[:,1]],1)
def seg_hits_strip(a, b, X0, side, ylo, yhi):
    """closed segment ab vs open set {side*(x-X0)>0, ylo<y<yhi}"""
    t0, t1 = 0.0, 1.0
    d = b - a
    for (lo, hi, comp) in [(ylo, yhi, 1)]:
        if abs(d[comp]) < 1e-15:
            if not (lo < a[comp] < hi): return False
        else:
            ta, tb = (lo - a[comp])/d[comp], (hi - a[comp])/d[comp]
            t0, t1 = max(t0, min(ta,tb)), min(t1, max(ta,tb))
    if t1 <= t0 + 1e-15: return False
    xa, xb = a[0] + t0*d[0], a[0] + t1*d[0]
    return max(side*(xa-X0), side*(xb-X0)) > 1e-12
def collides(car, q, L):
    C = to_world(car.corners_body(), q)
    if C[:,1].min() < -1e-12: return True
    for i in range(4):
        a, b = C[i], C[(i+1)%4]
        if seg_hits_strip(a, b, 0.0, -1, car.m, car.H): return True
        if seg_hits_strip(a, b, L, +1, car.m, car.H): return True
    # strip corner points inside polygon (convex, CCW)
    for c in ([0.0, car.m], [0.0, car.H], [L, car.m], [L, car.H]):
        c = np.array(c); inside = True
        for i in range(4):
            e = C[(i+1)%4]-C[i]; r = c-C[i]
            if e[0]*r[1]-e[1]*r[0] <= 1e-12: inside = False; break
        if inside: return True
    return False
def fits(car, q, L):
    C = to_world(car.corners_body(), q)
    return (not collides(car, q, L)) and C[:,1].max() <= car.H + 1e-12
def in_lane(car, q):
    return to_world(car.corners_body(), q)[:,1].min() >= car.H - 1e-12
def step(q, d, kappa, s):
    x,y,p = q
    if abs(kappa) < 1e-14: return np.array([x + d*s*np.cos(p), y + d*s*np.sin(p), p])
    p2 = p + d*kappa*s
    return np.array([x + (np.sin(p2)-np.sin(p))/kappa, y - (np.cos(p2)-np.cos(p))/kappa, p2])
def max_free(car, q, d, kappa, L, smax=20.0, ds=3e-3):
    s = 0.0
    while s < smax:
        if collides(car, step(q, d, kappa, s+ds), L):
            lo, hi = s, s+ds
            for _ in range(40):
                mid = (lo+hi)/2
                if collides(car, step(q, d, kappa, mid), L): hi = mid
                else: lo = mid
            return lo
        s += ds
    return smax
def escapes(car, q, L, ds=4e-3):
    """forward left-lock arc; success when in lane (moving up), fail on collision"""
    s = 0.0
    while s < 2*np.pi*car.R:
        s += ds; qq = step(q, +1, 1/car.R, s)
        if collides(car, qq, L): return False
        if in_lane(car, qq) and np.sin(qq[2]) > 0: return True
    return False
