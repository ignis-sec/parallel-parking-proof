"""Geometry + collision checks for the parallel-parking problem (wheel-curb model W and
relaxed model M0).  Coordinates: curb y=0, slot [0,L]x[0,w], lane y>=w.
State q=(x,y,psi): rear-axle midpoint P=(x,y), heading psi."""
import numpy as np

class Car:
    def __init__(s, df, dw, db, w, theta):
        s.df, s.dw, s.db, s.w, s.theta = df, dw, db, w, theta
        s.R = dw/np.tan(theta); s.b = dw+df; s.ell = df+dw+db
        s.Ri, s.Ro = s.R - w/2, s.R + w/2
        s.rho = np.hypot(s.b, s.Ro)
    def L1(s):
        return s.db + np.sqrt(s.b**2 + 2*s.R*s.w)
    # body-frame corner list: RR, FR, FL, RL  (x forward, y left)
    def corners_body(s):
        return np.array([[-s.db,-s.w/2],[s.b,-s.w/2],[s.b,s.w/2],[-s.db,s.w/2]])
    def wheels_body(s):
        return np.array([[0,-s.w/2],[s.dw,-s.w/2],[s.dw,s.w/2],[0,s.w/2]])
    @staticmethod
    def to_world(pts, q):
        x,y,p = q; c,sn = np.cos(p), np.sin(p)
        return np.stack([x + c*pts[:,0] - sn*pts[:,1], y + sn*pts[:,0] + c*pts[:,1]],1)

def seg_hits_quadrant(a, b, X0, w, side):
    """Does closed segment ab meet the OPEN quadrant {x<X0,y<w} (side=-1) or {x>X0,y<w} (side=+1)?"""
    # parametrize; quadrant is convex & open: check if some t in [0,1] has y<w and side*(x-X0)>0
    pts = [a, b]
    # endpoints
    for p in pts:
        if p[1] < w and side*(p[0]-X0) > 0: return True
    # crossing of boundary lines: points where y=w or x=X0 interior handled by checking
    # the sub-segment where y<w
    ya, yb = a[1]-w, b[1]-w
    if ya >= 0 and yb >= 0: return False
    # clip to y<w part
    if ya < 0 and yb < 0: t0,t1 = 0.0,1.0
    else:
        tc = ya/(ya-yb)
        t0,t1 = (0.0,tc) if ya<0 else (tc,1.0)
    xa = a[0] + t0*(b[0]-a[0]); xb = a[0] + t1*(b[0]-a[0])
    # open in y at the clip endpoint, so need strict side at some interior point
    return max(side*(xa-X0), side*(xb-X0)) > 0 and (t1 > t0)

def poly_hits_quadrant(P, X0, w, side):
    n = len(P)
    for i in range(n):
        if seg_hits_quadrant(P[i], P[(i+1)%n], X0, w, side): return True
    # quadrant corner inside polygon interior?  (polygon convex)
    c = np.array([X0, w]); inside = True
    for i in range(n):
        e = P[(i+1)%n]-P[i]; r = c-P[i]
        if e[0]*r[1]-e[1]*r[0] <= 1e-15: inside = False; break
    return inside

def collides(car, q, L, model='W', tol=0.0):
    C = Car.to_world(car.corners_body(), q)
    if poly_hits_quadrant(C, 0.0+tol, car.w, -1): return True
    if poly_hits_quadrant(C, L-tol, car.w, +1): return True
    if model == 'W':
        Wh = Car.to_world(car.wheels_body(), q)
        if Wh[:,1].min() < -1e-12: return True
    return False
