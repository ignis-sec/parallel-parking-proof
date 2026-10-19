import numpy as np
from scipy.optimize import brentq, minimize_scalar
from car2 import Car, to_world, collides, fits, step, escapes
car = Car(df=0.9, dw=2.6, db=0.8, w=1.8, theta=np.radians(35))
db,b,w,R,Ri,Ro,rho,rb,H,m = car.db,car.b,car.w,car.R,car.Ri,car.Ro,car.rho,car.rb,car.H,car.m
V  = lambda p: db*np.cos(p) - Ri*np.sin(p) + np.sqrt(rho**2 - (Ri*np.cos(p) - b*np.sin(p))**2)
Cy = lambda p: H + Ri*np.cos(p) - b*np.sin(p)
print("eps_b", rb-Ro, " m", m, " L1(classical)", car.L1(), " V(0)", V(0))
pdip = brentq(lambda p: Cy(p)-rb, 0, 0.5)
pfit = brentq(lambda p: H - car.ell*np.sin(p) - w*np.cos(p), 1e-6, 0.5)
res = minimize_scalar(V, bounds=(0,1.0), method='bounded')
print("psi_dip", pdip, " psi_fit", pfit, " psi_crit", res.x, " Vmin_uncon", res.fun)
ps = min(pdip, res.x); print("candidate L_min(1) = V(psi*) =", V(ps), " gain vs classical", car.L1()-V(ps))
# closed form at psi_dip:
chi = np.arctan(b/Ri); pd2 = np.arccos((rb-H)/np.hypot(b,Ri)) - chi
print("closed-form psi_dip", pd2, " V", db*np.cos(pd2)-Ri*np.sin(pd2)+np.sqrt(rho**2-(rb-H)**2))
# simulation check from the corner configuration
def start(p):
    Px = db*np.cos(p) + (w/2)*np.sin(p); Py = H - b*np.sin(p) - (w/2)*np.cos(p)
    return np.array([Px, Py, p])
for dL in [-2e-3, +2e-3]:
    L = V(ps) + dL; q0 = start(ps*(1-1e-6))
    print("L=V*%+.3f fits:" % dL, fits(car, q0, L), " escapes:", escapes(car, q0, L))
