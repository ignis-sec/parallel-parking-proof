import numpy as np, sys
from scipy.optimize import minimize
from fast import FastCar, arc_states
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R
def start(L, p, dx, dy):
    top = car.H - max(car.b*np.sin(p), -car.db*np.sin(p)) - (car.w/2)*np.cos(p)
    y = top - dy
    # minimal x with fit by bisection
    lo, hi = -1.0, 3.0
    for _ in range(40):
        mid=(lo+hi)/2
        if car.fits(np.array([[mid,y,p]]),L)[0] or mid > 0.5*(lo+hi)+9: hi=mid
        else: lo=mid
    return np.array([hi+dx, y, p])
def run(L, params, pattern):
    p, dx, dy = params[:3]; ts = params[3:]
    q = start(L, p, abs(dx), abs(dy))
    if not car.fits(q[None],L)[0]: return -9, q
    for (d,k), t in zip(pattern, ts):
        t = min(max(t,0),1)
        smax = car.max_free(q, d, k, L)
        q = arc_states(q, d, k, np.array([t*smax*0.999999]))[0]
    V,_,_ = car.V(q[None]); return L - V[0], q
if __name__=="__main__":
    pats={2:[(-1,-1/R)],3:[(+1,1/R),(-1,-1/R)],4:[(-1,-1/R),(+1,1/R),(-1,-1/R)]}
    n=int(sys.argv[1]); pat=pats[n]; rng=np.random.default_rng(0)
    def best_slack(L):
        best=-9; bq=None
        for trial in range(30):
            x0=np.concatenate([[rng.uniform(0,0.04), rng.uniform(0,0.3), rng.uniform(0,0.15)], rng.uniform(0.2,1,len(pat))])
            r=minimize(lambda z:-run(L,z,pat)[0], x0, method='Nelder-Mead', options={'maxiter':300,'xatol':1e-5,'fatol':1e-6})
            if -r.fun>best: best=-r.fun; bz=r.x
        return best, bz
    lo,hi=car.ell,5.9
    for _ in range(14):
        mid=(lo+hi)/2; sl,z=best_slack(mid)
        if sl>=0: hi=mid; zb=z
        else: lo=mid
    sl,q=run(hi,zb,pat)
    print(n,"L~",hi,"params",np.round(zb,4),"final q",np.round(q,4),"esc",car.escapes(q,hi+1e-4),flush=True)
