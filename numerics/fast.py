"""Vectorized margin-model collision checks + V function."""
import numpy as np
def arc_states(q, d, k, s):
    x,y,p = q; s = np.asarray(s)
    if abs(k) < 1e-14:
        return np.stack([x + d*s*np.cos(p), y + d*s*np.sin(p), p + 0*s], -1)
    p2 = p + d*k*s
    return np.stack([x + (np.sin(p2)-np.sin(p))/k, y - (np.cos(p2)-np.cos(p))/k, p2], -1)
class FastCar:
    def __init__(s, df, dw, db, w, theta, mfrac=0.1):
        s.df,s.dw,s.db,s.w=df,dw,db,w; s.R=dw/np.tan(theta); s.b=dw+df; s.ell=df+dw+db
        s.Ri,s.Ro=s.R-w/2,s.R+w/2; s.rho=np.hypot(s.b,s.Ro); s.rb=np.hypot(db,s.Ro)
        s.m=mfrac*w; s.H=s.m+w; s.gam=np.arctan2(s.Ro,s.b)
        s.cb=np.array([[-db,-w/2],[s.b,-w/2],[s.b,w/2],[-db,w/2]])
    def corners(s, Q):
        Q=np.atleast_2d(Q); c,sn=np.cos(Q[:,2]),np.sin(Q[:,2])
        X=Q[:,0,None]+c[:,None]*s.cb[None,:,0]-sn[:,None]*s.cb[None,:,1]
        Y=Q[:,1,None]+sn[:,None]*s.cb[None,:,0]+c[:,None]*s.cb[None,:,1]
        return X,Y
    def collide(s, Q, L, eps=1e-12, k=None):   # k: steering (unused for the rigid-curb car)
        X,Y=s.corners(Q); return (Y.min(1) < -eps) | s.strips(Q, L, eps)
    def strips(s, Q, L, eps=1e-12):
        """Footprint meets one of the parked cars (open strips x<0 or x>L, m<y<H)."""
        X,Y=s.corners(Q); bad=np.zeros(len(X),bool)
        m,H=s.m,s.H
        for i in range(4):
            j=(i+1)%4; xa,ya,xb,yb=X[:,i],Y[:,i],X[:,j],Y[:,j]
            dy=yb-ya; dyz=np.abs(dy)<1e-15
            with np.errstate(divide='ignore', invalid='ignore'):
                ta=np.where(dyz, -np.inf, (m-ya)/dy); tb=np.where(dyz, np.inf, (H-ya)/dy)
            lo=np.where(dyz, np.where((ya>m)&(ya<H),0.0,2.0), np.maximum(0,np.minimum(ta,tb)))
            hi=np.where(dyz, np.where((ya>m)&(ya<H),1.0,-1.0), np.minimum(1,np.maximum(ta,tb)))
            ok=hi>lo+1e-15
            x0=xa+lo*(xb-xa); x1=xa+hi*(xb-xa)
            bad |= ok & ((np.minimum(x0,x1) < -eps) | (np.maximum(x0,x1) > L+eps))
        return bad
    def fits(s, Q, L, k=None):
        X,Y=s.corners(Q); return (~s.collide(Q,L,k=k)) & (Y.max(1) <= s.H+1e-12)
    def V(s, Q):
        Q=np.atleast_2d(Q); Cx=Q[:,0]-s.R*np.sin(Q[:,2]); Cy=Q[:,1]+s.R*np.cos(Q[:,2])
        return Cx+np.sqrt(np.maximum(s.rho**2-(Cy-s.H)**2,0)), Cx, Cy
    def max_free(s, q, d, k, L, smax=12.0, ds=2e-3):
        S=np.arange(ds, smax+ds, ds); bad=s.collide(arc_states(q,d,k,S),L,k=k)
        if not bad.any(): return smax
        i=np.argmax(bad); lo=S[i-1] if i>0 else 0.0; hi=S[i]
        for _ in range(30):
            mid=(lo+hi)/2
            if s.collide(arc_states(q,d,k,np.array([mid])),L,k=k)[0]: hi=mid
            else: lo=mid
        return lo
    def escapes(s, q, L, ds=3e-3):
        S=np.arange(ds, 2*np.pi*s.R, ds); Q=arc_states(q,+1,1/s.R,S)
        bad=s.collide(Q,L,k=1/s.R); X,Y=s.corners(Q); good=(Y.min(1)>=s.H)&(np.sin(Q[:,2])>0)
        ib=np.argmax(bad) if bad.any() else len(S); ig=np.argmax(good) if good.any() else len(S)+1
        return ig < ib
