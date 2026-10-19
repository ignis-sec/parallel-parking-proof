"""Check the hypotheses of the n=1 theorem (margin model) over a grid of realistic cars."""
import numpy as np, itertools
from scipy.optimize import brentq
def quantities(df,dw,db,w,th,mfrac=0.1):
    R=dw/np.tan(th); b=dw+df; ell=df+dw+db; Ri,Ro=R-w/2,R+w/2; rho=np.hypot(b,Ro); rb=np.hypot(db,Ro)
    m=mfrac*w; H=m+w; q=rb-H
    return dict(R=R,b=b,ell=ell,Ri=Ri,Ro=Ro,rho=rho,rb=rb,m=m,H=H,q=q,db=db,w=w)
def check(df,dw,db,w,th,mfrac=0.1,verbose=False):
    Q=quantities(df,dw,db,w,th,mfrac); R,b,ell,Ri,Ro,rho,rb,m,H,q=[Q[k] for k in 'R b ell Ri Ro rho rb m H q'.split()]
    res={}
    res['H1 db<b']= db<b
    res['H2 Ri>0']= Ri>0
    res['H3 m>=eps_b']= m >= rb-Ro
    res['H4 H<ell']= H<ell
    res['H5 b>=H+w/2']= b>=H+w/2
    if not all(res.values()): return res, None
    psb=np.arcsin(H/ell)
    ac=brentq(lambda a: b*np.sin(a)+(w/2)*np.cos(a)-(H+w/2), 0, np.arctan2(2*b,w))
    pfit=brentq(lambda p: H-ell*np.sin(p)-w*np.cos(p), 1e-9, np.pi/2-0.01) if H<ell*np.sin(0.3)+w*np.cos(0.3) or True else None
    Y=lambda p: Ri*np.cos(p)-b*np.sin(p); X=lambda p: db*np.cos(p)-Ri*np.sin(p)
    pd=brentq(lambda p: Y(p)-q, -1e-12, pfit+1e-9) if Y(0)>=q else np.nan
    gam=np.arctan2(Ro,b); beta=np.arcsin(db/rb)
    c2=2*b/np.sin(psb)
    res['H6 R_o cos pfit>=H']= Ro*np.cos(pfit)>=H
    res['H7 b>H sin ac & b>m']= b>H*np.sin(ac) and b>m
    res['H8 H+rho sin(gam-beta)>=rb']= H+rho*np.sin(gam-beta)>=rb
    res['H8b psi_fit<min(ac,psb)']= pfit<min(ac,psb)
    res['H8c cos pfit>m/w']= np.cos(pfit)>m/w
    phi=lambda p: X(p)+np.sqrt(rho**2-Y(p)**2+c2*max(0.0,q-Y(p)))
    P=np.linspace(0,pfit,4001); vals=np.array([phi(p) for p in P])
    res['H9 argmin phi at pd']= abs(P[np.argmin(vals)]-pd) < 2*pfit/4000
    Lam1=X(pd)+np.sqrt(rho**2-q**2)
    res['H10 backward>=Lam1']= np.sqrt(db**2+2*R*w)+b*np.cos(pfit)-Ri*np.sin(pfit) >= Lam1
    res['H11 rb-db>=H']= rb-db>=H
    res['H12 Y(pfit)>=0']= Y(pfit)>=0
    return res, dict(Lam1=Lam1, L1=db+np.sqrt(b**2+2*R*w), pd=pd, pfit=pfit, psb=psb, ac=ac, beta=beta, ell=ell)
if __name__=="__main__":
    r,info=check(0.9,2.6,0.8,1.8,np.radians(35)); print(r); print(info)
    bad={}; n=0; nok=0
    for df,dw,db,w,thd in itertools.product([0.6,0.8,1.0,1.2],[2.3,2.6,2.9,3.2],[0.5,0.7,0.9,1.1,1.3],[1.6,1.75,1.9,2.05],[28,33,38,43]):
        n+=1; r,info=check(df,dw,db,w,np.radians(thd))
        if all(r.values()): nok+=1
        else:
            for k,v in r.items():
                if not v: bad[k]=bad.get(k,0)+1
    print("cars",n,"all hyps ok",nok); print("failures",bad)
