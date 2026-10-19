"""Exact check of Assumption 4.1 (A1)-(A7) as stated in the paper (margin model)."""
import numpy as np, itertools
from scipy.optimize import brentq
def derived(df,dw,db,w,th,mfrac=0.1):
    R=dw/np.tan(th); b=dw+df; ell=b+db; Rm,Rp=R-w/2,R+w/2
    rho=np.hypot(b,Rp); r=np.hypot(db,Rp); m=mfrac*w; H=m+w
    return R,b,ell,Rm,Rp,rho,r,m,H
def check(df,dw,db,w,th,mfrac=0.1):
    R,b,ell,Rm,Rp,rho,r,m,H=derived(df,dw,db,w,th,mfrac)
    out={}; X=lambda p: db*np.cos(p)-Rm*np.sin(p); Y=lambda p: Rm*np.cos(p)-b*np.sin(p)
    eps_b=r-Rp
    out['A1']= db<b and Rp**2>b*db and m>=eps_b
    if not (H<ell): out['A2']=False; return out,None
    pfit=brentq(lambda p: ell*np.sin(p)+w*np.cos(p)-H, 1e-12, np.arctan(ell/w))
    psb=np.arcsin(H/ell); beta=np.arctan2(db,Rp); gam=np.arctan2(Rp,b); c2=2*b/np.sin(psb)
    out['A2']= (H<min(ell,b)) and (H<Rm+db) and (np.cos(psb)>m/w) and (pfit<beta) and (Rp*np.cos(pfit)>max(H,Rm)) and (Rm>=db*np.tan(pfit/2))
    out['A3']= (2*R*b>w*rho) and (w*b>m*rho) and (b*rho>H*Rp)
    out['A4']= (Rp**2-b*db)/r >= r-H
    if not out['A1']: return out,None
    pd=brentq(lambda p: Y(p)-(r-H), -1e-12, np.pi/2-1e-9) if Y(0)>r-H else 0.0
    out['A5']= (np.cos(pd)*np.sqrt(b*b+2*R*w) > Rm*np.sin(pd)+b) and \
       (b*np.cos(pfit)*(2*Y(pfit)+c2) > 2*(Rm+db*np.sin(pfit))*np.sqrt(rho**2+c2*(r-H-Y(pfit))))
    out['A6']= (r-db>=H) and (X(pd)>=0)
    Lam1=X(pd)+np.sqrt(rho**2-(r-H)**2)
    psn=np.arcsin(min(H/b,1)); cpsi=np.cos(psn)
    try: psu=brentq(lambda p: Rm*(1-np.cos(p))+db*np.sin(p)-H, 1e-9, np.pi/2)
    except ValueError: psu=np.pi/2
    h0=H-w*np.cos(pfit)
    fb=lambda p: db*np.cos(p)-(w/2)*np.sin(p); pmin=min(fb(-psn),fb(psu))
    Bback=b*np.cos(pfit)-(w/2)*np.sin(pfit)+pmin+cpsi*(R*b/Rp)*np.log(H*b/(ell*h0)) if H*b>ell*h0 else -np.inf
    out["A7"]= (db*np.cos(pfit)-Rp*np.sin(pfit)+rho>=Lam1) and (Bback>=Lam1) and (H*b>ell*h0)
    return out, dict(Lam1=Lam1,L1=db+np.sqrt(b*b+2*R*w),pd=pd,pfit=pfit,psb=psb,beta=beta,gam=gam,Bback=Bback,eps_b=eps_b,m=m)
if __name__=="__main__":
    o,i=check(0.9,2.6,0.8,1.8,np.radians(35)); print(o); print({k:round(v,5) for k,v in i.items()})
    n=0; ok=0; fails={}
    for df,dw,db,w,thd in itertools.product([0.6,0.8,1.0,1.2],[2.3,2.6,2.9,3.2],[0.5,0.7,0.9,1.1,1.3],[1.6,1.75,1.9,2.05],[28,33,38,43]):
        n+=1; o,_=check(df,dw,db,w,np.radians(thd))
        if all(o.values()): ok+=1
        for k,v in o.items():
            if not v: fails[k]=fails.get(k,0)+1
    print("grid",n,"ok",ok,"fails",fails)
    # restrict to m>=eps_b
    n2=0; ok2=0
    for df,dw,db,w,thd in itertools.product([0.6,0.8,1.0,1.2],[2.3,2.6,2.9,3.2],[0.5,0.7,0.9,1.1,1.3],[1.6,1.75,1.9,2.05],[28,33,38,43]):
        o,_=check(df,dw,db,w,np.radians(thd))
        if o.get('A1'):
            n2+=1; ok2+= all(o.values())
    print("among cars with A1 (m>=eps_b):",n2,"all ok:",ok2)
