import os
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Rectangle, Circle
from fast import FastCar, arc_states
from assumptions import check
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'figures', '')
car=FastCar(0.9,2.6,0.8,1.8,np.radians(35)); R=car.R; w=car.w; m=car.m; H=car.H
o,info=check(0.9,2.6,0.8,1.8,np.radians(35)); pd=info['pd']; L1=info['Lam1']
plt.rcParams.update({'font.size':9,'font.family':'serif'})
def draw_scene(ax,L,xl=(-1.2,None),yl=(-0.6,None)):
    ax.add_patch(Rectangle((-4,m),4,w,fc='0.85',ec='0.4',lw=0.8))
    ax.add_patch(Rectangle((L,m),4,w,fc='0.85',ec='0.4',lw=0.8))
    ax.add_patch(Rectangle((-4,-1),L+8,1,fc='none',ec='0.3',hatch='////',lw=0))
    ax.plot([-4,L+4],[0,0],'k',lw=1.0)
    ax.plot([-4,L+4],[H,H],':',color='0.5',lw=0.7)
    ax.set_aspect('equal'); ax.set_xlim(xl[0], xl[1] if xl[1] else L+1.2); ax.set_ylim(yl[0], yl[1] if yl[1] else H+3.2)
    ax.set_xticks([]); ax.set_yticks([])
def car_poly(q,**kw):
    X,Y=car.corners(np.array(q)[None]); return Polygon(np.c_[X[0],Y[0]],closed=True,**kw)
def qd():
    return np.array([car.db*np.cos(pd)+(w/2)*np.sin(pd), H-car.b*np.sin(pd)-(w/2)*np.cos(pd), pd])
# ---------- Figure 1: geometry ----------
fig,ax=plt.subplots(figsize=(6.4,3.6)); L=L1
draw_scene(ax,L,xl=(-1.0,L+1.0),yl=(-0.8,5.6))
q=qd(); ax.add_patch(car_poly(q,fc=(0.75,0.85,1.0),ec='b',lw=1.0))
C=q[:2]+R*np.array([-np.sin(q[2]),np.cos(q[2])])
th=np.linspace(-np.pi/2-0.3,0.6,200)
ax.plot(C[0]+car.rho*np.cos(th),C[1]+car.rho*np.sin(th),'--',color='tab:red',lw=0.8)
th2=np.linspace(-np.pi/2-0.55,-np.pi/2+0.55,100)
ax.plot(C[0]+car.rb*np.cos(th2),C[1]+car.rb*np.sin(th2),'--',color='tab:green',lw=0.8)
ax.plot(*C,'k+',ms=7); ax.text(C[0]+0.08,C[1]+0.08,r'$C$')
ax.plot([L],[H],'ro',ms=3); ax.text(L+0.05,H+0.08,r'$Q_{\rm f}$',color='tab:red')
ax.plot([0],[H],'ko',ms=3); ax.text(-0.55,H+0.12,r'$Q_{\rm r}$')
X,Y=car.corners(q[None]); names=['RC','FC','FL','RL']; off=[(0.08,0.10),(-0.42,0.10),(-0.42,-0.28),(0.08,-0.30)]
for i,nm in enumerate(names): ax.text(X[0,i]+off[i][0],Y[0,i]+off[i][1],r'$\mathsf{%s}$'%nm,fontsize=8)
ax.annotate('',xy=(0,H+0.35),xytext=(L,H+0.35),arrowprops=dict(arrowstyle='<->',lw=0.7)); ax.text(L/2,H+0.45,r'$L$',ha='center')
ax.annotate('',xy=(L+0.35,0),xytext=(L+0.35,m),arrowprops=dict(arrowstyle='<->',lw=0.6)); ax.text(L+0.42,m/2-0.06,r'$m$',fontsize=8)
ax.text(L+0.45,H-0.25,r'$y=H$',fontsize=8,color='0.4'); ax.text(-0.95,-0.45,'curb',fontsize=8,bbox=dict(fc='w',ec='none',pad=0.5))
ax.text(C[0]+4.75,C[1]-2.0,r'$\rho$',color='tab:red'); ax.text(C[0]-1.35,C[1]-4.25,r'$r$',color='tab:green')
fig.tight_layout(); fig.savefig(OUT+'fig_geometry.pdf'); plt.close(fig)
# ---------- Figure 2: optimal one-manoeuvre path (exit time, S-curve) ----------
fig,ax=plt.subplots(figsize=(6.4,3.8)); L=L1+1e-6
draw_scene(ax,L,xl=(-1.0,L+3.0),yl=(-0.6,5.4))
q0=qd(); alpha=0.76
S1=np.linspace(0,(alpha-pd)*R,40); Q1=arc_states(q0,+1,1/R,S1)
S2=np.linspace(0,alpha*R,40); Q2=arc_states(Q1[-1],+1,-1/R,S2)
Q=np.vstack([Q1,Q2[1:]])
for i in range(0,len(Q),8):
    ax.add_patch(car_poly(Q[i],fc='none',ec=(0.2,0.3,0.9,0.35+0.65*i/len(Q)),lw=0.8))
ax.add_patch(car_poly(q0,fc=(0.75,0.85,1.0),ec='b',lw=1.0))
X,Y=car.corners(Q); ax.plot(X[:,1],Y[:,1],'r-',lw=0.8,label=r'$\mathsf{FC}$ trace'); ax.plot(X[:,0],Y[:,0],'g-',lw=0.8,label=r'$\mathsf{RC}$ trace')
ax.plot(Q[:,0],Q[:,1],'k-',lw=0.6,label='rear axle')
ax.plot([L],[H],'ro',ms=3); ax.legend(loc='upper left',fontsize=7,frameon=False)
fig.tight_layout(); fig.savefig(OUT+'fig_one.pdf'); plt.close(fig)
print("fig1,2 done")
# ---------- Figure 3: two-manoeuvre double-contact strategy ----------
from scipy.optimize import brentq
Rm,Rp,db,b=car.Ri,car.Ro,car.db,car.b
al=brentq(lambda a: Rm*(1-np.cos(a))+db*np.sin(a)-m,0,1)
L2=db*np.cos(al)-Rm*np.sin(al)+np.sqrt(car.rho**2-(2*R*np.cos(al)-Rp)**2)
fig,axs=plt.subplots(1,2,figsize=(6.6,2.7)); L=L2+1e-6
x0=db*np.cos(al)+Rp*np.sin(al); q0=np.array([x0,m+w/2,0.0])
Q1=arc_states(q0,-1,-1/R,np.linspace(0,al*R,20))
ax=axs[0]; draw_scene(ax,L,xl=(-0.6,L+0.6),yl=(-0.4,H+1.0))
for i in range(0,20,4): ax.add_patch(car_poly(Q1[i],fc='none',ec=(0.2,0.3,0.9,0.4),lw=0.7))
ax.add_patch(car_poly(q0,fc='none',ec='b',lw=1.0,ls='--')); ax.add_patch(car_poly(Q1[-1],fc=(0.75,0.85,1.0),ec='b',lw=1.0))
ax.set_title('(a) reverse, full right lock',fontsize=8)
ax=axs[1]; draw_scene(ax,L,xl=(-0.6,L+2.0),yl=(-0.4,4.6))
q1=Q1[-1]; Qe=arc_states(q1,+1,1/R,np.linspace(0,(0.8-al)*R,30))
for i in range(0,30,5): ax.add_patch(car_poly(Qe[i],fc='none',ec=(0.2,0.3,0.9,0.45),lw=0.7))
ax.add_patch(car_poly(q1,fc=(0.75,0.85,1.0),ec='b',lw=1.0))
X,Y=car.corners(Qe); ax.plot(X[:,1],Y[:,1],'r-',lw=0.8); ax.plot([L],[H],'ro',ms=3)
ax.set_title('(b) forward, full left lock',fontsize=8)
fig.tight_layout(); fig.savefig(OUT+'fig_two.pdf'); plt.close(fig)
# ---------- Figure 4: rescaled windows and ideal loops ----------
fig,axs=plt.subplots(1,2,figsize=(6.6,2.9))
for ax,u in zip(axs,[0.3*w,0.85*w]):
    k=max(0.0,u-w/2); sp,sm=1/(R+k),1/(R-k); D=(sm-sp)/2; c=1/(w-u)
    if u>=w/2: V=np.array([[0,0],[1,0],[0,c],[1,-c]]); P=V[[0,3,1,2]]
    else: P=np.array([[0,0],[(w/2)*c,-c],[1,0],[(w/2-u)*c,c]])
    ax.add_patch(Polygon(P,closed=True,fc='0.92',ec='0.3',lw=0.8))
    for lam,st in [(1.0,'-'),(0.8,'--')]:
        A=np.array([(1-lam)/2,lam*D/2]); B=np.array([(1+lam)/2,-lam*D/2])
        z=np.linspace(A[0],B[0],200)
        up=np.minimum(A[1]+sp*(z-A[0]),B[1]+sm*(B[0]-z)); lo=np.maximum(A[1]-sm*(z-A[0]),B[1]-sp*(B[0]-z))
        ax.plot(z,up,'b'+st,lw=1.0); ax.plot(z,lo,'r'+st,lw=1.0)
    ax.set_xlabel(r'$\zeta$'); ax.set_ylabel(r'$\phi$'); ax.set_xlim(-0.08,1.08); ax.set_ylim(-0.22,0.22)
    A=np.array([0,D/2]); B=np.array([1,-D/2]); ax.plot(*A,'ko',ms=3); ax.plot(*B,'ko',ms=3); ax.text(A[0]+0.02,A[1]+0.015,r'$\mathcal{A}$'); ax.text(B[0]-0.07,B[1]-0.04,r'$\mathcal{B}$')
    ax.set_title(r'$u=%.2fw$, $k=%.2f$'%(u/w,k),fontsize=8); ax.set_aspect('auto')
fig.tight_layout(); fig.savefig(OUT+'fig_window.pdf'); plt.close(fig)
print("fig3,4 done")
# ---------- Figure 6: tilted crawl ----------
import wiggle
def crawl_record(g, mode='T'):
    L=car.ell+g; q=np.array([car.db+1e-9, H-w/2, 0.0]); n=0; d=+1
    us=[0.0]; dense=[]
    while n<100000:
        X,Y=car.corners(q[None])
        if Y.min()>=H: break
        k=max(0.0,(q[1]-w/2-m)-w/2); tilt=(k/(R**2-k**2))*g if mode=='T' else 0.0
        h_end=-tilt/2 if d==+1 else tilt/2
        lo,hi=0.0,0.5; best=None; bsegs=None
        for _ in range(30):
            a=(lo+hi)/2
            a1=a; a2=a1+(q[2]-h_end) if d==+1 else a1+(h_end-q[2])
            if a2<0: lo=a; continue
            segs=wiggle.scurve(q,d,a1,a2); ok,qn=wiggle.path_ok(q,segs,L)
            if ok: lo=a; best=qn; bsegs=segs
            else: hi=a
        if best is None: break
        u=q[1]-w/2-m
        if 0.78*w<u<0.80*w and len(dense)<12:
            qq=q.copy()
            for (dd,kk,ss) in bsegs:
                S=np.linspace(0,ss,60); Qs=arc_states(qq,dd,kk,S); dense.append(Qs); qq=Qs[-1]
        q=best; n+=1; d=-d; us.append(q[1]-w/2-m)
    return np.array(us), dense
g=0.2; us,dense=crawl_record(g)
fig,axs=plt.subplots(1,2,figsize=(6.6,2.8))
ax=axs[0]
for Qs in dense:
    u=Qs[:,1]-w/2-m; k=max(0,np.mean(u)-w/2)
    xi=(Qs[:,0]-car.db)/g; ph=Qs[:,2]/g; ax.plot(xi+k*ph,ph,'b-',lw=0.6)
ax.set_xlabel(r'$\zeta=\xi+k\phi$'); ax.set_ylabel(r'$\phi$'); ax.set_title(r'(a) traces of 12 manoeuvres near $u=0.79w$',fontsize=8)
ax=axs[1]; nn=np.arange(len(us)); ax.plot(nn,us/w,'b-',lw=0.8,label='simulation')
uu=np.linspace(0,w,400); rr=np.where(uu<=w/2,1/(4*R),R/(4*(R**2-(uu-w/2)**2)))
cum=np.concatenate([[0],np.cumsum(np.diff(uu)/rr[1:])])/g**2
ax.plot(cum,uu/w,'k--',lw=0.8,label=r'$\int du/(g^2 r_*)$'); ax.set_xlabel('manoeuvres'); ax.set_ylabel(r'$u/w$')
ax.set_title(r'(b) lift, $g=%.1f$ m'%g,fontsize=8); ax.legend(fontsize=7,frameon=False)
fig.tight_layout(); fig.savefig(OUT+'fig_crawl.pdf'); plt.close(fig)
print("fig6 done", len(us))
