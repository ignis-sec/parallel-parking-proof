import os
import numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
plt.rcParams.update({'font.size':9,'font.family':'serif'})
ell=4.3; R=2.6/np.tan(np.radians(35)); w=1.8; K=np.sqrt(4*R*w-w**3/(6*R))
opt={1:5.833,2:5.411,3:5.280,4:5.180,5:5.050,6:4.978}
greedy=[(2,5.6),(3,5.4),(4,5.2),(8,5.0),(14,4.9)]
crawl=[(28,5.3),(40,5.1),(69,4.9),(97,4.8),(149,4.7),(261,4.6),(599,4.5),(2507,4.4),(10307,4.35),(41789,4.325)]
fig,ax=plt.subplots(figsize=(5.6,3.4))
n=np.logspace(0,4.7,200); ax.plot(n,ell+K/np.sqrt(n),'k--',lw=0.9,label=r'$\ell+K/\sqrt{n}$')
ax.axhline(ell,color='0.5',ls=':',lw=0.8); ax.text(1.1,ell+0.01,r'$\ell$',color='0.4')
ax.plot(list(opt),list(opt.values()),'o',color='tab:blue',ms=4,label='optimised zigzags ($n=1$ exact)')
ax.plot(*zip(*greedy),'s',color='tab:green',ms=3.5,mfc='none',label='greedy zigzag')
ax.plot(*zip(*crawl),'^',color='tab:red',ms=3.5,mfc='none',label='tilted crawl (simulated)')
ax.set_xscale('log'); ax.set_xlabel('number of manoeuvres $n$'); ax.set_ylabel('slot length [m]')
ax.set_ylim(4.2,6.0); ax.legend(fontsize=7,frameon=False,loc='upper right')
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'figures', 'fig_values.pdf'))
print('ok')
