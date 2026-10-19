# Asymptotics in margin model (L = ell + g, g -> 0)

Height variable u := P_y - w/2 - m  (car bottom minus band bottom m). Start u<=0, escape needs u ~ w.
Exact windows (u in (small, w - small), |psi| small):
  psi>0: P_x in [ d_b/cos psi + (w/2-u) tan psi ,  L - b cos psi - (w/2) sin psi ]
  psi<0: P_x in [ d_b cos psi + (w/2)|sin psi| ,  L - b/cos psi - (w/2-u)|tan psi| ]
 (derived: psi>0 leftmost-in-band point = rear edge crossing y=H; rightmost = FR.
           psi<0 leftmost = RR; rightmost-in-band = front edge crossing y=H.)
Scaled xi=(P_x-d_b)/g, phi=psi/g:  psi>0: xi in [(w/2-u)phi, 1-(w/2)phi]; psi<0: [(w/2)|phi|, 1-(w/2-u)|phi|]
Rise: dP_y = tan(psi) dP_x  -> du = g^2 phi dxi.  Slope dphi/dxi = kappa/cos psi in [-1/R,1/R].
Shear zeta = xi + k phi, k = max(0, u-w/2): window = parallelogram {0<=zeta<=1, 0<=zeta+(w-u)phi<=1}.
Calibration F = (zeta-1/2) phi: per maneuver  Delta u/g^2 <= (s+ + s-)/8 + Delta F + O(g),
  s+- = 1/(R +- k).  => r(u) = 1/(4R) (u<=w/2), R/(4(R^2-k^2)) (u>=w/2).
K^2 = int_0^w du/r(u) = 4Rw - w^3/(6R).  Claim: sqrt(n)(L_min(n)-ell) -> K.
Upper bound: tilted loops. fwd maneuver = F-left then F-right (S-curve) from cusp A (heading +Dg/2, left end)
 to cusp B (heading -Dg/2, right end); bwd = B-left then B-right back. Tilt D = (s- - s+)/2 = k/(R^2-k^2).
 Loop area = R/(2(R^2-k^2)) per 2 maneuvers. Fits in parallelogram since R > w/2.
Confinement: at g=0, window (FR in band, RL above H) open iff u >= Ups(psi) - g cot psi,
 Ups(psi) = (w/2)(1+cos psi) - tan(psi/2)(b cos psi - d_b) ~ w - (b-d_b)psi/2.
 => band [C g/delta, delta/(2b)] closed for all u in [-m, w-delta]; car stays |psi|<=Cg/delta until u>=w-delta.
 Large-tilt windows re-open (e.g. u=0.5,psi=30deg free) but unreachable (band).

## Numerics (typical car df=.9 dw=2.6 db=.8 w=1.8 th=35deg, m=.18): K^2=26.47, 4Rw=26.73
 S-wiggle n g^2: g=.4: 23.52, .2: 24.44, .1: 25.41 ;  T-loops: 23.84, 23.96, 25.07  (converging ~ sqrt(g))
## Small-n upper bounds (exit-time strategies, optimized families):
 n=1 5.8330 (exact), n=2 5.4247 (B-right double contact, F escape), n=3 5.2966 (F-left 60%, B-right, F),
 n=4 5.185 (B,F,B,F greedy, x0=1.574)
