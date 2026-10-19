# Working notes (math phase)

## Coordinates
Curb y=0, slot [0,L]x[0,w], lane y>=w. Car body frame: rear-axle midpoint P, heading psi.
a := d_b, b := d_w + d_f, R = d_w/tan(theta), R_i = R - w/2, R_o = R + w/2, rho^2 = b^2 + R_o^2.
Exit picture = time reversal of parking (n maneuvers <-> n maneuvers).

## Finding 1: literal model is degenerate
Hard curb (footprint in y>=0) + depth exactly w + d_b>0  ==> car can NEVER become flush.
Proof: y := P_y - w/2, c := min(d_b, d_w+d_f) > 0. Curb => y >= c|sin psi| - (w/2)(1-cos psi)
>= (c/2)|sin psi| when |sin psi| <= c/w. |dy/dt| = |v||sin psi| <= (2/c)|v| y. Gronwall backward
from final time (y=0) => y==0, psi==0 on maximal interval => whole motion straight along curb. Contradiction.
=> literal L_min(n) = +inf for all n. Must regularize.

## Regularized model M0' ("line curb"): obstacles = quadrants {x<0,y<w}, {x>L,y<w}; curb only target.
Upward-shift monotonicity: F + (0,h) subset F for h>=0.

## n=1 (M0'): L_1 = d_b + sqrt((d_w+d_f)^2 + 2 R w)   [= d_b + sqrt(rho^2 - R_i^2)]
Upper: exit fwd full-left-lock about C=(d_b, w/2+R); FR corner on circle radius rho; obstacle
quadrant meets closed disk only at Q*=(L,w) when L=L_1.
Lower: value fn V(q) = C_x + sqrt(rho^2 - (C_y - w)^2), C = left center. dC/ds=(1-R kappa) e(psi).
dV/ds = (1-R kappa) cos(psi+delta')/cos(delta') >= 0 while FR below w (arm angle psi-gamma < -delta').
Need care for psi < -90 deg cases.
Backward 1-maneuver exit worse: b + sqrt(a^2+2Rw) > a + sqrt(b^2+2Rw).

## n=2 candidate (M0'): exit B-right by alpha then F-left. Balance eq:
 2R sin(alpha) + b = sqrt(rho^2 - (R_i - 2R(1-cos alpha))^2),  L_2 = d_b cos(alpha) + R_o sin(alpha) + b.
 NOTE: this dips body below curb line (RR corner ~ d_b alpha). Curb-wall models forbid it.

## DECISION (model): main model = "wheel-curb" model W:
 - body footprint must avoid open quadrants O_r={x<0,y<w}, O_f={x>L,y<w}
 - the 4 wheel points (0,+-w/2),(d_w,+-w/2) (body frame) must have y>=0 (tyres can't mount curb;
   bodywork may overhang it).  Literal hard-curb model is degenerate (Thm 0).
 - variant M0' (no curb constraint at all) discussed in remarks; differs at n=2.
In W: from flush, backward motion must be straight; forward must have kappa>=0 initially.
 => exit must start forward-left. Exit (B,F) reduces to 1 maneuver. L_min(2) = min(L_1, L_FB).
 Conjecture: L_FB >= L_1 for realistic cars => L_min(2) = L_1 (2nd maneuver useless!).

## Asymptotics (big result): L = l + g, g->0. Scaled xi=(P_x-d_b)/g, phi=psi/g, eta = P_y - w/2.
 Rise: d eta = tan(psi) dP_x.  Windows (eta >> g): parallelogram 0<=zeta<=1, 0<=zeta+(w-eta)phi<=1
 in sheared coord zeta = xi + k phi, k = eta - w/2 (use k=0 if eta<w/2).
 Slopes (fwd, as fn of zeta): dphi/dzeta in [-1/(R-k), 1/(R+k)]; bwd same as fn of zeta.
 Calibration F=(zeta-1/2)phi gives sharp per-maneuver rise r = (s+ + s-)/8 = R/(4(R^2-k^2)) (k>0),
 r = 1/(4R) for eta<=w/2.  Achieved by tilted loops (tilt Delta = k/(R^2-k^2)).
 => conjecture: sqrt(n)(L_min(n)-l) -> K, K^2 = int_0^w d eta / r(eta) = 4Rw - w^3/(6R).
 S-curve wiggle gives 2 sqrt(Rw) (factor sqrt(1-w^2/(24R^2)) ~ 0.995 off).
 Lower-bound route: confinement lemma (|psi|<=Cg until eta>=w-delta) + calibration.

## Soft curb (2026-10-19; paper sections soft.tex, compare.tex)
 Final margin model + soft curb: only body-aligned tyre rectangles must avoid the curb
 (delta_s=0.0275, t_w=0.205, lambda=0.25 for every car; front tyres not steered in the model).
 - n=1: L1s = phi_0(psi_t) (Thm one-soft, hyps S1-S7, soft_theory.py); typical 5.809 vs rigid 5.833.
   City car fails S4 only; numerical 4.89485 vs closed 4.89480.
 - n=2: textbook exit (reverse right lock to rear-bumper contact, exit left lock), closed form
   L2s = b + d_b cos a_s + R+ sin a_s; typical 5.312 vs rigid 5.4104.
 - n=3..5 (zigzags, soft_table.py + soft_polish.py seeded from rigid motions), n=20 (twenty_search
   with SoftCar): typical 5.088, 4.978, 4.906, 4.704 (rigid 5.280, 5.180, 5.050, 4.855).
   Typical n=3,4,5 from the full search (soft_tight.py / soft_five.py): all optimal motions are
   contact zigzags (parameters at bounds), length bisected exactly. Light search was up to 2 cm worse.
   Appendices E/F (fig_five.py soft, fig_twenty.py soft): soft five- and twenty-manoeuvre motions.
   Gains grow roughly with d_b: city car <= 4.6 cm, van up to 40 cm (compare_tex.py).
 - soft_checks.py: all final motions free also with steered front tyres and (n>=2) with the largest
   tyres (delta_s=0, lambda=0.30); tyre clearance >= 6.7 cm (n=2), >= 11 cm (n=3..5), 16 cm (n=20).
 - soft_sens.py: typical L1s in [5.802, 5.817] for delta_s in [0,5] cm, lambda in [0.20,0.30] m.
 - Same K asymptotically (prop asym-soft); flush problem m=0 well posed (typical 5.856).
