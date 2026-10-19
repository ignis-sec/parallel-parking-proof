# n = 1 (margin model) -- proof plan
C = P + R n(psi) (left center).  FR = C + rho e(psi - gam), cos gam=b/rho, sin gam=R_o/rho.
RR = C + r_b e(psi - pi/2 - beta), sin beta = d_b/r_b, cos beta = R_o/r_b.  RR_y = C_y - r_b cos(psi-beta).
V(q) = C_x + sqrt(rho^2-(C_y-H)^2).  C' = (1-R kappa) e(psi)  (fwd).  V' = (1-Rk) rho cos(psi+delta)/sqrt(..),
 sin delta = (C_y-H)/rho.
THEOREM: L_min(1) = Lam1 := d_b cos pd - R_i sin pd + sqrt(rho^2 - q^2), q = r_b - H,
 pd in [0, psi_fit]:  R_i cos pd - b sin pd = q.   Closed form with s0^2=b^2+R_i^2:
 Lam1 = [ell R_i q + (b d_b - R_i^2) sqrt(s0^2-q^2)]/s0^2 + sqrt(rho^2-q^2).  (m=eps_b -> classical)
 typical car: 5.83295 (classical 5.86137).
FORWARD LOWER BOUND steps:
 L1: tau = first time FR_y = H.  FR_y(0) < H.
 L2: on [0,tau): psi < psi_b := asin(H/ell)  [psi in[0,pi/2] => FR_y >= ell sin psi via RR_y>=0]
     P_y < H + w/2 (P_y rises only if psi>0, then FR_y<H gives it); psi > -alpha_c where
     b sin a_c + (w/2) cos a_c = H + w/2 (curb at FR for psi<0).
 L3: psi(tau) >= 0 (else P_y(tau) = H + b|sin|+(w/2)cos > H+w/2), so FR on right branch, FR_x(tau)=V(tau).
 L4: FR_x(tau) <= L (continuity, FR in band just before tau).
 L5: V nondecreasing on [0,tau]: psi+delta < gam < pi/2 (from FR_y<H) and psi+delta >= -pi/2 if H <= rho cos a_c.
 L6: curb cost: V' >= c1 C_y',  c1 = cot psi_b - R_o/b > 0.  Either psi hits beta (C_y>=r_b there) or
     psi(tau)<beta => C_y(tau) > H + rho sin(gam-beta) = H + (R_o^2 - b d_b)/r_b.  => L >= V(q0)+c1 (r_b - C_y(q0))^+.
 L7: fitting q0: psi0<0 worse than corner at 0; psi0>=0: C_x >= d_b cos - R_i sin, C_y <= H + R_i cos - b sin
     (RL in band since RR_y>=0 & cos psi0 > m/w).  Phi~(psi) = V(psi) + c1 (r_b - Cy(psi))^+ minimized at pd if
     V'<0 on [0,pd] and V' + c1(b cos + R_i sin) > 0 on [pd, psi_fit].
BACKWARD: V_r = C_x - sqrt(r_b^2-(C_y-H)^2) nonincreasing in bwd motion; need V_r(q0)>=0 =>
 L >= sqrt(d_b^2+2Rw) + b cos psi_fit - R_i sin psi_fit  (>> Lam1).  needs analogous heading lemmas.
UPPER BOUND: corner config tilt pd, full left lock to heading pi/2 then right lock to 0.
 car subset of closed disk D(C,rho) (needs d_b<b); O_f misses open disk if |C-Q_f|>=rho, C_x<=L, C_y>=H.
 rear: polar-angle argument (points left of C are in lower-left quadrant, move right).
 curb: points passing bottom have radius <= r_b, and C_y = r_b.  end: rear bumper y = r_b - d_b >= H.

## Cleaner lower-bound tool (distance form)
d|C - Q_f|^2/ds = -2 (1-R kappa) q_x,  q_x := (Q_f - P).e(psi)   (forward). Nonincreasing while Q_f ahead of axle.
q_x = (Q_f-FR).e + b >= b - m sin psi (or b - H sin a_c) > 0 before tau.  At tau (psi in [0,pi/2]):
q_body in quadrant {x>=b, y<=-w/2} => |C-Q_f| >= rho.  Hence |C(0)-Q_f| >= rho <=> L >= V(q0).
Curb cost: d|C-Q_f|^2 <= -(2b/sin psi_b) dC_y when psi in (0,psi_b).
Backward: d|C-Q_r|^2/dsigma = 2(1-Rk)(Q_r-P).e ; need Q_r behind axle until RR passes (topological case analysis).

# n = 2 numerics (typical car): L_2 ~ 5.4247.  Strategy (exit time): start parallel at top (bottom at m),
 x0 = d_b cos a + R_o sin a; B-right (full lock) by a until RR on curb AND RL on rear face simultaneously:
   R_i(1-cos a) + d_b sin a = m   (a = 0.1726);  then F-left escape.
 L_2 = d_b cos a - R_i sin a + sqrt(rho^2 - (2R cos a - R_o)^2)   [valid if a >= beta (escape RR rises)].
 typical: a=0.1726 vs beta=0.1717 (barely).  C_L,y(q1) = r_b cos(a-beta).

## FINAL forward-proof hypotheses (to collect in Assumption):
 H<ell; 2Rb > w rho (FL below H at psi=-gam); w b > m rho (FC below curb if FL in gap); b>=w/2;
 b > H R_+/rho (Q_f ahead of axle); cos psi_b > m/w; psi_fit < beta; (R_+^2 - b d_b)/r >= r - H;
 R_+ cos psi_fit >= H; d_b cos psi_fit - R sin psi_fit + rho >= Lam1; phi minimized at psi_d; m>=eps_b; d_b<b;
 r - d_b >= H (upper bound end in lane).
 Nose-down bound now via right centre C' (FL = C' + rho e(psi+gam)), replaces b>=H+w/2.
## BACKWARD via Gronwall on rear-curb-wheel height h = P_y - (w/2)cos psi:
 bwd: h' = -sin psi (1+(w/2)psi'), increases only if psi<0, h' <= (R_+/(R b)) h (curb at FC: |sin|<=h/b).
 nose-up phases: h drops >= R_-(1-cos psi) => psi < psi_u, H = R_-(1-cos psi_u) + d_b sin psi_u.
 h(0) <= h0 := H - w cos psi_fit ; h(tau_r) >= H b/ell ; cos psi >= c_psi = sqrt(1-H^2/b^2) in psi<0 phases.
 => L >= b - O(psi_fit) - sqrt(d_b^2+w^2/4) + c_psi (R b/R_+) log(H b/(ell h0))  (~7.2 typical) >= Lam1.
