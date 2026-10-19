# USER CHANGE (authoritative from now on): margin model
- parked cars width w, margin m = 0.1 w from curb: occupy y in [m, H], H = m + w; rear x<=0, front x>=L
- curb y=0 HARD for whole footprint
- fit: footprint within 0<=y<=H (max y <= H), collision-free (corners may poke into gap y<m under parked cars)
- start in lane parallel.
Consequences (exit picture):
- n=1: tilted parked start helps. V(q)=C_x+sqrt(rho^2-(C_y-H)^2). Best start: RL on x=0, FL on y=H, tilt psi0.
  V(psi0)= d_b cos psi0 - R_i sin psi0 + sqrt(rho^2 - (R_i cos psi0 - b sin psi0)^2), V'(0)<0.
  Dip constraint (RR stays >=0 on full-lock circle): C_y >= r_b, r_b=sqrt(d_b^2+R_o^2):
  R_i cos psi - b sin psi >= r_b - H. Needs m >= eps_b := r_b - R_o at psi=0.
  Candidate: L_min(1) = V(psi*) , psi* = min(psi_dip, psi_crit); at psi_dip: sqrt-term = sqrt(rho^2-(r_b-H)^2).
  Lower-bound tool: dV >= (cot beta_b - tan delta') dD with D=C_y-r_b (curb cost), c >= R_o(1/d_b-1/b).
- asymptotics unchanged: K^2 = 4Rw - w^3/(6R) (start at car-bottom = m).
- free space NOT upward-shift monotone (gap under parked cars).
