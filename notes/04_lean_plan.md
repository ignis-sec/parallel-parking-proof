# Lean formalisation plan (Mathlib v4.35.0, project in lean/)
Files:
- Parking/Model.lean      : Car, Config, footprint, Slot, obstacle, Free/Parked/InLane, Manoeuvre (Lipschitz heading,
                            positions via interval integrals), Chain, ParkingMotion, Feasible, Lmin.   [written]
- Parking/Basic.lean      : monotonicity in L and n, Lmin antitone.                                     [written]
- Parking/Kinematics.lean : continuity of psi, HasDerivAt X/Y, Free.pt_y_nonneg.                         [written]
- Parking/Flush.lean      : zero margin degeneracy (Gronwall + connectedness)                             [in progress]
- Parking/Dini.lean       : continuous f with limsup right slope <= 0 everywhere is antitone
                            (via image_le_of_liminf_slope_right_lt_deriv_boundary').
- Parking/Centres.lean    : turning centres, distance identity in slope form (no a.e. calculus):
     f(s)=|C(s)-Q|^2, slope f s (s+h) = 2(d - R*dpsi/h)(P-Q).e + o(1).
- Parking/One.lean        : Theorem one: hypotheses structure AssumptionOne; upper bound (explicit path, trig ineqs);
                            lower bound forward (heading lemmas, tau, distance monotone, curb cost, minimisation);
                            reverse (Gronwall on rear-wheel height).
- Parking/Asymptotics.lean: calibration pointwise inequality + integral (s+ + s-)/8, K^2 identity, loop area;
                            Theorem asym stated with clearly labelled axioms for confinement/windows/construction.
Key decisions: Feasible stated directly (avoid sInf issues); Lmin corollaries.

## Status (after session restart)
DONE (no sorry): Model, Basic, Kinematics, Flush (not_feasible_zero_margin), Dini, Reversal, Centres (distSq_incr),
 AsymCore (K_sq_eq, calib_pointwise, calib_integral, loop_area), OneDefs (OneAssumptions), OneUpper (feasible_one_at_Λ₁).
TODO: OneParked (parked-config bounds), OneForward (forward exit lower bound), OneReverse (Gronwall),
 OneNormalize (2π shift + mirror), One (combine; file exists referencing exit_one_lower).
Paper: review fixes applied (see notes/05_review.md) except Lean section (C17).

## Status (2026-10-19) — COMPLETE
All files build, no sorry. `#print axioms`: only propext/Classical.choice/Quot.sound, except
AsymAxiom.lean (thm_asym, thm_mono_limit, thm_mono_gt use the labelled axiom paper_asym_bounds).
- One manoeuvre fully formalised: feasible_one_iff, Lmin_one (files OneParked, OneMin, OneForward,
  OneReverse, OneNormalize, One). Reverse bound uses monotone P_x + λ log(h+ε) instead of Gronwall+measure.
- Asym.lean: asym, len_lt_Lmin, Lmin_tendsto from hypotheses AsymLower/AsymUpper.
- Paper: new section sec:lean (sections/lean.tex), abstract + outline updated; 31 pages, 0 overfull.
- lean/README.md documents files and assumptions.

## Appendix car table (2026-10-19)
numerics/car_table.py (+ car_table_tex.py) -> out_car_table.json -> paper/sections/tab_cars.tex (app:cars).
6 cars, n=1 exact (A1-A7 hold for all), n=2 closed form for first 3 (prop:two-better), numeric for
sedan/SUV/van (alpha1<beta), n=3..5 warm-started zigzag search. Typical n=4 improved 5.183 -> 5.180
(updated intro tab, tab:zigzag, fig_values).
