/-
**Clearly labelled axiom.** This file is the only place in the development where a
non-standard axiom is introduced. No other file imports it.

`paper_asym_bounds` asserts Propositions `prop:asym-lower` and `prop:asym-upper` of the paper
under the hypotheses of Theorem `thm:asym`. Their proofs in the paper (Section 6: confinement,
exact description of the free windows, calibration, and the tilted S-curve construction with
its error estimates) are long, uniform-in-`g` perturbation arguments. They were not
formalised. The analytic core of those arguments is formalised in `Parking.AsymCore`, and the
deduction of the theorems from the two propositions is formalised in `Parking.Asym`, with the
propositions as explicit hypotheses. This file only packages the two into unconditional
statements, so that `#print axioms` shows exactly what is assumed.
-/
import Parking.Asym

open Real Filter Topology

namespace Parking

/-- **AXIOM (Propositions `prop:asym-lower` and `prop:asym-upper` of the paper).** -/
axiom paper_asym_bounds (c : Car) (m : ℝ) : AsymHyp c m → AsymLower c m ∧ AsymUpper c m

/-- **Theorem `thm:asym`** (using the axiom `paper_asym_bounds`). -/
theorem thm_asym {c : Car} {m : ℝ} (h : AsymHyp c m) :
    Tendsto (fun n : ℕ => √n * (Lmin c m n - c.len)) atTop (𝓝 (√c.Ksq)) :=
  asym h (paper_asym_bounds c m h).1 (paper_asym_bounds c m h).2

/-- **Theorem `thm:mono`** (limit part, using the axiom `paper_asym_bounds`). -/
theorem thm_mono_limit {c : Car} {m : ℝ} (h : AsymHyp c m) :
    Tendsto (fun n : ℕ => Lmin c m n) atTop (𝓝 c.len) :=
  Lmin_tendsto h (paper_asym_bounds c m h).1 (paper_asym_bounds c m h).2

/-- **Theorem `thm:mono`** (strict lower bound, using the axiom `paper_asym_bounds`). -/
theorem thm_mono_gt {c : Car} {m : ℝ} (h : AsymHyp c m) {n : ℕ}
    (hne : ∃ L, Feasible c m n L) : c.len < Lmin c m n :=
  len_lt_Lmin h (paper_asym_bounds c m h).1 hne

end Parking
