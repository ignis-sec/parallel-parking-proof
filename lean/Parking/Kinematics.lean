/-
Kinematic facts about manoeuvres: continuity of the heading, derivatives of the
position, curb constraints at free configurations.
-/
import Parking.Basic

open Real Set Filter Topology

noncomputable section

namespace Parking

variable {c : Car}

namespace Manoeuvre

variable (M : Manoeuvre c)

theorem invR_nonneg : 0 ≤ 1 / c.R := le_of_lt (one_div_pos.mpr c.R_pos)

/-- The heading is Lipschitz with constant `1/R`. -/
theorem lipschitzWith : LipschitzWith (Real.toNNReal (1 / c.R)) M.ψ := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (invR_nonneg (c := c))]
  have := M.lip s t
  calc |M.ψ s - M.ψ t| ≤ |s - t| / c.R := this
    _ = 1 / c.R * |s - t| := by ring

theorem continuous_ψ : Continuous M.ψ := M.lipschitzWith.continuous

theorem hasDerivAt_X (s : ℝ) : HasDerivAt M.X (M.d * cos (M.ψ s)) s := by
  unfold X
  have hc : Continuous fun σ => cos (M.ψ σ) := continuous_cos.comp M.continuous_ψ
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa using (h.const_mul M.d).const_add M.x0

theorem hasDerivAt_Y (s : ℝ) : HasDerivAt M.Y (M.d * sin (M.ψ s)) s := by
  unfold Y
  have hc : Continuous fun σ => sin (M.ψ σ) := continuous_sin.comp M.continuous_ψ
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa using (h.const_mul M.d).const_add M.y0

theorem continuous_X : Continuous M.X :=
  continuous_iff_continuousAt.mpr fun s => (M.hasDerivAt_X s).continuousAt

theorem continuous_Y : Continuous M.Y :=
  continuous_iff_continuousAt.mpr fun s => (M.hasDerivAt_Y s).continuousAt

end Manoeuvre

/-- At a free configuration every point of the footprint lies above the curb. -/
theorem Free.pt_y_nonneg {S : Slot} {q : Config} (h : Free c S q) {u v : ℝ}
    (hu1 : -c.db ≤ u) (hu2 : u ≤ c.b) (hv1 : -(c.w / 2) ≤ v) (hv2 : v ≤ c.w / 2) :
    0 ≤ (q.pt u v).2 := by
  by_contra hneg
  push Not at hneg
  have hfp : q.pt u v ∈ footprint c q := ⟨u, v, hu1, hu2, hv1, hv2, rfl⟩
  have hob : q.pt u v ∈ obstacle c S := Or.inl (Or.inl hneg)
  exact Set.disjoint_left.mp h hfp hob

end Parking
