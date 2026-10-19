/-
Analytic core of the many-manoeuvre asymptotics (Section 6 of the paper):
the constant `K²`, the pointwise calibration inequality and its integral,
and the area of the ideal loop.
-/
import Mathlib

open Real Set intervalIntegral

noncomputable section

namespace Parking

/-- Reciprocal of the optimal lift rate `1 / r_*(u)` (`R` and `w` are parameters). -/
def invRate (R w u : ℝ) : ℝ := if u ≤ w / 2 then 4 * R else 4 * (R ^ 2 - (u - w / 2) ^ 2) / R

theorem invRate_continuous (R w : ℝ) : Continuous (invRate R w) := by
  unfold invRate
  apply Continuous.if_le continuous_const (by fun_prop) continuous_id continuous_const
  intro x hx
  simp only [id] at hx
  rw [hx, sub_self]
  rcases eq_or_ne R 0 with h | h
  · simp [h]
  · field_simp
    ring

/-- `K² = ∫₀^w du / r_*(u) = 4 R w - w³ / (6 R)`. -/
theorem K_sq_eq (R w : ℝ) (hR : 0 < R) (hw : 0 < w) :
    (∫ u in (0 : ℝ)..w, invRate R w u) = 4 * R * w - w ^ 3 / (6 * R) := by
  have hc := invRate_continuous R w
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := w / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : (∫ u in (0 : ℝ)..(w / 2), invRate R w u) = ∫ u in (0 : ℝ)..(w / 2), 4 * R := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    simp [invRate, hu.2]
  have h2 : (∫ u in (w / 2)..w, invRate R w u) =
      ∫ u in (w / 2)..w, 4 * (R ^ 2 - (u - w / 2) ^ 2) / R := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    unfold invRate
    split_ifs with h
    · have : u = w / 2 := le_antisymm h hu.1
      subst this
      field_simp
      ring
    · rfl
  rw [h1, h2]
  have hF : ∀ u ∈ Set.uIcc (w / 2) w,
      HasDerivAt (fun u => 4 / R * (R ^ 2 * u - (u - w / 2) ^ 3 / 3))
        (4 * (R ^ 2 - (u - w / 2) ^ 2) / R) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => R ^ 2 * u) (R ^ 2) u := by
      simpa using (hasDerivAt_id u).const_mul (R ^ 2)
    have h2 : HasDerivAt (fun u : ℝ => (u - w / 2) ^ 3 / 3) ((u - w / 2) ^ 2) u := by
      have := (((hasDerivAt_id u).sub_const (w / 2)).pow 3).div_const 3
      convert this using 1
      · funext x; simp
      · simp
    have h3 := (h1.sub h2).const_mul (4 / R)
    convert h3 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun u => 4 * (R ^ 2 - (u - w / 2) ^ 2) / R).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- Pointwise calibration: for a slope `σ ∈ [-s₋, s₊]`,
`-(ζ - 1/2) σ ≤ s₊ (1/2 - ζ)⁺ + s₋ (ζ - 1/2)⁺`. -/
theorem calib_pointwise {sp sm σ ζ : ℝ} (_hsp : 0 ≤ sp) (_hsm : 0 ≤ sm)
    (h1 : -sm ≤ σ) (h2 : σ ≤ sp) :
    -(ζ - 1 / 2) * σ ≤ sp * max (1 / 2 - ζ) 0 + sm * max (ζ - 1 / 2) 0 := by
  rcases le_total ζ (1 / 2) with h | h
  · have hm1 : max (1 / 2 - ζ) 0 = 1 / 2 - ζ := max_eq_left (by linarith)
    have hm2 : max (ζ - 1 / 2) 0 = 0 := max_eq_right (by linarith)
    rw [hm1, hm2]
    nlinarith
  · have hm1 : max (1 / 2 - ζ) 0 = 0 := max_eq_right (by linarith)
    have hm2 : max (ζ - 1 / 2) 0 = ζ - 1 / 2 := max_eq_left (by linarith)
    rw [hm1, hm2]
    nlinarith

/-- The calibration integral over the unit window equals `(s₊ + s₋)/8`. -/
theorem calib_integral (sp sm : ℝ) :
    (∫ ζ in (0 : ℝ)..1, (sp * max (1 / 2 - ζ) 0 + sm * max (ζ - 1 / 2) 0)) = (sp + sm) / 8 := by
  have hc : Continuous fun ζ : ℝ => sp * max (1 / 2 - ζ) 0 + sm * max (ζ - 1 / 2) 0 := by
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : (∫ ζ in (0 : ℝ)..(1 / 2), (sp * max (1 / 2 - ζ) 0 + sm * max (ζ - 1 / 2) 0)) =
      ∫ ζ in (0 : ℝ)..(1 / 2), sp * (1 / 2 - ζ) := by
    apply intervalIntegral.integral_congr
    intro ζ hζ
    rw [Set.uIcc_of_le (by norm_num)] at hζ
    simp only
    rw [max_eq_left (by linarith [hζ.2]), max_eq_right (by linarith [hζ.2])]
    ring
  have h2 : (∫ ζ in (1 / 2 : ℝ)..1, (sp * max (1 / 2 - ζ) 0 + sm * max (ζ - 1 / 2) 0)) =
      ∫ ζ in (1 / 2 : ℝ)..1, sm * (ζ - 1 / 2) := by
    apply intervalIntegral.integral_congr
    intro ζ hζ
    rw [Set.uIcc_of_le (by norm_num)] at hζ
    simp only
    rw [max_eq_right (by linarith [hζ.1]), max_eq_left (by linarith [hζ.1])]
    ring
  rw [h1, h2]
  simp only [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp [integral_id]
  ring

/-- Area of the ideal loop (parallelogram with sides of slopes `s₊` and `-s₋` through the cusps
`(0, Δ/2)` and `(1, -Δ/2)`, `Δ = (s₋ - s₊)/2`) equals `(s₊ + s₋)/4`. -/
theorem loop_area (sp sm : ℝ) (hsp : 0 < sp) (hsm : 0 < sm) :
    let Δ := (sm - sp) / 2
    let ζu := (sm - Δ) / (sp + sm)
    let ζl := (sp + Δ) / (sp + sm)
    ζu * ζl * (sp + sm) = (sp + sm) / 4 := by
  intro Δ ζu ζl
  simp only [Δ, ζu, ζl]
  field_simp
  ring

end Parking
