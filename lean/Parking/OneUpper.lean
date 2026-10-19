/-
Upper bound of the one-manoeuvre theorem: an explicit parking manoeuvre for `L = Λ₁`.
We construct the exit manoeuvre (forward, full left lock from heading `ψ_d` to `π/2`,
then full right lock to `0`) and reverse it.
-/
import Parking.OneDefs
import Parking.Reversal

open Real Set intervalIntegral

noncomputable section

namespace Parking

variable {c : Car} {m : ℝ}

namespace OneAssumptions

variable (A : OneAssumptions c m)

/-- Length of the first (left-lock) arc. -/
def S1 : ℝ := c.R * (π / 2 - A.ψd)
/-- Length of the second (right-lock) arc. -/
def S2 (_A : OneAssumptions c m) : ℝ := c.R * (π / 2)

/-- Heading along the exit: a tent function. -/
def ψE (s : ℝ) : ℝ := A.ψd + (A.S1 - |s - A.S1|) / c.R

/-- Start of the exit: the parked configuration `q_d`. -/
def x0 : ℝ := c.db * cos A.ψd + c.w / 2 * sin A.ψd
def y0 (A : OneAssumptions c m) : ℝ := m + c.w - c.b * sin A.ψd - c.w / 2 * cos A.ψd

theorem ψd_lt_pi_div_two : A.ψd < π / 2 := by
  have := A.hψd_mem.2
  have h2 := A.A2e
  have h3 := A.hβ_mem.2
  linarith

/-- The exit manoeuvre. -/
def exitM : Manoeuvre c where
  d := 1
  hd := Or.inl rfl
  len := A.S1 + A.S2
  len_nonneg := by
    have hR := c.R_pos
    have := A.ψd_lt_pi_div_two
    unfold S1 S2
    have : 0 ≤ c.R * (π / 2 - A.ψd) := mul_nonneg hR.le (by linarith)
    have : 0 ≤ c.R * (π / 2) := mul_nonneg hR.le (by positivity)
    linarith
  x0 := A.x0
  y0 := A.y0
  ψ := A.ψE
  lip := fun s t => by
    have hR := c.R_pos
    unfold ψE
    have h := abs_abs_sub_abs_le_abs_sub (s - A.S1) (t - A.S1)
    rw [show s - A.S1 - (t - A.S1) = s - t by ring] at h
    rw [show A.ψd + (A.S1 - |s - A.S1|) / c.R - (A.ψd + (A.S1 - |t - A.S1|) / c.R)
        = -(|s - A.S1| - |t - A.S1|) / c.R by ring, abs_div, abs_neg, abs_of_pos hR]
    exact div_le_div_of_nonneg_right h hR.le


theorem S1_pos : 0 < A.S1 := by
  unfold S1; have := A.ψd_lt_pi_div_two; exact mul_pos c.R_pos (by linarith)

theorem ψE_arc1 {s : ℝ} (hs : s ≤ A.S1) : A.ψE s = A.ψd + s / c.R := by
  unfold ψE; rw [abs_of_nonpos (by linarith)]; ring

theorem ψE_arc2 {s : ℝ} (hs : A.S1 ≤ s) : A.ψE s = π / 2 - (s - A.S1) / c.R := by
  have hR := c.R_pos
  unfold ψE; rw [abs_of_nonneg (by linarith)]
  unfold S1; field_simp; ring

theorem ψd_add_S1 : A.ψd + A.S1 / c.R = π / 2 := by
  have hR := c.R_pos; unfold S1; field_simp; ring

/-- Left centre of the parked configuration `q_d`. -/
def Cx0 : ℝ := A.x0 - c.R * sin A.ψd
def Cy0 : ℝ := A.y0 + c.R * cos A.ψd

theorem Cx0_eq : A.Cx0 = c.Xf A.ψd := by
  unfold Cx0 x0 Car.Xf Car.Rm; ring

theorem Cy0_eq : A.Cy0 = c.r := by
  have := A.hψd
  unfold Cy0 y0; unfold Car.Yf Car.Rm at this; linarith

theorem exit_X_arc1 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ A.S1) :
    A.exitM.X s = A.Cx0 + c.R * sin (A.ψE s) := by
  have hR := c.R_pos
  have hcongr : (∫ σ in (0:ℝ)..s, cos (A.ψE σ)) = ∫ σ in (0:ℝ)..s, cos (A.ψd + σ / c.R) := by
    apply intervalIntegral.integral_congr
    intro σ hσ; rw [Set.uIcc_of_le hs0] at hσ
    simp only; rw [A.ψE_arc1 (by linarith [hσ.2])]
  have hF : ∀ σ ∈ Set.uIcc (0:ℝ) s,
      HasDerivAt (fun σ => c.R * sin (A.ψd + σ / c.R)) (cos (A.ψd + σ / c.R)) σ := by
    intro σ _
    have := ((((hasDerivAt_id' σ).div_const c.R).const_add A.ψd).sin).const_mul c.R
    convert this using 1; field_simp
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun σ => cos (A.ψd + σ / c.R)).intervalIntegrable _ _)
  show A.x0 + 1 * (∫ σ in (0:ℝ)..s, cos (A.ψE σ)) = _
  rw [hcongr, hint, A.ψE_arc1 hs]
  simp only [zero_div, add_zero]
  unfold Cx0; ring

theorem exit_Y_arc1 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ A.S1) :
    A.exitM.Y s = A.Cy0 - c.R * cos (A.ψE s) := by
  have hR := c.R_pos
  have hcongr : (∫ σ in (0:ℝ)..s, sin (A.ψE σ)) = ∫ σ in (0:ℝ)..s, sin (A.ψd + σ / c.R) := by
    apply intervalIntegral.integral_congr
    intro σ hσ; rw [Set.uIcc_of_le hs0] at hσ
    simp only; rw [A.ψE_arc1 (by linarith [hσ.2])]
  have hF : ∀ σ ∈ Set.uIcc (0:ℝ) s,
      HasDerivAt (fun σ => -(c.R * cos (A.ψd + σ / c.R))) (sin (A.ψd + σ / c.R)) σ := by
    intro σ _
    have := (((((hasDerivAt_id' σ).div_const c.R).const_add A.ψd).cos).const_mul c.R).neg
    convert this using 1; field_simp
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun σ => sin (A.ψd + σ / c.R)).intervalIntegrable _ _)
  show A.y0 + 1 * (∫ σ in (0:ℝ)..s, sin (A.ψE σ)) = _
  rw [hcongr, hint, A.ψE_arc1 hs]
  simp only [zero_div, add_zero]
  unfold Cy0; ring

theorem exit_X_sub (s t : ℝ) : A.exitM.X t - A.exitM.X s = ∫ σ in s..t, cos (A.ψE σ) := by
  have hc : Continuous fun σ => cos (A.ψE σ) := continuous_cos.comp A.exitM.continuous_ψ
  have := intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (hc.intervalIntegrable 0 s)
  show (A.x0 + 1 * ∫ σ in (0:ℝ)..t, cos (A.ψE σ)) - (A.x0 + 1 * ∫ σ in (0:ℝ)..s, cos (A.ψE σ)) = _
  rw [← this]; ring

theorem exit_Y_sub (s t : ℝ) : A.exitM.Y t - A.exitM.Y s = ∫ σ in s..t, sin (A.ψE σ) := by
  have hc : Continuous fun σ => sin (A.ψE σ) := continuous_sin.comp A.exitM.continuous_ψ
  have := intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (hc.intervalIntegrable 0 s)
  show (A.y0 + 1 * ∫ σ in (0:ℝ)..t, sin (A.ψE σ)) - (A.y0 + 1 * ∫ σ in (0:ℝ)..s, sin (A.ψE σ)) = _
  rw [← this]; ring

theorem ψE_S1 : A.ψE A.S1 = π / 2 := by rw [A.ψE_arc1 le_rfl, A.ψd_add_S1]

theorem exit_X_arc2 {s : ℝ} (hs : A.S1 ≤ s) :
    A.exitM.X s = A.Cx0 + 2 * c.R - c.R * sin (A.ψE s) := by
  have hR := c.R_pos
  have h1 := A.exit_X_arc1 (le_of_lt A.S1_pos) le_rfl
  rw [A.ψE_S1, sin_pi_div_two] at h1
  have hcongr : (∫ σ in A.S1..s, cos (A.ψE σ)) = ∫ σ in A.S1..s, cos (π / 2 - (σ - A.S1) / c.R) := by
    apply intervalIntegral.integral_congr
    intro σ hσ; rw [Set.uIcc_of_le hs] at hσ
    simp only; rw [A.ψE_arc2 hσ.1]
  have hF : ∀ σ ∈ Set.uIcc A.S1 s,
      HasDerivAt (fun σ => -(c.R * sin (π / 2 - (σ - A.S1) / c.R)))
        (cos (π / 2 - (σ - A.S1) / c.R)) σ := by
    intro σ _
    have := (((((hasDerivAt_id' σ).sub_const A.S1).div_const c.R).const_sub (π / 2)).sin.const_mul c.R).neg
    convert this using 1; field_simp
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun σ => cos (π / 2 - (σ - A.S1) / c.R)).intervalIntegrable _ _)
  have hsub := A.exit_X_sub A.S1 s
  rw [hcongr, hint] at hsub
  simp only [sub_self, zero_div, sub_zero, sin_pi_div_two] at hsub
  rw [A.ψE_arc2 hs]
  linarith

theorem exit_Y_arc2 {s : ℝ} (hs : A.S1 ≤ s) :
    A.exitM.Y s = A.Cy0 + c.R * cos (A.ψE s) := by
  have hR := c.R_pos
  have h1 := A.exit_Y_arc1 (le_of_lt A.S1_pos) le_rfl
  rw [A.ψE_S1, cos_pi_div_two] at h1
  have hcongr : (∫ σ in A.S1..s, sin (A.ψE σ)) = ∫ σ in A.S1..s, sin (π / 2 - (σ - A.S1) / c.R) := by
    apply intervalIntegral.integral_congr
    intro σ hσ; rw [Set.uIcc_of_le hs] at hσ
    simp only; rw [A.ψE_arc2 hσ.1]
  have hF : ∀ σ ∈ Set.uIcc A.S1 s,
      HasDerivAt (fun σ => c.R * cos (π / 2 - (σ - A.S1) / c.R))
        (sin (π / 2 - (σ - A.S1) / c.R)) σ := by
    intro σ _
    have := ((((hasDerivAt_id' σ).sub_const A.S1).div_const c.R).const_sub (π / 2)).cos.const_mul c.R
    convert this using 1; field_simp
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun σ => sin (π / 2 - (σ - A.S1) / c.R)).intervalIntegrable _ _)
  have hsub := A.exit_Y_sub A.S1 s
  rw [hcongr, hint] at hsub
  simp only [sub_self, zero_div, sub_zero, cos_pi_div_two] at hsub
  rw [A.ψE_arc2 hs]
  linarith

end OneAssumptions

end Parking

namespace Parking

variable {c : Car} {m : ℝ}

theorem Car.r_sq (c : Car) : c.r ^ 2 = c.db ^ 2 + c.Rp ^ 2 :=
  Real.sq_sqrt (by positivity)
theorem Car.ρ_sq (c : Car) : c.ρ ^ 2 = c.b ^ 2 + c.Rp ^ 2 :=
  Real.sq_sqrt (by positivity)
theorem Car.r_nonneg (c : Car) : 0 ≤ c.r := Real.sqrt_nonneg _
theorem Car.ρ_nonneg (c : Car) : 0 ≤ c.ρ := Real.sqrt_nonneg _

/-- A configuration is free if every footprint point is above the curb, right of `x = 0`
and not inside the front parked car. -/
theorem free_of_bounds {S : Slot} {q : Config}
    (h : ∀ u v, -c.db ≤ u → u ≤ c.b → -(c.w / 2) ≤ v → v ≤ c.w / 2 →
      0 ≤ (q.pt u v).2 ∧ 0 ≤ (q.pt u v).1 ∧ ¬ (S.L < (q.pt u v).1 ∧ (q.pt u v).2 < S.H c)) :
    Free c S q := by
  rw [Free, Set.disjoint_left]
  rintro p ⟨u, v, hu1, hu2, hv1, hv2, rfl⟩ hp
  obtain ⟨h1, h2, h3⟩ := h u v hu1 hu2 hv1 hv2
  simp only [obstacle, Set.mem_union, Set.mem_setOf_eq] at hp
  rcases hp with (hp | hp) | hp
  · linarith
  · linarith [hp.1]
  · exact h3 ⟨hp.1, hp.2.2⟩

/-- A configuration whose footprint lies above the parked cars is free. -/
theorem free_of_high {S : Slot} {q : Config} (hH : 0 < S.H c)
    (h : ∀ u v, -c.db ≤ u → u ≤ c.b → -(c.w / 2) ≤ v → v ≤ c.w / 2 → S.H c ≤ (q.pt u v).2) :
    Free c S q := by
  rw [Free, Set.disjoint_left]
  rintro p ⟨u, v, hu1, hu2, hv1, hv2, rfl⟩ hp
  have h1 := h u v hu1 hu2 hv1 hv2
  simp only [obstacle, Set.mem_union, Set.mem_setOf_eq] at hp
  rcases hp with (hp | hp) | hp
  · linarith
  · linarith [hp.2.2]
  · linarith [hp.2.2]

end Parking

namespace Parking

variable {c : Car} {m : ℝ}

namespace OneAssumptions

variable (A : OneAssumptions c m)
include A

theorem Rm_pos : 0 < c.Rm := by unfold Car.Rm; linarith [A.A0]

theorem ψd_nonneg : 0 ≤ A.ψd := A.hψd_mem.1

theorem r_ge_H : m + c.w ≤ c.r := by linarith [A.A6a, c.db_pos]

theorem ρ_sq_ge : (c.r - (m + c.w)) ^ 2 ≤ c.ρ ^ 2 := by
  have h1 := c.r_sq; have h2 := c.ρ_sq; have := A.A1a
  have hr := A.r_ge_H
  have hw := c.w_pos
  have hm := A.hm
  nlinarith [c.db_pos, c.r_nonneg]

/-- `d_b sin ψ + R₊ cos ψ ≤ r`. -/
theorem db_sin_add_Rp_cos_le (ψ : ℝ) : c.db * sin ψ + c.Rp * cos ψ ≤ c.r := by
  have h := c.r_sq
  have hsc := sin_sq_add_cos_sq ψ
  have hsq : (c.db * sin ψ + c.Rp * cos ψ) ^ 2 ≤ c.db ^ 2 + c.Rp ^ 2 := by
    nlinarith [sq_nonneg (c.db * cos ψ - c.Rp * sin ψ)]
  have := Real.abs_le_sqrt hsq
  exact (le_abs_self _).trans this

/-- Footprint point on the first arc, in terms of the centre. -/
theorem arc1_pt {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ A.S1) (u v : ℝ) :
    (A.exitM.config s).pt u v =
      (c.Xf A.ψd + (c.R - v) * sin (A.ψE s) + u * cos (A.ψE s),
        c.r + u * sin (A.ψE s) - (c.R - v) * cos (A.ψE s)) := by
  simp only [Config.pt, Manoeuvre.config]
  rw [A.exit_X_arc1 hs0 hs, A.exit_Y_arc1 hs0 hs, A.Cx0_eq, A.Cy0_eq]
  show (_, _) = (_, _)
  ext <;> simp [exitM] <;> ring

theorem arc2_pt {s : ℝ} (hs : A.S1 ≤ s) (u v : ℝ) :
    (A.exitM.config s).pt u v =
      (c.Xf A.ψd + 2 * c.R - (c.R + v) * sin (A.ψE s) + u * cos (A.ψE s),
        c.r + u * sin (A.ψE s) + (c.R + v) * cos (A.ψE s)) := by
  simp only [Config.pt, Manoeuvre.config]
  rw [A.exit_X_arc2 hs, A.exit_Y_arc2 hs, A.Cx0_eq, A.Cy0_eq]
  show (_, _) = (_, _)
  ext <;> simp [exitM] <;> ring

theorem ψE_arc1_mem {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ A.S1) :
    A.ψd ≤ A.ψE s ∧ A.ψE s ≤ π / 2 := by
  have hR := c.R_pos
  rw [A.ψE_arc1 hs]
  constructor
  · have : 0 ≤ s / c.R := div_nonneg hs0 hR.le
    linarith
  · have h1 := A.ψd_add_S1
    have : s / c.R ≤ A.S1 / c.R := div_le_div_of_nonneg_right hs hR.le
    linarith

theorem ψE_arc2_mem {s : ℝ} (hs1 : A.S1 ≤ s) (hs : s ≤ A.S1 + A.S2) :
    0 ≤ A.ψE s ∧ A.ψE s ≤ π / 2 := by
  have hR := c.R_pos
  rw [A.ψE_arc2 hs1]
  constructor
  · have : (s - A.S1) / c.R ≤ A.S2 / c.R := div_le_div_of_nonneg_right (by linarith) hR.le
    have h2 : A.S2 / c.R = π / 2 := by unfold S2; field_simp
    linarith
  · have : 0 ≤ (s - A.S1) / c.R := div_nonneg (by linarith) hR.le
    linarith


theorem exit_free_arc1 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ A.S1) :
    Free c ⟨m, A.Λ₁⟩ (A.exitM.config s) := by
  apply free_of_bounds
  intro u v hu1 hu2 hv1 hv2
  rw [A.arc1_pt hs0 hs]
  obtain ⟨hψ1, hψ2⟩ := A.ψE_arc1_mem hs0 hs
  set ψ := A.ψE s with hψ
  have hψ0 : 0 ≤ ψ := le_trans A.ψd_nonneg hψ1
  have hsin : 0 ≤ sin ψ := sin_nonneg_of_nonneg_of_le_pi hψ0 (by linarith [pi_pos])
  have hcos : 0 ≤ cos ψ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hψ2⟩
  have hRm := A.Rm_pos
  have hRv1 : c.Rm ≤ c.R - v := by unfold Car.Rm; linarith
  have hRv2 : c.R - v ≤ c.Rp := by unfold Car.Rp; linarith
  have hdb := c.db_pos
  refine ⟨?_, ?_, ?_⟩
  · -- above the curb
    have h1 : -c.db * sin ψ ≤ u * sin ψ := mul_le_mul_of_nonneg_right hu1 hsin
    have h2 : (c.R - v) * cos ψ ≤ c.Rp * cos ψ := mul_le_mul_of_nonneg_right hRv2 hcos
    have h3 := A.db_sin_add_Rp_cos_le ψ
    simp only
    linarith
  · -- right of the car behind
    have hs1 : sin A.ψd ≤ sin ψ :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith [A.ψd_nonneg, pi_pos]) hψ2 hψ1
    have hc1 : cos ψ ≤ cos A.ψd :=
      cos_le_cos_of_nonneg_of_le_pi A.ψd_nonneg (by linarith [pi_pos]) hψ1
    have h1 : c.Rm * sin ψ ≤ (c.R - v) * sin ψ := mul_le_mul_of_nonneg_right hRv1 hsin
    have h2 : -c.db * cos ψ ≤ u * cos ψ := mul_le_mul_of_nonneg_right hu1 hcos
    have h3 : c.Rm * sin A.ψd ≤ c.Rm * sin ψ := mul_le_mul_of_nonneg_left hs1 hRm.le
    have h4 : c.db * cos ψ ≤ c.db * cos A.ψd := mul_le_mul_of_nonneg_left hc1 hdb.le
    simp only [Car.Xf]
    linarith
  · -- not inside the car in front
    rintro ⟨hx, hy⟩
    simp only [Slot.H] at hx hy
    have hsc := sin_sq_add_cos_sq ψ
    have hdist : (c.R - v) ^ 2 + u ^ 2 ≤ c.ρ ^ 2 := by
      rw [c.ρ_sq]
      have hu : u ^ 2 ≤ c.b ^ 2 := by
        have := A.A1a; apply sq_le_sq'; linarith; linarith
      have hv : (c.R - v) ^ 2 ≤ c.Rp ^ 2 := by
        apply sq_le_sq'; linarith; linarith
      linarith
    -- the corner Q_f is at distance ρ from the centre
    set D := Real.sqrt (c.ρ ^ 2 - (c.r - (m + c.w)) ^ 2) with hD
    have hD0 : 0 ≤ D := Real.sqrt_nonneg _
    have hD2 : D ^ 2 = c.ρ ^ 2 - (c.r - (m + c.w)) ^ 2 :=
      Real.sq_sqrt (by linarith [A.ρ_sq_ge])
    have hΛ : A.Λ₁ = c.Xf A.ψd + D := rfl
    rw [hΛ] at hx
    have hrH := A.r_ge_H
    -- squared distance of the point from the centre
    have hpt : ((c.R - v) * sin ψ + u * cos ψ) ^ 2 + (u * sin ψ - (c.R - v) * cos ψ) ^ 2
        = (c.R - v) ^ 2 + u ^ 2 := by linear_combination ((c.R - v) ^ 2 + u ^ 2) * hsc
    have ha : D < (c.R - v) * sin ψ + u * cos ψ := by linarith
    have hb : c.r - (m + c.w) < (c.R - v) * cos ψ - u * sin ψ := by linarith
    have hb0 : 0 ≤ c.r - (m + c.w) := by linarith
    have e1 : D ^ 2 < ((c.R - v) * sin ψ + u * cos ψ) ^ 2 := pow_lt_pow_left₀ ha hD0 two_ne_zero
    have e2' : (c.r - (m + c.w)) ^ 2 < ((c.R - v) * cos ψ - u * sin ψ) ^ 2 :=
      pow_lt_pow_left₀ hb hb0 two_ne_zero
    have e2 : (c.r - (m + c.w)) ^ 2 < (u * sin ψ - (c.R - v) * cos ψ) ^ 2 := by
      have : ((c.R - v) * cos ψ - u * sin ψ) ^ 2 = (u * sin ψ - (c.R - v) * cos ψ) ^ 2 := by ring
      linarith
    have : D ^ 2 + (c.r - (m + c.w)) ^ 2 <
        ((c.R - v) * sin ψ + u * cos ψ) ^ 2 + (u * sin ψ - (c.R - v) * cos ψ) ^ 2 := by linarith
    rw [hD2, hpt] at this
    linarith

theorem arc2_high {s : ℝ} (hs1 : A.S1 ≤ s) (hs : s ≤ A.S1 + A.S2) (u v : ℝ)
    (hu1 : -c.db ≤ u) (hv1 : -(c.w / 2) ≤ v) :
    m + c.w ≤ ((A.exitM.config s).pt u v).2 := by
  rw [A.arc2_pt hs1]
  obtain ⟨hψ0, hψ2⟩ := A.ψE_arc2_mem hs1 hs
  set ψ := A.ψE s
  have hsin : 0 ≤ sin ψ := sin_nonneg_of_nonneg_of_le_pi hψ0 (by linarith [pi_pos])
  have hcos : 0 ≤ cos ψ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hψ2⟩
  have hs1' : sin ψ ≤ 1 := sin_le_one ψ
  have hRv : 0 ≤ c.R + v := by have := A.Rm_pos; unfold Car.Rm at this; linarith
  have h1 : -c.db * sin ψ ≤ u * sin ψ := mul_le_mul_of_nonneg_right hu1 hsin
  have h2 : 0 ≤ (c.R + v) * cos ψ := mul_nonneg hRv hcos
  have h3 : c.db * sin ψ ≤ c.db := by nlinarith [c.db_pos]
  have := A.A6a
  simp only
  linarith

theorem exit_free_arc2 {s : ℝ} (hs1 : A.S1 ≤ s) (hs : s ≤ A.S1 + A.S2) :
    Free c ⟨m, A.Λ₁⟩ (A.exitM.config s) := by
  apply free_of_high (by simp [Slot.H]; linarith [A.hm, c.w_pos])
  intro u v hu1 _ hv1 _
  simpa [Slot.H] using A.arc2_high hs1 hs u v hu1 hv1

theorem exit_free {s : ℝ} (hs : s ∈ Icc (0 : ℝ) A.exitM.len) :
    Free c ⟨m, A.Λ₁⟩ (A.exitM.config s) := by
  rcases le_total s A.S1 with h | h
  · exact A.exit_free_arc1 hs.1 h
  · exact A.exit_free_arc2 h hs.2

theorem exit_start_parked : Parked c ⟨m, A.Λ₁⟩ A.exitM.start := by
  refine ⟨A.exit_free ⟨le_rfl, A.exitM.len_nonneg⟩, ?_⟩
  rintro p ⟨u, v, hu1, hu2, hv1, hv2, rfl⟩
  rw [Manoeuvre.start, A.arc1_pt le_rfl (le_of_lt A.S1_pos)]
  have h0 : A.ψE 0 = A.ψd := by rw [A.ψE_arc1 (le_of_lt A.S1_pos)]; simp
  rw [h0]
  have hsin : 0 ≤ sin A.ψd := sin_nonneg_of_nonneg_of_le_pi A.ψd_nonneg
    (by linarith [A.ψd_lt_pi_div_two, pi_pos])
  have hcos : 0 ≤ cos A.ψd := cos_nonneg_of_mem_Icc
    ⟨by linarith [A.ψd_nonneg, pi_pos], le_of_lt A.ψd_lt_pi_div_two⟩
  have hY := A.hψd
  unfold Car.Yf Car.Rm at hY
  have h1 : (u - c.b) * sin A.ψd ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hsin
  have h2 : (v - c.w / 2) * cos A.ψd ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hcos
  simp only [Slot.H]
  nlinarith

theorem exit_finish_lane : InLane c ⟨m, A.Λ₁⟩ A.exitM.finish := by
  have hR := c.R_pos
  have hlen : A.exitM.len = A.S1 + A.S2 := rfl
  have hS : A.S1 ≤ A.S1 + A.S2 := by have : 0 ≤ A.S2 := by unfold S2; positivity
                                     linarith
  refine ⟨?_, 0, ?_⟩
  · rintro p ⟨u, v, hu1, hu2, hv1, hv2, rfl⟩
    simpa [Slot.H, Manoeuvre.finish, hlen] using A.arc2_high hS le_rfl u v hu1 hv1
  · show A.ψE A.exitM.len = _
    rw [hlen, A.ψE_arc2 hS]
    unfold S2; field_simp; ring

end OneAssumptions

/-- **Upper bound of the one-manoeuvre theorem**: parking with one manoeuvre is feasible
for the slot length `Λ₁`. -/
theorem feasible_one_at_Λ₁ {c : Car} {m : ℝ} (A : OneAssumptions c m) :
    Feasible c m 1 A.Λ₁ := by
  refine ⟨[A.exitM.reverse], A.exitM.reverse, A.exitM.reverse, rfl, rfl, le_rfl, trivial,
    ?_, ?_, ?_⟩
  · intro M hM s hs
    simp only [List.mem_singleton] at hM
    subst hM
    rw [Manoeuvre.reverse_config]
    have hl : A.exitM.reverse.len = A.exitM.len := rfl
    rw [hl] at hs
    exact A.exit_free ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · rw [Manoeuvre.reverse_start]; exact A.exit_finish_lane
  · rw [Manoeuvre.reverse_finish]; exact A.exit_start_parked

end Parking
