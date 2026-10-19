/-
Facts about the assumption package, and the final minimisation step of the forward lower
bound (Step 9 of Proposition `prop:one-forward`): the function `φ` attains its minimum
`Λ₁` over `[0, ψ_fit]` at `ψ_d`.
-/
import Parking.OneUpper

open Real Set

noncomputable section

namespace Parking

variable {c : Car} {m : ℝ}

namespace OneAssumptions

variable (A : OneAssumptions c m)
include A

theorem Rp_pos : 0 < c.Rp := by unfold Car.Rp; linarith [c.R_pos, c.w_pos]

theorem Rm_lt_Rp : c.Rm < c.Rp := by unfold Car.Rm Car.Rp; linarith [c.w_pos]

theorem ρ_pos : 0 < c.ρ := by
  have := A.Rp_pos
  exact Real.sqrt_pos.mpr (by positivity)

theorem r_pos : 0 < c.r := by
  have := A.Rp_pos
  exact Real.sqrt_pos.mpr (by positivity)

theorem sin_γ : sin A.γ = c.Rp / c.ρ := by
  rw [eq_div_iff A.ρ_pos.ne']; linarith [A.hγ.2]

theorem cos_γ : cos A.γ = c.b / c.ρ := by
  rw [eq_div_iff A.ρ_pos.ne']; linarith [A.hγ.1]

theorem sin_β : sin A.β = c.db / c.r := by
  rw [eq_div_iff A.r_pos.ne']; linarith [A.hβ.2]

theorem cos_β : cos A.β = c.Rp / c.r := by
  rw [eq_div_iff A.r_pos.ne']; linarith [A.hβ.1]

theorem β_lt_γ : A.β < A.γ := by
  have hρ := A.ρ_pos; have hr := A.r_pos
  have h : 0 < sin (A.γ - A.β) := by
    rw [sin_sub, A.sin_γ, A.cos_γ, A.sin_β, A.cos_β]
    have := A.A1b
    rw [show c.Rp / c.ρ * (c.Rp / c.r) - c.b / c.ρ * (c.db / c.r) =
      (c.Rp ^ 2 - c.b * c.db) / (c.ρ * c.r) by field_simp]
    apply div_pos (by linarith) (by positivity)
  by_contra hcon
  push Not at hcon
  have : sin (A.γ - A.β) ≤ 0 :=
    sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [A.hβ_mem.2, A.hγ_mem.1, pi_pos])
  linarith

theorem ψfit_lt_β : A.ψfit < A.β := A.A2e

theorem ψfit_lt_γ : A.ψfit < A.γ := A.A2e.trans A.β_lt_γ

theorem ψfit_lt_pi_div_two : A.ψfit < π / 2 := A.A2e.trans A.hβ_mem.2

theorem ψfit_pos : 0 < A.ψfit := A.hψfit_pos

theorem cos_ψfit_pos : 0 < cos A.ψfit :=
  cos_pos_of_mem_Ioo ⟨by linarith [A.ψfit_pos, pi_pos], A.ψfit_lt_pi_div_two⟩

theorem ψfit_lt_ψb : A.ψfit < A.ψb := by
  have h1 := A.hψfit; have h2 := A.hψb
  have hw := c.w_pos; have hl := c.len_pos
  have hc := A.cos_ψfit_pos
  have hs : sin A.ψfit < sin A.ψb := by
    have : c.len * sin A.ψfit < c.len * sin A.ψb := by nlinarith
    exact lt_of_mul_lt_mul_left this hl.le
  by_contra hcon
  push Not at hcon
  have := sin_le_sin_of_le_of_le_pi_div_two (by linarith [A.hψb_mem.1, pi_pos])
    A.ψfit_lt_pi_div_two.le hcon
  linarith

/-- `cos ψ > m / w` whenever `|ψ| ≤ ψ_b`. -/
theorem cos_gt_of_abs_le {ψ : ℝ} (hψ : |ψ| ≤ A.ψb) : m / c.w < cos ψ := by
  have hb := A.A2d
  have : cos A.ψb ≤ cos ψ := by
    rw [← cos_abs ψ]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [A.hψb_mem.2, pi_pos]) hψ
  linarith

/-- `w cos ψ > m` whenever `|ψ| ≤ ψ_b`. -/
theorem w_cos_gt_of_abs_le {ψ : ℝ} (hψ : |ψ| ≤ A.ψb) : m < c.w * cos ψ := by
  have h := A.cos_gt_of_abs_le hψ
  have hw := c.w_pos
  have := (div_lt_iff₀ hw).mp h
  linarith

/-- `R₊ sin ψ_fit < d_b cos ψ_fit` (from `ψ_fit < β`). -/
theorem Rp_sin_lt_db_cos : c.Rp * sin A.ψfit < c.db * cos A.ψfit := by
  have hr := A.r_pos
  have h : 0 < sin (A.β - A.ψfit) :=
    sin_pos_of_pos_of_lt_pi (by linarith [A.A2e]) (by linarith [A.hβ_mem.2, A.ψfit_pos, pi_pos])
  rw [sin_sub, A.sin_β, A.cos_β] at h
  have : 0 < (c.db * cos A.ψfit - c.Rp * sin A.ψfit) / c.r := by
    rw [show (c.db * cos A.ψfit - c.Rp * sin A.ψfit) / c.r =
      c.db / c.r * cos A.ψfit - c.Rp / c.r * sin A.ψfit by ring]; exact h
  have := (div_pos_iff_of_pos_right hr).mp this
  linarith

theorem ρ_sq_sub_Rm_sq : c.ρ ^ 2 - c.Rm ^ 2 = c.b ^ 2 + 2 * c.R * c.w := by
  rw [c.ρ_sq]; unfold Car.Rp Car.Rm; ring

theorem Rm_lt_ρ : c.Rm < c.ρ := by
  have h := A.ρ_sq_sub_Rm_sq
  have := A.Rm_pos; have := A.ρ_pos; have := c.b_pos; have := c.R_pos; have := c.w_pos
  nlinarith

theorem b_lt_ρ : c.b < c.ρ := by
  have h := c.ρ_sq; have := A.Rp_pos; have := A.ρ_pos; have := c.b_pos
  nlinarith

/-- `Y` is antitone on `[0, π/2]`. -/
theorem Yf_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) : c.Yf y ≤ c.Yf x := by
  unfold Car.Yf
  have h1 := cos_le_cos_of_nonneg_of_le_pi hx (by linarith [pi_pos]) hxy
  have h2 := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hy hxy
  have := A.Rm_pos; have := c.b_pos
  nlinarith

theorem Yf_le_Rm {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ π / 2) : c.Yf x ≤ c.Rm := by
  have := A.Yf_anti le_rfl hx hx2
  simpa [Car.Yf] using this

theorem neg_b_le_Yf {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ π / 2) : -c.b ≤ c.Yf x := by
  unfold Car.Yf
  have h1 : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hx2⟩
  have h2 := sin_le_one x
  have := A.Rm_pos; have := c.b_pos
  nlinarith

/-- The constant `c₂ = 2b / sin ψ_b`. -/
def c2 : ℝ := 2 * c.b / sin A.ψb

theorem sin_ψb_pos : 0 < sin A.ψb :=
  sin_pos_of_pos_of_lt_pi A.hψb_mem.1 (by linarith [A.hψb_mem.2, pi_pos])

theorem c2_pos : 0 < A.c2 := by
  unfold c2; have := A.sin_ψb_pos; have := c.b_pos; positivity

/-- The cost function `φ(ψ) = X(ψ) + √(ρ² - Y(ψ)² + c₂ (r - H - Y(ψ))⁺)`. -/
def φ (ψ : ℝ) : ℝ :=
  c.Xf ψ + √(c.ρ ^ 2 - c.Yf ψ ^ 2 + A.c2 * max 0 (c.r - (m + c.w) - c.Yf ψ))

/-- Monotonicity of the cost in the centre position. -/
theorem φ_le_of {ψ cx cy : ℝ} (hcx : c.Xf ψ ≤ cx) (hcy1 : m + c.w ≤ cy)
    (hcy2 : cy ≤ m + c.w + c.Yf ψ) :
    A.φ ψ ≤ cx + √(c.ρ ^ 2 - (cy - (m + c.w)) ^ 2 + A.c2 * max 0 (c.r - cy)) := by
  unfold φ
  have hc2 := A.c2_pos
  have h1 : (cy - (m + c.w)) ^ 2 ≤ c.Yf ψ ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have h2 : max 0 (c.r - (m + c.w) - c.Yf ψ) ≤ max 0 (c.r - cy) :=
    max_le_max le_rfl (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hc2.le
  have := Real.sqrt_le_sqrt (show c.ρ ^ 2 - c.Yf ψ ^ 2 + A.c2 * max 0 (c.r - (m + c.w) - c.Yf ψ)
    ≤ c.ρ ^ 2 - (cy - (m + c.w)) ^ 2 + A.c2 * max 0 (c.r - cy) by linarith)
  linarith

theorem ψd_le_ψfit : A.ψd ≤ A.ψfit := A.hψd_mem.2

theorem Yf_ψd : c.Yf A.ψd = c.r - (m + c.w) := A.hψd

theorem φ_ψd : A.φ A.ψd = A.Λ₁ := by
  unfold φ Λ₁
  rw [A.Yf_ψd, sub_self, max_self, mul_zero, add_zero]

/-- Derivatives of `X` and `Y`. -/
theorem hasDerivAt_Xf (x : ℝ) :
    HasDerivAt c.Xf (-(c.db * sin x) - c.Rm * cos x) x := by
  unfold Car.Xf
  have h1 := (hasDerivAt_cos x).const_mul c.db
  have h2 := (hasDerivAt_sin x).const_mul c.Rm
  convert h1.sub h2 using 1; ring

theorem hasDerivAt_Yf (x : ℝ) :
    HasDerivAt c.Yf (-(c.Rm * sin x) - c.b * cos x) x := by
  unfold Car.Yf
  have h1 := (hasDerivAt_cos x).const_mul c.Rm
  have h2 := (hasDerivAt_sin x).const_mul c.b
  convert h1.sub h2 using 1; ring

theorem continuous_Xf : Continuous c.Xf := by unfold Car.Xf; fun_prop
theorem continuous_Yf : Continuous c.Yf := by unfold Car.Yf; fun_prop

/-- First piece: `φ₁ = X + √(ρ² - Y²)` is antitone on `[0, ψ_d]`. -/
theorem φ1_anti :
    AntitoneOn (fun ψ => c.Xf ψ + √(c.ρ ^ 2 - c.Yf ψ ^ 2)) (Icc 0 A.ψd) := by
  have hψd2 : A.ψd < π / 2 := A.ψd_lt_pi_div_two
  have hRm := A.Rm_pos
  have hb := c.b_pos
  have hdb := c.db_pos
  set K := √(c.b ^ 2 + 2 * c.R * c.w) with hK
  have hKpos : 0 < K := Real.sqrt_pos.mpr (by have := c.R_pos; have := c.w_pos; positivity)
  have hA5 := A.A5a
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 A.ψd)
    (f' := fun x => -(c.db * sin x) - c.Rm * cos x +
      (-(2 * c.Yf x * (-(c.Rm * sin x) - c.b * cos x))) / (2 * √(c.ρ ^ 2 - c.Yf x ^ 2)))
  · exact ((A.continuous_Xf).add ((continuous_const.sub (A.continuous_Yf.pow 2)).sqrt)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hYle := A.Yf_le_Rm hx.1.le (by linarith [hx.2])
    have hYge : c.r - (m + c.w) ≤ c.Yf x := by
      rw [← A.Yf_ψd]; exact A.Yf_anti hx.1.le hx.2.le hψd2.le
    have hY0 : 0 < c.Yf x := by linarith [A.A6a]
    have hne : c.ρ ^ 2 - c.Yf x ^ 2 ≠ 0 := by
      have := A.Rm_lt_ρ
      have : c.Yf x ^ 2 < c.ρ ^ 2 := by nlinarith
      linarith
    have hYsq := (A.hasDerivAt_Yf x).pow 2
    have hin := (hasDerivAt_const x (c.ρ ^ 2)).sub hYsq
    have hsq := hin.sqrt hne
    have := (A.hasDerivAt_Xf x).add hsq
    refine HasDerivAt.hasDerivWithinAt ?_
    convert this using 1
    simp
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 := hx.1; have hx1 := hx.2
    have hYle := A.Yf_le_Rm hx.1.le (by linarith [hx.2])
    have hYge : c.r - (m + c.w) ≤ c.Yf x := by
      rw [← A.Yf_ψd]; exact A.Yf_anti hx.1.le hx.2.le hψd2.le
    have hY0 : 0 < c.Yf x := by linarith [A.A6a]
    have hsx : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith [pi_pos])
    have hcx : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
    have hsxd : sin x ≤ sin A.ψd :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hψd2.le hx1.le
    have hcxd : cos A.ψd ≤ cos x :=
      cos_le_cos_of_nonneg_of_le_pi hx0.le (by linarith [pi_pos]) hx1.le
    have hc1 : cos x ≤ 1 := cos_le_one x
    -- the square root is at least `K`
    have hSK : K ≤ √(c.ρ ^ 2 - c.Yf x ^ 2) := by
      apply Real.sqrt_le_sqrt
      have := A.ρ_sq_sub_Rm_sq
      have : c.Yf x ^ 2 ≤ c.Rm ^ 2 := pow_le_pow_left₀ hY0.le hYle 2
      linarith
    have hSpos : 0 < √(c.ρ ^ 2 - c.Yf x ^ 2) := lt_of_lt_of_le hKpos hSK
    -- the fraction is at most `R₋ (R₋ sin ψ_d + b) / K`
    have hnum : c.Yf x * (c.Rm * sin x + c.b * cos x) ≤ c.Rm * (c.Rm * sin A.ψd + c.b) := by
      have h1 : 0 ≤ c.Rm * sin x + c.b * cos x := by positivity
      have h2 : c.Rm * sin x + c.b * cos x ≤ c.Rm * sin A.ψd + c.b := by nlinarith
      calc c.Yf x * (c.Rm * sin x + c.b * cos x) ≤ c.Rm * (c.Rm * sin x + c.b * cos x) :=
            mul_le_mul_of_nonneg_right hYle h1
        _ ≤ c.Rm * (c.Rm * sin A.ψd + c.b) := mul_le_mul_of_nonneg_left h2 hRm.le
    have hfrac : (-(2 * c.Yf x * (-(c.Rm * sin x) - c.b * cos x))) / (2 * √(c.ρ ^ 2 - c.Yf x ^ 2))
        ≤ c.Rm * (c.Rm * sin A.ψd + c.b) / K := by
      rw [show (-(2 * c.Yf x * (-(c.Rm * sin x) - c.b * cos x))) / (2 * √(c.ρ ^ 2 - c.Yf x ^ 2))
        = c.Yf x * (c.Rm * sin x + c.b * cos x) / √(c.ρ ^ 2 - c.Yf x ^ 2) by
          field_simp; ring]
      have hnn : 0 ≤ c.Rm * (c.Rm * sin A.ψd + c.b) := by
        have := sin_nonneg_of_nonneg_of_le_pi A.ψd_nonneg (by linarith [pi_pos]); positivity
      calc c.Yf x * (c.Rm * sin x + c.b * cos x) / √(c.ρ ^ 2 - c.Yf x ^ 2)
          ≤ c.Rm * (c.Rm * sin A.ψd + c.b) / √(c.ρ ^ 2 - c.Yf x ^ 2) :=
            div_le_div_of_nonneg_right hnum hSpos.le
        _ ≤ c.Rm * (c.Rm * sin A.ψd + c.b) / K := div_le_div_of_nonneg_left hnn hKpos hSK
    have hlast : c.Rm * (c.Rm * sin A.ψd + c.b) / K < c.Rm * cos A.ψd := by
      rw [div_lt_iff₀ hKpos]
      have := mul_lt_mul_of_pos_left hA5 hRm
      linarith
    have : -(c.db * sin x) - c.Rm * cos x ≤ -(c.Rm * cos A.ψd) := by nlinarith
    show -(c.db * sin x) - c.Rm * cos x +
      (-(2 * c.Yf x * (-(c.Rm * sin x) - c.b * cos x))) / (2 * √(c.ρ ^ 2 - c.Yf x ^ 2)) ≤ 0
    linarith

/-- Second piece: `φ₂ = X + √(ρ² - Y² + c₂ (r - H - Y))` is monotone on `[ψ_d, ψ_fit]`. -/
theorem φ2_mono :
    MonotoneOn (fun ψ => c.Xf ψ + √(c.ρ ^ 2 - c.Yf ψ ^ 2 + A.c2 * (c.r - (m + c.w) - c.Yf ψ)))
      (Icc A.ψd A.ψfit) := by
  have hfit2 := A.ψfit_lt_pi_div_two
  have hRm := A.Rm_pos
  have hb := c.b_pos
  have hdb := c.db_pos
  have hc2 := A.c2_pos
  have hcf := A.cos_ψfit_pos
  set G := √(c.ρ ^ 2 + A.c2 * (c.r - (m + c.w) - c.Yf A.ψfit)) with hG
  have hA5 : 2 * (c.Rm + c.db * sin A.ψfit) * G <
      c.b * cos A.ψfit * (2 * c.Yf A.ψfit + A.c2) := A.A5b
  have hsf : 0 ≤ sin A.ψfit := sin_nonneg_of_nonneg_of_le_pi A.ψfit_pos.le (by linarith [pi_pos])
  have hP0 : 0 < 2 * c.Yf A.ψfit + A.c2 := by
    have h1 : 0 ≤ 2 * (c.Rm + c.db * sin A.ψfit) * G := by
      have := Real.sqrt_nonneg (c.ρ ^ 2 + A.c2 * (c.r - (m + c.w) - c.Yf A.ψfit)); positivity
    have h2 : 0 < c.b * cos A.ψfit * (2 * c.Yf A.ψfit + A.c2) := lt_of_le_of_lt h1 hA5
    exact pos_of_mul_pos_right h2 (by positivity)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc A.ψd A.ψfit)
    (f' := fun x => -(c.db * sin x) - c.Rm * cos x +
      (-(2 * c.Yf x * (-(c.Rm * sin x) - c.b * cos x)) + A.c2 * (-(-(c.Rm * sin x) - c.b * cos x))) /
        (2 * √(c.ρ ^ 2 - c.Yf x ^ 2 + A.c2 * (c.r - (m + c.w) - c.Yf x))))
  · exact ((A.continuous_Xf).add ((continuous_const.sub (A.continuous_Yf.pow 2)).add
      (continuous_const.mul (continuous_const.sub A.continuous_Yf))).sqrt).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := le_trans A.ψd_nonneg hx.1.le
    have hYle := A.Yf_le_Rm hx0 (by linarith [hx.2])
    have hYge := A.neg_b_le_Yf hx0 (by linarith [hx.2])
    have hYpen : c.Yf x ≤ c.r - (m + c.w) := by
      rw [← A.Yf_ψd]; exact A.Yf_anti A.ψd_nonneg hx.1.le (by linarith [hx.2])
    have hne : c.ρ ^ 2 - c.Yf x ^ 2 + A.c2 * (c.r - (m + c.w) - c.Yf x) ≠ 0 := by
      have := A.Rm_lt_ρ; have := A.b_lt_ρ
      have : c.Yf x ^ 2 < c.ρ ^ 2 := by nlinarith
      have : 0 ≤ A.c2 * (c.r - (m + c.w) - c.Yf x) := mul_nonneg hc2.le (by linarith)
      linarith
    have hYsq := (A.hasDerivAt_Yf x).pow 2
    have hpen := ((hasDerivAt_const x (c.r - (m + c.w))).sub (A.hasDerivAt_Yf x)).const_mul A.c2
    have hin := ((hasDerivAt_const x (c.ρ ^ 2)).sub hYsq).add hpen
    have hsq := hin.sqrt hne
    have := (A.hasDerivAt_Xf x).add hsq
    refine HasDerivAt.hasDerivWithinAt ?_
    convert this using 1
    simp
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := le_trans A.ψd_nonneg hx.1.le
    have hx1 := hx.2
    have hYle := A.Yf_le_Rm hx0 (by linarith [hx.2])
    have hYge := A.neg_b_le_Yf hx0 (by linarith [hx.2])
    have hYpen : c.Yf x ≤ c.r - (m + c.w) := by
      rw [← A.Yf_ψd]; exact A.Yf_anti A.ψd_nonneg hx.1.le (by linarith [hx.2])
    have hYfit : c.Yf A.ψfit ≤ c.Yf x := A.Yf_anti hx0 hx1.le hfit2.le
    have hsx : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [pi_pos])
    have hsxf : sin x ≤ sin A.ψfit :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hfit2.le hx1.le
    have hcxf : cos A.ψfit ≤ cos x :=
      cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith [pi_pos]) hx1.le
    have hc1 : cos x ≤ 1 := cos_le_one x
    set g := c.ρ ^ 2 - c.Yf x ^ 2 + A.c2 * (c.r - (m + c.w) - c.Yf x) with hg
    have hgpos : 0 < g := by
      have := A.Rm_lt_ρ; have := A.b_lt_ρ
      have : c.Yf x ^ 2 < c.ρ ^ 2 := by nlinarith
      have : 0 ≤ A.c2 * (c.r - (m + c.w) - c.Yf x) := mul_nonneg hc2.le (by linarith)
      linarith
    have hS : 0 < √g := Real.sqrt_pos.mpr hgpos
    have hSG : √g ≤ G := by
      apply Real.sqrt_le_sqrt
      have : A.c2 * (c.r - (m + c.w) - c.Yf x) ≤ A.c2 * (c.r - (m + c.w) - c.Yf A.ψfit) :=
        mul_le_mul_of_nonneg_left (by linarith) hc2.le
      nlinarith
    -- numerator lower bound
    have hnum : c.b * cos A.ψfit * (2 * c.Yf A.ψfit + A.c2) ≤
        (2 * c.Yf x + A.c2) * (c.Rm * sin x + c.b * cos x) := by
      have h1 : c.b * cos A.ψfit ≤ c.Rm * sin x + c.b * cos x := by nlinarith
      have h2 : 2 * c.Yf A.ψfit + A.c2 ≤ 2 * c.Yf x + A.c2 := by linarith
      calc c.b * cos A.ψfit * (2 * c.Yf A.ψfit + A.c2)
          ≤ (c.Rm * sin x + c.b * cos x) * (2 * c.Yf A.ψfit + A.c2) :=
            mul_le_mul_of_nonneg_right h1 hP0.le
        _ ≤ (c.Rm * sin x + c.b * cos x) * (2 * c.Yf x + A.c2) :=
            mul_le_mul_of_nonneg_left h2 (by linarith [mul_pos hb hcf])
        _ = (2 * c.Yf x + A.c2) * (c.Rm * sin x + c.b * cos x) := by ring
    have hdsq : 2 * (c.db * sin x + c.Rm * cos x) * √g ≤ 2 * (c.Rm + c.db * sin A.ψfit) * G := by
      have h1 : 0 ≤ c.db * sin x + c.Rm * cos x := by
        have : 0 ≤ cos x := hcf.le.trans hcxf; positivity
      have h2 : c.db * sin x + c.Rm * cos x ≤ c.Rm + c.db * sin A.ψfit := by nlinarith
      have h3 : 0 ≤ G := Real.sqrt_nonneg _
      have := mul_le_mul h2 hSG (Real.sqrt_nonneg _) (by linarith)
      linarith
    show 0 ≤ -(c.db * sin x) - c.Rm * cos x +
      (-(2 * c.Yf x * (-(c.Rm * sin x) - c.b * cos x)) + A.c2 * (-(-(c.Rm * sin x) - c.b * cos x))) /
        (2 * √g)
    rw [show (-(2 * c.Yf x * (-(c.Rm * sin x) - c.b * cos x)) +
        A.c2 * (-(-(c.Rm * sin x) - c.b * cos x))) / (2 * √g) =
        (2 * c.Yf x + A.c2) * (c.Rm * sin x + c.b * cos x) / (2 * √g) by ring_nf]
    have hfrac : 2 * (c.db * sin x + c.Rm * cos x) * √g / (2 * √g) ≤
        (2 * c.Yf x + A.c2) * (c.Rm * sin x + c.b * cos x) / (2 * √g) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have heq : 2 * (c.db * sin x + c.Rm * cos x) * √g / (2 * √g) = c.db * sin x + c.Rm * cos x := by
      field_simp
    linarith

/-- **Minimisation**: `φ ψ ≥ Λ₁` on `[0, ψ_fit]`. -/
theorem Λ₁_le_φ {ψ : ℝ} (hψ : ψ ∈ Icc 0 A.ψfit) : A.Λ₁ ≤ A.φ ψ := by
  have hfit2 := A.ψfit_lt_pi_div_two
  have hψd2 := A.ψd_lt_pi_div_two
  rcases le_total ψ A.ψd with h | h
  · have hY : c.r - (m + c.w) ≤ c.Yf ψ := by
      rw [← A.Yf_ψd]; exact A.Yf_anti hψ.1 h hψd2.le
    have hφ : A.φ ψ = c.Xf ψ + √(c.ρ ^ 2 - c.Yf ψ ^ 2) := by
      unfold φ; rw [max_eq_left (by linarith), mul_zero, add_zero]
    have := A.φ1_anti ⟨hψ.1, h⟩ ⟨A.ψd_nonneg, le_rfl⟩ h
    rw [hφ, ← A.φ_ψd]
    unfold φ
    rw [A.Yf_ψd, sub_self, max_self, mul_zero, add_zero]
    beta_reduce at this; rw [A.Yf_ψd] at this; exact this
  · have hY : c.Yf ψ ≤ c.r - (m + c.w) := by
      rw [← A.Yf_ψd]; exact A.Yf_anti A.ψd_nonneg h (by linarith [hψ.2])
    have hφ : A.φ ψ = c.Xf ψ + √(c.ρ ^ 2 - c.Yf ψ ^ 2 + A.c2 * (c.r - (m + c.w) - c.Yf ψ)) := by
      unfold φ; rw [max_eq_right (by linarith)]
    have := A.φ2_mono ⟨le_rfl, A.ψd_le_ψfit⟩ ⟨h, hψ.2⟩ h
    rw [hφ, ← A.φ_ψd]
    unfold φ
    rw [A.Yf_ψd, sub_self, max_self]
    simpa [A.Yf_ψd] using this

end OneAssumptions

end Parking
