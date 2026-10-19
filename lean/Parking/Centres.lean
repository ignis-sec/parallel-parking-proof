/-
Turning centres and the distance identity (in slope form, valid for Lipschitz headings).
-/
import Parking.Kinematics
import Parking.Dini

open Real Set Filter Topology

noncomputable section

namespace Parking

variable {c : Car}

namespace Manoeuvre

variable (M : Manoeuvre c)

/-- Left turning centre `C = P + R n(ψ)`. -/
def Cx (s : ℝ) : ℝ := M.X s - c.R * sin (M.ψ s)
def Cy (s : ℝ) : ℝ := M.Y s + c.R * cos (M.ψ s)

/-- Right turning centre `C' = P - R n(ψ)`. -/
def C'x (s : ℝ) : ℝ := M.X s + c.R * sin (M.ψ s)
def C'y (s : ℝ) : ℝ := M.Y s - c.R * cos (M.ψ s)

theorem continuous_Cx : Continuous M.Cx :=
  M.continuous_X.sub (continuous_const.mul (continuous_sin.comp M.continuous_ψ))
theorem continuous_Cy : Continuous M.Cy :=
  M.continuous_Y.add (continuous_const.mul (continuous_cos.comp M.continuous_ψ))

/-- Increment of the position: `|X z - X s - d (z-s) cos ψ(s)| ≤ (z-s)^2/R` for `s ≤ z`. -/
theorem X_incr (s z : ℝ) (hsz : s ≤ z) :
    |M.X z - M.X s - M.d * (z - s) * cos (M.ψ s)| ≤ (z - s) ^ 2 / c.R := by
  have hR := c.R_pos
  have hc : Continuous fun σ => cos (M.ψ σ) := continuous_cos.comp M.continuous_ψ
  have hsub : (∫ σ in (0:ℝ)..z, cos (M.ψ σ)) - ∫ σ in (0:ℝ)..s, cos (M.ψ σ)
      = ∫ σ in s..z, cos (M.ψ σ) :=
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hconst : ∫ σ in s..z, cos (M.ψ s) = (z - s) * cos (M.ψ s) := by simp
  have hdiff : M.X z - M.X s - M.d * (z - s) * cos (M.ψ s)
      = M.d * ∫ σ in s..z, (cos (M.ψ σ) - cos (M.ψ s)) := by
    unfold X
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const, hconst]
    rw [← hsub]; ring
  rw [hdiff, abs_mul]
  have hd1 : |M.d| = 1 := by rcases M.hd with h | h <;> simp [h]
  rw [hd1, one_mul]
  have hbound : ∀ σ ∈ Set.uIoc s z, ‖cos (M.ψ σ) - cos (M.ψ s)‖ ≤ (z - s) / c.R := by
    intro σ hσ
    rw [Set.uIoc_of_le hsz] at hσ
    rw [Real.norm_eq_abs]
    calc |cos (M.ψ σ) - cos (M.ψ s)| ≤ |M.ψ σ - M.ψ s| := Real.abs_cos_sub_cos_le _ _
      _ ≤ |σ - s| / c.R := M.lip σ s
      _ ≤ (z - s) / c.R := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hR)
          rw [abs_of_nonneg (by linarith [hσ.1])]; linarith [hσ.2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ z - s)] at this
  calc |∫ σ in s..z, (cos (M.ψ σ) - cos (M.ψ s))| ≤ (z - s) / c.R * (z - s) := this
    _ = (z - s) ^ 2 / c.R := by ring

theorem Y_incr (s z : ℝ) (hsz : s ≤ z) :
    |M.Y z - M.Y s - M.d * (z - s) * sin (M.ψ s)| ≤ (z - s) ^ 2 / c.R := by
  have hR := c.R_pos
  have hc : Continuous fun σ => sin (M.ψ σ) := continuous_sin.comp M.continuous_ψ
  have hsub : (∫ σ in (0:ℝ)..z, sin (M.ψ σ)) - ∫ σ in (0:ℝ)..s, sin (M.ψ σ)
      = ∫ σ in s..z, sin (M.ψ σ) :=
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hconst : ∫ σ in s..z, sin (M.ψ s) = (z - s) * sin (M.ψ s) := by simp
  have hdiff : M.Y z - M.Y s - M.d * (z - s) * sin (M.ψ s)
      = M.d * ∫ σ in s..z, (sin (M.ψ σ) - sin (M.ψ s)) := by
    unfold Y
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const, hconst]
    rw [← hsub]; ring
  rw [hdiff, abs_mul]
  have hd1 : |M.d| = 1 := by rcases M.hd with h | h <;> simp [h]
  rw [hd1, one_mul]
  have hbound : ∀ σ ∈ Set.uIoc s z, ‖sin (M.ψ σ) - sin (M.ψ s)‖ ≤ (z - s) / c.R := by
    intro σ hσ
    rw [Set.uIoc_of_le hsz] at hσ
    rw [Real.norm_eq_abs]
    calc |sin (M.ψ σ) - sin (M.ψ s)| ≤ |M.ψ σ - M.ψ s| := Real.abs_sin_sub_sin_le _ _
      _ ≤ |σ - s| / c.R := M.lip σ s
      _ ≤ (z - s) / c.R := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hR)
          rw [abs_of_nonneg (by linarith [hσ.1])]; linarith [hσ.2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ z - s)] at this
  calc |∫ σ in s..z, (sin (M.ψ σ) - sin (M.ψ s))| ≤ (z - s) / c.R * (z - s) := this
    _ = (z - s) ^ 2 / c.R := by ring


/-- Squared distance from the left centre to a fixed point `Q`. -/
def distSq (Q : ℝ × ℝ) (s : ℝ) : ℝ := (M.Cx s - Q.1) ^ 2 + (M.Cy s - Q.2) ^ 2

/-- Purely algebraic identity behind the distance identity. -/
theorem distSq_alg (px py Ex Ey sb cb sd cd d h R dX dY : ℝ) (hsc : sb ^ 2 + cb ^ 2 = 1)
    (hX : dX = d * h * cb + Ex) (hY : dY = d * h * sb + Ey) :
    2 * (px - R * sb) * (dX - R * ((sb * cd + cb * sd) - sb)) +
      2 * (py + R * cb) * (dY + R * ((cb * cd - sb * sd) - cb)) =
    2 * (px * cb + py * sb) * (d * h - R * sd) +
      (2 * (px * Ex + py * Ey) + 2 * R * (cd - 1) * (-px * sb + py * cb) +
        2 * R * (-sb * Ex + cb * Ey) + 2 * R ^ 2 * (cd - 1)) := by
  subst hX hY
  linear_combination (2 * R ^ 2 * (cd - 1)) * hsc

/-- Bound on the increment of the position (crude): `|X z - X s| ≤ z - s`. -/
theorem X_lip (s z : ℝ) (hsz : s ≤ z) : |M.X z - M.X s| ≤ z - s := by
  have hc : Continuous fun σ => cos (M.ψ σ) := continuous_cos.comp M.continuous_ψ
  have hsub : (∫ σ in (0:ℝ)..z, cos (M.ψ σ)) - ∫ σ in (0:ℝ)..s, cos (M.ψ σ)
      = ∫ σ in s..z, cos (M.ψ σ) :=
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have : M.X z - M.X s = M.d * ∫ σ in s..z, cos (M.ψ σ) := by
    unfold X; rw [← hsub]; ring
  rw [this, abs_mul]
  have hd : |M.d| = 1 := by rcases M.hd with h' | h' <;> simp [h']
  rw [hd, one_mul]
  have hb1 : ∀ σ ∈ Set.uIoc s z, ‖cos (M.ψ σ)‖ ≤ 1 := fun σ _ => by
    rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb1
  simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ z - s)] using this

theorem Y_lip (s z : ℝ) (hsz : s ≤ z) : |M.Y z - M.Y s| ≤ z - s := by
  have hc : Continuous fun σ => sin (M.ψ σ) := continuous_sin.comp M.continuous_ψ
  have hsub : (∫ σ in (0:ℝ)..z, sin (M.ψ σ)) - ∫ σ in (0:ℝ)..s, sin (M.ψ σ)
      = ∫ σ in s..z, sin (M.ψ σ) :=
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have : M.Y z - M.Y s = M.d * ∫ σ in s..z, sin (M.ψ σ) := by
    unfold Y; rw [← hsub]; ring
  rw [this, abs_mul]
  have hd : |M.d| = 1 := by rcases M.hd with h' | h' <;> simp [h']
  rw [hd, one_mul]
  have hb1 : ∀ σ ∈ Set.uIoc s z, ‖sin (M.ψ σ)‖ ≤ 1 := fun σ _ => by
    rw [Real.norm_eq_abs]; exact abs_sin_le_one _
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb1
  simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ z - s)] using this

theorem ψ_incr (s z : ℝ) (hsz : s ≤ z) : |M.ψ z - M.ψ s| ≤ (z - s) / c.R := by
  have := M.lip z s
  rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ z - s)] at this

set_option maxHeartbeats 1000000 in
theorem distSq_incr (Q : ℝ × ℝ) (s z : ℝ) (hsz : s ≤ z) :
    M.distSq Q z - M.distSq Q s ≤
      2 * ((M.X s - Q.1) * cos (M.ψ s) + (M.Y s - Q.2) * sin (M.ψ s)) *
          (M.d * (z - s) - c.R * sin (M.ψ z - M.ψ s)) +
        (3 * (|M.X s - Q.1| + |M.Y s - Q.2|) / c.R + 12) * (z - s) ^ 2 := by
  have hR := c.R_pos
  have hh0 : 0 ≤ z - s := by linarith
  -- abbreviations
  obtain ⟨b0, hb0⟩ : ∃ b0, b0 = M.ψ s := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = M.ψ z - M.ψ s := ⟨_, rfl⟩
  obtain ⟨px, hpx⟩ : ∃ px, px = M.X s - Q.1 := ⟨_, rfl⟩
  obtain ⟨py, hpy⟩ : ∃ py, py = M.Y s - Q.2 := ⟨_, rfl⟩
  obtain ⟨Ex, hEx⟩ : ∃ Ex, Ex = M.X z - M.X s - M.d * (z - s) * cos b0 := ⟨_, rfl⟩
  obtain ⟨Ey, hEy⟩ : ∃ Ey, Ey = M.Y z - M.Y s - M.d * (z - s) * sin b0 := ⟨_, rfl⟩
  have hEx' : |Ex| ≤ (z - s) ^ 2 / c.R := by rw [hEx, hb0]; exact M.X_incr s z hsz
  have hEy' : |Ey| ≤ (z - s) ^ 2 / c.R := by rw [hEy, hb0]; exact M.Y_incr s z hsz
  have hδb : |δ| ≤ (z - s) / c.R := by rw [hδ]; exact M.ψ_incr s z hsz
  have hsa : sin (M.ψ z) = sin b0 * cos δ + cos b0 * sin δ := by
    rw [hδ, hb0, ← sin_add]; ring_nf
  have hca : cos (M.ψ z) = cos b0 * cos δ - sin b0 * sin δ := by
    rw [hδ, hb0, ← cos_add]; ring_nf
  -- centre increments
  have hdCx : M.Cx z - M.Cx s = (M.X z - M.X s) - c.R * (sin (M.ψ z) - sin b0) := by
    unfold Cx; rw [hb0]; ring
  have hdCy : M.Cy z - M.Cy s = (M.Y z - M.Y s) + c.R * (cos (M.ψ z) - cos b0) := by
    unfold Cy; rw [hb0]; ring
  have hRh : c.R * ((z - s) / c.R) = z - s := by field_simp
  have hdCxb : |M.Cx z - M.Cx s| ≤ 2 * (z - s) := by
    rw [hdCx]
    have h1 := M.X_lip s z hsz
    have h2 : |c.R * (sin (M.ψ z) - sin b0)| ≤ z - s := by
      rw [abs_mul, abs_of_pos hR, ← hRh]
      exact mul_le_mul_of_nonneg_left ((abs_sin_sub_sin_le _ _).trans (by rw [hb0]; exact M.ψ_incr s z hsz)) hR.le
    linarith [abs_sub (M.X z - M.X s) (c.R * (sin (M.ψ z) - sin b0))]
  have hdCyb : |M.Cy z - M.Cy s| ≤ 2 * (z - s) := by
    rw [hdCy]
    have h1 := M.Y_lip s z hsz
    have h2 : |c.R * (cos (M.ψ z) - cos b0)| ≤ z - s := by
      rw [abs_mul, abs_of_pos hR, ← hRh]
      exact mul_le_mul_of_nonneg_left ((abs_cos_sub_cos_le _ _).trans (by rw [hb0]; exact M.ψ_incr s z hsz)) hR.le
    linarith [abs_add_le (M.Y z - M.Y s) (c.R * (cos (M.ψ z) - cos b0))]
  have hsq : (M.Cx z - M.Cx s) ^ 2 + (M.Cy z - M.Cy s) ^ 2 ≤ 8 * (z - s) ^ 2 := by
    have h1 := sq_le_sq' (abs_le.mp hdCxb).1 (abs_le.mp hdCxb).2
    have h2 := sq_le_sq' (abs_le.mp hdCyb).1 (abs_le.mp hdCyb).2
    nlinarith
  -- the main identity
  have hCxs : M.Cx s - Q.1 = px - c.R * sin b0 := by unfold Cx; rw [hpx, hb0]; ring
  have hCys : M.Cy s - Q.2 = py + c.R * cos b0 := by unfold Cy; rw [hpy, hb0]; ring
  have hexp : M.distSq Q z - M.distSq Q s =
      2 * (M.Cx s - Q.1) * (M.Cx z - M.Cx s) + 2 * (M.Cy s - Q.2) * (M.Cy z - M.Cy s) +
        ((M.Cx z - M.Cx s) ^ 2 + (M.Cy z - M.Cy s) ^ 2) := by
    unfold distSq; ring
  have hX : M.X z - M.X s = M.d * (z - s) * cos b0 + Ex := by rw [hEx]; ring
  have hY : M.Y z - M.Y s = M.d * (z - s) * sin b0 + Ey := by rw [hEy]; ring
  have hident := distSq_alg px py Ex Ey (sin b0) (cos b0) (sin δ) (cos δ) M.d (z - s) c.R
    (M.X z - M.X s) (M.Y z - M.Y s) (sin_sq_add_cos_sq b0) hX hY
  rw [← hsa, ← hca] at hident
  rw [← hdCx, ← hdCy, ← hCxs, ← hCys] at hident
  rw [hexp, hident]
  -- error terms
  have hcos1 : cos δ ≤ 1 := cos_le_one δ
  have hcd : 1 - cos δ ≤ (z - s) ^ 2 / (2 * c.R ^ 2) := by
    have h1 := one_sub_sq_div_two_le_cos (x := δ)
    have h2 : δ ^ 2 ≤ ((z - s) / c.R) ^ 2 := by
      have := sq_le_sq' (abs_le.mp hδb).1 (abs_le.mp hδb).2; simpa using this
    have h3 : ((z - s) / c.R) ^ 2 / 2 = (z - s) ^ 2 / (2 * c.R ^ 2) := by field_simp
    linarith
  have hpE : px * Ex + py * Ey ≤ (|px| + |py|) * ((z - s) ^ 2 / c.R) := by
    have h1 : px * Ex ≤ |px| * ((z - s) ^ 2 / c.R) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hEx' (abs_nonneg _))
    have h2 : py * Ey ≤ |py| * ((z - s) ^ 2 / c.R) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hEy' (abs_nonneg _))
    linarith
  have hpn : |(-px * sin b0 + py * cos b0)| ≤ |px| + |py| := by
    calc |(-px * sin b0 + py * cos b0)| ≤ |-px * sin b0| + |py * cos b0| := abs_add_le _ _
      _ ≤ |px| + |py| := by
          rw [abs_mul, abs_mul, abs_neg]
          exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _))
            (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
  have hterm2 : 2 * c.R * (cos δ - 1) * (-px * sin b0 + py * cos b0) ≤
      (|px| + |py|) * ((z - s) ^ 2 / c.R) := by
    have h0 : 0 ≤ 2 * c.R * (1 - cos δ) := mul_nonneg (by positivity) (by linarith)
    have h1 : 2 * c.R * (cos δ - 1) * (-px * sin b0 + py * cos b0) ≤
        2 * c.R * (1 - cos δ) * (|px| + |py|) := by
      calc 2 * c.R * (cos δ - 1) * (-px * sin b0 + py * cos b0)
          ≤ |2 * c.R * (cos δ - 1) * (-px * sin b0 + py * cos b0)| := le_abs_self _
        _ = 2 * c.R * (1 - cos δ) * |(-px * sin b0 + py * cos b0)| := by
            rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * c.R),
              abs_of_nonpos (by linarith : cos δ - 1 ≤ 0)]; ring
        _ ≤ 2 * c.R * (1 - cos δ) * (|px| + |py|) := mul_le_mul_of_nonneg_left hpn h0
    have h2 : 2 * c.R * (1 - cos δ) * (|px| + |py|) ≤
        2 * c.R * ((z - s) ^ 2 / (2 * c.R ^ 2)) * (|px| + |py|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcd (by positivity)
    have h3 : 2 * c.R * ((z - s) ^ 2 / (2 * c.R ^ 2)) * (|px| + |py|) =
        (|px| + |py|) * ((z - s) ^ 2 / c.R) := by field_simp
    linarith
  have hterm3 : 2 * c.R * (-sin b0 * Ex + cos b0 * Ey) ≤ 4 * (z - s) ^ 2 := by
    have h1 : -sin b0 * Ex + cos b0 * Ey ≤ 2 * ((z - s) ^ 2 / c.R) := by
      have a1 : -sin b0 * Ex ≤ (z - s) ^ 2 / c.R :=
        (le_abs_self _).trans (by rw [abs_mul, abs_neg]; exact (mul_le_of_le_one_left (abs_nonneg _) (abs_sin_le_one _)).trans hEx')
      have a2 : cos b0 * Ey ≤ (z - s) ^ 2 / c.R :=
        (le_abs_self _).trans (by rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans hEy')
      linarith
    have h2 : 2 * c.R * (2 * ((z - s) ^ 2 / c.R)) = 4 * (z - s) ^ 2 := by field_simp; ring
    calc 2 * c.R * (-sin b0 * Ex + cos b0 * Ey) ≤ 2 * c.R * (2 * ((z - s) ^ 2 / c.R)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * (z - s) ^ 2 := h2
  have hterm4 : 2 * c.R ^ 2 * (cos δ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hfinal : (3 * (|px| + |py|) / c.R + 12) * (z - s) ^ 2 =
      2 * ((|px| + |py|) * ((z - s) ^ 2 / c.R)) + (|px| + |py|) * ((z - s) ^ 2 / c.R) +
        4 * (z - s) ^ 2 + 8 * (z - s) ^ 2 := by
    field_simp; ring
  rw [← hδ, ← hpx, ← hpy, ← hb0, hfinal]
  linarith

end Manoeuvre

end Parking
