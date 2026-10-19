/-
General tools for the lower bounds: first hitting times of continuous functions, and
monotonicity from second-order increment bounds (via the Dini lemma).
Also increment bounds for the turning centres.
-/
import Parking.Dini
import Parking.Centres

open Real Set Filter Topology

noncomputable section

namespace Parking

/-- First time a continuous function reaches a level from below. -/
theorem exists_first_ge {f : ℝ → ℝ} (hf : Continuous f) {a t c : ℝ} (hat : a ≤ t)
    (ha : f a < c) (ht : c ≤ f t) :
    ∃ t' ∈ Ioc a t, f t' = c ∧ ∀ s ∈ Ico a t', f s < c := by
  set T := {s ∈ Icc a t | c ≤ f s} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le continuous_const hf)
  have hTne : T.Nonempty := ⟨t, ⟨hat, le_rfl⟩, ht⟩
  have hTb : BddBelow T := ⟨a, fun s hs => hs.1.1⟩
  have hmem : sInf T ∈ T := hTc.csInf_mem hTne hTb
  have hlow : ∀ s ∈ Ico a (sInf T), f s < c := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hsT : s ∈ T := ⟨⟨hs.1, le_trans hs.2.le hmem.1.2⟩, hcon⟩
    have := csInf_le hTb hsT
    linarith [hs.2]
  have hat' : a < sInf T := by
    rcases eq_or_lt_of_le hmem.1.1 with h | h
    · have h2 : c ≤ f (sInf T) := hmem.2
      rw [← h] at h2
      linarith
    · exact h
  refine ⟨sInf T, ⟨hat', hmem.1.2⟩, ?_, hlow⟩
  rcases eq_or_lt_of_le hmem.2 with h | h
  · exact h.symm
  · exfalso
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hmem.1.1 hf.continuousOn ⟨ha.le, h.le⟩
    have hst : s < sInf T := lt_of_le_of_ne hs.2 (by rintro rfl; linarith)
    linarith [hlow s ⟨hs.1, hst⟩]

/-- First time a continuous function reaches a level from above. -/
theorem exists_first_le {f : ℝ → ℝ} (hf : Continuous f) {a t c : ℝ} (hat : a ≤ t)
    (ha : c < f a) (ht : f t ≤ c) :
    ∃ t' ∈ Ioc a t, f t' = c ∧ ∀ s ∈ Ico a t', c < f s := by
  obtain ⟨t', ht', h1, h2⟩ := exists_first_ge (f := fun s => -f s) hf.neg hat
    (show -f a < -c by linarith) (show -c ≤ -f t by linarith)
  exact ⟨t', ht', by linarith, fun s hs => by linarith [h2 s hs]⟩

/-- First exit of a continuous function from an open interval. -/
theorem exists_first_exit {f : ℝ → ℝ} (hf : Continuous f) {a t lo hi : ℝ} (hat : a ≤ t)
    (ha1 : lo < f a) (ha2 : f a < hi) (ht : f t ≤ lo ∨ hi ≤ f t) :
    ∃ t' ∈ Ioc a t, (f t' = lo ∨ f t' = hi) ∧ ∀ s ∈ Ico a t', lo < f s ∧ f s < hi := by
  have hg : Continuous (fun s => max (lo - f s) (f s - hi)) := by fun_prop
  obtain ⟨t', ht', h1, h2⟩ := exists_first_ge hg hat (c := 0)
    (max_lt (by linarith) (by linarith))
    (by rcases ht with h | h
        · exact le_max_of_le_left (by linarith)
        · exact le_max_of_le_right (by linarith))
  refine ⟨t', ht', ?_, fun s hs => ?_⟩
  · rcases le_total (lo - f t') (f t' - hi) with h | h
    · rw [max_eq_right h] at h1; right; linarith
    · rw [max_eq_left h] at h1; left; linarith
  · have := h2 s hs
    exact ⟨by linarith [le_max_left (lo - f s) (f s - hi)],
      by linarith [le_max_right (lo - f s) (f s - hi)]⟩

/-- A second-order increment bound gives small right slopes. -/
theorem eventually_slope_lt_of_sq {f : ℝ → ℝ} {x K : ℝ}
    (h : ∀ z, x < z → f z - f x ≤ K * (z - x) ^ 2) :
    ∀ r > 0, ∀ᶠ z in 𝓝[>] x, slope f x z < r := by
  intro r hr
  have hK : ∀ z, x < z → slope f x z ≤ K * (z - x) := by
    intro z hz
    rw [slope_def_field, div_le_iff₀ (by linarith)]
    have h1 := h z hz
    have h2 : K * (z - x) ^ 2 = K * (z - x) * (z - x) := by ring
    linarith
  have hc : Continuous (fun z : ℝ => K * (z - x)) := by fun_prop
  have hev : ∀ᶠ z in 𝓝[>] x, K * (z - x) < r :=
    ((hc.tendsto' x 0 (by simp)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hr)
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hzx
  exact lt_of_le_of_lt (hK z hzx) hz

/-- Monotonicity from second-order increment bounds. -/
theorem antitoneOn_of_sq_incr {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (h : ∀ x ∈ Ico a b, ∃ K, ∀ z, x < z → f z - f x ≤ K * (z - x) ^ 2) :
    AntitoneOn f (Icc a b) :=
  antitoneOn_of_slope_right_le_zero hf fun x hx => by
    obtain ⟨K, hK⟩ := h x hx
    exact eventually_slope_lt_of_sq hK

/-- Variant of `eventually_slope_lt_of_sq` where the increment bound is only known up to `b`. -/
theorem eventually_slope_lt_of_sq' {f : ℝ → ℝ} {x b K : ℝ} (hxb : x < b)
    (h : ∀ z, x < z → z ≤ b → f z - f x ≤ K * (z - x) ^ 2) :
    ∀ r > 0, ∀ᶠ z in 𝓝[>] x, slope f x z < r := by
  intro r hr
  have hc : Continuous (fun z : ℝ => K * (z - x)) := by fun_prop
  have hev : ∀ᶠ z in 𝓝[>] x, K * (z - x) < r :=
    ((hc.tendsto' x 0 (by simp)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hr)
  have hb : ∀ᶠ z in 𝓝[>] x, z < b := (eventually_lt_nhds hxb).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, hb, self_mem_nhdsWithin] with z hz hzb hzx
  have hzx' : x < z := hzx
  have hK : slope f x z ≤ K * (z - x) := by
    rw [slope_def_field, div_le_iff₀ (by linarith)]
    have h1 := h z hzx' hzb.le
    have h2 : K * (z - x) ^ 2 = K * (z - x) * (z - x) := by ring
    linarith
  exact lt_of_le_of_lt hK hz

/-- Monotonicity from second-order increment bounds known only inside the interval. -/
theorem antitoneOn_of_sq_incr' {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (h : ∀ x ∈ Ico a b, ∃ K, ∀ z, x < z → z ≤ b → f z - f x ≤ K * (z - x) ^ 2) :
    AntitoneOn f (Icc a b) :=
  antitoneOn_of_slope_right_le_zero hf fun x hx => by
    obtain ⟨K, hK⟩ := h x hx
    exact eventually_slope_lt_of_sq' hx.2 hK

namespace Manoeuvre

variable {c : Car} (M : Manoeuvre c)

theorem continuous_C'x : Continuous M.C'x :=
  M.continuous_X.add (continuous_const.mul (continuous_sin.comp M.continuous_ψ))

theorem continuous_C'y : Continuous M.C'y :=
  M.continuous_Y.sub (continuous_const.mul (continuous_cos.comp M.continuous_ψ))

theorem one_sub_cos_incr (s z : ℝ) (hsz : s ≤ z) :
    c.R * (1 - cos (M.ψ z - M.ψ s)) ≤ (z - s) ^ 2 / (2 * c.R) := by
  have hR := c.R_pos
  have hδb := M.ψ_incr s z hsz
  have h1 := one_sub_sq_div_two_le_cos (x := M.ψ z - M.ψ s)
  have h2 : (M.ψ z - M.ψ s) ^ 2 ≤ ((z - s) / c.R) ^ 2 := by
    have := sq_le_sq' (abs_le.mp hδb).1 (abs_le.mp hδb).2; simpa using this
  have h3 : c.R * (((z - s) / c.R) ^ 2 / 2) = (z - s) ^ 2 / (2 * c.R) := by field_simp
  have h4 : c.R * (1 - cos (M.ψ z - M.ψ s)) ≤ c.R * (((z - s) / c.R) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hR.le
  linarith

theorem one_sub_cos_nonneg (s z : ℝ) : 0 ≤ 1 - cos (M.ψ z - M.ψ s) := by
  linarith [cos_le_one (M.ψ z - M.ψ s)]

/-- `|R sin(ψ z - ψ s)| ≤ z - s`. -/
theorem R_sin_incr (s z : ℝ) (hsz : s ≤ z) : |c.R * sin (M.ψ z - M.ψ s)| ≤ z - s := by
  have hR := c.R_pos
  rw [abs_mul, abs_of_pos hR]
  have h1 := (abs_sin_le_abs (x := M.ψ z - M.ψ s)).trans (M.ψ_incr s z hsz)
  calc c.R * |sin (M.ψ z - M.ψ s)| ≤ c.R * ((z - s) / c.R) := mul_le_mul_of_nonneg_left h1 hR.le
    _ = z - s := by field_simp

/-- Increment of the height of the left centre. -/
theorem Cy_incr (s z : ℝ) (hsz : s ≤ z) :
    M.Cy z - M.Cy s ≤ sin (M.ψ s) * (M.d * (z - s) - c.R * sin (M.ψ z - M.ψ s)) +
      2 * (z - s) ^ 2 / c.R := by
  have hR := c.R_pos
  have hY := M.Y_incr s z hsz
  have hcd := M.one_sub_cos_incr s z hsz
  have hcd0 := M.one_sub_cos_nonneg s z
  have hca : cos (M.ψ z) = cos (M.ψ s) * cos (M.ψ z - M.ψ s) - sin (M.ψ s) * sin (M.ψ z - M.ψ s) := by
    rw [← cos_add]; ring_nf
  have h1 : M.Y z - M.Y s ≤ M.d * (z - s) * sin (M.ψ s) + (z - s) ^ 2 / c.R := by
    have := (abs_le.mp hY).2; linarith
  have h2 : c.R * (cos (M.ψ s) * (cos (M.ψ z - M.ψ s) - 1)) ≤ c.R * (1 - cos (M.ψ z - M.ψ s)) := by
    apply mul_le_mul_of_nonneg_left _ hR.le
    have := neg_one_le_cos (M.ψ s)
    nlinarith
  have h3 : (z - s) ^ 2 / (2 * c.R) ≤ (z - s) ^ 2 / c.R :=
    div_le_div_of_nonneg_left (sq_nonneg _) hR (by linarith)
  have h4 : 2 * (z - s) ^ 2 / c.R = (z - s) ^ 2 / c.R + (z - s) ^ 2 / c.R := by ring
  unfold Cy
  rw [hca]
  nlinarith

/-- Increment of the abscissa of the right centre (lower bound). -/
theorem C'x_incr (s z : ℝ) (hsz : s ≤ z) :
    cos (M.ψ s) * (M.d * (z - s) + c.R * sin (M.ψ z - M.ψ s)) - 2 * (z - s) ^ 2 / c.R ≤
      M.C'x z - M.C'x s := by
  have hR := c.R_pos
  have hX := M.X_incr s z hsz
  have hcd := M.one_sub_cos_incr s z hsz
  have hcd0 := M.one_sub_cos_nonneg s z
  have hsa : sin (M.ψ z) = sin (M.ψ s) * cos (M.ψ z - M.ψ s) + cos (M.ψ s) * sin (M.ψ z - M.ψ s) := by
    rw [← sin_add]; ring_nf
  have h1 : M.d * (z - s) * cos (M.ψ s) - (z - s) ^ 2 / c.R ≤ M.X z - M.X s := by
    have := (abs_le.mp hX).1; linarith
  have h2 : -(c.R * (1 - cos (M.ψ z - M.ψ s))) ≤ c.R * (sin (M.ψ s) * (cos (M.ψ z - M.ψ s) - 1)) := by
    rw [← mul_neg]
    apply mul_le_mul_of_nonneg_left _ hR.le
    have := sin_le_one (M.ψ s)
    nlinarith
  have h3 : (z - s) ^ 2 / (2 * c.R) ≤ (z - s) ^ 2 / c.R :=
    div_le_div_of_nonneg_left (sq_nonneg _) hR (by linarith)
  have h4 : 2 * (z - s) ^ 2 / c.R = (z - s) ^ 2 / c.R + (z - s) ^ 2 / c.R := by ring
  unfold C'x
  rw [hsa]
  nlinarith

/-- Increment of the height of the body point `(0, v)` for `|v| ≤ R`. -/
theorem Yv_incr (v : ℝ) (hv : |v| ≤ c.R) (s z : ℝ) (hsz : s ≤ z) :
    (M.Y z + v * cos (M.ψ z)) - (M.Y s + v * cos (M.ψ s)) ≤
      sin (M.ψ s) * (M.d * (z - s) - v * sin (M.ψ z - M.ψ s)) + 2 * (z - s) ^ 2 / c.R := by
  have hR := c.R_pos
  have hY := M.Y_incr s z hsz
  have hcd := M.one_sub_cos_incr s z hsz
  have hcd0 := M.one_sub_cos_nonneg s z
  have hca : cos (M.ψ z) = cos (M.ψ s) * cos (M.ψ z - M.ψ s) -
      sin (M.ψ s) * sin (M.ψ z - M.ψ s) := by
    rw [← cos_add]; ring_nf
  have h1 : M.Y z - M.Y s ≤ M.d * (z - s) * sin (M.ψ s) + (z - s) ^ 2 / c.R := by
    have := (abs_le.mp hY).2; linarith
  have hvc : -c.R ≤ v * cos (M.ψ s) := by
    have : |v * cos (M.ψ s)| ≤ c.R := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)).trans hv
    linarith [neg_abs_le (v * cos (M.ψ s))]
  have h2 : v * cos (M.ψ s) * (cos (M.ψ z - M.ψ s) - 1) ≤ c.R * (1 - cos (M.ψ z - M.ψ s)) := by
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ v * cos (M.ψ s) + c.R)
      (by linarith : cos (M.ψ z - M.ψ s) - 1 ≤ 0)
    nlinarith
  have h3 : (z - s) ^ 2 / (2 * c.R) ≤ (z - s) ^ 2 / c.R :=
    div_le_div_of_nonneg_left (sq_nonneg _) hR (by linarith)
  have h4 : 2 * (z - s) ^ 2 / c.R = (z - s) ^ 2 / c.R + (z - s) ^ 2 / c.R := by ring
  rw [hca]
  nlinarith

end Manoeuvre

end Parking
