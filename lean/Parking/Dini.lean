/-
A Dini-type monotonicity criterion: a continuous function whose upper right slopes are
eventually below every positive number is antitone. This lets us avoid a.e. calculus for
Lipschitz headings.
-/
import Mathlib

open Set Filter Topology

namespace Parking

/-- If `f` is continuous on `[a, b]` and at every `x ∈ [a, b)` the right slopes of `f` are
eventually `< r` for every `r > 0`, then `f x ≤ f a` for all `x ∈ [a, b]`. -/
theorem le_of_slope_right_le_zero {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hslope : ∀ x ∈ Ico a b, ∀ r > 0, ∀ᶠ z in 𝓝[>] x, slope f x z < r) :
    ∀ x ∈ Icc a b, f x ≤ f a := by
  intro x hx
  -- compare with B(t) = f a + ε (t - a) for every ε > 0
  have key : ∀ ε > 0, f x ≤ f a + ε * (x - a) := by
    intro ε hε
    have := image_le_of_liminf_slope_right_lt_deriv_boundary' (f := f) (f' := fun _ => 0)
      (a := a) (b := b) hf
      (fun t ht r hr => (hslope t ht r hr).frequently)
      (B := fun t => f a + ε * (t - a)) (B' := fun _ => ε) (by simp)
      (by fun_prop)
      (fun t _ => by
        have : HasDerivAt (fun t => f a + ε * (t - a)) ε t := by
          simpa using ((hasDerivAt_id t).sub_const a).const_mul ε |>.const_add (f a)
        exact this.hasDerivWithinAt)
      (fun t _ _ => hε)
    exact this hx
  by_contra hcon
  push Not at hcon
  have hxa : 0 ≤ x - a := by linarith [hx.1]
  rcases eq_or_lt_of_le hxa with h0 | hpos
  · have : x = a := by linarith
    rw [this] at hcon; exact lt_irrefl _ hcon
  · set δ := f x - f a with hδ
    have hδpos : 0 < δ := by linarith
    have := key (δ / (2 * (x - a))) (by positivity)
    have : δ / (2 * (x - a)) * (x - a) = δ / 2 := by field_simp
    linarith [key (δ / (2 * (x - a))) (by positivity)]

/-- Antitone version. -/
theorem antitoneOn_of_slope_right_le_zero {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hslope : ∀ x ∈ Ico a b, ∀ r > 0, ∀ᶠ z in 𝓝[>] x, slope f x z < r) :
    AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  exact le_of_slope_right_le_zero (hf.mono (Icc_subset_Icc hx.1 le_rfl))
    (fun t ht r hr => hslope t ⟨le_trans hx.1 ht.1, ht.2⟩ r hr) y ⟨hxy, hy.2⟩

end Parking
