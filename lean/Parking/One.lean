/-
The one-manoeuvre theorem (Theorem `thm:one`): under `OneAssumptions`,
parking with one manoeuvre is feasible iff `L ≥ Λ₁`.
-/
import Parking.OneUpper
import Parking.OneNormalize

open Real Set

noncomputable section

namespace Parking

variable {c : Car} {m : ℝ}

/-- **Theorem (one manoeuvre).** -/
theorem feasible_one_iff (A : OneAssumptions c m) (L : ℝ) :
    Feasible c m 1 L ↔ A.Λ₁ ≤ L := by
  constructor
  · intro hf
    by_contra hlt
    push Not at hlt
    obtain ⟨μ, M₀, M₁, h0, h1, hlen, hch, hfree, hlane, hpark⟩ := hf
    -- a motion with at most one manoeuvre and a head is a single manoeuvre
    have hμ : μ = [M₀] := by
      cases μ with
      | nil => simp at h0
      | cons M rest =>
        cases rest with
        | nil => simp at h0; rw [h0]
        | cons _ _ => simp at hlen
    subst hμ
    have hM : M₁ = M₀ := by simpa using h1.symm
    subst hM
    -- reverse it into an exit manoeuvre
    have hfreeR : ∀ s ∈ Icc (0 : ℝ) M₁.reverse.len, Free c ⟨m, L⟩ (M₁.reverse.config s) := by
      intro s hs
      rw [Manoeuvre.reverse_config]
      exact hfree M₁ (by simp) _ ⟨by simp [Manoeuvre.reverse] at hs ⊢; linarith [hs.2],
        by simp [Manoeuvre.reverse] at hs ⊢; linarith [hs.1]⟩
    have hstart : Parked c ⟨m, L⟩ M₁.reverse.start := by rw [Manoeuvre.reverse_start]; exact hpark
    have hend : InLane c ⟨m, L⟩ M₁.reverse.finish := by rw [Manoeuvre.reverse_finish]; exact hlane
    exact absurd (exit_one_lower A M₁.reverse hfreeR hstart hend) (not_le.mpr hlt)
  · intro hL
    exact (feasible_one_at_Λ₁ A).mono_L hL


theorem OneAssumptions.Λ₁_pos (A : OneAssumptions c m) : 0 < A.Λ₁ := by
  unfold OneAssumptions.Λ₁
  have h1 := A.A6b
  have hr := A.r_ge_H
  have hlt : (c.r - (m + c.w)) ^ 2 < c.ρ ^ 2 := by
    have := c.r_sq; have := c.ρ_sq; have := A.A1a; have := c.db_pos; have := A.r_pos
    have := A.ρ_pos; have := A.hm; have := c.w_pos
    nlinarith
  have := Real.sqrt_pos.mpr (by linarith : (0:ℝ) < c.ρ ^ 2 - (c.r - (m + c.w)) ^ 2)
  linarith

/-- **Corollary**: `L_min(1) = Λ₁`. -/
theorem Lmin_one (A : OneAssumptions c m) : Lmin c m 1 = A.Λ₁ := by
  have hpos := A.Λ₁_pos
  unfold Lmin
  have e : {L | 0 < L ∧ Feasible c m 1 L} = Ici A.Λ₁ := by
    ext L
    simp only [mem_ofPred_eq, mem_Ici, feasible_one_iff A]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hpos h, h⟩⟩
  rw [e, csInf_Ici]

end Parking
