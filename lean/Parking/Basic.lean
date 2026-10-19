/-
Elementary properties of the model: monotonicity of feasibility in the slot length
and in the number of manoeuvres.
-/
import Parking.Model

open Real Set

noncomputable section

namespace Parking

variable {c : Car}

theorem obstacle_mono {m L L' : ℝ} (h : L ≤ L') :
    obstacle c ⟨m, L'⟩ ⊆ obstacle c ⟨m, L⟩ := by
  intro p hp
  simp only [obstacle, Slot.H, mem_union, mem_ofPred_eq] at hp ⊢
  rcases hp with (hp | hp) | hp
  · exact Or.inl (Or.inl hp)
  · exact Or.inl (Or.inr hp)
  · exact Or.inr ⟨lt_of_le_of_lt h hp.1, hp.2.1, hp.2.2⟩

theorem Free.mono {m L L' : ℝ} (h : L ≤ L') {q : Config} (hq : Free c ⟨m, L⟩ q) :
    Free c ⟨m, L'⟩ q :=
  hq.mono_right (obstacle_mono h)

theorem Parked.mono {m L L' : ℝ} (h : L ≤ L') {q : Config} (hq : Parked c ⟨m, L⟩ q) :
    Parked c ⟨m, L'⟩ q :=
  ⟨hq.1.mono h, by simpa [Slot.H] using hq.2⟩

theorem InLane.slot_indep {m L L' : ℝ} {q : Config} (hq : InLane c ⟨m, L⟩ q) :
    InLane c ⟨m, L'⟩ q := by
  simpa [InLane, Slot.H] using hq

/-- Feasibility is monotone in the slot length. -/
theorem Feasible.mono_L {m L L' : ℝ} {n : ℕ} (h : L ≤ L') (hf : Feasible c m n L) :
    Feasible c m n L' := by
  obtain ⟨μ, M₀, M₁, h0, h1, hlen, hch, hfree, hlane, hpark⟩ := hf
  exact ⟨μ, M₀, M₁, h0, h1, hlen, hch,
    fun M hM s hs => (hfree M hM s hs).mono h, hlane.slot_indep, hpark.mono h⟩

/-- Feasibility is monotone in the number of manoeuvres. -/
theorem Feasible.mono_n {m L : ℝ} {n n' : ℕ} (h : n ≤ n') (hf : Feasible c m n L) :
    Feasible c m n' L := by
  obtain ⟨μ, M₀, M₁, h0, h1, hlen, rest⟩ := hf
  exact ⟨μ, M₀, M₁, h0, h1, hlen.trans h, rest⟩

/-- `Lmin` is non-increasing in the number of manoeuvres (whenever the feasible set for
`n` manoeuvres is nonempty). -/
theorem Lmin_antitone {m L : ℝ} {n n' : ℕ} (h : n ≤ n') (hL : 0 < L) (hf : Feasible c m n L) :
    Lmin c m n' ≤ Lmin c m n := by
  unfold Lmin
  apply csInf_le_csInf
  · exact ⟨0, fun x hx => le_of_lt hx.1⟩
  · exact ⟨L, hL, hf⟩
  · intro x hx; exact ⟨hx.1, hx.2.mono_n h⟩

end Parking
