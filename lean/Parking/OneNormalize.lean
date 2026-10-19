/-
Normalisation of one-manoeuvre exits (Lemma `lem:mirror` of the paper): a parked heading is
within `ψ_fit` of a multiple of `π`, and shifting the heading by `2π j` or mirroring the slot
(`x ↦ L - x`, `ψ ↦ π - ψ`) reduces every exit to one with `|ψ(0)| ≤ ψ_fit`.
-/
import Parking.OneReverse

open Real Set

noncomputable section

namespace Parking

variable {c : Car} {m : ℝ}

/-- The vertical extent of a parked footprint is at most `H`. -/
theorem Parked.extent {S : Slot} {q : Config} (hp : Parked c S q) :
    c.len * |sin q.ψ| + c.w * |cos q.ψ| ≤ S.H c := by
  have hdb := c.db_pos
  have hb := c.b_pos
  have hw := c.w_pos
  have top : ∀ u v, -c.db ≤ u → u ≤ c.b → -(c.w / 2) ≤ v → v ≤ c.w / 2 →
      q.y + u * sin q.ψ + v * cos q.ψ ≤ S.H c :=
    fun u v h1 h2 h3 h4 => hp.2 _ ⟨u, v, h1, h2, h3, h4, rfl⟩
  have bot : ∀ u v, -c.db ≤ u → u ≤ c.b → -(c.w / 2) ≤ v → v ≤ c.w / 2 →
      0 ≤ q.y + u * sin q.ψ + v * cos q.ψ :=
    fun u v h1 h2 h3 h4 => hp.1.pt_y_nonneg h1 h2 h3 h4
  unfold Car.len
  rcases le_total 0 (sin q.ψ) with hs | hs <;> rcases le_total 0 (cos q.ψ) with hc | hc
  · have h1 := top c.b (c.w / 2) (by linarith) le_rfl (by linarith) le_rfl
    have h2 := bot (-c.db) (-(c.w / 2)) le_rfl (by linarith) le_rfl (by linarith)
    rw [abs_of_nonneg hs, abs_of_nonneg hc]; linarith
  · have h1 := top c.b (-(c.w / 2)) (by linarith) le_rfl le_rfl (by linarith)
    have h2 := bot (-c.db) (c.w / 2) le_rfl (by linarith) (by linarith) le_rfl
    rw [abs_of_nonneg hs, abs_of_nonpos hc]; linarith
  · have h1 := top (-c.db) (c.w / 2) le_rfl (by linarith) (by linarith) le_rfl
    have h2 := bot c.b (-(c.w / 2)) (by linarith) le_rfl le_rfl (by linarith)
    rw [abs_of_nonpos hs, abs_of_nonneg hc]; linarith
  · have h1 := top (-c.db) (-(c.w / 2)) le_rfl (by linarith) le_rfl (by linarith)
    have h2 := bot c.b (c.w / 2) (by linarith) le_rfl (by linarith) le_rfl
    rw [abs_of_nonpos hs, abs_of_nonpos hc]; linarith

/-- A parked heading is within `ψ_fit` of a multiple of `π`. -/
theorem OneAssumptions.heading_near (A : OneAssumptions c m) {L : ℝ} {q : Config}
    (hp : Parked c ⟨m, L⟩ q) : ∃ k : ℤ, |q.ψ - k * π| ≤ A.ψfit := by
  have hext := hp.extent
  have hH : Slot.H c ⟨m, L⟩ = m + c.w := rfl
  rw [hH] at hext
  refine ⟨round (q.ψ / π), ?_⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = q.ψ - (round (q.ψ / π) : ℤ) * π := ⟨_, rfl⟩
  rw [← hθ]
  have hθb : |θ| ≤ π / 2 := by
    have h := abs_sub_round (q.ψ / π)
    have e : θ = π * (q.ψ / π - (round (q.ψ / π) : ℤ)) := by
      rw [hθ]; field_simp
    rw [e, abs_mul, abs_of_pos pi_pos]
    have := mul_le_mul_of_nonneg_left h pi_pos.le
    linarith
  have hψ : q.ψ = θ + (round (q.ψ / π) : ℤ) * π := by rw [hθ]; ring
  have hs : |sin q.ψ| = |sin θ| := by
    rw [hψ, sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have hc : |cos q.ψ| = |cos θ| := by
    rw [hψ, cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  rw [hs, hc] at hext
  have hθ2 := abs_le.mp hθb
  have hsφ : |sin θ| = sin |θ| := by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h (by linarith [pi_pos]))]
    · rw [abs_of_nonpos h, sin_neg,
        abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith [pi_pos]))]
  have hcφ : |cos θ| = cos |θ| := by
    rw [cos_abs]; exact abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hθ2.1, hθ2.2⟩)
  rw [hsφ, hcφ] at hext
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = |θ| := ⟨_, rfl⟩
  rw [← hφ] at hext hθb ⊢
  by_contra hcon
  push Not at hcon
  have hfit := A.hψfit
  have hl := A.A2a
  have hca : 0 < cos A.ψfit := A.cos_ψfit_pos
  have hsx : 0 < sin (φ - A.ψfit) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [A.ψfit_pos, pi_pos])
  have hcx : 0 ≤ cos φ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, A.ψfit_pos], hθb⟩
  have hsφ1 : sin φ ≤ 1 := sin_le_one φ
  have hcd : cos (φ - A.ψfit) ≤ 1 := cos_le_one _
  have hid : (c.len * sin φ + c.w * cos φ) * cos A.ψfit =
      (m + c.w) * cos φ + c.len * sin (φ - A.ψfit) := by
    rw [sin_sub, ← hfit]; ring
  have hsum : cos A.ψfit ≤ cos φ + sin (φ - A.ψfit) := by
    have e : cos A.ψfit = cos φ * cos (φ - A.ψfit) + sin φ * sin (φ - A.ψfit) := by
      rw [← cos_sub]; ring_nf
    nlinarith [mul_nonneg hcx (sub_nonneg.2 hcd), mul_nonneg (sub_nonneg.2 hsφ1) hsx.le]
  have hH0 : (0:ℝ) ≤ m + c.w := by linarith [A.hm, c.w_pos]
  have h1 : (m + c.w) * cos A.ψfit < (c.len * sin φ + c.w * cos φ) * cos A.ψfit := by
    rw [hid]
    have := mul_lt_mul_of_pos_right hl hsx
    have := mul_le_mul_of_nonneg_left hsum hH0
    nlinarith
  have := lt_of_mul_lt_mul_right h1 hca.le
  linarith

/-! ### Shifted and mirrored configurations -/

namespace Config

/-- Shift of the heading by `2π j`. -/
def shift (q : Config) (j : ℤ) : Config := ⟨q.x, q.y, q.ψ + j * (2 * π)⟩

/-- Mirror image in the slot of length `L`. -/
def mirror (q : Config) (L : ℝ) : Config := ⟨L - q.x, q.y, π - q.ψ⟩

theorem shift_pt (q : Config) (j : ℤ) (u v : ℝ) : (q.shift j).pt u v = q.pt u v := by
  simp only [shift, pt, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

theorem mirror_pt (q : Config) (L u v : ℝ) :
    (q.mirror L).pt u v = (L - (q.pt u (-v)).1, (q.pt u (-v)).2) := by
  simp only [mirror, pt, cos_pi_sub, sin_pi_sub, Prod.mk.injEq]
  constructor <;> ring

end Config

theorem footprint_shift (q : Config) (j : ℤ) : footprint c (q.shift j) = footprint c q := by
  ext p
  simp only [footprint, mem_ofPred_eq, Config.shift_pt]

theorem Free.shift {S : Slot} {q : Config} (h : Free c S q) (j : ℤ) : Free c S (q.shift j) := by
  unfold Free; rw [footprint_shift]; exact h

theorem Parked.shift {S : Slot} {q : Config} (h : Parked c S q) (j : ℤ) :
    Parked c S (q.shift j) := ⟨h.1.shift j, by rw [footprint_shift]; exact h.2⟩

theorem InLane.shift {S : Slot} {q : Config} (h : InLane c S q) (j : ℤ) :
    InLane c S (q.shift j) := by
  refine ⟨by rw [footprint_shift]; exact h.1, ?_⟩
  obtain ⟨k, hk⟩ := h.2
  refine ⟨k + 2 * j, ?_⟩
  simp only [Config.shift, hk]; push_cast; ring

/-- The mirror image of an obstacle point is an obstacle point. -/
theorem mirror_mem_obstacle {L : ℝ} {p : ℝ × ℝ} (hp : p ∈ obstacle c ⟨m, L⟩) :
    (L - p.1, p.2) ∈ obstacle c ⟨m, L⟩ := by
  rcases hp with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr ⟨show L < L - p.1 by linarith [h.1], h.2.1, h.2.2⟩
  · exact Or.inl (Or.inr ⟨show L - p.1 < 0 by linarith [h.1], h.2.1, h.2.2⟩)

theorem Free.mirror {L : ℝ} {q : Config} (hf : Free c ⟨m, L⟩ q) :
    Free c ⟨m, L⟩ (q.mirror L) := by
  rw [Free, Set.disjoint_left]
  rintro p ⟨u, v, h1, h2, h3, h4, rfl⟩ hob
  have hfp : q.pt u (-v) ∈ footprint c q := ⟨u, -v, h1, h2, by linarith, by linarith, rfl⟩
  have hob' : q.pt u (-v) ∈ obstacle c ⟨m, L⟩ := by
    have := mirror_mem_obstacle hob
    rw [Config.mirror_pt] at this
    simpa using this
  exact Set.disjoint_left.mp hf hfp hob'

theorem Parked.mirror {L : ℝ} {q : Config} (h : Parked c ⟨m, L⟩ q) :
    Parked c ⟨m, L⟩ (q.mirror L) := by
  refine ⟨h.1.mirror, ?_⟩
  rintro p ⟨u, v, h1, h2, h3, h4, rfl⟩
  rw [Config.mirror_pt]
  exact h.2 (q.pt u (-v)) ⟨u, -v, h1, h2, by linarith, by linarith, rfl⟩

theorem InLane.mirror {L : ℝ} {q : Config} (h : InLane c ⟨m, L⟩ q) :
    InLane c ⟨m, L⟩ (q.mirror L) := by
  refine ⟨?_, ?_⟩
  · rintro p ⟨u, v, h1, h2, h3, h4, rfl⟩
    rw [Config.mirror_pt]
    exact h.1 (q.pt u (-v)) ⟨u, -v, h1, h2, by linarith, by linarith, rfl⟩
  · obtain ⟨k, hk⟩ := h.2
    refine ⟨1 - k, ?_⟩
    simp only [Config.mirror, hk]; push_cast; ring

/-! ### Shifted and mirrored manoeuvres -/

namespace Manoeuvre

variable (M : Manoeuvre c)

/-- Shift of the heading by `2π j`. -/
def shift (j : ℤ) : Manoeuvre c where
  d := M.d
  hd := M.hd
  len := M.len
  len_nonneg := M.len_nonneg
  x0 := M.x0
  y0 := M.y0
  ψ := fun s => M.ψ s + j * (2 * π)
  lip := fun s t => by
    have := M.lip s t
    simp only [add_sub_add_right_eq_sub]
    exact this

theorem shift_config (j : ℤ) (s : ℝ) : (M.shift j).config s = (M.config s).shift j := by
  simp only [config, X, Y, shift, Config.shift, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

/-- Mirror image in the slot of length `L`. -/
def mirror (L : ℝ) : Manoeuvre c where
  d := M.d
  hd := M.hd
  len := M.len
  len_nonneg := M.len_nonneg
  x0 := L - M.x0
  y0 := M.y0
  ψ := fun s => π - M.ψ s
  lip := fun s t => by
    have := M.lip s t
    rw [show π - M.ψ s - (π - M.ψ t) = -(M.ψ s - M.ψ t) by ring, abs_neg]
    exact this

theorem mirror_config (L s : ℝ) : (M.mirror L).config s = (M.config s).mirror L := by
  simp only [config, X, Y, mirror, Config.mirror, cos_pi_sub, sin_pi_sub,
    intervalIntegral.integral_neg, Config.mk.injEq]
  refine ⟨by ring, trivial, trivial⟩

end Manoeuvre

/-- **Normalised lower bound for one manoeuvre**: every one-manoeuvre exit needs `L ≥ Λ₁`. -/
theorem exit_one_lower (A : OneAssumptions c m) {L : ℝ} (M : Manoeuvre c)
    (hfree : ∀ s ∈ Icc (0 : ℝ) M.len, Free c ⟨m, L⟩ (M.config s))
    (hstart : Parked c ⟨m, L⟩ M.start) (hend : InLane c ⟨m, L⟩ M.finish) : A.Λ₁ ≤ L := by
  have key : ∀ M' : Manoeuvre c, (∀ s ∈ Icc (0 : ℝ) M'.len, Free c ⟨m, L⟩ (M'.config s)) →
      Parked c ⟨m, L⟩ M'.start → InLane c ⟨m, L⟩ M'.finish → |M'.ψ 0| ≤ A.ψfit → A.Λ₁ ≤ L := by
    intro M' h1 h2 h3 h4
    rcases M'.hd with hd | hd
    · exact exit_forward_lower A M' hd h1 h2 h3 h4
    · exact exit_reverse_lower A M' hd h1 h2 h3 h4
  obtain ⟨k, hk⟩ := A.heading_near hstart
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · refine key (M.shift (-j)) (fun s hs => ?_) ?_ ?_ ?_
    · rw [M.shift_config]; exact (hfree s hs).shift _
    · unfold Manoeuvre.start; rw [M.shift_config]; exact hstart.shift _
    · unfold Manoeuvre.finish; rw [M.shift_config]; exact hend.shift _
    · have e : (M.shift (-j)).ψ 0 = M.ψ 0 - k * π := by
        simp only [Manoeuvre.shift, hj]; push_cast; ring
      rw [e]; exact hk
  · refine key ((M.mirror L).shift j) (fun s hs => ?_) ?_ ?_ ?_
    · rw [Manoeuvre.shift_config, Manoeuvre.mirror_config]; exact (hfree s hs).mirror.shift _
    · unfold Manoeuvre.start
      rw [Manoeuvre.shift_config, Manoeuvre.mirror_config]; exact hstart.mirror.shift _
    · unfold Manoeuvre.finish
      rw [Manoeuvre.shift_config, Manoeuvre.mirror_config]; exact hend.mirror.shift _
    · have e : ((M.mirror L).shift j).ψ 0 = -(M.ψ 0 - k * π) := by
        simp only [Manoeuvre.shift, Manoeuvre.mirror, hj]; push_cast; ring
      rw [e, abs_neg]; exact hk

end Parking
