/-
Zero margin is degenerate: a car with positive rear overhang can never become flush
with a rigid curb (Proposition `prop:flush` of the paper).
-/
import Parking.Kinematics

open Real Set Filter Topology

noncomputable section

namespace Parking

variable {c : Car}

/-- `c0 = min (d_b, b, w/2)`. -/
def Car.c0 (c : Car) : ℝ := min c.db (min c.b (c.w / 2))

theorem Car.c0_pos (c : Car) : 0 < c.c0 :=
  lt_min c.db_pos (lt_min c.b_pos (by linarith [c.w_pos]))

theorem Car.c0_le_db (c : Car) : c.c0 ≤ c.db := min_le_left _ _
theorem Car.c0_le_b (c : Car) : c.c0 ≤ c.b := (min_le_right _ _).trans (min_le_left _ _)
theorem Car.c0_le_hw (c : Car) : c.c0 ≤ c.w / 2 := (min_le_right _ _).trans (min_le_right _ _)

/-- Flush with the curb: parallel to it and touching it with the whole side. -/
def Flush (c : Car) (q : Config) : Prop := sin q.ψ = 0 ∧ q.y = c.w / 2

/-- Curb constraint: lower bound on the height of the rear axle. -/
theorem Free.curb_lower {S : Slot} {q : Config} (h : Free c S q) :
    c.c0 * |sin q.ψ| - c.w / 2 * (1 - |cos q.ψ|) ≤ q.y - c.w / 2 := by
  -- choose the side of the car facing the curb
  have hw := c.w_pos
  set v : ℝ := if 0 ≤ cos q.ψ then -(c.w / 2) else c.w / 2 with hv
  have hv1 : -(c.w / 2) ≤ v := by rw [hv]; split_ifs <;> linarith
  have hv2 : v ≤ c.w / 2 := by rw [hv]; split_ifs <;> linarith
  have hvc : v * cos q.ψ = -(c.w / 2) * |cos q.ψ| := by
    rw [hv]; split_ifs with hc
    · rw [abs_of_nonneg hc]
    · push Not at hc; rw [abs_of_neg hc]; ring
  have h1 := h.pt_y_nonneg (u := -c.db) (v := v) (by linarith) (by linarith [c.db_pos, c.b_pos]) hv1 hv2
  have h2 := h.pt_y_nonneg (u := c.b) (v := v) (by linarith [c.db_pos, c.b_pos]) le_rfl hv1 hv2
  simp only [Config.pt] at h1 h2
  rw [hvc] at h1 h2
  rcases le_total 0 (sin q.ψ) with hs | hs
  · rw [abs_of_nonneg hs]
    nlinarith [c.c0_le_db, c.c0_le_b]
  · rw [abs_of_nonpos hs]
    nlinarith [c.c0_le_db, c.c0_le_b]

/-- In the regime `|sin ψ| ≤ c0 / w` the curb gives `(c0/2) |sin ψ| ≤ y - w/2`. -/
theorem Free.regime {S : Slot} {q : Config} (h : Free c S q) (hs : |sin q.ψ| ≤ c.c0 / c.w) :
    c.c0 / 2 * |sin q.ψ| ≤ q.y - c.w / 2 := by
  have hw := c.w_pos
  have h1 := h.curb_lower
  -- 1 - |cos| ≤ sin^2
  have hsc : 1 - |cos q.ψ| ≤ sin q.ψ ^ 2 := by
    have hcs : sin q.ψ ^ 2 + cos q.ψ ^ 2 = 1 := sin_sq_add_cos_sq q.ψ
    have habs : |cos q.ψ| ≤ 1 := abs_cos_le_one q.ψ
    have h0 : 0 ≤ |cos q.ψ| := abs_nonneg _
    have : cos q.ψ ^ 2 = |cos q.ψ| ^ 2 := (sq_abs _).symm
    nlinarith
  have hs2 : sin q.ψ ^ 2 = |sin q.ψ| ^ 2 := (sq_abs _).symm
  have hsabs : 0 ≤ |sin q.ψ| := abs_nonneg _
  have hkey : c.w / 2 * sin q.ψ ^ 2 ≤ c.c0 / 2 * |sin q.ψ| := by
    rw [hs2]
    have : c.w * |sin q.ψ| ≤ c.c0 := by
      have := mul_le_mul_of_nonneg_left hs (le_of_lt hw)
      rwa [mul_div_cancel₀ _ (ne_of_gt hw)] at this
    nlinarith
  nlinarith

end Parking

namespace Parking

variable {c : Car}

/-- Backward propagation of flushness along a single free manoeuvre. -/
theorem Manoeuvre.flush_propagates {S : Slot} (M : Manoeuvre c)
    (hfree : ∀ s ∈ Icc (0 : ℝ) M.len, Free c S (M.config s))
    (hend : Flush c M.finish) :
    ∀ s ∈ Icc (0 : ℝ) M.len, Flush c (M.config s) := by
  classical
  set T := M.len with hT
  -- the set of times from which the motion is flush until the end
  set A : Set ℝ := {s | s ∈ Icc 0 T ∧ ∀ t ∈ Icc s T, Flush c (M.config t)} with hA
  have hTA : T ∈ A := ⟨⟨M.len_nonneg, le_rfl⟩, fun t ht => by
      have : t = T := le_antisymm ht.2 ht.1
      rw [this]; exact hend⟩
  have hbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
  set s0 := sInf A with hs0
  have hs0_le : s0 ≤ T := csInf_le hbdd hTA
  have hs0_nonneg : 0 ≤ s0 := le_csInf ⟨T, hTA⟩ fun s hs => hs.1.1
  -- continuity facts
  have hcψ := M.continuous_ψ
  have hcY := M.continuous_Y
  -- flushness holds on (s0, T]
  have hflush_after : ∀ t ∈ Ioc s0 T, Flush c (M.config t) := by
    intro t ht
    obtain ⟨s, hsA, hst⟩ := exists_lt_of_csInf_lt ⟨T, hTA⟩ ht.1
    exact hsA.2 t ⟨le_of_lt hst, ht.2⟩
  -- closedness: flushness at s0
  have hflush_s0 : Flush c (M.config s0) := by
    rcases eq_or_lt_of_le hs0_le with h | h
    · rw [h]; exact hend
    · -- approach s0 from the right
      have hlim : Tendsto (fun t => (sin (M.ψ t), M.Y t)) (𝓝[>] s0)
          (𝓝 (sin (M.ψ s0), M.Y s0)) :=
        ((continuous_sin.comp hcψ).prodMk hcY).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ t in 𝓝[>] s0, (sin (M.ψ t), M.Y t) = (0, c.w / 2) := by
        have : Ioo s0 T ∈ 𝓝[>] s0 := Ioo_mem_nhdsGT h
        filter_upwards [this] with t ht
        have := hflush_after t ⟨ht.1, le_of_lt ht.2⟩
        simp only [Flush, Manoeuvre.config] at this
        exact Prod.ext this.1 this.2
      have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hev))
      simp only [Prod.mk.injEq] at this
      exact ⟨this.1, this.2⟩
  -- show s0 = 0, by contradiction
  have hc0 := c.c0_pos
  have hw := c.w_pos
  by_cases hz : s0 = 0
  · intro s hs
    rcases eq_or_lt_of_le hs.1 with h' | h'
    · rw [← h']; rw [hz] at hflush_s0; exact hflush_s0
    · exact hflush_after s ⟨by rw [hz]; exact h', hs.2⟩
  exfalso
  have hs0pos : 0 < s0 := lt_of_le_of_ne hs0_nonneg (Ne.symm hz)
  -- near s0 the heading is small
  have hsin0 : sin (M.ψ s0) = 0 := hflush_s0.1
  have hY0 : M.Y s0 = c.w / 2 := hflush_s0.2
  have hcont : ContinuousAt (fun t => sin (M.ψ t)) s0 :=
    (continuous_sin.comp hcψ).continuousAt
  have hpos : 0 < c.c0 / c.w := div_pos hc0 hw
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hcont (c.c0 / c.w) hpos
  set η := min (ε / 2) s0 with hη
  have hηpos : 0 < η := lt_min (by linarith) hs0pos
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηs0 : η ≤ s0 := min_le_right _ _
  -- regime on [s0 - η, s0]
  have hreg : ∀ t ∈ Icc (s0 - η) s0, |sin (M.ψ t)| ≤ c.c0 / c.w := by
    intro t ht
    have hd : dist t s0 < ε := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2])]; linarith [ht.1]
    have := hball hd
    rw [Real.dist_eq, hsin0, sub_zero] at this
    exact le_of_lt this
  have hfree' : ∀ t ∈ Icc (s0 - η) s0, Free c S (M.config t) := fun t ht =>
    hfree t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- f(τ) = Y(s0 - τ) - w/2 vanishes on [0, η] by Gronwall
  set f : ℝ → ℝ := fun τ => M.Y (s0 - τ) - c.w / 2 with hf
  have hfd : ∀ τ, HasDerivAt f (-(M.d * sin (M.ψ (s0 - τ)))) τ := by
    intro τ
    have h1 := (M.hasDerivAt_Y (s0 - τ)).comp τ ((hasDerivAt_id τ).const_sub s0)
    simpa [f, mul_comm] using h1.sub_const (c.w / 2)
  have hzero : ∀ τ ∈ Icc (0 : ℝ) η, f τ = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := 2 / c.c0)
    · exact (continuous_iff_continuousAt.mpr fun τ => (hfd τ).continuousAt).continuousOn
    · exact fun τ _ => (hfd τ).hasDerivWithinAt
    · simp [f, hY0]
    · intro τ hτ
      have ht : s0 - τ ∈ Icc (s0 - η) s0 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      have hr := (hfree' _ ht).regime (hreg _ ht)
      simp only [Manoeuvre.config] at hr
      have hd1 : |M.d| = 1 := by rcases M.hd with h | h <;> simp [h]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_mul, hd1, one_mul]
      have hfnn : 0 ≤ f τ := by
        simp only [f]; nlinarith [abs_nonneg (sin (M.ψ (s0 - τ)))]
      rw [abs_of_nonneg hfnn]
      simp only [f]
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
      nlinarith
  -- hence flush on [s0 - η, s0]
  have hflush_before : ∀ t ∈ Icc (s0 - η) s0, Flush c (M.config t) := by
    intro t ht
    have hτ : s0 - t ∈ Icc (0 : ℝ) η := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h0 := hzero _ hτ
    simp only [f, sub_sub_cancel] at h0
    have hY : M.Y t = c.w / 2 := by linarith
    have hr := (hfree' t ht).regime (hreg t ht)
    simp only [Manoeuvre.config] at hr
    rw [hY, sub_self] at hr
    have habs : |sin (M.ψ t)| = 0 := by
      have := abs_nonneg (sin (M.ψ t))
      nlinarith
    exact ⟨abs_eq_zero.mp habs, hY⟩
  -- so s0 - η ∈ A, contradicting the definition of s0
  have hmem : s0 - η ∈ A := by
    refine ⟨⟨by linarith, by linarith⟩, fun t ht => ?_⟩
    rcases le_or_gt t s0 with h | h
    · exact hflush_before t ⟨ht.1, h⟩
    · exact hflush_after t ⟨h, ht.2⟩
  have := csInf_le hbdd hmem
  linarith

end Parking

namespace Parking

variable {c : Car}

/-- Flushness propagates backwards along a free chain of manoeuvres. -/
theorem chain_flush {S : Slot} :
    ∀ (μ : List (Manoeuvre c)) (M₀ M₁ : Manoeuvre c), μ.head? = some M₀ → μ.getLast? = some M₁ →
      Chain μ → AllFree c S μ → Flush c M₁.finish → Flush c M₀.start
  | [], _, _, h0, _, _, _, _ => by simp at h0
  | [M], M₀, M₁, h0, h1, _, hfree, hf => by
      simp at h0 h1; subst h0; subst h1
      have := M.flush_propagates (hfree M (by simp)) hf 0 ⟨le_rfl, M.len_nonneg⟩
      simpa [Manoeuvre.start] using this
  | M :: M' :: rest, M₀, M₁, h0, h1, hch, hfree, hf => by
      simp only [List.head?_cons, Option.some.injEq] at h0; subst h0
      have hlast : (M' :: rest).getLast? = some M₁ := by
        rw [List.getLast?_cons_cons] at h1; exact h1
      have hrest := chain_flush (M' :: rest) M' M₁ rfl hlast hch.2
        (fun N hN => hfree N (List.mem_cons_of_mem _ hN)) hf
      have hfin : Flush c M.finish := by rw [hch.1]; exact hrest
      have := M.flush_propagates (hfree M (by simp)) hfin 0 ⟨le_rfl, M.len_nonneg⟩
      simpa [Manoeuvre.start] using this

/-- With zero margin a parked car is flush (if the car is longer than wide). -/
theorem parked_zero_flush {L : ℝ} {q : Config} (hlen : c.w < c.len) (h : Parked c ⟨0, L⟩ q) :
    Flush c q := by
  have hw := c.w_pos
  have hpt : ∀ u v, -c.db ≤ u → u ≤ c.b → -(c.w / 2) ≤ v → v ≤ c.w / 2 →
      0 ≤ (q.pt u v).2 ∧ (q.pt u v).2 ≤ c.w := by
    intro u v hu1 hu2 hv1 hv2
    refine ⟨h.1.pt_y_nonneg hu1 hu2 hv1 hv2, ?_⟩
    have := h.2 (q.pt u v) ⟨u, v, hu1, hu2, hv1, hv2, rfl⟩
    simpa [Slot.H] using this
  have hdb := c.db_pos; have hb := c.b_pos
  obtain ⟨a1, b1⟩ := hpt (-c.db) (-(c.w / 2)) le_rfl (by linarith) le_rfl (by linarith)
  obtain ⟨a2, b2⟩ := hpt c.b (-(c.w / 2)) (by linarith) le_rfl le_rfl (by linarith)
  obtain ⟨a3, b3⟩ := hpt c.b (c.w / 2) (by linarith) le_rfl (by linarith) le_rfl
  obtain ⟨a4, b4⟩ := hpt (-c.db) (c.w / 2) le_rfl (by linarith) (by linarith) le_rfl
  simp only [Config.pt] at a1 b1 a2 b2 a3 b3 a4 b4
  have hsc := sin_sq_add_cos_sq q.ψ
  have hl : c.len = c.b + c.db := rfl
  -- |ℓ s + w c| ≤ w and |-ℓ s + w c| ≤ w
  have e1 : (c.len * sin q.ψ + c.w * cos q.ψ) ^ 2 ≤ c.w ^ 2 := by
    apply sq_le_sq' <;> rw [hl] <;> linarith
  have e2 : (-(c.len * sin q.ψ) + c.w * cos q.ψ) ^ 2 ≤ c.w ^ 2 := by
    apply sq_le_sq' <;> rw [hl] <;> linarith
  have hs : sin q.ψ = 0 := by
    have : (c.len ^ 2 - c.w ^ 2) * sin q.ψ ^ 2 ≤ 0 := by nlinarith
    have hpos : 0 < c.len ^ 2 - c.w ^ 2 := by nlinarith
    have : sin q.ψ ^ 2 ≤ 0 := by
      by_contra hcon; push Not at hcon; nlinarith
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  have hc2 : cos q.ψ ^ 2 = 1 := by rw [hs] at hsc; linarith
  refine ⟨hs, ?_⟩
  rw [hs] at a1 b1 a4 b4
  rcases sq_eq_one_iff.mp hc2 with hc | hc <;> rw [hc] at a1 b1 a4 b4 <;> nlinarith

/-- A lane configuration is never flush when the margin is zero. -/
theorem inLane_not_flush {L : ℝ} {q : Config} (h : InLane c ⟨0, L⟩ q) (hf : Flush c q) : False := by
  have hw := c.w_pos
  have hdb := c.db_pos
  have hc2 : cos q.ψ ^ 2 = 1 := by have := sin_sq_add_cos_sq q.ψ; rw [hf.1] at this; linarith
  rcases sq_eq_one_iff.mp hc2 with hc | hc
  · have := h.1 (q.pt 0 (-(c.w / 2))) ⟨0, -(c.w / 2), by linarith, le_of_lt c.b_pos, le_rfl, by linarith, rfl⟩
    simp [Config.pt, hf.1, hf.2, hc, Slot.H] at this; linarith
  · have := h.1 (q.pt 0 (c.w / 2)) ⟨0, c.w / 2, by linarith, le_of_lt c.b_pos, by linarith, le_rfl, rfl⟩
    simp [Config.pt, hf.1, hf.2, hc, Slot.H] at this; linarith

/-- **Proposition (flush parking is impossible).** With zero margin, no parking motion exists. -/
theorem not_feasible_zero_margin (hlen : c.w < c.len) (n : ℕ) (L : ℝ) : ¬ Feasible c 0 n L := by
  rintro ⟨μ, M₀, M₁, h0, h1, _, hch, hfree, hlane, hpark⟩
  exact inLane_not_flush hlane (chain_flush μ M₀ M₁ h0 h1 hch hfree (parked_zero_flush hlen hpark))

end Parking
