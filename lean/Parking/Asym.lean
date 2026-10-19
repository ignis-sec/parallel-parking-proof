/-
The many-manoeuvre asymptotics (Theorems `thm:mono` and `thm:asym` of the paper).

The two propositions `prop:asym-lower` and `prop:asym-upper` of the paper (whose proofs use the
confinement lemma, the exact description of the free windows, the calibration and the
tilted S-curve construction) are **not** formalised. They enter here as the explicit
hypotheses `AsymLower c m` and `AsymUpper c m`. Everything else, namely the passage from these
two bounds on the minimal number of manoeuvres `N(g)` to the statements about `L_min(n)`,
is proved. The analytic core of the two propositions (the value of `K²`, the calibration
inequality and the loop area) is proved in `Parking.AsymCore`.
-/
import Parking.Basic
import Parking.AsymCore

open Real Set Filter Topology

noncomputable section

namespace Parking

/-- The constant `K² = 4 R w - w³ / (6 R)`. -/
def Car.Ksq (c : Car) : ℝ := 4 * c.R * c.w - c.w ^ 3 / (6 * c.R)

variable {c : Car} {m : ℝ}

theorem Car.Ksq_eq_integral (c : Car) : c.Ksq = ∫ u in (0 : ℝ)..c.w, invRate c.R c.w u :=
  (K_sq_eq c.R c.w c.R_pos c.w_pos).symm

theorem Car.Ksq_pos (c : Car) (hR : c.w / 2 < c.R) : 0 < c.Ksq := by
  unfold Car.Ksq
  have hR0 := c.R_pos
  have hw := c.w_pos
  have h : c.w ^ 3 / (6 * c.R) < 4 * c.R * c.w := by
    rw [div_lt_iff₀ (by positivity)]
    have : c.w ^ 2 < 24 * c.R ^ 2 := by nlinarith
    nlinarith
  linarith

/-- Hypotheses of Theorem `thm:asym`: `R > w/2`, `0 < m < w`, `H < ℓ`, `d_b ≤ b` and the
margin condition `(mcond)`. -/
structure AsymHyp (c : Car) (m : ℝ) : Prop where
  hR : c.w / 2 < c.R
  hm : 0 < m
  hmw : m < c.w
  hHl : m + c.w < c.len
  hdb : c.db ≤ c.b
  mcond : ∃ ψfit : ℝ, 0 < ψfit ∧ ψfit < Real.arctan (c.len / c.w) ∧
    c.len * sin ψfit + c.w * cos ψfit = m + c.w ∧
    m < 2 * c.w * cos ψfit ^ 2 / (1 + 2 * cos ψfit)

/-- **Proposition `prop:asym-lower`** (statement, not formalised):
`liminf_{g → 0} g² N(g) ≥ K²`, i.e. every parking motion in a slot of length `ℓ + g` with
small `g` uses at least about `K² / g²` manoeuvres. -/
def AsymLower (c : Car) (m : ℝ) : Prop :=
  ∀ ε > 0, ∃ g₀ > 0, ∀ g : ℝ, 0 < g → g ≤ g₀ → ∀ n : ℕ,
    Feasible c m n (c.len + g) → c.Ksq - ε ≤ g ^ 2 * n

/-- **Proposition `prop:asym-upper`** (statement, not formalised):
`limsup_{g → 0} g² N(g) ≤ K²`, i.e. for small `g` there is a parking motion in a slot of
length `ℓ + g` with at most about `K² / g²` manoeuvres. -/
def AsymUpper (c : Car) (m : ℝ) : Prop :=
  ∀ ε > 0, ∃ g₀ > 0, ∀ g : ℝ, 0 < g → g ≤ g₀ → ∃ n : ℕ,
    g ^ 2 * n ≤ c.Ksq + ε ∧ Feasible c m n (c.len + g)

/-- No parking motion has zero manoeuvres. -/
theorem not_feasible_zero (c : Car) (m L : ℝ) : ¬ Feasible c m 0 L := by
  rintro ⟨μ, M₀, M₁, h0, h1, hlen, -⟩
  have : μ = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp [this] at h0

theorem Lmin_le_of {n : ℕ} {L : ℝ} (hf : Feasible c m n L) (hL : 0 < L) : Lmin c m n ≤ L :=
  csInf_le ⟨0, fun _ hx => hx.1.le⟩ ⟨hL, hf⟩

/-- Under `AsymLower`, no slot of length `≤ ℓ` admits a parking motion. -/
theorem len_lt_of_feasible (hl : AsymLower c m) (hK : 0 < c.Ksq) {n : ℕ} {L : ℝ}
    (hf : Feasible c m n L) : c.len < L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g₀, hg₀, h⟩ := hl (c.Ksq / 2) (by linarith)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hq : 0 < c.Ksq / (4 * (n + 1)) := by positivity
  obtain ⟨g, hg⟩ : ∃ g, g = min g₀ (√(c.Ksq / (4 * (n + 1)))) := ⟨_, rfl⟩
  have hgpos : 0 < g := by rw [hg]; exact lt_min hg₀ (Real.sqrt_pos.mpr hq)
  have hf' : Feasible c m n (c.len + g) := hf.mono_L (by linarith)
  have h1 := h g hgpos (by rw [hg]; exact min_le_left _ _) n hf'
  have hg2 : g ^ 2 ≤ c.Ksq / (4 * (n + 1)) := by
    have := min_le_right g₀ (√(c.Ksq / (4 * (n + 1))))
    rw [← hg] at this
    calc g ^ 2 ≤ (√(c.Ksq / (4 * (n + 1)))) ^ 2 := pow_le_pow_left₀ hgpos.le this 2
      _ = c.Ksq / (4 * (n + 1)) := Real.sq_sqrt hq.le
  have h2 : g ^ 2 * n < c.Ksq / 2 := by
    have := mul_le_mul_of_nonneg_right hg2 hn
    have h3 : c.Ksq / (4 * (n + 1)) * n < c.Ksq / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  linarith

/-- Quantitative lower bound on feasible slot lengths. -/
theorem lower_bound (hl : AsymLower c m) (hK : 0 < c.Ksq) {ε : ℝ} (hε : 0 < ε) :
    ∃ g₀ > 0, ∀ (n : ℕ) (L : ℝ), Feasible c m n L →
      c.len + min g₀ (√((c.Ksq - ε) / n)) ≤ L := by
  obtain ⟨g₀, hg₀, h⟩ := hl ε hε
  refine ⟨g₀, hg₀, fun n L hf => ?_⟩
  have hLl := len_lt_of_feasible hl hK hf
  have hg : 0 < L - c.len := by linarith
  rcases le_or_gt (L - c.len) g₀ with hgg | hgg
  · have hf' : Feasible c m n (c.len + (L - c.len)) := by
      rw [show c.len + (L - c.len) = L by ring]; exact hf
    have h1 := h (L - c.len) hg hgg n hf'
    have h2 : √((c.Ksq - ε) / n) ≤ L - c.len := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · rw [hn, Nat.cast_zero, div_zero, Real.sqrt_zero]; exact hg.le
      · rw [Real.sqrt_le_left hg.le, div_le_iff₀ (by exact_mod_cast hn)]
        linarith
    have := min_le_right g₀ (√((c.Ksq - ε) / n))
    linarith
  · have := min_le_left g₀ (√((c.Ksq - ε) / n))
    linarith

theorem Lmin_ge (hl : AsymLower c m) (hK : 0 < c.Ksq) {ε : ℝ} (hε : 0 < ε) :
    ∃ g₀ > 0, ∀ n : ℕ, (∃ L, Feasible c m n L) →
      c.len + min g₀ (√((c.Ksq - ε) / n)) ≤ Lmin c m n := by
  obtain ⟨g₀, hg₀, h⟩ := lower_bound hl hK hε
  refine ⟨g₀, hg₀, fun n hne => ?_⟩
  obtain ⟨L, hL⟩ := hne
  unfold Lmin
  refine le_csInf ⟨L, lt_trans c.len_pos (len_lt_of_feasible hl hK hL), hL⟩ ?_
  rintro x ⟨_, hx⟩
  exact h n x hx

/-- Under `AsymUpper`, eventually `L = ℓ + √((K² + ε)/n)` is feasible with `n` manoeuvres. -/
theorem eventually_feasible (hu : AsymUpper c m) (hK : 0 < c.Ksq) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Feasible c m n (c.len + √((c.Ksq + ε) / n)) := by
  obtain ⟨g₀, hg₀, h⟩ := hu ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (c.Ksq + ε) / g₀ ^ 2 < N := exists_nat_gt _
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
  have hKe : 0 < c.Ksq + ε := by linarith
  have hg : 0 < √((c.Ksq + ε) / n) := Real.sqrt_pos.mpr (by positivity)
  have hg2 : (√((c.Ksq + ε) / n)) ^ 2 = (c.Ksq + ε) / n := Real.sq_sqrt (by positivity)
  have hgg : √((c.Ksq + ε) / n) ≤ g₀ := by
    rw [Real.sqrt_le_left hg₀.le, div_le_iff₀ hnpos]
    have := (div_lt_iff₀ (by positivity)).mp hN
    nlinarith
  obtain ⟨n', hn', hf⟩ := h _ hg hgg
  rw [hg2] at hn'
  have hle : (n' : ℝ) ≤ n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hnpos] at hn'
    nlinarith
  exact hf.mono_n (by exact_mod_cast hle)

theorem sqrt_mul_sqrt_div {x : ℝ} {n : ℕ} (hn : (0:ℝ) < n) : √n * √(x / n) = √x := by
  rw [← Real.sqrt_mul hn.le]
  congr 1
  field_simp

/-- **Theorem `thm:asym`** (modulo Propositions `prop:asym-lower` and `prop:asym-upper`):
`√n (L_min(n) - ℓ) → K`. -/
theorem asym (h : AsymHyp c m) (hl : AsymLower c m) (hu : AsymUpper c m) :
    Tendsto (fun n : ℕ => √n * (Lmin c m n - c.len)) atTop (𝓝 (√c.Ksq)) := by
  have hK := c.Ksq_pos h.hR
  rw [tendsto_order]
  constructor
  · intro a ha
    have ha' : max a 0 < √c.Ksq := max_lt ha (Real.sqrt_pos.mpr hK)
    have ha'sq : (max a 0) ^ 2 < c.Ksq := (Real.lt_sqrt (le_max_right a 0)).mp ha'
    have hε : 0 < (c.Ksq - (max a 0) ^ 2) / 2 := by linarith
    obtain ⟨g₀, hg₀, hlow⟩ := Lmin_ge hl hK hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, c.Ksq / g₀ ^ 2 < N := exists_nat_gt _
    filter_upwards [eventually_ge_atTop (N + 1), eventually_feasible hu hK one_pos] with n hn hfeas
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
    set ε := (c.Ksq - (max a 0) ^ 2) / 2 with hεdef
    have hKe : 0 ≤ c.Ksq - ε := by nlinarith [sq_nonneg (max a 0)]
    have hmin : min g₀ (√((c.Ksq - ε) / n)) = √((c.Ksq - ε) / n) := by
      apply min_eq_right
      rw [Real.sqrt_le_left hg₀.le, div_le_iff₀ hnpos]
      have := (div_lt_iff₀ (by positivity)).mp hN
      nlinarith [sq_nonneg (max a 0)]
    have hb := hlow n ⟨_, hfeas⟩
    rw [hmin] at hb
    have e := sqrt_mul_sqrt_div (x := c.Ksq - ε) hnpos
    have h1 : max a 0 < √(c.Ksq - ε) := by
      rw [Real.lt_sqrt (le_max_right a 0)]; linarith
    have h2 : √n * √((c.Ksq - ε) / n) ≤ √n * (Lmin c m n - c.len) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    linarith [le_max_left a 0]
  · intro a ha
    have ha0 : 0 < a := lt_of_le_of_lt (Real.sqrt_nonneg _) ha
    have hasq : c.Ksq < a ^ 2 := (Real.sqrt_lt' ha0).mp ha
    have hε : 0 < (a ^ 2 - c.Ksq) / 2 := by linarith
    filter_upwards [eventually_feasible hu hK hε, eventually_ge_atTop 1] with n hfeas hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hL := Lmin_le_of hfeas (add_pos_of_pos_of_nonneg c.len_pos (Real.sqrt_nonneg _))
    have e := sqrt_mul_sqrt_div (x := c.Ksq + (a ^ 2 - c.Ksq) / 2) hnpos
    have h1 : √(c.Ksq + (a ^ 2 - c.Ksq) / 2) < a := by
      rw [Real.sqrt_lt' ha0]; linarith
    have h2 : √n * (Lmin c m n - c.len) ≤ √n * √((c.Ksq + (a ^ 2 - c.Ksq) / 2) / n) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    linarith

/-- **Theorem `thm:mono`**, second part (modulo the two propositions): `ℓ < L_min(n)` whenever
some slot admits an `n`-manoeuvre parking motion, and `L_min(n) → ℓ`. -/
theorem len_lt_Lmin (h : AsymHyp c m) (hl : AsymLower c m) {n : ℕ}
    (hne : ∃ L, Feasible c m n L) : c.len < Lmin c m n := by
  have hK := c.Ksq_pos h.hR
  obtain ⟨g₀, hg₀, hlow⟩ := Lmin_ge hl hK (ε := c.Ksq / 2) (by linarith)
  have hb := hlow n hne
  rcases Nat.eq_zero_or_pos n with hn | hn
  · obtain ⟨L, hL⟩ := hne
    rw [hn] at hL
    exact absurd hL (not_feasible_zero c m L)
  · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have : 0 < min g₀ (√((c.Ksq - c.Ksq / 2) / n)) :=
      lt_min hg₀ (Real.sqrt_pos.mpr (div_pos (by linarith) hnpos))
    linarith

theorem Lmin_tendsto (h : AsymHyp c m) (hl : AsymLower c m) (hu : AsymUpper c m) :
    Tendsto (fun n : ℕ => Lmin c m n) atTop (𝓝 c.len) := by
  have h1 := asym h hl hu
  have h2 : Tendsto (fun n : ℕ => 1 / √(n : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => √(1 / (n : ℝ))) atTop (𝓝 (√0)) :=
      (Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
    rw [Real.sqrt_zero] at this
    refine this.congr (fun n => ?_)
    rw [Real.sqrt_div' 1 (Nat.cast_nonneg n), Real.sqrt_one]
  have h3 := (h1.mul h2).const_add c.len
  rw [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  field_simp
  ring

/-- `L_min` is non-increasing on the (upward closed) set of `n` for which some slot is
feasible. -/
theorem Lmin_antitone' {n n' : ℕ} (h : n ≤ n') (hne : ∃ L, 0 < L ∧ Feasible c m n L) :
    Lmin c m n' ≤ Lmin c m n := by
  obtain ⟨L, hL, hf⟩ := hne
  exact Lmin_antitone h hL hf

end Parking
