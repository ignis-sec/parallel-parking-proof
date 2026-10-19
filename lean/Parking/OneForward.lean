/-
Lower bound for forward one-manoeuvre exits (Proposition `prop:one-forward` of the paper).

The proof follows the paper: the crossing time `τ` of the front curb-side corner through the
height `H`, heading bounds on `[0, τ]`, the "ahead" inequality for the corner `Q_f = (L, H)` of
the car in front, monotonicity of `|C - Q_f|²` and `|C - Q_f|² + c₂ C_y`, the curb cost, and the
final minimisation (file `OneMin`).
-/
import Parking.OneParked
import Parking.OneMin
import Parking.Monotone

open Real Set Filter Topology

noncomputable section

namespace Parking

variable {c : Car} {m : ℝ}

namespace Manoeuvre

variable (M : Manoeuvre c)

theorem config_pt (s u v : ℝ) : (M.config s).pt u v =
    (M.X s + u * cos (M.ψ s) - v * sin (M.ψ s), M.Y s + u * sin (M.ψ s) + v * cos (M.ψ s)) :=
  rfl

/-- The front curb-side corner `FC = pt b (-w/2)`. -/
def FCx (s : ℝ) : ℝ := M.X s + c.b * cos (M.ψ s) + c.w / 2 * sin (M.ψ s)
def FCy (s : ℝ) : ℝ := M.Y s + c.b * sin (M.ψ s) - c.w / 2 * cos (M.ψ s)

theorem FC_eq (s : ℝ) : (M.config s).pt c.b (-(c.w / 2)) = (M.FCx s, M.FCy s) := by
  rw [config_pt]; unfold FCx FCy
  simp only [Prod.mk.injEq]; constructor <;> ring

theorem continuous_FCx : Continuous M.FCx := by
  have := M.continuous_ψ; have := M.continuous_X; unfold FCx; fun_prop

theorem continuous_FCy : Continuous M.FCy := by
  have := M.continuous_ψ; have := M.continuous_Y; unfold FCy; fun_prop

theorem continuous_distSq (Q : ℝ × ℝ) : Continuous (M.distSq Q) := by
  unfold distSq
  exact ((M.continuous_Cx.sub continuous_const).pow 2).add
    ((M.continuous_Cy.sub continuous_const).pow 2)

end Manoeuvre

/-- Data of a (hypothetical) forward exit in a slot of length `L < Λ₁`, together with the
first time `τ` at which the front curb-side corner reaches the height `H`. -/
structure Fwd (A : OneAssumptions c m) (L : ℝ) (M : Manoeuvre c) where
  hd : M.d = 1
  hfree : ∀ s ∈ Icc (0 : ℝ) M.len, Free c ⟨m, L⟩ (M.config s)
  hstart : Parked c ⟨m, L⟩ (M.config 0)
  hψ0 : |M.ψ 0| ≤ A.ψfit
  hL : L < A.Λ₁
  τ : ℝ
  hτ0 : 0 < τ
  hτlen : τ ≤ M.len
  hτH : M.FCy τ = m + c.w
  hτlt : ∀ s ∈ Ico 0 τ, M.FCy s < m + c.w

namespace Fwd

variable {A : OneAssumptions c m} {L : ℝ} {M : Manoeuvre c} (F : Fwd A L M)
include F

theorem free {s : ℝ} (hs : s ∈ Icc 0 F.τ) : Free c ⟨m, L⟩ (M.config s) :=
  F.hfree s ⟨hs.1, hs.2.trans F.hτlen⟩

theorem curb {s : ℝ} (hs : s ∈ Icc 0 F.τ) {u v : ℝ} (hu1 : -c.db ≤ u) (hu2 : u ≤ c.b)
    (hv1 : -(c.w / 2) ≤ v) (hv2 : v ≤ c.w / 2) :
    0 ≤ M.Y s + u * sin (M.ψ s) + v * cos (M.ψ s) :=
  (F.free hs).pt_y_nonneg hu1 hu2 hv1 hv2

theorem top0 {u v : ℝ} (hu1 : -c.db ≤ u) (hu2 : u ≤ c.b) (hv1 : -(c.w / 2) ≤ v)
    (hv2 : v ≤ c.w / 2) :
    M.Y 0 + u * sin (M.ψ 0) + v * cos (M.ψ 0) ≤ m + c.w :=
  F.hstart.2 _ ⟨u, v, hu1, hu2, hv1, hv2, rfl⟩

theorem cos0 : m / c.w < cos (M.ψ 0) := A.cos_gt_of_abs_le (F.hψ0.trans A.ψfit_lt_ψb.le)

theorem cos0_pos : 0 < cos (M.ψ 0) :=
  lt_of_le_of_lt (div_nonneg A.hm.le c.w_pos.le) F.cos0

theorem lane0 : 0 ≤ M.X 0 - c.db * cos (M.ψ 0) - c.w / 2 * sin (M.ψ 0) ∧
    M.X 0 + c.b * cos (M.ψ 0) - c.w / 2 * sin (M.ψ 0) ≤ L := by
  have := Parked.lane_corners F.hstart A.hm.le F.cos0
  simp only [Manoeuvre.config_pt] at this
  constructor <;> linarith [this.1, this.2]

theorem ψ0_bounds : -A.ψfit ≤ M.ψ 0 ∧ M.ψ 0 ≤ A.ψfit := abs_le.mp F.hψ0

theorem FCy_le {s : ℝ} (hs : s ∈ Icc 0 F.τ) : M.FCy s ≤ m + c.w := by
  rcases eq_or_lt_of_le hs.2 with h | h
  · rw [h, F.hτH]
  · exact (F.hτlt s ⟨hs.1, h⟩).le

theorem FCy_nonneg {s : ℝ} (hs : s ∈ Icc 0 F.τ) : 0 ≤ M.FCy s := by
  have := F.curb hs (u := c.b) (v := -(c.w / 2)) (by linarith [c.db_pos, c.b_pos]) le_rfl le_rfl
    (by linarith [c.w_pos])
  unfold Manoeuvre.FCy; linarith

theorem len_sin_le_FCy {s : ℝ} (hs : s ∈ Icc 0 F.τ) : c.len * sin (M.ψ s) ≤ M.FCy s := by
  have := F.curb hs (u := -c.db) (v := -(c.w / 2)) le_rfl (by linarith [c.db_pos, c.b_pos])
    le_rfl (by linarith [c.w_pos])
  unfold Manoeuvre.FCy Car.len; linarith

theorem ψ_lt_ψb {s : ℝ} (hs : s ∈ Ico 0 F.τ) : M.ψ s < A.ψb := by
  by_contra hcon
  push Not at hcon
  have h0 : M.ψ 0 < A.ψb := by linarith [F.ψ0_bounds.2, A.ψfit_lt_ψb]
  obtain ⟨t, ht, hψt⟩ := intermediate_value_Icc hs.1 M.continuous_ψ.continuousOn ⟨h0.le, hcon⟩
  have htτ : t ∈ Ico 0 F.τ := ⟨ht.1, lt_of_le_of_lt ht.2 hs.2⟩
  have h1 := F.hτlt t htτ
  have h2 := F.len_sin_le_FCy ⟨htτ.1, htτ.2.le⟩
  rw [hψt, A.hψb] at h2
  linarith

theorem ψ_le_ψb {s : ℝ} (hs : s ∈ Icc 0 F.τ) : M.ψ s ≤ A.ψb := by
  by_contra hcon
  push Not at hcon
  have h0 : M.ψ 0 < A.ψb := by linarith [F.ψ0_bounds.2, A.ψfit_lt_ψb]
  obtain ⟨t, ht, hψt⟩ := intermediate_value_Icc hs.1 M.continuous_ψ.continuousOn
    (show (A.ψb + M.ψ s) / 2 ∈ Icc (M.ψ 0) (M.ψ s) by constructor <;> linarith)
  have hts : t ≠ s := by rintro rfl; linarith
  have := F.ψ_lt_ψb ⟨ht.1, lt_of_lt_of_le (lt_of_le_of_ne ht.2 hts) hs.2⟩
  linarith

theorem ψ_le_pi_div_two {s : ℝ} (hs : s ∈ Icc 0 F.τ) : M.ψ s ≤ π / 2 :=
  (F.ψ_le_ψb hs).trans A.hψb_mem.2.le

/-- Where the heading is non-negative, the rear axle is below `H + w/2`. -/
theorem Y_le_of_nonneg {s : ℝ} (hs : s ∈ Icc 0 F.τ) (hψ : 0 ≤ M.ψ s) :
    M.Y s ≤ m + c.w + c.w / 2 := by
  have h1 := F.FCy_le hs
  have h2 : 0 ≤ sin (M.ψ s) :=
    sin_nonneg_of_nonneg_of_le_pi hψ (by linarith [F.ψ_le_pi_div_two hs, pi_pos])
  have h3 := cos_le_one (M.ψ s)
  have hb := c.b_pos; have hw := c.w_pos
  unfold Manoeuvre.FCy at h1
  nlinarith

/-- The rear axle descends while the heading is in `[-π, 0]`. -/
theorem Y_anti {a t : ℝ} (hat : a ≤ t) (hneg : ∀ s ∈ Ioo a t, M.ψ s ≤ 0 ∧ -π ≤ M.ψ s) :
    M.Y t ≤ M.Y a := by
  have := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a t) (f := M.Y)
    (f' := fun s => M.d * sin (M.ψ s)) M.continuous_Y.continuousOn
    (fun x _ => (M.hasDerivAt_Y x).hasDerivWithinAt) (fun x hx => by
      rw [interior_Icc] at hx
      rw [F.hd, one_mul]
      exact sin_nonpos_of_nonpos_of_neg_pi_le (hneg x hx).1 (hneg x hx).2)
  exact this ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat

/-- Step 2(ii): `P_y ≤ H + w/2` as long as the heading stays above `-γ`. -/
theorem Y_le {t : ℝ} (ht : t ∈ Icc 0 F.τ) (hγ : ∀ s ∈ Icc 0 t, -A.γ ≤ M.ψ s) :
    M.Y t ≤ m + c.w + c.w / 2 := by
  have hγπ : -π ≤ -A.γ := by linarith [A.hγ_mem.2, pi_pos]
  by_cases hex : ∃ s ∈ Icc 0 t, 0 ≤ M.ψ s
  · set T := {s ∈ Icc 0 t | 0 ≤ M.ψ s} with hT
    have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le continuous_const M.continuous_ψ)
    obtain ⟨s1, hs1, hs1'⟩ := hex
    have hTne : T.Nonempty := ⟨s1, hs1, hs1'⟩
    have hTb : BddAbove T := ⟨t, fun s hs => hs.1.2⟩
    have hmem : sSup T ∈ T := hTc.csSup_mem hTne hTb
    have hs0 : sSup T ∈ Icc 0 F.τ := ⟨hmem.1.1, hmem.1.2.trans ht.2⟩
    have h1 := F.Y_le_of_nonneg hs0 hmem.2
    have h2 : M.Y t ≤ M.Y (sSup T) := F.Y_anti hmem.1.2 (fun s hs => by
      have hst : s ∈ Icc 0 t := ⟨le_trans hmem.1.1 hs.1.le, hs.2.le⟩
      constructor
      · by_contra hcon
        push Not at hcon
        have := le_csSup hTb ⟨hst, hcon.le⟩
        linarith [hs.1]
      · linarith [hγ s hst])
    linarith
  · push Not at hex
    have h2 : M.Y t ≤ M.Y 0 := F.Y_anti ht.1 (fun s hs =>
      ⟨(hex s ⟨hs.1.le, hs.2.le⟩).le, by linarith [hγ s ⟨hs.1.le, hs.2.le⟩]⟩)
    have h3 := F.top0 (u := 0) (v := c.w / 2) (by linarith [c.db_pos]) (by linarith [c.b_pos])
      (by linarith [c.w_pos]) le_rfl
    have h4 := mul_pos (half_pos c.w_pos) F.cos0_pos
    simp only [zero_mul, add_zero] at h3
    linarith [c.w_pos]

/-- Step 2(iii): `C'_x` is non-decreasing while `cos ψ ≥ 0`. -/
theorem C'x_le {t : ℝ} (ht0 : 0 ≤ t) (hcos : ∀ s ∈ Ico 0 t, 0 ≤ cos (M.ψ s)) :
    M.C'x 0 ≤ M.C'x t := by
  have hR := c.R_pos
  have := antitoneOn_of_sq_incr (f := fun s => -M.C'x s) (a := 0) (b := t)
    (M.continuous_C'x.neg.continuousOn) (fun x hx => ⟨2 / c.R, fun z hxz => by
      show -M.C'x z - -M.C'x x ≤ 2 / c.R * (z - x) ^ 2
      have h1 := M.C'x_incr x z hxz.le
      have h2 := M.R_sin_incr x z hxz.le
      rw [F.hd, one_mul] at h1
      have h3 : 0 ≤ (z - x) + c.R * sin (M.ψ z - M.ψ x) := by linarith [(abs_le.mp h2).1]
      have h4 := mul_nonneg (hcos x hx) h3
      have h5 : 2 * (z - x) ^ 2 / c.R = 2 / c.R * (z - x) ^ 2 := by ring
      linarith⟩)
  have := this ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  simp only at this
  linarith

theorem C'x0_ge : c.db * cos A.ψfit - c.Rp * sin A.ψfit ≤ M.C'x 0 := by
  have hl := F.lane0.1
  have hψ := F.ψ0_bounds
  have hfit2 := A.ψfit_lt_pi_div_two
  have hc : cos A.ψfit ≤ cos (M.ψ 0) := by
    rw [← cos_abs (M.ψ 0)]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) F.hψ0
  have hs : -sin A.ψfit ≤ sin (M.ψ 0) := by
    rw [← sin_neg]; exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) hψ.1
  have h1 := mul_le_mul_of_nonneg_left hc c.db_pos.le
  have h2 := mul_le_mul_of_nonneg_left hs A.Rp_pos.le
  have key : c.Rp * sin (M.ψ 0) = c.R * sin (M.ψ 0) + c.w / 2 * sin (M.ψ 0) := by
    unfold Car.Rp; ring
  unfold Manoeuvre.C'x
  linarith

/-- Step 2: the heading stays above `-γ` on `[0, τ]` (this is where `L < Λ₁` is used). -/
theorem ψ_gt {s : ℝ} (hs : s ∈ Icc 0 F.τ) : -A.γ < M.ψ s := by
  by_contra hcon
  push Not at hcon
  have h0 : -A.γ < M.ψ 0 := by linarith [F.ψ0_bounds.1, A.ψfit_lt_γ]
  obtain ⟨t1, ht1, hψt1, hbefore⟩ := exists_first_le M.continuous_ψ hs.1 h0 hcon
  have ht1τ : t1 ∈ Icc 0 F.τ := ⟨ht1.1.le, ht1.2.trans hs.2⟩
  have hγ2 := A.hγ_mem
  have hγle : ∀ u ∈ Icc 0 t1, -A.γ ≤ M.ψ u := fun u hu => by
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h, hψt1]
    · exact (hbefore u ⟨hu.1, h⟩).le
  have hY := F.Y_le ht1τ hγle
  have hcos : ∀ u ∈ Ico 0 t1, 0 ≤ cos (M.ψ u) := fun u hu => by
    have h1 := hbefore u hu
    have h2 := F.ψ_le_pi_div_two ⟨hu.1, (hu.2.trans_le ht1.2).le.trans hs.2⟩
    exact cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩
  have hC' := F.C'x_le ht1.1.le hcos
  have hC'0 := F.C'x0_ge
  have hρ := A.ρ_pos
  have hsγ := A.sin_γ
  have hcγ := A.cos_γ
  have hFLx : L < M.X t1 + c.b * cos (M.ψ t1) - c.w / 2 * sin (M.ψ t1) := by
    have hC'eq : M.C'x t1 = M.X t1 - c.R * (c.Rp / c.ρ) := by
      unfold Manoeuvre.C'x; rw [hψt1, sin_neg, hsγ]; ring
    rw [hψt1, cos_neg, sin_neg, hsγ, hcγ]
    have hρeq : c.b * (c.b / c.ρ) + c.w / 2 * (c.Rp / c.ρ) + c.R * (c.Rp / c.ρ) = c.ρ := by
      have h := c.ρ_sq
      rw [show c.b * (c.b / c.ρ) + c.w / 2 * (c.Rp / c.ρ) + c.R * (c.Rp / c.ρ) =
        (c.b ^ 2 + c.Rp * (c.R + c.w / 2)) / c.ρ by field_simp; ring]
      rw [show c.R + c.w / 2 = c.Rp from rfl, ← sq, ← h]
      field_simp
    have hA7 := A.A7a
    have hLΛ := F.hL
    unfold OneAssumptions.Λ₁ at hLΛ
    linarith
  have hFLy : M.Y t1 + c.b * sin (M.ψ t1) + c.w / 2 * cos (M.ψ t1) < m + c.w := by
    rw [hψt1, cos_neg, sin_neg, hsγ, hcγ]
    have hA3 := A.A3a
    have e : c.b * (c.Rp / c.ρ) - c.w / 2 * (c.b / c.ρ) = c.R * c.b / c.ρ := by
      unfold Car.Rp; field_simp; ring
    have : c.w / 2 < c.R * c.b / c.ρ := by rw [lt_div_iff₀ hρ]; linarith
    linarith
  have hfree := F.free ht1τ
  by_cases hm' : m < M.Y t1 + c.b * sin (M.ψ t1) + c.w / 2 * cos (M.ψ t1)
  · have hfp : (M.config t1).pt c.b (c.w / 2) ∈ footprint c (M.config t1) :=
      ⟨c.b, c.w / 2, by linarith [c.db_pos, c.b_pos], le_rfl, by linarith [c.w_pos], le_rfl, rfl⟩
    have hob : (M.config t1).pt c.b (c.w / 2) ∈ obstacle c ⟨m, L⟩ := Or.inr ⟨hFLx, hm', hFLy⟩
    exact Set.disjoint_left.mp hfree hfp hob
  · push Not at hm'
    have hc := F.curb ht1τ (u := c.b) (v := -(c.w / 2)) (by linarith [c.db_pos, c.b_pos]) le_rfl
      le_rfl (by linarith [c.w_pos])
    rw [hψt1, cos_neg, sin_neg, hsγ, hcγ] at hc hm'
    have hA3b := A.A3b
    have : m < c.w * (c.b / c.ρ) := by rw [mul_div_assoc', lt_div_iff₀ hρ]; linarith
    linarith

/-- Step 3: `ψ(τ) ≥ 0`. -/
theorem ψτ_nonneg : 0 ≤ M.ψ F.τ := by
  by_contra hcon
  push Not at hcon
  have hτI : F.τ ∈ Icc 0 F.τ := ⟨F.hτ0.le, le_rfl⟩
  have hY := F.Y_le hτI (fun s hs => (F.ψ_gt ⟨hs.1, hs.2.trans hτI.2⟩).le)
  have hγ := F.ψ_gt hτI
  have hH := F.hτH
  unfold Manoeuvre.FCy at hH
  obtain ⟨x, hx⟩ : ∃ x, x = -M.ψ F.τ := ⟨_, rfl⟩
  have hx0 : 0 < x := by linarith
  have hx1 : x < π / 2 := by linarith [A.hγ_mem.2]
  have hsx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
  have hcx : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith, hx1.le⟩
  have hsc := sin_sq_add_cos_sq x
  have hs1 := sin_le_one x
  have hc1 := cos_le_one x
  have hkey : 1 - cos x ≤ sin x := by
    nlinarith [mul_nonneg hsx.le (sub_nonneg.mpr hs1), mul_nonneg hcx (sub_nonneg.mpr hc1)]
  have hψ : M.ψ F.τ = -x := by rw [hx]; ring
  rw [hψ, sin_neg, cos_neg] at hH
  have hbw : c.w / 2 < c.b := by linarith [A.A2b, A.hm, c.w_pos]
  have h1 := mul_pos (sub_pos.mpr hbw) hsx
  have h2 := mul_le_mul_of_nonneg_left hkey (half_pos c.w_pos).le
  nlinarith

/-- Step 4: `FC_x(τ) ≤ L`. -/
theorem FCx_τ_le : M.FCx F.τ ≤ L := by
  have hmH : m < M.FCy F.τ := by rw [F.hτH]; linarith [c.w_pos]
  have hy : ∀ᶠ s in 𝓝[<] F.τ, m < M.FCy s :=
    (((M.continuous_FCy).tendsto F.τ).eventually_const_lt hmH).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ s in 𝓝[<] F.τ, 0 < s :=
    ((continuous_id.tendsto F.τ).eventually_const_lt F.hτ0).filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] F.τ, M.FCx s ≤ L := by
    filter_upwards [hy, hpos, self_mem_nhdsWithin] with s hs1 hs2 hs3
    have hsI : s ∈ Ico 0 F.τ := ⟨hs2.le, hs3⟩
    have hlt := F.hτlt s hsI
    by_contra hcon
    push Not at hcon
    have hfp : (M.config s).pt c.b (-(c.w / 2)) ∈ footprint c (M.config s) :=
      ⟨c.b, -(c.w / 2), by linarith [c.db_pos, c.b_pos], le_rfl, le_rfl, by linarith [c.w_pos], rfl⟩
    have hob : (M.config s).pt c.b (-(c.w / 2)) ∈ obstacle c ⟨m, L⟩ := by
      rw [M.FC_eq]; exact Or.inr ⟨hcon, hs1, hlt⟩
    exact Set.disjoint_left.mp (F.free ⟨hsI.1, hsI.2.le⟩) hfp hob
  exact le_of_tendsto ((M.continuous_FCx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- A point of the front edge in the band `(m, H]`, left of the car in front. -/
theorem edge {s : ℝ} (hs : s ∈ Ico 0 F.τ) (hk : m < c.w * cos (M.ψ s)) (hk0 : 0 < cos (M.ψ s)) :
    ∃ v, -(c.w / 2) < v ∧ v ≤ c.w / 2 ∧
      m < M.Y s + c.b * sin (M.ψ s) + v * cos (M.ψ s) ∧
      M.Y s + c.b * sin (M.ψ s) + v * cos (M.ψ s) ≤ m + c.w ∧
      M.X s + c.b * cos (M.ψ s) - v * sin (M.ψ s) ≤ L := by
  have hsI : s ∈ Icc 0 F.τ := ⟨hs.1, hs.2.le⟩
  have hfree := F.free hsI
  have hFC0 := F.FCy_nonneg hsI
  have hFCH := F.hτlt s hs
  unfold Manoeuvre.FCy at hFC0 hFCH
  have hw := c.w_pos
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ : ∃ v, -(c.w / 2) < v ∧ v ≤ c.w / 2 ∧
      m < M.Y s + c.b * sin (M.ψ s) + v * cos (M.ψ s) ∧
      M.Y s + c.b * sin (M.ψ s) + v * cos (M.ψ s) ≤ m + c.w := by
    by_cases hFL : M.Y s + c.b * sin (M.ψ s) + c.w / 2 * cos (M.ψ s) ≤ m + c.w
    · exact ⟨c.w / 2, by linarith, le_rfl, by linarith, hFL⟩
    · push Not at hFL
      set D := m + c.w - (M.Y s + c.b * sin (M.ψ s) - c.w / 2 * cos (M.ψ s)) with hD
      have hDpos : 0 < D := by linarith
      have hvc : (-(c.w / 2) + D / cos (M.ψ s)) * cos (M.ψ s) = -(c.w / 2) * cos (M.ψ s) + D := by
        rw [add_mul, div_mul_cancel₀ _ hk0.ne']
      refine ⟨-(c.w / 2) + D / cos (M.ψ s), ?_, ?_, ?_, ?_⟩
      · have := div_pos hDpos hk0; linarith
      · have : D / cos (M.ψ s) ≤ c.w := by rw [div_le_iff₀ hk0]; linarith
        linarith
      · rw [hvc]; linarith
      · rw [hvc]; linarith
  refine ⟨v, hv1, hv2, hv3, hv4, ?_⟩
  exact band_right (u := c.b) (v := v) hfree (by linarith [c.db_pos, c.b_pos]) le_rfl hv1 hv2 hk0
    hv3 hv4

/-- The quantity `(Q_f - P) · e(ψ)` with `Q_f = (L, H)`. -/
def Aq (_F : Fwd A L M) (s : ℝ) : ℝ := (L - M.X s) * cos (M.ψ s) + (m + c.w - M.Y s) * sin (M.ψ s)

theorem Aq_decomp (s : ℝ) : F.Aq s - c.b =
    (L - M.FCx s) * cos (M.ψ s) + (m + c.w - M.FCy s) * sin (M.ψ s) := by
  unfold Aq Manoeuvre.FCx Manoeuvre.FCy
  linear_combination c.b * sin_sq_add_cos_sq (M.ψ s)

/-- Step 5: `Q_f` stays ahead of the rear axle. -/
theorem ahead {s : ℝ} (hs : s ∈ Icc 0 F.τ) :
    0 ≤ F.Aq s ∧ (0 ≤ M.ψ s → c.b ≤ F.Aq s) := by
  have hdec := F.Aq_decomp s
  have hψb := F.ψ_le_ψb hs
  have hγ := F.ψ_gt hs
  have hb := c.b_pos
  have hγ2 := A.hγ_mem
  have hψ2 := F.ψ_le_pi_div_two hs
  have hcos : 0 < cos (M.ψ s) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith [A.hψb_mem.2]⟩
  have hFC0 := F.FCy_nonneg hs
  have hFCH := F.FCy_le hs
  rcases eq_or_lt_of_le hs.2 with hsτ | hsτ
  · subst hsτ
    have h1 := F.FCx_τ_le
    have h2 := F.hτH
    have h3 : 0 ≤ (L - M.FCx F.τ) * cos (M.ψ F.τ) := mul_nonneg (by linarith) hcos.le
    rw [h2, sub_self, zero_mul, add_zero] at hdec
    exact ⟨by linarith, fun _ => by linarith⟩
  · have hsI : s ∈ Ico 0 F.τ := ⟨hs.1, hsτ⟩
    rcases le_or_gt 0 (M.ψ s) with hψ | hψ
    · have hk := A.w_cos_gt_of_abs_le (by rw [abs_of_nonneg hψ]; exact hψb)
      obtain ⟨v, hv1, hv2, hv3, hv4, hv5⟩ := F.edge hsI hk hcos
      have hsin : 0 ≤ sin (M.ψ s) := sin_nonneg_of_nonneg_of_le_pi hψ (by linarith [pi_pos])
      have h1 : (M.X s + c.b * cos (M.ψ s) - v * sin (M.ψ s) - M.FCx s) * cos (M.ψ s) ≤
          (L - M.FCx s) * cos (M.ψ s) := mul_le_mul_of_nonneg_right (by linarith) hcos.le
      have h2 : 0 ≤ sin (M.ψ s) * (m + c.w - (M.Y s + c.b * sin (M.ψ s) + v * cos (M.ψ s))) :=
        mul_nonneg hsin (by linarith)
      have h3 : (M.X s + c.b * cos (M.ψ s) - v * sin (M.ψ s) - M.FCx s) * cos (M.ψ s) +
          (m + c.w - M.FCy s) * sin (M.ψ s) =
          sin (M.ψ s) * (m + c.w - (M.Y s + c.b * sin (M.ψ s) + v * cos (M.ψ s))) := by
        unfold Manoeuvre.FCx Manoeuvre.FCy; ring
      exact ⟨by linarith, fun _ => by linarith⟩
    · -- negative heading: `cos ψ > cos γ = b / ρ`, so `w cos ψ > m`
      have hρ := A.ρ_pos
      have hcg : cos A.γ < cos (M.ψ s) := by
        rw [← cos_neg (M.ψ s)]
        exact cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]) (by linarith)
      rw [A.cos_γ] at hcg
      have hk : m < c.w * cos (M.ψ s) := by
        have hA3b := A.A3b
        have : m < c.w * (c.b / c.ρ) := by rw [mul_div_assoc', lt_div_iff₀ hρ]; linarith
        nlinarith [c.w_pos]
      obtain ⟨v, hv1, hv2, hv3, hv4, hv5⟩ := F.edge hsI hk hcos
      have hsin : sin (M.ψ s) < 0 := sin_neg_of_neg_of_neg_pi_lt hψ (by linarith [pi_pos])
      have hFCx : M.FCx s ≤ L := by
        have : M.FCx s ≤ M.X s + c.b * cos (M.ψ s) - v * sin (M.ψ s) := by
          unfold Manoeuvre.FCx; nlinarith
        linarith
      have hsg : -(c.Rp / c.ρ) < sin (M.ψ s) := by
        rw [← A.sin_γ, ← sin_neg]
        exact sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hγ
      have h1 : 0 ≤ (L - M.FCx s) * cos (M.ψ s) := mul_nonneg (by linarith) hcos.le
      have h2 : (m + c.w) * sin (M.ψ s) ≤ (m + c.w - M.FCy s) * sin (M.ψ s) := by nlinarith
      have h3 : (m + c.w) * (-(c.Rp / c.ρ)) ≤ (m + c.w) * sin (M.ψ s) :=
        mul_le_mul_of_nonneg_left hsg.le (by linarith [A.hm, c.w_pos])
      have h4 : (m + c.w) * (c.Rp / c.ρ) < c.b := by
        rw [mul_div_assoc', div_lt_iff₀ hρ]; linarith [A.A3c]
      exact ⟨by linarith, fun h => absurd h (not_le.mpr hψ)⟩


/-- Step 7a: `|C - Q_f|²` is non-increasing on `[0, τ]`. -/
theorem dist_anti : AntitoneOn (M.distSq (L, m + c.w)) (Icc 0 F.τ) := by
  apply antitoneOn_of_sq_incr ((M.continuous_distSq _).continuousOn)
  intro x hx
  refine ⟨3 * (|M.X x - L| + |M.Y x - (m + c.w)|) / c.R + 12, fun z hxz => ?_⟩
  have h1 := M.distSq_incr (L, m + c.w) x z hxz.le
  have h2 := M.R_sin_incr x z hxz.le
  have hA := (F.ahead ⟨hx.1, hx.2.le⟩).1
  rw [F.hd, one_mul] at h1
  dsimp only at h1
  have h3 : 0 ≤ (z - x) - c.R * sin (M.ψ z - M.ψ x) := by linarith [(abs_le.mp h2).2]
  have h4 : (M.X x - L) * cos (M.ψ x) + (M.Y x - (m + c.w)) * sin (M.ψ x) = -F.Aq x := by
    unfold Aq; ring
  rw [h4] at h1
  nlinarith [mul_nonneg hA h3]

/-- Step 7b: `|C - Q_f|² + c₂ C_y` is non-increasing on `[0, τ]`. -/
theorem F2_anti :
    AntitoneOn (fun s => M.distSq (L, m + c.w) s + A.c2 * M.Cy s) (Icc 0 F.τ) := by
  apply antitoneOn_of_sq_incr
    (((M.continuous_distSq _).add (continuous_const.mul M.continuous_Cy)).continuousOn)
  intro x hx
  refine ⟨3 * (|M.X x - L| + |M.Y x - (m + c.w)|) / c.R + 12 + A.c2 * (2 / c.R),
    fun z hxz => ?_⟩
  have h1 := M.distSq_incr (L, m + c.w) x z hxz.le
  have h1' := M.Cy_incr x z hxz.le
  have h2 := M.R_sin_incr x z hxz.le
  have hxI : x ∈ Icc 0 F.τ := ⟨hx.1, hx.2.le⟩
  have hA := F.ahead hxI
  rw [F.hd, one_mul] at h1 h1'
  dsimp only at h1
  have h3 : 0 ≤ (z - x) - c.R * sin (M.ψ z - M.ψ x) := by linarith [(abs_le.mp h2).2]
  have h4 : (M.X x - L) * cos (M.ψ x) + (M.Y x - (m + c.w)) * sin (M.ψ x) = -F.Aq x := by
    unfold Aq; ring
  rw [h4] at h1
  have hkey : A.c2 * sin (M.ψ x) ≤ 2 * F.Aq x := by
    rcases le_or_gt 0 (M.ψ x) with hψ | hψ
    · have hb := hA.2 hψ
      have hs : sin (M.ψ x) ≤ sin A.ψb :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) A.hψb_mem.2.le (F.ψ_le_ψb hxI)
      have he : A.c2 * sin A.ψb = 2 * c.b := by
        unfold OneAssumptions.c2; field_simp [A.sin_ψb_pos.ne']
      have := mul_le_mul_of_nonneg_left hs A.c2_pos.le
      linarith
    · have hs : sin (M.ψ x) < 0 :=
        sin_neg_of_neg_of_neg_pi_lt hψ (by linarith [F.ψ_gt hxI, A.hγ_mem.2, pi_pos])
      have := mul_neg_of_pos_of_neg A.c2_pos hs
      linarith [hA.1]
  have h5 := mul_nonneg (sub_nonneg.mpr hkey) h3
  have h6 := mul_le_mul_of_nonneg_left h1' A.c2_pos.le
  show (M.distSq (L, m + c.w) z + A.c2 * M.Cy z) - (M.distSq (L, m + c.w) x + A.c2 * M.Cy x) ≤
    (3 * (|M.X x - L| + |M.Y x - (m + c.w)|) / c.R + 12 + A.c2 * (2 / c.R)) * (z - x) ^ 2
  have e : A.c2 * (2 * (z - x) ^ 2 / c.R) = A.c2 * (2 / c.R) * (z - x) ^ 2 := by ring
  nlinarith

/-- Step 6: at time `τ` the centre is at distance at least `ρ` from `Q_f`. -/
theorem dist_τ : c.ρ ^ 2 ≤ M.distSq (L, m + c.w) F.τ := by
  have hH := F.hτH
  have hx := F.FCx_τ_le
  have hψ0 := F.ψτ_nonneg
  have hψ2 := F.ψ_le_pi_div_two ⟨F.hτ0.le, le_rfl⟩
  have hs : 0 ≤ sin (M.ψ F.τ) := sin_nonneg_of_nonneg_of_le_pi hψ0 (by linarith [pi_pos])
  have hc : 0 ≤ cos (M.ψ F.τ) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hψ2⟩
  have hsc := sin_sq_add_cos_sq (M.ψ F.τ)
  have hρ := c.ρ_sq
  unfold Manoeuvre.FCy at hH
  unfold Manoeuvre.FCx at hx
  unfold Manoeuvre.distSq Manoeuvre.Cx Manoeuvre.Cy
  dsimp only
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = L - (M.X F.τ + c.b * cos (M.ψ F.τ) + c.w / 2 * sin (M.ψ F.τ)) :=
    ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by linarith
  have e1 : M.X F.τ - c.R * sin (M.ψ F.τ) - L =
      -(c.Rp * sin (M.ψ F.τ) + c.b * cos (M.ψ F.τ) + δ) := by
    rw [hδ]; unfold Car.Rp; ring
  have e2 : M.Y F.τ + c.R * cos (M.ψ F.τ) - (m + c.w) =
      c.Rp * cos (M.ψ F.τ) - c.b * sin (M.ψ F.τ) := by
    unfold Car.Rp; linear_combination hH
  rw [e1, e2]
  have e3 : (-(c.Rp * sin (M.ψ F.τ) + c.b * cos (M.ψ F.τ) + δ)) ^ 2 +
      (c.Rp * cos (M.ψ F.τ) - c.b * sin (M.ψ F.τ)) ^ 2 =
      c.ρ ^ 2 + 2 * δ * (c.Rp * sin (M.ψ F.τ) + c.b * cos (M.ψ F.τ)) + δ ^ 2 := by
    rw [hρ]; linear_combination (c.Rp ^ 2 + c.b ^ 2) * hsc
  rw [e3]
  have hRp := A.Rp_pos
  have := mul_nonneg hδ0 (add_nonneg (mul_nonneg hRp.le hs) (mul_nonneg c.b_pos.le hc))
  nlinarith [sq_nonneg δ]

/-- Step 8: the curb forces `C_y ≥ r` at some time of `[0, τ]`. -/
theorem exists_Cy_ge : ∃ t ∈ Icc 0 F.τ, c.r ≤ M.Cy t := by
  have hr := A.r_pos
  have hsβ := A.sin_β
  have hcβ := A.cos_β
  by_cases hβ : ∃ t ∈ Icc 0 F.τ, M.ψ t = A.β
  · obtain ⟨t, ht, hψt⟩ := hβ
    refine ⟨t, ht, ?_⟩
    have hc := F.curb ht (u := -c.db) (v := -(c.w / 2)) le_rfl (by linarith [c.db_pos, c.b_pos])
      le_rfl (by linarith [c.w_pos])
    unfold Manoeuvre.Cy
    simp only [hψt, hsβ, hcβ] at hc ⊢
    have key : c.db * (c.db / c.r) + c.w / 2 * (c.Rp / c.r) + c.R * (c.Rp / c.r) = c.r := by
      have h := c.r_sq
      rw [show c.db * (c.db / c.r) + c.w / 2 * (c.Rp / c.r) + c.R * (c.Rp / c.r) =
        (c.db ^ 2 + c.Rp * (c.R + c.w / 2)) / c.r by field_simp; ring]
      rw [show c.R + c.w / 2 = c.Rp from rfl, ← sq, ← h]
      field_simp
    linarith
  · push Not at hβ
    have h0 : M.ψ 0 < A.β := by linarith [F.ψ0_bounds.2, A.A2e]
    have hτβ : M.ψ F.τ < A.β := by
      by_contra hcon
      push Not at hcon
      obtain ⟨t, ht, hψt⟩ :=
        intermediate_value_Icc F.hτ0.le M.continuous_ψ.continuousOn ⟨h0.le, hcon⟩
      exact hβ t ht hψt
    refine ⟨F.τ, ⟨F.hτ0.le, le_rfl⟩, ?_⟩
    have hψ0 := F.ψτ_nonneg
    have hβ2 := A.hβ_mem.2
    have hH := F.hτH
    unfold Manoeuvre.FCy at hH
    have h1 : cos A.β ≤ cos (M.ψ F.τ) :=
      cos_le_cos_of_nonneg_of_le_pi hψ0 (by linarith [pi_pos]) hτβ.le
    have h2 : sin (M.ψ F.τ) ≤ sin A.β :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hβ2.le hτβ.le
    rw [hsβ] at h2
    rw [hcβ] at h1
    have hA4 := A.A4
    have e : M.Cy F.τ = m + c.w + c.Rp * cos (M.ψ F.τ) - c.b * sin (M.ψ F.τ) := by
      unfold Manoeuvre.Cy Car.Rp; linear_combination hH
    rw [e]
    have hRp := A.Rp_pos
    have h3 := mul_le_mul_of_nonneg_left h1 hRp.le
    have h4 := mul_le_mul_of_nonneg_left h2 c.b_pos.le
    have h5 : c.Rp * (c.Rp / c.r) - c.b * (c.db / c.r) = (c.Rp ^ 2 - c.b * c.db) / c.r := by
      field_simp
    linarith

/-- Curb cost (inequality `eq:curbcost`). -/
theorem dist0 : c.ρ ^ 2 + A.c2 * max 0 (c.r - M.Cy 0) ≤ M.distSq (L, m + c.w) 0 := by
  have h0I : (0:ℝ) ∈ Icc 0 F.τ := ⟨le_rfl, F.hτ0.le⟩
  have hτI : F.τ ∈ Icc 0 F.τ := ⟨F.hτ0.le, le_rfl⟩
  have hdτ := F.dist_τ
  have hd0 := F.dist_anti h0I hτI F.hτ0.le
  obtain ⟨t, ht, hrt⟩ := F.exists_Cy_ge
  have h1 := F.F2_anti h0I ht ht.1
  have h2 := F.dist_anti ht hτI ht.2
  simp only at h1
  have hc2 := A.c2_pos
  rcases le_total (c.r - M.Cy 0) 0 with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h, mul_sub]
    have := mul_le_mul_of_nonneg_left hrt hc2.le
    linarith

theorem Cx0_lt : M.Cx 0 < L := by
  have hl := F.lane0.2
  have hψ := F.ψ0_bounds
  have hfit2 := A.ψfit_lt_pi_div_two
  have hc : cos A.ψfit ≤ cos (M.ψ 0) := by
    rw [← cos_abs (M.ψ 0)]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) F.hψ0
  have hs : -sin A.ψfit ≤ sin (M.ψ 0) := by
    rw [← sin_neg]; exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) hψ.1
  have h1 := A.Rp_sin_lt_db_cos
  have hsf : 0 ≤ sin A.ψfit :=
    sin_nonneg_of_nonneg_of_le_pi A.ψfit_pos.le (by linarith [pi_pos])
  have hcf := A.cos_ψfit_pos
  have h3 : c.Rm * sin A.ψfit ≤ c.Rp * sin A.ψfit := mul_le_mul_of_nonneg_right A.Rm_lt_Rp.le hsf
  have h4 : c.db * cos A.ψfit < c.b * cos A.ψfit := mul_lt_mul_of_pos_right A.A1a hcf
  have h5 : c.b * cos A.ψfit ≤ c.b * cos (M.ψ 0) := mul_le_mul_of_nonneg_left hc c.b_pos.le
  have h6 : -(c.Rm * sin A.ψfit) ≤ c.Rm * sin (M.ψ 0) := by
    have := mul_le_mul_of_nonneg_left hs A.Rm_pos.le; linarith
  have e : c.R * sin (M.ψ 0) = c.Rm * sin (M.ψ 0) + c.w / 2 * sin (M.ψ 0) := by
    unfold Car.Rm; ring
  unfold Manoeuvre.Cx
  linarith

/-- Inequality `eq:Phi`: `L ≥ Φ(q₀)`. -/
theorem L_ge :
    M.Cx 0 + √(c.ρ ^ 2 - (M.Cy 0 - (m + c.w)) ^ 2 + A.c2 * max 0 (c.r - M.Cy 0)) ≤ L := by
  have hd := F.dist0
  have hlt := F.Cx0_lt
  unfold Manoeuvre.distSq at hd
  dsimp only at hd
  have : √(c.ρ ^ 2 - (M.Cy 0 - (m + c.w)) ^ 2 + A.c2 * max 0 (c.r - M.Cy 0)) ≤ L - M.Cx 0 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  linarith

/-- Parked bounds on the centre (Lemma `lem:parked`). -/
theorem Cx0_ge : c.Xf (M.ψ 0) ≤ M.Cx 0 := by
  have hl := F.lane0.1
  unfold Manoeuvre.Cx Car.Xf Car.Rm
  linarith

theorem Cy0_ge : m + c.w ≤ M.Cy 0 := by
  have h0I : (0:ℝ) ∈ Icc 0 F.τ := ⟨le_rfl, F.hτ0.le⟩
  have hc := F.curb h0I (u := 0) (v := -(c.w / 2)) (by linarith [c.db_pos]) (by linarith [c.b_pos])
    le_rfl (by linarith [c.w_pos])
  have hfit2 := A.ψfit_lt_pi_div_two
  have hcos : cos A.ψfit ≤ cos (M.ψ 0) := by
    rw [← cos_abs (M.ψ 0)]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) F.hψ0
  have h1 := mul_le_mul_of_nonneg_left hcos A.Rp_pos.le
  have h2 := A.A2f.1
  have e : c.Rp * cos (M.ψ 0) = c.R * cos (M.ψ 0) + c.w / 2 * cos (M.ψ 0) := by
    unfold Car.Rp; ring
  unfold Manoeuvre.Cy
  simp only [zero_mul, add_zero] at hc
  linarith

theorem Cy0_le_Yf : M.Cy 0 ≤ m + c.w + c.Yf (M.ψ 0) := by
  have h := F.top0 (u := c.b) (v := c.w / 2) (by linarith [c.db_pos, c.b_pos]) le_rfl
    (by linarith [c.w_pos]) le_rfl
  unfold Manoeuvre.Cy Car.Yf Car.Rm
  linarith

theorem Cy0_le_Rm : M.Cy 0 ≤ m + c.w + c.Rm := by
  have h := F.top0 (u := 0) (v := c.w / 2) (by linarith [c.db_pos]) (by linarith [c.b_pos])
    (by linarith [c.w_pos]) le_rfl
  simp only [zero_mul, add_zero] at h
  have hc := cos_le_one (M.ψ 0)
  have h1 := mul_le_mul_of_nonneg_left hc A.Rm_pos.le
  have e : c.R * cos (M.ψ 0) = c.Rm * cos (M.ψ 0) + c.w / 2 * cos (M.ψ 0) := by
    unfold Car.Rm; ring
  unfold Manoeuvre.Cy
  linarith

end Fwd

namespace OneAssumptions

variable (A : OneAssumptions c m)
include A

/-- `X(-x) ≥ d_b` for `x ∈ [0, ψ_fit]` (uses `R₋ ≥ d_b tan(ψ_fit/2)`). -/
theorem db_le_Xf_neg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ A.ψfit) : c.db ≤ c.Xf (-x) := by
  have hfit2 := A.ψfit_lt_pi_div_two
  have hh0 : 0 ≤ x / 2 := by linarith
  have hh1 : x / 2 < π / 2 := by linarith [pi_pos]
  have hcpos : 0 < cos (x / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hh1⟩
  have hspos : 0 ≤ sin (x / 2) := sin_nonneg_of_nonneg_of_le_pi hh0 (by linarith [pi_pos])
  have htan : tan (x / 2) ≤ tan (A.ψfit / 2) := by
    rcases eq_or_lt_of_le hx with h | h
    · rw [h]
    · exact (tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [pi_pos]) (by linarith)
        (by linarith)).le
  have h1 : c.db * tan (x / 2) ≤ c.Rm := le_trans (mul_le_mul_of_nonneg_left htan c.db_pos.le) A.A2g
  rw [tan_eq_sin_div_cos, mul_div_assoc', div_le_iff₀ hcpos] at h1
  have hc2 := cos_two_mul (x / 2)
  have hs2 := sin_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc2 hs2
  have hsc := sin_sq_add_cos_sq (x / 2)
  have h2 := mul_le_mul_of_nonneg_left h1 hspos
  unfold Car.Xf
  rw [cos_neg, sin_neg, hc2, hs2]
  have e : c.db * (2 * cos (x / 2) ^ 2 - 1) - c.Rm * -(2 * sin (x / 2) * cos (x / 2)) - c.db =
      2 * (sin (x / 2) * (c.Rm * cos (x / 2)) - sin (x / 2) * (c.db * sin (x / 2))) := by
    linear_combination (2 * c.db) * hsc
  linarith

end OneAssumptions

namespace Fwd

variable {A : OneAssumptions c m} {L : ℝ} {M : Manoeuvre c} (F : Fwd A L M)
include F

/-- Step 9 and conclusion: a forward exit cannot exist when `L < Λ₁`. -/
theorem false_of : False := by
  have h := F.L_ge
  have hψ := F.ψ0_bounds
  have hcy1 := F.Cy0_ge
  have key : A.Λ₁ ≤ L := by
    rcases le_or_gt 0 (M.ψ 0) with h0 | h0
    · have h1 := A.φ_le_of F.Cx0_ge hcy1 F.Cy0_le_Yf
      have h2 := A.Λ₁_le_φ ⟨h0, hψ.2⟩
      linarith
    · have hX : c.Xf 0 ≤ M.Cx 0 := by
        have := A.db_le_Xf_neg (x := -M.ψ 0) (by linarith) (by linarith)
        rw [neg_neg] at this
        have h' : c.Xf 0 = c.db := by simp [Car.Xf]
        linarith [F.Cx0_ge]
      have hY : M.Cy 0 ≤ m + c.w + c.Yf 0 := by
        have h' : c.Yf 0 = c.Rm := by simp [Car.Yf]
        rw [h']; exact F.Cy0_le_Rm
      have h1 := A.φ_le_of hX hcy1 hY
      have h2 := A.Λ₁_le_φ ⟨le_rfl, A.ψfit_pos.le⟩
      linarith
  linarith [F.hL]

end Fwd

/-- **Proposition (forward exits).** A forward manoeuvre from a parked configuration with
`|ψ(0)| ≤ ψ_fit` to a lane configuration through free configurations needs `L ≥ Λ₁`. -/
theorem exit_forward_lower (A : OneAssumptions c m) {L : ℝ} (M : Manoeuvre c) (hd : M.d = 1)
    (hfree : ∀ s ∈ Icc (0 : ℝ) M.len, Free c ⟨m, L⟩ (M.config s))
    (hstart : Parked c ⟨m, L⟩ M.start) (hend : InLane c ⟨m, L⟩ M.finish)
    (hψ0 : |M.ψ 0| ≤ A.ψfit) : A.Λ₁ ≤ L := by
  by_contra hL
  push Not at hL
  have hcos0 : 0 < cos (M.ψ 0) := by
    have := A.cos_gt_of_abs_le (hψ0.trans A.ψfit_lt_ψb.le)
    exact lt_of_le_of_lt (div_nonneg A.hm.le c.w_pos.le) this
  have hFC0 : M.FCy 0 < m + c.w := by
    have := hstart.2 _ ⟨c.b, c.w / 2, by linarith [c.db_pos, c.b_pos], le_rfl,
      by linarith [c.w_pos], le_rfl, rfl⟩
    have h2 := mul_pos c.w_pos hcos0
    simp only [Manoeuvre.start, Manoeuvre.config_pt] at this
    unfold Manoeuvre.FCy
    have e : Slot.H c ⟨m, L⟩ = m + c.w := rfl
    linarith
  have hFCend : m + c.w ≤ M.FCy M.len := by
    have := hend.1 _ ⟨c.b, -(c.w / 2), by linarith [c.db_pos, c.b_pos], le_rfl, le_rfl,
      by linarith [c.w_pos], rfl⟩
    simp only [Manoeuvre.finish, Manoeuvre.config_pt] at this
    unfold Manoeuvre.FCy
    have e : Slot.H c ⟨m, L⟩ = m + c.w := rfl
    linarith
  obtain ⟨τ, hτ, hτH, hτlt⟩ := exists_first_ge M.continuous_FCy M.len_nonneg hFC0 hFCend
  exact (Fwd.mk hd hfree hstart hψ0 hL τ hτ.1 hτ.2 hτH hτlt).false_of

end Parking
