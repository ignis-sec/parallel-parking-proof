/-
Lower bound for reverse one-manoeuvre exits (Proposition `prop:one-reverse` of the paper):
`L ≥ B_back`, hence `L ≥ Λ₁` by (A7).

We follow the height `h = P_y - (w/2) cos ψ` of the curb-side rear wheel. The Gronwall
estimate of the paper is replaced by the monotonicity of `P_x + λ log (h + ε)`, which avoids
measuring the set of times with negative heading.
-/
import Parking.OneForward

open Real Set Filter Topology

noncomputable section

namespace Parking

variable {c : Car} {m : ℝ}

namespace Manoeuvre

variable (M : Manoeuvre c)

/-- The rear curb-side corner `RC = pt (-d_b) (-w/2)`. -/
def RCx (s : ℝ) : ℝ := M.X s - c.db * cos (M.ψ s) + c.w / 2 * sin (M.ψ s)
def RCy (s : ℝ) : ℝ := M.Y s - c.db * sin (M.ψ s) - c.w / 2 * cos (M.ψ s)
/-- Height of the curb-side rear wheel `pt 0 (-w/2)`. -/
def RWy (s : ℝ) : ℝ := M.Y s - c.w / 2 * cos (M.ψ s)

theorem RC_eq (s : ℝ) : (M.config s).pt (-c.db) (-(c.w / 2)) = (M.RCx s, M.RCy s) := by
  rw [config_pt]; unfold RCx RCy
  simp only [Prod.mk.injEq]; constructor <;> ring

theorem continuous_RCx : Continuous M.RCx := by
  have := M.continuous_ψ; have := M.continuous_X; unfold RCx; fun_prop

theorem continuous_RCy : Continuous M.RCy := by
  have := M.continuous_ψ; have := M.continuous_Y; unfold RCy; fun_prop

theorem continuous_RWy : Continuous M.RWy := by
  have := M.continuous_ψ; have := M.continuous_Y; unfold RWy; fun_prop

theorem RCy_eq (s : ℝ) : M.RCy s = M.RWy s - c.db * sin (M.ψ s) := by
  unfold RCy RWy; ring

theorem RWy_eq_C'y (s : ℝ) : M.RWy s = M.C'y s + c.Rm * cos (M.ψ s) := by
  unfold RWy C'y Car.Rm; ring

end Manoeuvre

namespace OneAssumptions

variable (A : OneAssumptions c m)
include A

theorem sin_ψn : c.b * sin A.ψn = m + c.w := A.hψn

theorem ψfit_lt_ψn : A.ψfit < A.ψn := by
  have h1 := A.hψfit
  have h2 := A.hψn
  have hc := A.cos_ψfit_pos
  have hsf : 0 ≤ sin A.ψfit :=
    sin_nonneg_of_nonneg_of_le_pi A.ψfit_pos.le (by linarith [A.ψfit_lt_pi_div_two, pi_pos])
  have hbl : c.b ≤ c.len := by unfold Car.len; linarith [c.db_pos]
  have h3 : c.b * sin A.ψfit < c.b * sin A.ψn := by
    have := mul_le_mul_of_nonneg_right hbl hsf
    have := mul_pos c.w_pos hc
    linarith
  have hs : sin A.ψfit < sin A.ψn := lt_of_mul_lt_mul_left h3 c.b_pos.le
  by_contra hcon
  push Not at hcon
  have := sin_le_sin_of_le_of_le_pi_div_two (by linarith [A.hψn_mem.1, pi_pos])
    A.ψfit_lt_pi_div_two.le hcon
  linarith

/-- `f_b(ψ) = d_b cos ψ - (w/2) sin ψ` is at least `min (f_b(-ψ_n)) (f_b(ψ_u))` on `[-ψ_n, ψ_u]`. -/
theorem fb_ge {ψ : ℝ} (h1 : -A.ψn ≤ ψ) (h2 : ψ ≤ A.ψu) :
    min (c.db * cos A.ψn + c.w / 2 * sin A.ψn) (c.db * cos A.ψu - c.w / 2 * sin A.ψu) ≤
      c.db * cos ψ - c.w / 2 * sin ψ := by
  have hu := A.hψu_mem
  have hn := A.hψn_mem
  have hdb := c.db_pos
  have hw := c.w_pos
  -- monotone on `[0, ψ_u]`
  have hmono : ∀ x, 0 ≤ x → x ≤ A.ψu →
      c.db * cos A.ψu - c.w / 2 * sin A.ψu ≤ c.db * cos x - c.w / 2 * sin x := by
    intro x hx0 hx1
    have a1 := cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith [pi_pos]) hx1
    have a2 := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hu.2.le hx1
    nlinarith
  rcases le_total 0 ψ with h | h
  · exact (min_le_right _ _).trans (hmono ψ h h2)
  · set x := -ψ with hx
    have hx0 : 0 ≤ x := by linarith
    have hx1 : x ≤ A.ψn := by linarith
    have hψ : ψ = -x := by rw [hx]; ring
    rw [hψ, cos_neg, sin_neg]
    have hsn : 0 < sin A.ψn := sin_pos_of_pos_of_lt_pi hn.1 (by linarith [pi_pos])
    have hcn : 0 < cos A.ψn := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hn.2⟩
    have hsx : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [pi_pos])
    have hsd : 0 ≤ sin (A.ψn - x) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
    have hcd : cos (A.ψn - x) ≤ 1 := cos_le_one _
    have hcx : cos x ≤ 1 := cos_le_one _
    -- the sinusoid identity
    have hid : (c.db * cos x - c.w / 2 * -sin x) * sin A.ψn =
        c.db * sin (A.ψn - x) + (c.db * cos A.ψn + c.w / 2 * sin A.ψn) * sin x := by
      rw [sin_sub]; ring
    have hsum : sin A.ψn ≤ sin (A.ψn - x) + sin x := by
      have : sin A.ψn = sin (A.ψn - x) * cos x + cos (A.ψn - x) * sin x := by
        rw [← sin_add]; ring_nf
      nlinarith
    set μ := min c.db (c.db * cos A.ψn + c.w / 2 * sin A.ψn) with hμ
    have hμ1 : μ ≤ c.db := min_le_left _ _
    have hμ2 : μ ≤ c.db * cos A.ψn + c.w / 2 * sin A.ψn := min_le_right _ _
    have hμpos : 0 < μ := lt_min hdb (by positivity)
    have hge : μ ≤ c.db * cos x - c.w / 2 * -sin x := by
      have e1 : μ * sin A.ψn ≤ (c.db * cos x - c.w / 2 * -sin x) * sin A.ψn := by
        rw [hid]
        have := mul_le_mul_of_nonneg_left hsum hμpos.le
        nlinarith [mul_le_mul_of_nonneg_right hμ1 hsd, mul_le_mul_of_nonneg_right hμ2 hsx]
      exact le_of_mul_le_mul_right e1 hsn
    have h0 := hmono 0 le_rfl hu.1.le
    simp only [cos_zero, sin_zero, mul_one, mul_zero, sub_zero] at h0
    have : min (c.db * cos A.ψn + c.w / 2 * sin A.ψn) (c.db * cos A.ψu - c.w / 2 * sin A.ψu) ≤ μ :=
      le_min ((min_le_right _ _).trans h0) (min_le_left _ _)
    linarith

end OneAssumptions


/-- Pure inequality behind `Rev.G_anti`. Here `t = z - x`, `h = h(x)`, `sψ = sin ψ(x)`,
`cx = cos ψ(x)`, `sδ = sin (ψ z - ψ x)` and `D = h(z) - h(x)`. -/
theorem rev_key_ineq {R w b ε t h E sδ cx sψ D cψ : ℝ} (hR : 0 < R) (hw : 0 < w)
    (hA0 : w / 2 < R) (hb : 0 < b) (hε : 0 < ε) (ht : 0 < t) (hh : 0 ≤ h) (hE : 0 ≤ E)
    (hsd : |sδ| ≤ t / R) (hcx : 0 ≤ cx)
    (hD : D ≤ sψ * (-1 * t - -(w / 2) * sδ) + E) (hFC : 0 ≤ h + b * sψ) (hcψ : 0 < cψ)
    (hcn : sψ < 0 → cψ ≤ cx) :
    cψ * (R * b / (R + w / 2)) * (D / (h + ε)) ≤ t * cx + cψ * (R * b / (R + w / 2)) * (E / ε) := by
  have hRp : 0 < R + w / 2 := by linarith
  have hlam : 0 < cψ * (R * b / (R + w / 2)) := by positivity
  have hp : 0 < h + ε := by linarith
  have hEp : E / (h + ε) ≤ E / ε := div_le_div_of_nonneg_left hE hε (by linarith)
  have hwt : w / 2 * (t / R) ≤ t := by
    rw [mul_div_assoc', div_le_iff₀ hR]; nlinarith
  have a1 := mul_le_mul_of_nonneg_left (le_abs_self sδ) (half_pos hw).le
  have a1' := mul_le_mul_of_nonneg_left (neg_le_abs sδ) (half_pos hw).le
  have a2 := mul_le_mul_of_nonneg_left hsd (half_pos hw).le
  rcases le_or_gt 0 sψ with hs | hs
  · have h4 : sψ * (-1 * t - -(w / 2) * sδ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs (by linarith)
    have hD' : D ≤ E := by linarith
    have : D / (h + ε) ≤ E / ε := (div_le_div_of_nonneg_right hD' hp.le).trans hEp
    have := mul_le_mul_of_nonneg_left this hlam.le
    have := mul_nonneg ht.le hcx
    linarith
  · have hcn' := hcn hs
    have a4 : t - w / 2 * sδ ≤ t * (R + w / 2) / R := by
      have e : t * (R + w / 2) / R = t + w / 2 * (t / R) := by field_simp
      rw [e]; linarith
    have t1 : sψ * (-1 * t - -(w / 2) * sδ) ≤ (-sψ) * (t * (R + w / 2) / R) := by
      have := mul_le_mul_of_nonneg_left a4 (by linarith : (0:ℝ) ≤ -sψ)
      nlinarith
    have hK0 : 0 ≤ t * (R + w / 2) / R := by positivity
    have t2 : (-sψ) * (t * (R + w / 2) / R) ≤ h * (t * (R + w / 2) / (R * b)) := by
      have b1 : -sψ ≤ h / b := by rw [le_div_iff₀ hb]; linarith
      have := mul_le_mul_of_nonneg_right b1 hK0
      have e : h / b * (t * (R + w / 2) / R) = h * (t * (R + w / 2) / (R * b)) := by
        field_simp
      linarith
    have hK'0 : 0 ≤ t * (R + w / 2) / (R * b) := by positivity
    have hDp : D / (h + ε) ≤ t * (R + w / 2) / (R * b) + E / ε := by
      rw [div_le_iff₀ hp]
      have e : (t * (R + w / 2) / (R * b) + E / ε) * (h + ε) =
          t * (R + w / 2) / (R * b) * h + t * (R + w / 2) / (R * b) * ε + E / ε * h + E := by
        field_simp; ring
      have := mul_nonneg hK'0 hε.le
      have := mul_nonneg (div_nonneg hE hε.le) hh
      rw [e]; nlinarith
    have hlamK : cψ * (R * b / (R + w / 2)) * (t * (R + w / 2) / (R * b)) = cψ * t := by
      field_simp
    have := mul_le_mul_of_nonneg_left hDp hlam.le
    have := mul_le_mul_of_nonneg_left hcn' ht.le
    nlinarith

/-- Data of a reverse exit, with the first time `τ` at which the rear curb-side corner
reaches the height `H`. -/
structure Rev (A : OneAssumptions c m) (L : ℝ) (M : Manoeuvre c) where
  hd : M.d = -1
  hfree : ∀ s ∈ Icc (0 : ℝ) M.len, Free c ⟨m, L⟩ (M.config s)
  hstart : Parked c ⟨m, L⟩ (M.config 0)
  hψ0 : |M.ψ 0| ≤ A.ψfit
  τ : ℝ
  hτ0 : 0 < τ
  hτlen : τ ≤ M.len
  hτH : M.RCy τ = m + c.w
  hτlt : ∀ s ∈ Ico 0 τ, M.RCy s < m + c.w

namespace Rev

variable {A : OneAssumptions c m} {L : ℝ} {M : Manoeuvre c} (F : Rev A L M)
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

theorem cos_ψfit_le_cos0 : cos A.ψfit ≤ cos (M.ψ 0) := by
  rw [← cos_abs (M.ψ 0)]
  exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    (by linarith [A.ψfit_lt_pi_div_two, pi_pos]) F.hψ0

theorem RW_nonneg {s : ℝ} (hs : s ∈ Icc 0 F.τ) : 0 ≤ M.RWy s := by
  have := F.curb hs (u := 0) (v := -(c.w / 2)) (by linarith [c.db_pos]) (by linarith [c.b_pos])
    le_rfl (by linarith [c.w_pos])
  unfold Manoeuvre.RWy; linarith

theorem FC_curb {s : ℝ} (hs : s ∈ Icc 0 F.τ) : 0 ≤ M.RWy s + c.b * sin (M.ψ s) := by
  have := F.curb hs (u := c.b) (v := -(c.w / 2)) (by linarith [c.db_pos, c.b_pos]) le_rfl
    le_rfl (by linarith [c.w_pos])
  unfold Manoeuvre.RWy; linarith

theorem RC_curb {s : ℝ} (hs : s ∈ Icc 0 F.τ) : 0 ≤ M.RWy s - c.db * sin (M.ψ s) := by
  have := F.curb hs (u := -c.db) (v := -(c.w / 2)) le_rfl (by linarith [c.db_pos, c.b_pos])
    le_rfl (by linarith [c.w_pos])
  unfold Manoeuvre.RWy; linarith

theorem RW0_le : M.RWy 0 ≤ m + c.w - c.w * cos (M.ψ 0) := by
  have := F.top0 (u := 0) (v := c.w / 2) (by linarith [c.db_pos]) (by linarith [c.b_pos])
    (by linarith [c.w_pos]) le_rfl
  unfold Manoeuvre.RWy; linarith

theorem RCy_le {s : ℝ} (hs : s ∈ Icc 0 F.τ) : M.RCy s ≤ m + c.w := by
  rcases eq_or_lt_of_le hs.2 with h | h
  · rw [h, F.hτH]
  · exact (F.hτlt s ⟨hs.1, h⟩).le

/-- The wheel height does not increase while `sin ψ ≥ 0`. -/
theorem RWy_anti {a t : ℝ} (hat : a ≤ t) (hsin : ∀ s ∈ Ico a t, 0 ≤ sin (M.ψ s)) :
    M.RWy t ≤ M.RWy a := by
  have hR := c.R_pos
  have hw := c.w_pos
  have hA0 := A.A0
  have := antitoneOn_of_sq_incr (f := M.RWy) (a := a) (b := t) M.continuous_RWy.continuousOn
    (fun x hx => ⟨2 / c.R, fun z hxz => by
      have h1 := M.Yv_incr (-(c.w / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
        x z hxz.le
      have h2 := M.R_sin_incr x z hxz.le
      rw [F.hd] at h1
      have h3 : c.w / 2 * |sin (M.ψ z - M.ψ x)| ≤ z - x := by
        rw [abs_mul, abs_of_pos hR] at h2
        have := mul_le_mul_of_nonneg_right hA0.le (abs_nonneg (sin (M.ψ z - M.ψ x)))
        linarith
      have h4 : 0 ≤ -(-1 * (z - x) - -(c.w / 2) * sin (M.ψ z - M.ψ x)) := by
        have := mul_le_mul_of_nonneg_left (le_abs_self (sin (M.ψ z - M.ψ x))) (half_pos hw).le
        linarith
      have h5 := mul_nonneg (hsin x hx) h4
      have e : M.RWy z - M.RWy x = (M.Y z + -(c.w / 2) * cos (M.ψ z)) -
          (M.Y x + -(c.w / 2) * cos (M.ψ x)) := by unfold Manoeuvre.RWy; ring
      have e2 : 2 * (z - x) ^ 2 / c.R = 2 / c.R * (z - x) ^ 2 := by ring
      rw [e]
      nlinarith⟩)
  exact this ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat

/-- `C'_y` does not increase while `sin ψ ≥ 0`. -/
theorem C'y_anti {a t : ℝ} (hat : a ≤ t) (hsin : ∀ s ∈ Ico a t, 0 ≤ sin (M.ψ s)) :
    M.C'y t ≤ M.C'y a := by
  have hR := c.R_pos
  have := antitoneOn_of_sq_incr (f := M.C'y) (a := a) (b := t) M.continuous_C'y.continuousOn
    (fun x hx => ⟨2 / c.R, fun z hxz => by
      have h1 := M.Yv_incr (-c.R) (by rw [abs_neg, abs_of_pos hR]) x z hxz.le
      have h2 := M.R_sin_incr x z hxz.le
      rw [F.hd] at h1
      have h4 : 0 ≤ -(-1 * (z - x) - -c.R * sin (M.ψ z - M.ψ x)) := by
        have := (abs_le.mp h2).2
        linarith
      have h5 := mul_nonneg (hsin x hx) h4
      have e : M.C'y z - M.C'y x = (M.Y z + -c.R * cos (M.ψ z)) -
          (M.Y x + -c.R * cos (M.ψ x)) := by unfold Manoeuvre.C'y; ring
      have e2 : 2 * (z - x) ^ 2 / c.R = 2 / c.R * (z - x) ^ 2 := by ring
      rw [e]
      nlinarith⟩)
  exact this ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat

/-- The last time before `t` with non-positive heading, if any; the heading vanishes there
unless it is `t` itself. -/
theorem last_nonpos {t : ℝ} (hex : ∃ s ∈ Icc 0 t, M.ψ s ≤ 0) :
    ∃ sa ∈ Icc 0 t, M.ψ sa ≤ 0 ∧ (∀ s ∈ Ioc sa t, 0 < M.ψ s) ∧ (sa < t → M.ψ sa = 0) := by
  set T := {s ∈ Icc 0 t | M.ψ s ≤ 0} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le M.continuous_ψ continuous_const)
  obtain ⟨s1, hs1, hs1'⟩ := hex
  have hTne : T.Nonempty := ⟨s1, hs1, hs1'⟩
  have hTb : BddAbove T := ⟨t, fun s hs => hs.1.2⟩
  have hmem : sSup T ∈ T := hTc.csSup_mem hTne hTb
  have hafter : ∀ s ∈ Ioc (sSup T) t, 0 < M.ψ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have := le_csSup hTb ⟨⟨le_trans hmem.1.1 hs.1.le, hs.2⟩, hcon⟩
    linarith [hs.1]
  refine ⟨sSup T, hmem.1, hmem.2, hafter, fun hlt => ?_⟩
  rcases eq_or_lt_of_le hmem.2 with h | h
  · exact h
  · exfalso
    have ht : 0 < M.ψ t := hafter t ⟨hlt, le_rfl⟩
    obtain ⟨s', hs', hψs'⟩ := intermediate_value_Icc hmem.1.2 M.continuous_ψ.continuousOn
      (show (0:ℝ) ∈ Icc (M.ψ (sSup T)) (M.ψ t) by constructor <;> linarith)
    have hne : s' ≠ sSup T := by rintro rfl; linarith
    have := hafter s' ⟨lt_of_le_of_ne hs'.1 (Ne.symm hne), hs'.2⟩
    linarith

/-- Step (a): `h ≤ H` on `[0, τ]` and `h < H` before `τ`, as long as `|ψ| < π/2`. -/
theorem RW_lt_aux {t : ℝ} (ht : t ∈ Icc 0 F.τ)
    (hψ : ∀ s ∈ Icc 0 t, -(π / 2) < M.ψ s ∧ M.ψ s < π / 2) :
    M.RWy t ≤ m + c.w ∧ (t < F.τ → M.RWy t < m + c.w) := by
  by_cases hex : ∃ s ∈ Icc 0 t, M.ψ s ≤ 0
  · obtain ⟨sa, hsa, hψsa, hafter, hzero⟩ := F.last_nonpos hex
    have hsaτ : sa ∈ Icc 0 F.τ := ⟨hsa.1, hsa.2.trans ht.2⟩
    have hsin : sin (M.ψ sa) ≤ 0 :=
      sin_nonpos_of_nonpos_of_neg_pi_le hψsa (by linarith [(hψ sa hsa).1, pi_pos])
    have hRC := F.RCy_le hsaτ
    have hRCeq := M.RCy_eq sa
    have hdb := c.db_pos
    have hsa_le : M.RWy sa ≤ M.RCy sa := by nlinarith
    have hmono : M.RWy t ≤ M.RWy sa := by
      rcases eq_or_lt_of_le hsa.2 with h | h
      · rw [h]
      · apply F.RWy_anti hsa.2
        intro s hs
        have h0 : 0 ≤ M.ψ s := by
          rcases eq_or_lt_of_le hs.1 with h' | h'
          · rw [← h', hzero h]
          · exact (hafter s ⟨h', hs.2.le⟩).le
        exact sin_nonneg_of_nonneg_of_le_pi h0
          (by linarith [(hψ s ⟨le_trans hsa.1 hs.1, hs.2.le⟩).2, pi_pos])
    refine ⟨by linarith, fun hlt => ?_⟩
    have := F.hτlt sa ⟨hsa.1, lt_of_le_of_lt hsa.2 hlt⟩
    linarith
  · push Not at hex
    have hmono : M.RWy t ≤ M.RWy 0 := F.RWy_anti ht.1 (fun s hs =>
      sin_nonneg_of_nonneg_of_le_pi (hex s ⟨hs.1, hs.2.le⟩).le
        (by linarith [(hψ s ⟨hs.1, hs.2.le⟩).2, pi_pos]))
    have h0 := F.RW0_le
    have := mul_pos c.w_pos F.cos0_pos
    exact ⟨by linarith, fun _ => by linarith⟩

/-- The parked start has heading below `ψ_u`. -/
theorem ψ0_lt_ψu : M.ψ 0 < A.ψu := by
  by_contra hcon
  push Not at hcon
  have h0I : (0 : ℝ) ∈ Icc 0 F.τ := ⟨le_rfl, F.hτ0.le⟩
  have hRC := F.RC_curb h0I
  have hRW := F.RW0_le
  have hfit2 := A.ψfit_lt_pi_div_two
  have hψ := F.ψ0_bounds
  have hu := A.hψu_mem
  have a1 : cos (M.ψ 0) ≤ cos A.ψu :=
    cos_le_cos_of_nonneg_of_le_pi hu.1.le (by linarith [pi_pos]) hcon
  have a2 : sin A.ψu ≤ sin (M.ψ 0) :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) hcon
  have hψu := A.hψu
  have hRm := A.Rm_pos
  have h1 := mul_le_mul_of_nonneg_left a1 hRm.le
  have h2 := mul_le_mul_of_nonneg_left a2 c.db_pos.le
  have h3 := A.A2f.2
  have h4 := mul_le_mul_of_nonneg_left F.cos_ψfit_le_cos0 A.Rp_pos.le
  have e : c.Rp = c.Rm + c.w := by unfold Car.Rp Car.Rm; ring
  rw [e] at h3 h4
  nlinarith

/-- Heading bounds on `[0, τ]`: `-ψ_n < ψ < ψ_u`. -/
theorem heading {s : ℝ} (hs : s ∈ Icc 0 F.τ) : -A.ψn < M.ψ s ∧ M.ψ s < A.ψu := by
  by_contra hcon
  have ht : M.ψ s ≤ -A.ψn ∨ A.ψu ≤ M.ψ s := by
    by_cases h : -A.ψn < M.ψ s
    · right; by_contra h'; push Not at h'; exact hcon ⟨h, h'⟩
    · left; linarith
  have h0 : -A.ψn < M.ψ 0 := by linarith [F.ψ0_bounds.1, A.ψfit_lt_ψn]
  obtain ⟨t, htI, hval, hbefore⟩ := exists_first_exit M.continuous_ψ hs.1 h0 F.ψ0_lt_ψu ht
  have htτ : t ∈ Icc 0 F.τ := ⟨htI.1.le, htI.2.trans hs.2⟩
  have hn := A.hψn_mem
  have hu := A.hψu_mem
  have hrange : ∀ u ∈ Icc 0 t, -(π / 2) < M.ψ u ∧ M.ψ u < π / 2 := fun u hu' => by
    rcases eq_or_lt_of_le hu'.2 with h | h
    · rw [h]; rcases hval with hv | hv <;> rw [hv] <;> constructor <;> linarith
    · have := hbefore u ⟨hu'.1, h⟩; constructor <;> linarith
  have hRW := F.RW_lt_aux htτ hrange
  rcases hval with hv | hv
  · -- the front curb-side corner would be below the curb
    have hFC := F.FC_curb htτ
    rw [hv, sin_neg] at hFC
    have hsn := A.sin_ψn
    rcases eq_or_lt_of_le htτ.2 with h | h
    · have hRC := M.RCy_eq t
      rw [hv, sin_neg, h, F.hτH] at hRC
      have : 0 < sin A.ψn := sin_pos_of_pos_of_lt_pi hn.1 (by linarith [pi_pos])
      have := mul_pos c.db_pos this
      rw [← h] at hRC
      linarith [hRW.1]
    · have := hRW.2 h
      linarith
  · -- the rear curb-side corner would be below the curb
    have key : M.RWy t < c.db * sin A.ψu := by
      have hψu := A.hψu
      by_cases hex : ∃ u ∈ Icc 0 t, M.ψ u ≤ 0
      · obtain ⟨sa, hsa, hψsa, hafter, hzero⟩ := F.last_nonpos hex
        have hsat : sa < t := by
          rcases eq_or_lt_of_le hsa.2 with h | h
          · rw [h, hv] at hψsa; linarith
          · exact h
        have hψ0 := hzero hsat
        have hC' := F.C'y_anti hsa.2 (fun u hu' => by
          have h0 : 0 ≤ M.ψ u := by
            rcases eq_or_lt_of_le hu'.1 with h' | h'
            · rw [← h', hψ0]
            · exact (hafter u ⟨h', hu'.2.le⟩).le
          exact sin_nonneg_of_nonneg_of_le_pi h0
            (by linarith [(hrange u ⟨le_trans hsa.1 hu'.1, hu'.2.le⟩).2, pi_pos]))
        have hsaτ : sa ∈ Icc 0 F.τ := ⟨hsa.1, hsa.2.trans htτ.2⟩
        have hRWsa := (F.RW_lt_aux hsaτ (fun u hu' => hrange u ⟨hu'.1, hu'.2.trans hsa.2⟩)).2
          (lt_of_lt_of_le hsat htτ.2)
        have e1 := M.RWy_eq_C'y t
        have e2 := M.RWy_eq_C'y sa
        rw [hv] at e1
        rw [hψ0, cos_zero] at e2
        linarith
      · push Not at hex
        have hC' := F.C'y_anti htτ.1 (fun u hu' =>
          sin_nonneg_of_nonneg_of_le_pi (hex u ⟨hu'.1, hu'.2.le⟩).le
            (by linarith [(hrange u ⟨hu'.1, hu'.2.le⟩).2, pi_pos]))
        have e1 := M.RWy_eq_C'y t
        have e2 := M.RWy_eq_C'y 0
        rw [hv] at e1
        have h0 := F.RW0_le
        have h3 := A.A2f.2
        have h4 := mul_le_mul_of_nonneg_left F.cos_ψfit_le_cos0 A.Rp_pos.le
        have e : c.Rp = c.Rm + c.w := by unfold Car.Rp Car.Rm; ring
        rw [e] at h3 h4
        nlinarith
    have hRC := F.RC_curb htτ
    rw [hv] at hRC
    linarith


/-- The constant `λ = cos ψ_n · R b / R₊`. -/
def lam (_F : Rev A L M) : ℝ := cos A.ψn * (c.R * c.b / c.Rp)

theorem lam_pos : 0 < F.lam := by
  unfold lam
  have hn := A.hψn_mem
  have : 0 < cos A.ψn := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hn.2⟩
  have := A.Rp_pos; have := c.R_pos; have := c.b_pos
  positivity

/-- Replacement of the Gronwall step: `P_x + λ log (h + ε)` is non-increasing on `[0, τ]`. -/
theorem G_anti {ε : ℝ} (hε : 0 < ε) :
    AntitoneOn (fun s => M.X s + F.lam * Real.log (M.RWy s + ε)) (Icc 0 F.τ) := by
  have hR := c.R_pos
  have hw := c.w_pos
  have hlam := F.lam_pos
  apply antitoneOn_of_sq_incr'
  · refine M.continuous_X.continuousOn.add (continuousOn_const.mul ?_)
    refine (M.continuous_RWy.add continuous_const).continuousOn.log ?_
    intro x hx
    have := F.RW_nonneg hx
    exact (by linarith : (0:ℝ) < M.RWy x + ε).ne'
  intro x hx
  refine ⟨1 / c.R + 2 * F.lam / (c.R * ε), fun z hxz hzτ => ?_⟩
  have hxI : x ∈ Icc 0 F.τ := ⟨hx.1, hx.2.le⟩
  have hzI : z ∈ Icc 0 F.τ := ⟨by linarith [hx.1], hzτ⟩
  have hRWx := F.RW_nonneg hxI
  have hRWz := F.RW_nonneg hzI
  have hp : 0 < M.RWy x + ε := by linarith
  have hq : 0 < M.RWy z + ε := by linarith
  have hlog : Real.log (M.RWy z + ε) - Real.log (M.RWy x + ε) ≤
      (M.RWy z - M.RWy x) / (M.RWy x + ε) := by
    rw [← Real.log_div hq.ne' hp.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hq hp)
    have e : (M.RWy z + ε) / (M.RWy x + ε) - 1 = (M.RWy z - M.RWy x) / (M.RWy x + ε) := by
      field_simp; ring
    linarith
  have hX : M.X z - M.X x ≤ -(z - x) * cos (M.ψ x) + (z - x) ^ 2 / c.R := by
    have := (abs_le.mp (M.X_incr x z hxz.le)).2
    rw [F.hd] at this
    linarith
  have hYv := M.Yv_incr (-(c.w / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith [A.A0])
    x z hxz.le
  rw [F.hd] at hYv
  have eRW : M.RWy z - M.RWy x = (M.Y z + -(c.w / 2) * cos (M.ψ z)) -
      (M.Y x + -(c.w / 2) * cos (M.ψ x)) := by unfold Manoeuvre.RWy; ring
  rw [← eRW] at hYv
  have h2 := M.R_sin_incr x z hxz.le
  have hsd : |sin (M.ψ z - M.ψ x)| ≤ (z - x) / c.R := by
    rw [abs_mul, abs_of_pos hR] at h2
    rw [le_div_iff₀ hR]; linarith
  have hhead := F.heading hxI
  have hn := A.hψn_mem
  have hu := A.hψu_mem
  have hcos0 : 0 ≤ cos (M.ψ x) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hcn : sin (M.ψ x) < 0 → cos A.ψn ≤ cos (M.ψ x) := by
    intro hs
    have hψneg : M.ψ x < 0 := by
      by_contra hcon
      push Not at hcon
      have := sin_nonneg_of_nonneg_of_le_pi hcon (by linarith [pi_pos])
      linarith
    rw [← cos_neg (M.ψ x)]
    exact cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]) (by linarith)
  have hcψ : 0 < cos A.ψn := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hn.2⟩
  have hkey := rev_key_ineq hR hw A.A0 c.b_pos hε (by linarith : (0:ℝ) < z - x) hRWx
    (by positivity : (0:ℝ) ≤ 2 * (z - x) ^ 2 / c.R) hsd hcos0 hYv (F.FC_curb hxI) hcψ hcn
  have hlamdef : F.lam = cos A.ψn * (c.R * c.b / (c.R + c.w / 2)) := rfl
  rw [← hlamdef] at hkey
  have hlog' := mul_le_mul_of_nonneg_left hlog hlam.le
  show M.X z + F.lam * Real.log (M.RWy z + ε) - (M.X x + F.lam * Real.log (M.RWy x + ε)) ≤
    (1 / c.R + 2 * F.lam / (c.R * ε)) * (z - x) ^ 2
  have e : (1 / c.R + 2 * F.lam / (c.R * ε)) * (z - x) ^ 2 =
      (z - x) ^ 2 / c.R + F.lam * (2 * (z - x) ^ 2 / c.R / ε) := by
    field_simp
  rw [e]
  linarith

/-- At `τ` the wheel is high: `h(τ) ℓ ≥ H b`. -/
theorem RWτ_ge : (m + c.w) * c.b ≤ M.RWy F.τ * c.len := by
  have hτI : F.τ ∈ Icc 0 F.τ := ⟨F.hτ0.le, le_rfl⟩
  have hH := F.hτH
  rw [M.RCy_eq] at hH
  have hFC := F.FC_curb hτI
  have hRW := F.RW_nonneg hτI
  have hb := c.b_pos
  have hdb := c.db_pos
  unfold Car.len
  rcases le_or_gt (sin (M.ψ F.τ)) 0 with hs | hs
  · nlinarith
  · have : m + c.w < M.RWy F.τ := by nlinarith
    nlinarith [A.hm, c.w_pos]

/-- Step "room": the rear curb-side corner is right of the car behind at `τ`. -/
theorem RCx_τ_ge : 0 ≤ M.RCx F.τ := by
  have hmH : m < M.RCy F.τ := by rw [F.hτH]; linarith [c.w_pos]
  have hy : ∀ᶠ s in 𝓝[<] F.τ, m < M.RCy s :=
    (((M.continuous_RCy).tendsto F.τ).eventually_const_lt hmH).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ s in 𝓝[<] F.τ, 0 < s :=
    ((continuous_id.tendsto F.τ).eventually_const_lt F.hτ0).filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] F.τ, 0 ≤ M.RCx s := by
    filter_upwards [hy, hpos, self_mem_nhdsWithin] with s hs1 hs2 hs3
    have hsI : s ∈ Ico 0 F.τ := ⟨hs2.le, hs3⟩
    have hlt := F.hτlt s hsI
    by_contra hcon
    push Not at hcon
    have hfp : (M.config s).pt (-c.db) (-(c.w / 2)) ∈ footprint c (M.config s) :=
      ⟨-c.db, -(c.w / 2), le_rfl, by linarith [c.db_pos, c.b_pos], le_rfl,
        by linarith [c.w_pos], rfl⟩
    have hob : (M.config s).pt (-c.db) (-(c.w / 2)) ∈ obstacle c ⟨m, L⟩ := by
      rw [M.RC_eq]; exact Or.inl (Or.inr ⟨hcon, hs1, hlt⟩)
    exact Set.disjoint_left.mp (F.free ⟨hsI.1, hsI.2.le⟩) hfp hob
  exact ge_of_tendsto ((M.continuous_RCx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

theorem Xτ_ge : min (c.db * cos A.ψn + c.w / 2 * sin A.ψn) (c.db * cos A.ψu - c.w / 2 * sin A.ψu)
    ≤ M.X F.τ := by
  have h := F.heading ⟨F.hτ0.le, le_rfl⟩
  have h1 := A.fb_ge h.1.le h.2.le
  have h2 := F.RCx_τ_ge
  unfold Manoeuvre.RCx at h2
  linarith

theorem X0_le : M.X 0 ≤ L - c.b * cos A.ψfit + c.w / 2 * sin A.ψfit := by
  have hl := F.lane0.2
  have hψ := F.ψ0_bounds
  have hfit2 := A.ψfit_lt_pi_div_two
  have hc := F.cos_ψfit_le_cos0
  have hs : sin (M.ψ 0) ≤ sin A.ψfit :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hfit2.le hψ.2
  have := mul_le_mul_of_nonneg_left hc c.b_pos.le
  have := mul_le_mul_of_nonneg_left hs (half_pos c.w_pos).le
  linarith

theorem h0_pos : 0 < m + c.w - c.w * cos A.ψfit := by
  have := cos_le_one A.ψfit
  have := mul_le_mul_of_nonneg_left this c.w_pos.le
  linarith [A.hm]

/-- The estimate for each `ε > 0`. -/
theorem eps_bound {ε : ℝ} (hε : 0 < ε) :
    F.lam * (Real.log ((m + c.w) * c.b / c.len) - Real.log (m + c.w - c.w * cos A.ψfit + ε)) ≤
      M.X 0 - M.X F.τ := by
  have h0I : (0:ℝ) ∈ Icc 0 F.τ := ⟨le_rfl, F.hτ0.le⟩
  have hτI : F.τ ∈ Icc 0 F.τ := ⟨F.hτ0.le, le_rfl⟩
  have hG := F.G_anti hε h0I hτI F.hτ0.le
  simp only at hG
  have hlam := F.lam_pos
  have hl := c.len_pos
  have hHb : 0 < (m + c.w) * c.b / c.len := by
    have := A.hm; have := c.w_pos; have := c.b_pos; positivity
  have h1 : Real.log ((m + c.w) * c.b / c.len) ≤ Real.log (M.RWy F.τ + ε) := by
    apply Real.log_le_log hHb
    have := F.RWτ_ge
    rw [div_le_iff₀ hl]; nlinarith
  have hRW0 := F.RW_nonneg h0I
  have h2 : Real.log (M.RWy 0 + ε) ≤ Real.log (m + c.w - c.w * cos A.ψfit + ε) := by
    apply Real.log_le_log (by linarith)
    have := F.RW0_le
    have := mul_le_mul_of_nonneg_left F.cos_ψfit_le_cos0 c.w_pos.le
    linarith
  have := mul_le_mul_of_nonneg_left h1 hlam.le
  have := mul_le_mul_of_nonneg_left h2 hlam.le
  nlinarith

/-- Letting `ε → 0`. -/
theorem log_bound :
    F.lam * Real.log ((m + c.w) * c.b / (c.len * (m + c.w - c.w * cos A.ψfit))) ≤
      M.X 0 - M.X F.τ := by
  have h0 := F.h0_pos
  have hl := c.len_pos
  have hHb : 0 < (m + c.w) * c.b / c.len := by
    have := A.hm; have := c.w_pos; have := c.b_pos; positivity
  have e : Real.log ((m + c.w) * c.b / (c.len * (m + c.w - c.w * cos A.ψfit))) =
      Real.log ((m + c.w) * c.b / c.len) - Real.log (m + c.w - c.w * cos A.ψfit) := by
    rw [← Real.log_div hHb.ne' h0.ne']; congr 1; field_simp
  rw [e]
  have hc : ContinuousAt (fun ε : ℝ => F.lam * (Real.log ((m + c.w) * c.b / c.len) -
      Real.log (m + c.w - c.w * cos A.ψfit + ε))) 0 := by
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.sub continuousAt_const
    apply ContinuousAt.log (continuousAt_const.add continuousAt_id)
    simpa using h0.ne'
  have ht : Tendsto (fun ε : ℝ => F.lam * (Real.log ((m + c.w) * c.b / c.len) -
      Real.log (m + c.w - c.w * cos A.ψfit + ε))) (𝓝[>] 0)
      (𝓝 (F.lam * (Real.log ((m + c.w) * c.b / c.len) -
        Real.log (m + c.w - c.w * cos A.ψfit)))) := by
    convert hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0)) using 2 <;> simp
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact F.eps_bound hε

/-- **Proposition (reverse exits)**: `L ≥ B_back`, hence `L ≥ Λ₁`. -/
theorem Λ₁_le : A.Λ₁ ≤ L := by
  have h1 := F.log_bound
  have h2 := F.Xτ_ge
  have h3 := F.X0_le
  have h4 := A.A7c
  unfold lam at h1
  unfold OneAssumptions.Λ₁
  linarith

end Rev

end Parking

namespace Parking

variable {c : Car} {m : ℝ}

/-- **Proposition (reverse exits).** A reverse manoeuvre from a parked configuration with
`|ψ(0)| ≤ ψ_fit` to a lane configuration through free configurations needs `L ≥ Λ₁`. -/
theorem exit_reverse_lower (A : OneAssumptions c m) {L : ℝ} (M : Manoeuvre c) (hd : M.d = -1)
    (hfree : ∀ s ∈ Icc (0 : ℝ) M.len, Free c ⟨m, L⟩ (M.config s))
    (hstart : Parked c ⟨m, L⟩ M.start) (hend : InLane c ⟨m, L⟩ M.finish)
    (hψ0 : |M.ψ 0| ≤ A.ψfit) : A.Λ₁ ≤ L := by
  have hcos0 : 0 < cos (M.ψ 0) := by
    have := A.cos_gt_of_abs_le (hψ0.trans A.ψfit_lt_ψb.le)
    exact lt_of_le_of_lt (div_nonneg A.hm.le c.w_pos.le) this
  have hRC0 : M.RCy 0 < m + c.w := by
    have := hstart.2 _ ⟨-c.db, c.w / 2, le_rfl, by linarith [c.db_pos, c.b_pos],
      by linarith [c.w_pos], le_rfl, rfl⟩
    have h2 := mul_pos c.w_pos hcos0
    simp only [Manoeuvre.start, Manoeuvre.config_pt] at this
    unfold Manoeuvre.RCy
    have e : Slot.H c ⟨m, L⟩ = m + c.w := rfl
    linarith
  have hRCend : m + c.w ≤ M.RCy M.len := by
    have := hend.1 _ ⟨-c.db, -(c.w / 2), le_rfl, by linarith [c.db_pos, c.b_pos], le_rfl,
      by linarith [c.w_pos], rfl⟩
    simp only [Manoeuvre.finish, Manoeuvre.config_pt] at this
    unfold Manoeuvre.RCy
    have e : Slot.H c ⟨m, L⟩ = m + c.w := rfl
    linarith
  obtain ⟨τ, hτ, hτH, hτlt⟩ := exists_first_ge M.continuous_RCy M.len_nonneg hRC0 hRCend
  exact (Rev.mk hd hfree hstart hψ0 τ hτ.1 hτ.2 hτH hτlt).Λ₁_le

end Parking
