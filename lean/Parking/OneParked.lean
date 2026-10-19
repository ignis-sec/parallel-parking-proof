/-
Geometric facts about free and parked configurations: the "band" arguments showing that
footprint points at heights in `(m, H]` lie between the parked cars.
-/
import Parking.OneUpper

open Real Set

noncomputable section

namespace Parking

variable {c : Car}

/-- A footprint point at a height in `(m, H]` lies right of the car behind. -/
theorem band_left {S : Slot} {q : Config} (hf : Free c S q) {u v : ℝ}
    (hu1 : -c.db ≤ u) (hu2 : u ≤ c.b) (hv1 : -(c.w / 2) < v) (hv2 : v ≤ c.w / 2)
    (hk : 0 < cos q.ψ) (hm : S.m < (q.pt u v).2) (hH : (q.pt u v).2 ≤ S.H c) :
    0 ≤ (q.pt u v).1 := by
  by_contra hx
  push Not at hx
  set x := (q.pt u v).1 with hxdef
  set y := (q.pt u v).2 with hydef
  set ε := min (min ((v + c.w / 2) / 2) ((y - S.m) / (2 * cos q.ψ))) (-x / 2) with hε
  have hε1 : ε ≤ (v + c.w / 2) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ (y - S.m) / (2 * cos q.ψ) := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ -x / 2 := min_le_right _ _
  have hεpos : 0 < ε := lt_min (lt_min (by linarith) (div_pos (by linarith) (by positivity)))
    (by linarith)
  have hp : q.pt u (v - ε) ∈ footprint c q :=
    ⟨u, v - ε, hu1, hu2, by linarith, by linarith, rfl⟩
  have hob : q.pt u (v - ε) ∈ obstacle c S := by
    have hy' : (q.pt u (v - ε)).2 = y - ε * cos q.ψ := by
      simp only [hydef, Config.pt]; ring
    have hx' : (q.pt u (v - ε)).1 = x + ε * sin q.ψ := by
      simp only [hxdef, Config.pt]; ring
    have hεk : ε * cos q.ψ ≤ (y - S.m) / 2 := by
      calc ε * cos q.ψ ≤ (y - S.m) / (2 * cos q.ψ) * cos q.ψ :=
            mul_le_mul_of_nonneg_right hε2 hk.le
        _ = (y - S.m) / 2 := by field_simp
    have hs : ε * sin q.ψ ≤ ε := by
      have := sin_le_one q.ψ; nlinarith
    refine Or.inl (Or.inr ⟨?_, ?_, ?_⟩)
    · rw [hx']; linarith
    · rw [hy']; linarith
    · rw [hy']; have : 0 < ε * cos q.ψ := mul_pos hεpos hk; linarith
  exact Set.disjoint_left.mp hf hp hob

/-- A footprint point at a height in `(m, H]` lies left of the car in front. -/
theorem band_right {S : Slot} {q : Config} (hf : Free c S q) {u v : ℝ}
    (hu1 : -c.db ≤ u) (hu2 : u ≤ c.b) (hv1 : -(c.w / 2) < v) (hv2 : v ≤ c.w / 2)
    (hk : 0 < cos q.ψ) (hm : S.m < (q.pt u v).2) (hH : (q.pt u v).2 ≤ S.H c) :
    (q.pt u v).1 ≤ S.L := by
  by_contra hx
  push Not at hx
  set x := (q.pt u v).1 with hxdef
  set y := (q.pt u v).2 with hydef
  set ε := min (min ((v + c.w / 2) / 2) ((y - S.m) / (2 * cos q.ψ))) ((x - S.L) / 2) with hε
  have hε1 : ε ≤ (v + c.w / 2) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ (y - S.m) / (2 * cos q.ψ) := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ (x - S.L) / 2 := min_le_right _ _
  have hεpos : 0 < ε := lt_min (lt_min (by linarith) (div_pos (by linarith) (by positivity)))
    (by linarith)
  have hp : q.pt u (v - ε) ∈ footprint c q :=
    ⟨u, v - ε, hu1, hu2, by linarith, by linarith, rfl⟩
  have hob : q.pt u (v - ε) ∈ obstacle c S := by
    have hy' : (q.pt u (v - ε)).2 = y - ε * cos q.ψ := by
      simp only [hydef, Config.pt]; ring
    have hx' : (q.pt u (v - ε)).1 = x + ε * sin q.ψ := by
      simp only [hxdef, Config.pt]; ring
    have hεk : ε * cos q.ψ ≤ (y - S.m) / 2 := by
      calc ε * cos q.ψ ≤ (y - S.m) / (2 * cos q.ψ) * cos q.ψ :=
            mul_le_mul_of_nonneg_right hε2 hk.le
        _ = (y - S.m) / 2 := by field_simp
    have hs : -ε ≤ ε * sin q.ψ := by
      have := neg_one_le_sin q.ψ; nlinarith
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [hx']; linarith
    · rw [hy']; linarith
    · rw [hy']; have : 0 < ε * cos q.ψ := mul_pos hεpos hk; linarith
  exact Set.disjoint_left.mp hf hp hob

/-- For a parked car whose heading has `cos ψ > m / w`, the rear lane-side corner is right of
the car behind and the front lane-side corner is left of the car in front. -/
theorem Parked.lane_corners {m L : ℝ} {q : Config} (hp : Parked c ⟨m, L⟩ q) (hm : 0 ≤ m)
    (hk : m / c.w < cos q.ψ) :
    0 ≤ (q.pt (-c.db) (c.w / 2)).1 ∧ (q.pt c.b (c.w / 2)).1 ≤ L := by
  have hw := c.w_pos
  have hdb := c.db_pos
  have hb := c.b_pos
  have hk0 : 0 < cos q.ψ := lt_of_le_of_lt (div_nonneg hm hw.le) hk
  have hwk : m < c.w * cos q.ψ := by
    have := (div_lt_iff₀ hw).mp hk; linarith
  have hRC := hp.1.pt_y_nonneg (u := -c.db) (v := -(c.w / 2)) le_rfl (by linarith) le_rfl
    (by linarith)
  have hFC := hp.1.pt_y_nonneg (u := c.b) (v := -(c.w / 2)) (by linarith) le_rfl le_rfl
    (by linarith)
  have hRLtop := hp.2 (q.pt (-c.db) (c.w / 2)) ⟨-c.db, c.w / 2, le_rfl, by linarith, by linarith,
    le_rfl, rfl⟩
  have hFLtop := hp.2 (q.pt c.b (c.w / 2)) ⟨c.b, c.w / 2, by linarith, le_rfl, by linarith,
    le_rfl, rfl⟩
  simp only [Config.pt] at hRC hFC
  constructor
  · apply band_left hp.1 le_rfl (by linarith) (by linarith) le_rfl hk0
    · simp only [Config.pt]; linarith
    · exact hRLtop
  · apply band_right hp.1 (by linarith) le_rfl (by linarith) le_rfl hk0
    · simp only [Config.pt]; linarith
    · exact hFLtop

end Parking
