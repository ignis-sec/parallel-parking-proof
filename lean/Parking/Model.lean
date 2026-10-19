/-
Copyright (c) 2026. All rights reserved.
Formalisation of the parallel-parking model of the accompanying paper
"How long must a parallel-parking space be?".

This file contains the model: car geometry, configurations, footprints,
the slot (margin model), manoeuvres and motions, and the feasibility predicate.
-/
import Mathlib

open Real Set

noncomputable section

namespace Parking

/-- Car parameters: front overhang `df`, wheelbase `dw`, rear overhang `db`,
width `w`, maximal steering angle `θ`. -/
structure Car where
  df : ℝ
  dw : ℝ
  db : ℝ
  w : ℝ
  θ : ℝ
  df_pos : 0 < df
  dw_pos : 0 < dw
  db_pos : 0 < db
  w_pos : 0 < w
  θ_pos : 0 < θ
  θ_lt : θ < π / 2

namespace Car

variable (c : Car)

/-- Minimal turning radius of the rear-axle midpoint. -/
def R : ℝ := c.dw / Real.tan c.θ

/-- Distance from the rear axle to the front bumper. -/
def b : ℝ := c.dw + c.df

/-- Length of the car. -/
def len : ℝ := c.b + c.db

/-- Inner and outer radii `R ∓ w/2`. -/
def Rm : ℝ := c.R - c.w / 2
def Rp : ℝ := c.R + c.w / 2

/-- Distance from the left turning centre to the front curb-side corner. -/
def ρ : ℝ := Real.sqrt (c.b ^ 2 + c.Rp ^ 2)

/-- Distance from the left turning centre to the rear curb-side corner. -/
def r : ℝ := Real.sqrt (c.db ^ 2 + c.Rp ^ 2)

theorem R_pos : 0 < c.R := by
  unfold R
  have h1 : 0 < Real.tan c.θ := Real.tan_pos_of_pos_of_lt_pi_div_two c.θ_pos c.θ_lt
  exact div_pos c.dw_pos h1

theorem b_pos : 0 < c.b := by unfold b; linarith [c.dw_pos, c.df_pos]

theorem len_pos : 0 < c.len := by unfold len; linarith [c.b_pos, c.db_pos]

end Car

/-- A configuration: rear-axle midpoint `(x, y)` and heading `ψ`. -/
@[ext]
structure Config where
  x : ℝ
  y : ℝ
  ψ : ℝ

/-- The world point with body coordinates `(u, v)` (u forward, v to the left). -/
def Config.pt (q : Config) (u v : ℝ) : ℝ × ℝ :=
  (q.x + u * cos q.ψ - v * sin q.ψ, q.y + u * sin q.ψ + v * cos q.ψ)

/-- The footprint of the car in configuration `q`. -/
def footprint (c : Car) (q : Config) : Set (ℝ × ℝ) :=
  {p | ∃ u v, -c.db ≤ u ∧ u ≤ c.b ∧ -(c.w / 2) ≤ v ∧ v ≤ c.w / 2 ∧ p = q.pt u v}

/-- The slot: margin `m` of the parked cars from the curb and slot length `L`. -/
structure Slot where
  m : ℝ
  L : ℝ

/-- Height of the outer sides of the parked cars. -/
def Slot.H (c : Car) (S : Slot) : ℝ := S.m + c.w

/-- The obstacles: the curb half-plane and the two parked cars (open sets). -/
def obstacle (c : Car) (S : Slot) : Set (ℝ × ℝ) :=
  {p | p.2 < 0} ∪ {p | p.1 < 0 ∧ S.m < p.2 ∧ p.2 < S.H c} ∪
    {p | S.L < p.1 ∧ S.m < p.2 ∧ p.2 < S.H c}

/-- A configuration is free if its footprint misses the obstacles. -/
def Free (c : Car) (S : Slot) (q : Config) : Prop :=
  Disjoint (footprint c q) (obstacle c S)

/-- Parked: free and below the outer sides of the parked cars. -/
def Parked (c : Car) (S : Slot) (q : Config) : Prop :=
  Free c S q ∧ ∀ p ∈ footprint c q, p.2 ≤ S.H c

/-- Lane configuration: entirely in the lane and parallel to the curb. -/
def InLane (c : Car) (S : Slot) (q : Config) : Prop :=
  (∀ p ∈ footprint c q, S.H c ≤ p.2) ∧ ∃ k : ℤ, q.ψ = k * π

/-- A manoeuvre of direction `d = ±1` and length `len`, parametrised by arc length.
The heading is `1/R`-Lipschitz (bounded curvature) and the rear-axle midpoint moves
with unit speed along `d • (cos ψ, sin ψ)`. -/
structure Manoeuvre (c : Car) where
  d : ℝ
  hd : d = 1 ∨ d = -1
  len : ℝ
  len_nonneg : 0 ≤ len
  x0 : ℝ
  y0 : ℝ
  ψ : ℝ → ℝ
  lip : ∀ s t, |ψ s - ψ t| ≤ |s - t| / c.R

namespace Manoeuvre

variable {c : Car} (M : Manoeuvre c)

/-- Position of the rear-axle midpoint at arc length `s`. -/
def X (s : ℝ) : ℝ := M.x0 + M.d * ∫ σ in (0 : ℝ)..s, cos (M.ψ σ)
def Y (s : ℝ) : ℝ := M.y0 + M.d * ∫ σ in (0 : ℝ)..s, sin (M.ψ σ)

/-- Configuration at arc length `s`. -/
def config (s : ℝ) : Config := ⟨M.X s, M.Y s, M.ψ s⟩

def start : Config := M.config 0
def finish : Config := M.config M.len

end Manoeuvre

/-- A motion: a list of manoeuvres whose consecutive endpoints match. -/
def Chain {c : Car} : List (Manoeuvre c) → Prop
  | [] => True
  | [_] => True
  | M :: M' :: rest => M.finish = M'.start ∧ Chain (M' :: rest)

/-- All configurations along all manoeuvres are free. -/
def AllFree (c : Car) (S : Slot) (μ : List (Manoeuvre c)) : Prop :=
  ∀ M ∈ μ, ∀ s ∈ Icc (0 : ℝ) M.len, Free c S (M.config s)

/-- A parking motion with at most `n` manoeuvres. -/
def ParkingMotion (c : Car) (S : Slot) (n : ℕ) (μ : List (Manoeuvre c)) : Prop :=
  ∃ (M₀ M₁ : Manoeuvre c), μ.head? = some M₀ ∧ μ.getLast? = some M₁ ∧
    μ.length ≤ n ∧ Chain μ ∧ AllFree c S μ ∧ InLane c S M₀.start ∧ Parked c S M₁.finish

/-- Feasibility of parking in a slot of length `L` with at most `n` manoeuvres. -/
def Feasible (c : Car) (m : ℝ) (n : ℕ) (L : ℝ) : Prop :=
  ∃ μ, ParkingMotion c ⟨m, L⟩ n μ

/-- The minimal slot length (as an infimum in `ℝ`; meaningful when feasible slots exist). -/
def Lmin (c : Car) (m : ℝ) (n : ℕ) : ℝ := sInf {L | 0 < L ∧ Feasible c m n L}

end Parking
