/-
Definitions for the one-manoeuvre theorem (Theorem `thm:one` of the paper):
the assumption package `OneAssumptions` (Assumption 4.1) and the value `Λ₁`.

All auxiliary angles are carried as data together with their defining equations,
which avoids having to manipulate closed forms involving `arcsin`/`arccos`.
-/
import Parking.Centres

open Real Set

noncomputable section

namespace Parking

namespace Car

variable (c : Car)

/-- `X(ψ) = d_b cos ψ - R₋ sin ψ` and `Y(ψ) = R₋ cos ψ - b sin ψ`. -/
def Xf (ψ : ℝ) : ℝ := c.db * cos ψ - c.Rm * sin ψ
def Yf (ψ : ℝ) : ℝ := c.Rm * cos ψ - c.b * sin ψ

end Car

/-- Assumption 4.1 of the paper, for a car `c` and margin `m` (with `H = m + w`).
The angles are given with their defining properties. -/
structure OneAssumptions (c : Car) (m : ℝ) where
  -- auxiliary angles
  ψfit : ℝ
  ψb : ℝ
  ψd : ℝ
  γ : ℝ
  β : ℝ
  ψn : ℝ
  ψu : ℝ
  hψfit : c.len * sin ψfit + c.w * cos ψfit = m + c.w
  hψfit_pos : 0 < ψfit
  hψfit_lt : ψfit < Real.arctan (c.len / c.w)
  hψb : c.len * sin ψb = m + c.w
  hψb_mem : 0 < ψb ∧ ψb < π / 2
  hγ : c.ρ * cos γ = c.b ∧ c.ρ * sin γ = c.Rp
  hγ_mem : 0 < γ ∧ γ < π / 2
  hβ : c.r * cos β = c.Rp ∧ c.r * sin β = c.db
  hβ_mem : 0 < β ∧ β < π / 2
  hψd : c.Yf ψd = c.r - (m + c.w)
  hψd_mem : 0 ≤ ψd ∧ ψd ≤ ψfit
  hψn : c.b * sin ψn = m + c.w
  hψn_mem : 0 < ψn ∧ ψn < π / 2
  hψu : c.Rm * (1 - cos ψu) + c.db * sin ψu = m + c.w
  hψu_mem : 0 < ψu ∧ ψu < π / 2
  -- (A1)
  A1a : c.db < c.b
  A1b : c.b * c.db < c.Rp ^ 2
  A1c : c.r - c.Rp ≤ m
  -- standing assumption R > w/2
  A0 : c.w / 2 < c.R
  hm : 0 < m
  -- (A2)
  A2a : m + c.w < c.len
  A2b : m + c.w < c.b
  A2c : m + c.w < c.Rm + c.db
  A2d : m / c.w < cos ψb
  A2e : ψfit < β
  A2f : m + c.w < c.Rp * cos ψfit ∧ c.Rm < c.Rp * cos ψfit
  A2g : c.db * Real.tan (ψfit / 2) ≤ c.Rm
  -- (A3)
  A3a : c.w * c.ρ < 2 * c.R * c.b
  A3b : m * c.ρ < c.w * c.b
  A3c : (m + c.w) * c.Rp < c.b * c.ρ
  -- (A4)
  A4 : c.r - (m + c.w) ≤ (c.Rp ^ 2 - c.b * c.db) / c.r
  -- (A5)
  A5a : c.Rm * sin ψd + c.b < cos ψd * Real.sqrt (c.b ^ 2 + 2 * c.R * c.w)
  A5b : 2 * (c.Rm + c.db * sin ψfit) *
          Real.sqrt (c.ρ ^ 2 + 2 * c.b / sin ψb * (c.r - (m + c.w) - c.Yf ψfit)) <
        c.b * cos ψfit * (2 * c.Yf ψfit + 2 * c.b / sin ψb)
  -- (A6)
  A6a : m + c.w ≤ c.r - c.db
  A6b : 0 ≤ c.Xf ψd
  -- (A7)
  A7a : c.Xf ψd + Real.sqrt (c.ρ ^ 2 - (c.r - (m + c.w)) ^ 2) ≤
          c.db * cos ψfit - c.Rp * sin ψfit + c.ρ
  A7b : c.len * (m + c.w - c.w * cos ψfit) < (m + c.w) * c.b
  A7c : c.Xf ψd + Real.sqrt (c.ρ ^ 2 - (c.r - (m + c.w)) ^ 2) ≤
          c.b * cos ψfit - c.w / 2 * sin ψfit +
            min (c.db * cos ψn + c.w / 2 * sin ψn) (c.db * cos ψu - c.w / 2 * sin ψu) +
            cos ψn * (c.R * c.b / c.Rp) *
              Real.log ((m + c.w) * c.b / (c.len * (m + c.w - c.w * cos ψfit)))

/-- The one-manoeuvre length `Λ₁ = X(ψ_d) + √(ρ² - (r - H)²)`. -/
def OneAssumptions.Λ₁ {c : Car} {m : ℝ} (A : OneAssumptions c m) : ℝ :=
  c.Xf A.ψd + Real.sqrt (c.ρ ^ 2 - (c.r - (m + c.w)) ^ 2)

end Parking
