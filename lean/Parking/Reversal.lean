/-
Time reversal of manoeuvres (Lemma `lem:reversal`).
-/
import Parking.Kinematics

open Real Set intervalIntegral

noncomputable section

namespace Parking

variable {c : Car}

namespace Manoeuvre

/-- The reversed manoeuvre: same path traversed backwards, opposite direction. -/
def reverse (M : Manoeuvre c) : Manoeuvre c where
  d := -M.d
  hd := by rcases M.hd with h | h <;> simp [h]
  len := M.len
  len_nonneg := M.len_nonneg
  x0 := M.X M.len
  y0 := M.Y M.len
  ψ := fun s => M.ψ (M.len - s)
  lip := fun s t => by
    have := M.lip (M.len - s) (M.len - t)
    rwa [show M.len - s - (M.len - t) = -(s - t) by ring, abs_neg] at this

theorem reverse_X (M : Manoeuvre c) (s : ℝ) : M.reverse.X s = M.X (M.len - s) := by
  have hc : Continuous fun σ => cos (M.ψ σ) := continuous_cos.comp M.continuous_ψ
  simp only [X, reverse]
  have h1 : (∫ σ in (0:ℝ)..s, cos (M.ψ (M.len - σ))) = ∫ σ in (M.len - s)..M.len, cos (M.ψ σ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun σ => cos (M.ψ σ))]
    simp
  have h2 : (∫ σ in (0:ℝ)..M.len, cos (M.ψ σ)) =
      (∫ σ in (0:ℝ)..(M.len - s), cos (M.ψ σ)) + ∫ σ in (M.len - s)..M.len, cos (M.ψ σ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  rw [h1, h2]; ring

theorem reverse_Y (M : Manoeuvre c) (s : ℝ) : M.reverse.Y s = M.Y (M.len - s) := by
  have hc : Continuous fun σ => sin (M.ψ σ) := continuous_sin.comp M.continuous_ψ
  simp only [Y, reverse]
  have h1 : (∫ σ in (0:ℝ)..s, sin (M.ψ (M.len - σ))) = ∫ σ in (M.len - s)..M.len, sin (M.ψ σ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun σ => sin (M.ψ σ))]
    simp
  have h2 : (∫ σ in (0:ℝ)..M.len, sin (M.ψ σ)) =
      (∫ σ in (0:ℝ)..(M.len - s), sin (M.ψ σ)) + ∫ σ in (M.len - s)..M.len, sin (M.ψ σ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  rw [h1, h2]; ring

theorem reverse_config (M : Manoeuvre c) (s : ℝ) :
    M.reverse.config s = M.config (M.len - s) := by
  ext
  · exact M.reverse_X s
  · exact M.reverse_Y s
  · rfl

theorem reverse_start (M : Manoeuvre c) : M.reverse.start = M.finish := by
  simp [start, finish, reverse_config]

theorem reverse_finish (M : Manoeuvre c) : M.reverse.finish = M.start := by
  show M.reverse.config M.reverse.len = M.config 0
  rw [reverse_config]
  simp [reverse]

end Manoeuvre

end Parking
