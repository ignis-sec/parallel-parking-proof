# Lean formalisation of "minimal parallel-parking slot length"

Lean 4 (v4.35.0) + Mathlib (v4.35.0). Build with

    lake exe cache get   # optional, fetches Mathlib binaries
    lake build           # builds the library `Parking` (all files except AsymAxiom)
    lake build Parking.AsymAxiom

The development has no `sorry`. Every theorem depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The exceptions are the three theorems in
`Parking/AsymAxiom.lean`, which use the single labelled axiom `paper_asym_bounds` (see below).

## Files

| File | Content |
|---|---|
| `Model.lean` | car, configurations, footprint, slot with margin `m` (parked cars at `m < y < H`, `H = m + w`), open obstacles, `Free`, `Parked`, `InLane`, `Manoeuvre` (1/R-Lipschitz heading, position as an integral), parking motions, `Feasible c m n L`, `Lmin` |
| `Basic.lean` | monotonicity in `L` and `n`; `Lmin_antitone` |
| `Kinematics.lean` | continuity, derivatives of the position, curb constraint |
| `Flush.lean` | **zero margin is degenerate**: `not_feasible_zero_margin` |
| `Dini.lean`, `Monotone.lean` | Dini-type monotonicity from second-order increment bounds; first hitting times; increment bounds |
| `Reversal.lean` | time reversal of manoeuvres |
| `Centres.lean` | turning centres; distance identity in increment form (`distSq_incr`) |
| `OneDefs.lean` | `OneAssumptions c m` = Assumption (A1)–(A7) of the paper; `Λ₁` |
| `OneUpper.lean` | explicit exit for `L = Λ₁`: `feasible_one_at_Λ₁` |
| `OneParked.lean` | band lemmas; lane-side corners of a parked car |
| `OneMin.lean` | facts about the assumptions; minimisation of `φ` (Step 9) |
| `OneForward.lean` | **forward exits**: `exit_forward_lower` |
| `OneReverse.lean` | **reverse exits**: `exit_reverse_lower` |
| `OneNormalize.lean` | parked headings are near `kπ`; `2π`-shift and mirror; `exit_one_lower` |
| `One.lean` | **Theorem one**: `feasible_one_iff : Feasible c m 1 L ↔ A.Λ₁ ≤ L`, `Lmin_one : Lmin c m 1 = A.Λ₁` |
| `AsymCore.lean` | `K² = ∫₀^w du/r_*(u) = 4Rw - w³/(6R)`, calibration inequality, loop area |
| `Asym.lean` | **Theorems asym / mono (limit part)** from the hypotheses `AsymLower`, `AsymUpper` |
| `AsymAxiom.lean` | the labelled axiom `paper_asym_bounds` and unconditional `thm_asym`, `thm_mono_limit`, `thm_mono_gt` |

## What is assumed

* `OneAssumptions c m` collects the geometric inequalities (A1)–(A7) under which the paper
  proves Theorem one. They are hypotheses of the theorem, as in the paper. Checking them for a
  concrete car is numerical (appendix A of the paper) and is not done in Lean.
* Propositions `prop:asym-lower` and `prop:asym-upper` of the paper (the bounds
  `liminf g² N(g) ≥ K²` and `limsup g² N(g) ≤ K²`) are **not formalised**. In `Asym.lean` they
  are the explicit hypotheses `AsymLower c m` and `AsymUpper c m`. Their proofs (confinement,
  windows, calibration error terms, tilted S-curve construction) are long, uniform-in-`g`
  perturbation arguments.
  `AsymAxiom.lean` packages them as the axiom `paper_asym_bounds`, which is imported by
  no other file.
* Convention: `Lmin` is a real infimum, so `Lmin c m n = 0` when no slot is feasible. This is why
  monotonicity statements carry a feasibility hypothesis.

## Not formalised

The two-manoeuvre constructions and all numerical values in Section 5 of the paper, and the
soft-curb variant of Sections 7 and 8.
