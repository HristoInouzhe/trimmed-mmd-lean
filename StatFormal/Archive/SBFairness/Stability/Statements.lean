import StatFormal.Archive.SBFairness.Decay.Statements
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# FROZEN STATEMENTS — SB fairness repair: `prop:stability` and the constant of `eq:modulus`

Sources: `schrodinger_bridge_fairness_repair.tex:1747-1760` (`prop:stability`, proof `:2887-2899`) and
`:1368-1395` (`prop:twopoint`, `eq:modulus` and its proof). DEFECTS #1.

* `prop:stability` is stated in `ℝᵈ` (paper: `d = 1`, plans on `ℝ²` with the Euclidean metric). Plans
  live on `ℝᵈ × ℝᵈ` with Lean's product (max) metric; since `W₂^{max} ≤ W₂^{Euclid}` this is *stronger*
  than the paper's statement, and it holds because `|(1−t)Δ₀ + tΔ₁| ≤ max(|Δ₀|,|Δ₁|)`.
* Total variation is defined here (`tv`) as `sup_A |μ(A) − ν(A)|` over measurable `A` (this Mathlib pin
  predates `tvDist`). `μ^{⊗n}` is `Measure.pi`. "Laws on `[0,1]^d`" = probability measures concentrated on the
  cube.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal

namespace StatFormal.SBFairness.Stability

open StatFormal.SBFairness.Decay

/-- Total variation distance `sup_A |μ(A) − ν(A)|` (finite measures). -/
def tv {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |(μ A.1).toReal - (ν A.1).toReal|

/-- The unit cube `[0,1]^d` in `EuclideanSpace ℝ (Fin d)`. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

namespace Claims

/-- `prop:stability`: for every `t ∈ [0,1]`, `W₂(μ̂_t, μ_t) ≤ W₂(π̂, π)` (bridges built with the same `ε`). -/
def stability : Prop :=
  ∀ (d : ℕ) (π π' : Measure ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))))
    [IsProbabilityMeasure π] [IsProbabilityMeasure π'] (ε t : ℝ), 0 ≤ ε → t ∈ Icc (0 : ℝ) 1 →
      wassersteinEDist 2 (bridge π' ε t) (bridge π ε t) ≤ wassersteinEDist 2 π' π

/-- `eq:modulus` is false as printed: it is not true that for all `d, n ≥ 1` and all laws `μ, μ'` on
`[0,1]^d` with `TV(μ^{⊗n}, μ'^{⊗n}) ≤ ½` one has `W₂(μ,μ') ≤ d^{1/4}(2 log 2)^{1/4} n^{−1/4}`
(witness `n = 1`, `d = 6`, `μ = δ₀`, `μ' = ½δ₀ + ½δ_{(1,…,1)}`, `W₂ = √3`). -/
def modulus_false : Prop :=
  ¬ ∀ (d n : ℕ) (μ μ' : Measure (EuclideanSpace ℝ (Fin d))), 1 ≤ d → 1 ≤ n →
      IsProbabilityMeasure μ → IsProbabilityMeasure μ' → μ (cube d)ᶜ = 0 → μ' (cube d)ᶜ = 0 →
      tv (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => μ') ≤ 1 / 2 →
        wassersteinEDist 2 μ μ' ≤
          ENNReal.ofReal ((d : ℝ) ^ ((1 : ℝ) / 4) * (2 * Real.log 2) ^ ((1 : ℝ) / 4) *
            (n : ℝ) ^ (-(1 : ℝ) / 4))

end Claims
end StatFormal.SBFairness.Stability
