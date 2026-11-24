import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic

/-!
# FROZEN STATEMENTS — context distributions for ICL: uniform deviation over joint laws (risk part)

Source (verbatim in `inventory/extracted/context-distribution-icl.md`): `thm:joint`
(`paper/v3/sections/06_estimation.tex:76`), with the setting of `subsec:free-guarantees` (`:66-75`):
conditionally on the pool, validation points are i.i.d. `P_0`; for a law `Π` on index tuples the
per-query risk is `G(·;Π) = Σ_j Π(j) L(·; z_j)`; `𝒜` is the mean risk.

Covered: the **risk part** (`λ_cov = 0`): with probability `≥ 1 − δ`,
`sup_Π |J_m(Π) − J_pool(Π)| ≤ 4 B_L √(2M log n / m) + B_L √(log(1/δ)/(2m))` over all laws on `[n]^M`,
and the refinement for laws on `M`-subsets (`2 B_L √(2 log(2 C(n,M))/m)` as first term), plus
`log C(n,M) ≤ M log(e n/M)`.
Not covered (declared): the coverage term (`λ_cov > 0`, kernel ratio `K_max/K_min`), which needs
Rademacher contraction; `cor:consistency`.

Encodings (see card):
* the pool is fixed: `L j z ∈ [0, B_L]` is the (measurable) loss of query `z` under context tuple `j`;
* index tuples `[n]^M` are `Fin M → Fin n`; `M`-subsets are `{S : Finset (Fin n) // S.card = M}`;
* a law `Π` on a finite index type is a probability vector; `J_m(Π) − J_pool(Π) =
  Σ_j Π(j) (m⁻¹ Σ_i L_j(Z_i) − E_{P_0} L_j)`;
* the validation sample is `X : Fin m → Ω → Z`, independent with law `P_0 = μ`;
* context length `M ≥ 1` (implicit in the paper; for `M = 0` the first term vanishes and the two-sided
  bound fails, e.g. `m = 1`, `L ∈ {0, B_L}` a fair coin, `δ > e^{-1/2}`).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset MeasureTheory ProbabilityTheory

namespace StatFormal.ICL.Joint

/-- Probability vectors on a finite index type. -/
def ProbVec {ι : Type*} [Fintype ι] (law : ι → ℝ) : Prop := (∀ j, 0 ≤ law j) ∧ ∑ j, law j = 1

/-- `J_m(Π) − J_pool(Π)` for the mean risk, `λ_cov = 0`. -/
def devJ {ι Z : Type*} [Fintype ι] [MeasurableSpace Z] (μ : Measure Z) (m : ℕ) (L : ι → Z → ℝ)
    (law : ι → ℝ) (zs : Fin m → Z) : ℝ :=
  ∑ j, law j * ((1 / (m : ℝ)) * ∑ i, L j (zs i) - ∫ z, L j z ∂μ)

namespace Claims

/-- `thm:joint`, risk part, laws on `[n]^M`. -/
def joint_risk : Prop :=
  ∀ (Z Ω : Type) [MeasurableSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n M m : ℕ) (L : (Fin M → Fin n) → Z → ℝ)
    (BL δ : ℝ) (X : Fin m → Ω → Z),
    2 ≤ n → 1 ≤ M → 0 < m → 0 < δ → δ < 1 →
    (∀ j, Measurable (L j)) → (∀ j z, 0 ≤ L j z ∧ L j z ≤ BL) →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = μ) →
      ENNReal.ofReal (1 - δ) ≤
        P {ω | ∀ law : (Fin M → Fin n) → ℝ, ProbVec law →
          |devJ μ m L law (fun i => X i ω)| ≤
            4 * BL * √(2 * M * Real.log n / m) + BL * √(Real.log (1 / δ) / (2 * m))}

/-- `thm:joint`, risk part, laws on `M`-subsets: first term `2 B_L √(2 log(2 C(n,M))/m)`. -/
def joint_risk_subsets : Prop :=
  ∀ (Z Ω : Type) [MeasurableSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n M m : ℕ)
    (L : {S : Finset (Fin n) // S.card = M} → Z → ℝ) (BL δ : ℝ) (X : Fin m → Ω → Z),
    2 ≤ n → M ≤ n → 0 < m → 0 < δ → δ < 1 →
    (∀ j, Measurable (L j)) → (∀ j z, 0 ≤ L j z ∧ L j z ≤ BL) →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = μ) →
      ENNReal.ofReal (1 - δ) ≤
        P {ω | ∀ law : {S : Finset (Fin n) // S.card = M} → ℝ, ProbVec law →
          |devJ μ m L law (fun i => X i ω)| ≤
            2 * BL * √(2 * Real.log (2 * (n.choose M : ℝ)) / m) +
              BL * √(Real.log (1 / δ) / (2 * m))}

/-- `log C(n,M) ≤ M log(e n / M)` for `1 ≤ M ≤ n`. -/
def log_choose_le : Prop :=
  ∀ n M : ℕ, 1 ≤ M → M ≤ n →
    Real.log (n.choose M : ℝ) ≤ M * Real.log (Real.exp 1 * n / M)

end Claims
end StatFormal.ICL.Joint
