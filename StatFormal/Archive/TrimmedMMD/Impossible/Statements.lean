import StatFormal.Lib.Distances.TV
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# FROZEN STATEMENTS — trimmed MMD: no assumption-free upper confidence bound for total variation

Source (verbatim in `inventory/extracted/trimmed-mmd.md`): `thm:impossible` (`trimmed-mmd/paper.tex`,
proof `supplement.tex:442-484`).

Encodings (see card):
* "probability measures on `[0,1]` with bounded densities": probability measures `P` on `ℝ` with
  `P ≤ C • λ|_{[0,1]}` for some finite `C` (equivalent to a density bounded by `C`, vanishing off `[0,1]`).
* `TV(P,Q)` is `StatFormal.Distances.tvDist` (`sup_A |P(A) − Q(A)| = ½∫|p − q|`).
* "possibly randomized": `Û` is a measurable function of `(X_{1:n}, Y_{1:m}, ξ)` with `ξ` an independent
  randomiser of arbitrary law `R` on an arbitrary measurable space; the data law is
  `P^n ⊗ Q^m ⊗ R`.
* `P₀` is Lebesgue measure restricted to `[0,1]`.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory
open scoped NNReal

namespace StatFormal.TrimmedMMD.Impossible

/-- Probability measures on `ℝ` concentrated on `[0,1]` with a bounded density. -/
def BddDensity01 (P : Measure ℝ) : Prop :=
  IsProbabilityMeasure P ∧ ∃ C : ℝ≥0, P ≤ (C : ENNReal) • volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The law of `(X_{1:n}, Y_{1:m}, ξ)`. -/
def dataLaw {Ξ : Type*} [MeasurableSpace Ξ] (n m : ℕ) (P Q : Measure ℝ) (R : Measure Ξ) :
    Measure (((Fin n → ℝ) × (Fin m → ℝ)) × Ξ) :=
  ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).prod R

namespace Claims

/-- `thm:impossible`: a (possibly randomised) upper bound `Û` with `Pr_{P,Q}(TV(P,Q) ≤ Û) ≥ 1 − δ` for
every pair with bounded densities on `[0,1]` satisfies `Pr_{P₀,P₀}(Û ≥ 1) ≥ 1 − δ`. -/
def impossible : Prop :=
  ∀ (n m : ℕ) (δ : ℝ) (Ξ : Type) [MeasurableSpace Ξ] (R : Measure Ξ) [IsProbabilityMeasure R]
    (U : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
    1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 → Measurable U →
    (∀ P Q : Measure ℝ, BddDensity01 P → BddDensity01 Q →
      1 - δ ≤ (dataLaw n m P Q R).real {z | StatFormal.Distances.tvDist P Q ≤ U z}) →
      1 - δ ≤ (dataLaw n m (volume.restrict (Set.Icc (0 : ℝ) 1))
          (volume.restrict (Set.Icc (0 : ℝ) 1)) R).real {z | 1 ≤ U z}

end Claims
end StatFormal.TrimmedMMD.Impossible
