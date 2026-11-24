import StatFormal.Archive.TrimmedMMD.Impossible.Statements
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tm: trimmed MMD (JMLR) `thm:impossible`, uniform density bound 2

Source (`trimmed-mmd/jmlr/`, untracked working copy, read 2026-11-07): `sections/06_splitting.tex:226-244`
(`thm:impossible`, "No informative upper bound, even for bounded densities"), proof `appendix/B_split.tex:186-225`.
Printed statement: "Fix `n, m ≥ 1` and `δ ∈ (0,1)`, and let `𝒫₂` be the set of pairs of probability measures on
`[0,1]` whose densities with respect to Lebesgue measure are bounded by `2`. Suppose `Û = Û(X_{1:n}, Y_{1:m})`,
measurable and possibly randomized, satisfies the coverage requirement `P_{P,Q}(TV(P,Q) ≤ Û) ≥ 1 − δ` for every
`(P,Q) ∈ 𝒫₂`. Then, writing `P_u` for the uniform law on `[0,1]`, `P_{P_u,P_u}(Û ≥ 1) ≥ 1 − δ`."
`TV(P,Q) = sup_A |P(A) − Q(A)|` (`sections/03_regions.tex:17`).

This strengthens the long version's `thm:impossible` (frozen in `Archive/TrimmedMMD/Impossible/Statements.lean`, where
each law has its own finite density bound `C`): here the bound `2` is the same for every law of the class. Reused, not
copied: `StatFormal.TrimmedMMD.Impossible.dataLaw` (the law `P^n ⊗ Q^m ⊗ R` of `(X_{1:n}, Y_{1:m}, ξ)`) and
`StatFormal.Distances.tvDist`; the claim has literally the shape of the archived `Claims.impossible`, with the class
`BddDensity01` replaced by `Density2`.

Encodings (see card `certify/cards/trimmedmmd_jmlr_impossible.md`):
* "probability measure on `[0,1]` whose density with respect to Lebesgue measure is bounded by `2`": a probability
  measure `P` on `ℝ` with `P ≤ 2 • λ|_{[0,1]}` (`Density2`). Claim `density2_iff` certifies that this is the same as
  having a measurable Lebesgue density `f ≤ 2` that vanishes off `[0,1]`.
* `𝒫₂` is the product class: `(P, Q) ∈ 𝒫₂` iff `Density2 P ∧ Density2 Q`.
* "possibly randomized": `Û` is a measurable function of `(X_{1:n}, Y_{1:m}, ξ)`, `ξ` an independent randomiser of
  arbitrary law `R` on an arbitrary measurable space `Ξ`; deterministic `Û` is the case `Ξ = Unit`.
* `P_u` is Lebesgue measure restricted to `[0,1]`.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace StatFormal.Wave30tm

open StatFormal.TrimmedMMD.Impossible (dataLaw)

/-- A probability measure on `ℝ`, concentrated on `[0,1]`, whose density with respect to Lebesgue measure is bounded
by `2`: `P ≤ 2 • λ|_{[0,1]}`. The class `𝒫₂` of the theorem is the set of pairs `(P, Q)` with `Density2 P ∧ Density2 Q`. -/
def Density2 (P : Measure ℝ) : Prop :=
  IsProbabilityMeasure P ∧ P ≤ (2 : ℝ≥0∞) • volume.restrict (Set.Icc (0 : ℝ) 1)

namespace Claims

/-- `thm:impossible` (JMLR): a (possibly randomised) `Û` with `Pr_{P,Q}(TV(P,Q) ≤ Û) ≥ 1 − δ` for every pair of
probability measures on `[0,1]` with densities bounded by `2` satisfies `Pr_{P_u,P_u}(Û ≥ 1) ≥ 1 − δ`. -/
def impossible : Prop :=
  ∀ (n m : ℕ) (δ : ℝ) (Ξ : Type) [MeasurableSpace Ξ] (R : Measure Ξ) [IsProbabilityMeasure R]
    (U : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
    1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 → Measurable U →
    (∀ P Q : Measure ℝ, Density2 P → Density2 Q →
      1 - δ ≤ (dataLaw n m P Q R).real {z | StatFormal.Distances.tvDist P Q ≤ U z}) →
      1 - δ ≤ (dataLaw n m (volume.restrict (Set.Icc (0 : ℝ) 1))
          (volume.restrict (Set.Icc (0 : ℝ) 1)) R).real {z | 1 ≤ U z}

/-- Encoding check for `Density2`: `P ≤ 2 • λ|_{[0,1]}` (with `P` a probability measure) iff `P` has a measurable
density `f` with respect to Lebesgue measure on `ℝ` that is bounded by `2` and vanishes off `[0,1]`. -/
def density2_iff : Prop :=
  ∀ P : Measure ℝ, Density2 P ↔
    (IsProbabilityMeasure P ∧ ∃ f : ℝ → ℝ≥0∞, Measurable f ∧ (∀ x, f x ≤ 2) ∧
      (∀ x, x ∉ Set.Icc (0 : ℝ) 1 → f x = 0) ∧ P = volume.withDensity f)

/-- Sanity: the JMLR theorem (uniform bound `2`) implies the long version's frozen `thm:impossible` (a finite bound
for each law), because `𝒫₂` is contained in the class of pairs with bounded densities. -/
def impossible_implies_archived : Prop :=
  impossible → StatFormal.TrimmedMMD.Impossible.Claims.impossible

end Claims
end StatFormal.Wave30tm
