import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# FROZEN STATEMENTS — robust equality (JASA): coverage at the free end

Sources (verbatim in `inventory/extracted/robust-equality-jasa.md`): `thm:coverage-general`
(`jasa/supp_proofs.tex:523`) and `thm:coverage` (`jasa/main.tex:484`), with the folds of
`supp_proofs.tex:35-41`: the sample is split into folds `I_1, …, I_V`, `P̂_v` the empirical law of fold `v`,
`w_v = |I_v|/n`, `P̂ = Σ_v w_v P̂_v`.

Covered:
* `coverage_general`: if each `ρ̂_v` satisfies `Pr[OT_ε(P̂_v, P) ≤ ρ̂_v] ≥ 1 − a/V`, then
  `Pr[OT_ε(P̂, P) ≤ Σ_v w_v ρ̂_v] ≥ 1 − a` (convexity of `OT_ε` in the fold mixture + union bound);
* `coverage_fold_hoeffding`: the Hoeffding deviation term of `thm:coverage` is valid **conditionally on the
  fold** (the form in which `thm:coverage` states its hypothesis): for a fixed fold `μ = Σ_i a_i δ_{x_i}` and
  held-out `Y_1, …, Y_m` i.i.d. `P`, `Pr[OT_ε(μ, P) ≤ OT_ε(μ, P̂_m) + B_c √(log(1/α)/(2m))] ≥ 1 − α`
  (the paper uses `α = a/V`).
Not covered (declared): the passage from the conditional per-fold statement to the unconditional one when
the fold's points are themselves random (needs joint measurability of the deviation events in the whole
sample; the canonical potential is chosen non-constructively); `prop:allpairs` (empirical Bernstein); the
adaptive-bound clause of `thm:coverage-general` (`thm:ad-valid`).

Encodings (see card):
* membership `P ∈ 𝓑^{𝒫(K)}(r̂)` is `OT_ε(P̂, P) ≤ r̂` (the free-end case of `lem:tax`, stated there);
* `OT_ε` is `OTdisc` of the frozen `SemidualStrong` statements (labelled atoms); the full sample has
  `N` labels with weights `1/N` and costs `c(x_i, ·)`; folds are a surjection `fold : Fin N → Fin V` with,
  for each block, an enumeration `e v : Fin (n v) ≃ {i // fold i = v}` (the claim holds for every
  enumeration); fold `v` has weights `1/n v` and costs `c(x_{e v j}, ·)`; `w_v = n v / N`;
* the per-fold events are assumed measurable ("`ρ̂_v` a function of the sample"); this is necessary — with
  outer measures the claim is false (critic: `V = 2`, events `A`, `Aᶜ` of outer measure 1);
* the folds are a fixed partition; a random split with fixed sizes and independent randomisation enters
  through `x ω` and `Ω`;
* `B_c` enters as any bound on the oscillation `c_i(y) − c_i(y')` of the fold's costs.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace StatFormal.RobustEquality.Coverage

open StatFormal.RobustEquality.SemidualStrong

/-- Empirical measure of `y_1, …, y_m`. -/
def empMeasure {K : Type*} [MeasurableSpace K] {m : ℕ} (y : Fin m → K) : Measure K :=
  ∑ j, ENNReal.ofReal (1 / m) • Measure.dirac (y j)

namespace Claims

/-- `thm:coverage-general`. -/
def coverage_general : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (μΩ : Measure Ω) [IsProbabilityMeasure μΩ]
    (P : Measure K) [IsProbabilityMeasure P] (N V : ℕ) (fold : Fin N → Fin V) (n : Fin V → ℕ)
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (c : K → K → ℝ) (x : Ω → Fin N → K)
    (ρ : Fin V → Ω → ℝ) (ε a : ℝ),
    0 < ε → 0 < a → a < 1 → 0 < N → Function.Surjective fold →
    (∀ x0, Measurable (c x0)) → (∃ B, ∀ x0 y, |c x0 y| ≤ B) →
    (∀ v, MeasurableSet {ω | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
        (fun j => c (x ω (e v j))) P ≤ (ρ v ω : EReal)}) →
    (∀ v, ENNReal.ofReal (1 - a / V) ≤ μΩ {ω | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
        (fun j => c (x ω (e v j))) P ≤ (ρ v ω : EReal)}) →
      ENNReal.ofReal (1 - a) ≤ μΩ {ω | OTdisc ε (fun _ : Fin N => (1 : ℝ) / N)
          (fun i => c (x ω i)) P ≤ ((∑ v, ((n v : ℝ) / N) * ρ v ω : ℝ) : EReal)}

/-- `thm:coverage`, Hoeffding deviation term, conditionally on the fold. -/
def coverage_fold_hoeffding : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (k m : ℕ) (ε Bc α : ℝ)
    (a : Fin k → ℝ) (c : Fin k → K → ℝ) (P : Measure K) [IsProbabilityMeasure P]
    (μΩ : Measure Ω) [IsProbabilityMeasure μΩ] (Y : Fin m → Ω → K),
    Setting ε a c → 0 < Bc → (∀ i y y', c i y - c i y' ≤ Bc) → 0 < m →
    (∀ j, Measurable (Y j)) → iIndepFun Y μΩ → (∀ j, μΩ.map (Y j) = P) → 0 < α → α ≤ 1 →
      ENNReal.ofReal (1 - α) ≤
        μΩ {ω | OTdisc ε a c P ≤ OTdisc ε a c (empMeasure fun j => Y j ω) +
          ((Bc * √(Real.log (1 / α) / (2 * m)) : ℝ) : EReal)}

end Claims
end StatFormal.RobustEquality.Coverage
