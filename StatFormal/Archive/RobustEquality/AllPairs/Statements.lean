import StatFormal.Archive.RobustEquality.Coverage.Statements

/-!
# FROZEN STATEMENTS — robust equality (JASA): the all-pairs empirical-Bernstein deviation term

Source: `prop:allpairs` (`jasa/main.tex:506-515`), proof `jasa/supp_proofs.tex` ≈ 548-560 (empirical Bernstein of
Maurer–Pontil 2009, Thm 4, applied to `g̃_v(X_j)`; `|g̃_v(y) − g̃_v(y')| ≤ D̄_v(y,y')` by `lem:semidual`(ii)).

Covered: for a fixed fold `μ = Σ_i a_i δ_{x_i}` (labelled atoms, costs `c_i = c(x_i, ·)`) and `m ≥ 2` held-out points
`Y_1, …, Y_m` i.i.d. `P`, with `D̄(y,y') = max_i |c_i(y) − c_i(y')|`, `V = {m(m−1)}⁻¹ Σ_{j<l} D̄(Y_j,Y_l)²` and `b`
any bound on the oscillations `c_i(y) − c_i(y')`, there is a measurable event of probability `≥ 1 − α` on which
`OT_ε(μ, P) ≤ OT_ε(μ, P̂_m) + √(2V log(2/α)/m) + 7b log(2/α)/(3(m−1))`
— i.e. `dev_v` is a valid deviation term at level `α = a/V` (conditionally on the fold, the form in which
`thm:coverage` takes its hypothesis; random folds as in `CoverageRandom`). The paper's literal definition of
"valid" is the centred-potential event `E_P g̃ − m⁻¹Σ g̃(Y_j) ≤ dev`; it is covered here through its consequence
(the subgradient step), which is what `thm:coverage` consumes.
Not covered (declared): the combination with random folds (same Fubini argument as `CoverageRandom`).

Encodings: as in `Coverage/Statements.lean` (`OTdisc`, `Setting`, `empMeasure`); the paper's `b_v` is the max of the
oscillations, here any upper bound of them (weaker hypothesis, same conclusion form); probability as a measurable
event (inner form).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace StatFormal.RobustEquality.AllPairs

open StatFormal.RobustEquality.SemidualStrong StatFormal.RobustEquality.Coverage

/-- `D̄(y,y') = max_i |c_i(y) − c_i(y')|`. -/
def Dbar {K : Type*} {k : ℕ} (c : Fin k → K → ℝ) (y y' : K) : ℝ := ⨆ i, |c i y - c i y'|

/-- The all-pairs variance proxy `V = {m(m−1)}⁻¹ Σ_{j<l} D̄(Y_j, Y_l)²`. -/
def Vall {K : Type*} {k m : ℕ} (c : Fin k → K → ℝ) (y : Fin m → K) : ℝ :=
  (1 / ((m : ℝ) * (m - 1))) *
    ∑ j : Fin m, ∑ l : Fin m, if j < l then Dbar c (y j) (y l) ^ 2 else 0

namespace Claims

/-- `prop:allpairs`, per fold. -/
def allpairs : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (k m : ℕ) (ε b α : ℝ)
    (a : Fin k → ℝ) (c : Fin k → K → ℝ) (P : Measure K) [IsProbabilityMeasure P]
    (μΩ : Measure Ω) [IsProbabilityMeasure μΩ] (Y : Fin m → Ω → K),
    Setting ε a c → (∀ i y y', c i y - c i y' ≤ b) → 2 ≤ m →
    (∀ j, Measurable (Y j)) → iIndepFun Y μΩ → (∀ j, μΩ.map (Y j) = P) → 0 < α → α < 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ μΩ E ∧
        E ⊆ {ω | OTdisc ε a c P ≤ OTdisc ε a c (empMeasure fun j => Y j ω) +
          ((√(2 * Vall c (fun j => Y j ω) * Real.log (2 / α) / m) +
              7 * b * Real.log (2 / α) / (3 * (m - 1)) : ℝ) : EReal)}

end Claims
end StatFormal.RobustEquality.AllPairs
