import StatFormal.Archive.RobustEquality.Statements
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# FROZEN STATEMENTS — robust equality (JASA): entropic transport with a discrete marginal

Source (verbatim in `inventory/extracted/robust-equality-jasa.md`): `lem:semidual`
(`jasa/supp_proofs.tex:63`), with the notation of `supp_proofs.tex:35-45`:
`μ = Σ_{i≤k} a_i δ_{x_i}` (labelled atoms, ties allowed — so atoms are indexed by `Fin k`),
`c_i = c(x_i, ·)`, `g_f(y) = −ε log Σ_i a_i e^{(f_i − c_i(y))/ε}`, `J_Q(f) = ⟨a, f⟩ + ∫ g_f dQ`.

Covered:
* (i) weak duality: `E_γ c + ε KL(γ ‖ μ⊗Q) ≥ J_Q(f)` for every `f ∈ ℝ^k` and coupling `γ ∈ Π(μ, Q)`;
* (ii) increments: `g_f(y) − g_f(y') ≤ max_i {c_i(y) − c_i(y')}` and `sup_K |g_f − g_{f'}| ≤ ‖f − f'‖_∞`.
Not covered (declared): strong duality `Θ(Q) = max_f J_Q(f)`, the first-order condition and `F_W`
(they need existence of Schrödinger potentials), and (iii)–(iv), which follow from strong duality; the corollaries `|g_f(y) − g_f(y')| ≤ D̄(y,y')`
(two applications of `semidual_incr`) and `osc_K g_f ≤ b`.

Encodings (see card):
* the cost enters only through the bounded measurable functions `c_i = c(x_i, ·)` on `K`; `K` is any
  measurable space (the paper's compact `K`), `Q` a probability measure;
* `μ` is the measure `Σ_i a_i δ_i` on `Fin k`, with `a_i > 0`, `Σ a_i = 1`; a coupling is a probability
  measure `γ` on `Fin k × K` with marginals `μ` and `Q`;
* `KL` is the paper's `klRef` (for the probability measure `μ ⊗ Q` it is the usual relative entropy,
  `+∞` unless `γ ≪ μ⊗Q` with integrable log-likelihood ratio); the inequality is in `EReal`;
* "max over `i`" in (ii) enters as any upper bound `B` of the increments (`k ≥ 1`), and `‖f − f'‖_∞` as
  any bound `D` on `|f_i − f'_i|`.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset MeasureTheory

namespace StatFormal.RobustEquality.Semidual

/-- Soft-min potential `g_f(y) = −ε log Σ_i a_i e^{(f_i − c_i(y))/ε}`. -/
def gsoft {K : Type*} {k : ℕ} (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ) (y : K) : ℝ :=
  -ε * Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε))

/-- The discrete marginal `μ = Σ_i a_i δ_i` on the labels. -/
def muDisc {k : ℕ} (a : Fin k → ℝ) : Measure (Fin k) :=
  ∑ i, ENNReal.ofReal (a i) • Measure.dirac i

namespace Claims

/-- `lem:semidual` (i), weak duality: `E_γ c + ε KL(γ‖μ⊗Q) ≥ ⟨a,f⟩ + ∫ g_f dQ`. -/
def semidual_weak : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) [IsProbabilityMeasure Q] (γ : Measure (Fin k × K)) [IsProbabilityMeasure γ]
    (ε : ℝ),
    0 < ε → (∀ i, 0 < a i) → ∑ i, a i = 1 → (∀ i, Measurable (c i)) →
    (∃ B, ∀ i y, |c i y| ≤ B) →
    γ.map Prod.fst = muDisc a → γ.map Prod.snd = Q →
      (((∑ i, a i * f i) + ∫ y, gsoft ε a f c y ∂Q : ℝ) : EReal) ≤
        ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) + (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod Q)

/-- `lem:semidual` (ii), increments: `g_f(y) − g_f(y') ≤ max_i {c_i(y) − c_i(y')}`. -/
def semidual_incr : Prop :=
  ∀ (K : Type) (k : ℕ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ) (ε B : ℝ) (y y' : K),
    0 < k → 0 < ε → (∀ i, 0 < a i) → (∀ i, c i y - c i y' ≤ B) →
      gsoft ε a f c y - gsoft ε a f c y' ≤ B

/-- `lem:semidual` (ii), Lipschitz in `f`: `|g_f(y) − g_{f'}(y)| ≤ ‖f − f'‖_∞`. -/
def semidual_lip : Prop :=
  ∀ (K : Type) (k : ℕ) (a f f' : Fin k → ℝ) (c : Fin k → K → ℝ) (ε D : ℝ) (y : K),
    0 < k → 0 < ε → (∀ i, 0 < a i) → (∀ i, |f i - f' i| ≤ D) →
      |gsoft ε a f c y - gsoft ε a f' c y| ≤ D

end Claims
end StatFormal.RobustEquality.Semidual
