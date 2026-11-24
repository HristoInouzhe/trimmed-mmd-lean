import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Donsker library — shared definitions (untrusted library code)

* `HasExpNets X`: for every `j`, a finite `2^{-j}`-net of `X` of cardinality `≤ C A^j` (the metric-entropy
  condition `log N(ε) = O(log(1/ε))` used by the chaining argument; holds for bounded subsets of finite-dimensional
  normed spaces, finite products and disjoint unions).
* `linEval x u f = Σ_i u_i f(x_i)`, a finite linear combination of evaluations on `C(X, ℝ)`.
-/

noncomputable section

namespace StatFormal.Foundations.Donsker

/-- `X` has exponential nets: for every `j`, a finite `2^{-j}`-net of cardinality `≤ C A^j`. -/
def HasExpNets (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ C A : ℝ, ∀ j : ℕ, ∃ T : Finset X, (T.card : ℝ) ≤ C * A ^ j ∧ ∀ x, ∃ t ∈ T, dist x t ≤ (1 / 2 : ℝ) ^ j

/-- The finite linear combination of evaluations `f ↦ Σ_i u_i f(x_i)`. -/
def linEval {X : Type*} [TopologicalSpace X] {p : ℕ} (x : Fin p → X) (u : Fin p → ℝ) (f : C(X, ℝ)) : ℝ :=
  ∑ i, u i * f (x i)

end StatFormal.Foundations.Donsker
