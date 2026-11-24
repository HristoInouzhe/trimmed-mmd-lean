import StatFormal.Archive.ICL.Statements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# FROZEN STATEMENTS — ICL conditional policies: `lem:cond-osc`, `lem:cond-tilt`, `lem:cond-metric`

Source: `context-distribution-ICL/paper/v3/supp/proofs_conditional.tex:298-360, 460-470` (two of these had
wrong constants once: the TV bound off by a factor 2, and the log-Lipschitz constant `½diam² + 2/ε_min`,
refuted numerically; see `reviews/swor_check/conditional_review.md`). `Π_w` is the CPS law `cps` of
`StatFormal.ICL.Statements`; `w^{⊗M}` is the i.i.d. law of `M`-tuples.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset Real

namespace StatFormal.ICL.Cond

/-- Total-variation `½‖p − q‖₁` of two vectors indexed by a finset. -/
def tv1 {ι : Type*} (s : Finset ι) (p q : ι → ℝ) : ℝ := (1 / 2) * ∑ i ∈ s, |p i - q i|

/-- The i.i.d. law of `M`-tuples: `w^{⊗M}(j) = ∏_k w_{j_k}`. -/
def iidLaw {n : ℕ} (w : Fin n → ℝ) (M : ℕ) (j : Fin M → Fin n) : ℝ := ∏ k, w (j k)

/-- Tilted gate `c(t,ϖ) = t ⊙ ϖ / ⟨t,ϖ⟩`. -/
def tilt {A : ℕ} (t ϖ : Fin A → ℝ) (a : Fin A) : ℝ := t a * ϖ a / ∑ b, t b * ϖ b

/-- Metric-retrieval weights `w_j(x;θ) = (1−ε) softmax_j{−½ Σ_l τ_l (x_l − x_{jl})²} + ε/n`. -/
def wRetr {n d : ℕ} (xs : Fin n → Fin d → ℝ) (x : Fin d → ℝ) (τ : Fin d → ℝ) (ε : ℝ) (j : Fin n) : ℝ :=
  (1 - ε) * (Real.exp (-(1 / 2) * ∑ l, τ l * (x l - xs j l) ^ 2) /
    ∑ k, Real.exp (-(1 / 2) * ∑ l, τ l * (x l - xs k l) ^ 2)) + ε / n

namespace Claims

/-- `lem:cond-osc` (i): same support and `log(p_i/q_i) ∈ [a, a+ω]` there ⇒ `½‖p−q‖₁ ≤ tanh(ω/4)`. -/
def cond_osc_i : Prop :=
  ∀ (N : ℕ) (p q : Fin N → ℝ) (a ω : ℝ), (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ q i) →
    ∑ i, p i = 1 → ∑ i, q i = 1 → (∀ i, p i = 0 ↔ q i = 0) →
    (∀ i, p i ≠ 0 → a ≤ Real.log (p i / q i) ∧ Real.log (p i / q i) ≤ a + ω) →
      tv1 univ p q ≤ Real.tanh (ω / 4)

/-- `lem:cond-osc` (ii): for positive `w, w' ∈ Δ^{n−1}`, `n ≥ M ≥ 1`, `Δ = max_j |log w_j − log w'_j|`:
`½‖Π_w − Π_{w'}‖₁ ≤ tanh(MΔ/2)`, `½‖w^{⊗M} − w'^{⊗M}‖₁ ≤ tanh(MΔ/2)`, and for losses in `[0, B_L]`,
`|G(w) − G(w')| ≤ B_L tanh(MΔ/2) ≤ B_L M Δ / 2`. -/
def cond_osc_ii : Prop :=
  ∀ (n M : ℕ) (w w' : Fin n → ℝ) (Δ BL : ℝ) (L : Finset (Fin n) → ℝ), 1 ≤ M → M ≤ n →
    (∀ j, 0 < w j) → (∀ j, 0 < w' j) → ∑ j, w j = 1 → ∑ j, w' j = 1 →
    (∀ j, |Real.log (w j) - Real.log (w' j)| ≤ Δ) → (∀ S, 0 ≤ L S ∧ L S ≤ BL) →
      tv1 (univ.powersetCard M) (cps w univ M) (cps w' univ M) ≤ Real.tanh (M * Δ / 2) ∧
      tv1 univ (iidLaw w M) (iidLaw w' M) ≤ Real.tanh (M * Δ / 2) ∧
      |Grisk w M L - Grisk w' M L| ≤ BL * Real.tanh (M * Δ / 2) ∧
      BL * Real.tanh (M * Δ / 2) ≤ BL * M * Δ / 2

/-- `lem:cond-tilt`: for `t` in the simplex and `ϖ ∈ [ϖ_min, 1]`, `‖c(t,ϖ) − c(t',ϖ)‖₁ ≤ 2‖t−t'‖₁/ϖ_min`;
and if `|log ϖ_α − log ϖ'_α| ≤ s` for all `α` then `‖c(t,ϖ) − c(t,ϖ')‖₁ ≤ 2 tanh(s/2)`. -/
def cond_tilt : Prop :=
  ∀ (A : ℕ) (t t' ϖ ϖ' : Fin A → ℝ) (ϖmin s : ℝ), 0 < ϖmin →
    (∀ a, 0 ≤ t a) → ∑ a, t a = 1 → (∀ a, 0 ≤ t' a) → ∑ a, t' a = 1 →
    (∀ a, ϖmin ≤ ϖ a ∧ ϖ a ≤ 1) → (∀ a, ϖmin ≤ ϖ' a ∧ ϖ' a ≤ 1) →
      ∑ a, |tilt t ϖ a - tilt t' ϖ a| ≤ 2 * (∑ a, |t a - t' a|) / ϖmin ∧
      ((∀ a, |Real.log (ϖ a) - Real.log (ϖ' a)| ≤ s) →
        ∑ a, |tilt t ϖ a - tilt t ϖ' a| ≤ 2 * Real.tanh (s / 2))

/-- `lem:cond-metric`: for inputs in a set of diameter `diam` (encoded as `Σ_l (x_l − x_{kl})² ≤ diam²` for
the query `x` and all pool points `k`), `0 < ε_min < ½`, `τ, τ' ≥ 0`, `ε, ε' ∈ [ε_min, 1 − ε_min]`, and any
`v ≥ ‖τ − τ'‖_∞`: `|log w_j(x;θ) − log w_j(x;θ')| ≤ diam² v + |ε − ε'|/ε_min`. (The fixed-floor case
`ε = ε'` is the special case with no second term.) -/
def cond_metric : Prop :=
  ∀ (n d : ℕ) (xs : Fin n → Fin d → ℝ) (x : Fin d → ℝ) (diam εmin v : ℝ) (τ τ' : Fin d → ℝ)
    (ε ε' : ℝ) (j : Fin n), 0 < εmin → εmin < 1 / 2 →
    (∀ k, ∑ l, (x l - xs k l) ^ 2 ≤ diam ^ 2) → (∀ l, 0 ≤ τ l) → (∀ l, 0 ≤ τ' l) →
    (∀ l, |τ l - τ' l| ≤ v) → 0 ≤ v →
    εmin ≤ ε → ε ≤ 1 - εmin → εmin ≤ ε' → ε' ≤ 1 - εmin →
      |Real.log (wRetr xs x τ ε j) - Real.log (wRetr xs x τ' ε' j)| ≤
        diam ^ 2 * v + |ε - ε'| / εmin

/-- `lem:cond-metric`, isotropic case `τ = s𝟙`, `τ' = s'𝟙`: the factor `diam²` improves to `½diam²`. -/
def cond_metric_iso : Prop :=
  ∀ (n d : ℕ) (xs : Fin n → Fin d → ℝ) (x : Fin d → ℝ) (diam εmin s s' : ℝ) (ε ε' : ℝ) (j : Fin n),
    0 < εmin → εmin < 1 / 2 →
    (∀ k, ∑ l, (x l - xs k l) ^ 2 ≤ diam ^ 2) → 0 ≤ s → 0 ≤ s' →
    εmin ≤ ε → ε ≤ 1 - εmin → εmin ≤ ε' → ε' ≤ 1 - εmin →
      |Real.log (wRetr xs x (fun _ => s) ε j) - Real.log (wRetr xs x (fun _ => s') ε' j)| ≤
        (1 / 2) * diam ^ 2 * |s - s'| + |ε - ε'| / εmin

end Claims
end StatFormal.ICL.Cond
