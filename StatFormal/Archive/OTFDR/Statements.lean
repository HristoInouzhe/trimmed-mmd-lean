import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# FROZEN STATEMENTS — otfd R: breakdown of the trimmed entropic quantile map, part (a)

Source: `otfd/papers/R_robustness/sections/s8_unbalanced.tex:100-140` (`def:trimmed`, `eq:trim-kkt`,
`thm:trimmed`), proof `appendix_b.tex:225-245`; out-of-sample map `s2_setting.tex:25-28` (`eq:oos`).

Conditional formalisation: the entropic solution enters through the facts the proof uses —
potentials `f_i ≤ 0`; row masses `m_i > 0` ("every entropic mass is strictly positive"), summing to 1,
capped by `c = 1/(n(1−α))`, with `m_i = c` whenever `f_i < 0`; the conditional law `π(·|u)` is the softmax
of `eq:oos`. `O` is the set of `ℓ` replaced points, `B` bounds the unreplaced points
(`thm:entropic`: `B = max ‖z_j‖` over unreplaced `j`), `ν` supported in `{‖u‖ ≤ D_ν}`.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Real Finset

namespace StatFormal.OTFDR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `eq:oos`: `π(i|u) = exp((f_i − ½‖u−z_i‖²)/ε) / Σ_j exp((f_j − ½‖u−z_j‖²)/ε)`. -/
def piCond {n : ℕ} (z : Fin n → E) (f : Fin n → ℝ) (ε : ℝ) (u : E) (i : Fin n) : ℝ :=
  Real.exp ((f i - ‖u - z i‖ ^ 2 / 2) / ε) / ∑ j, Real.exp ((f j - ‖u - z j‖ ^ 2 / 2) / ε)

/-- `eq:oos`: `Q̂(u) = Σ_i π(i|u) z_i`. -/
def Qhat {n : ℕ} (z : Fin n → E) (f : Fin n → ℝ) (ε : ℝ) (u : E) : E :=
  ∑ i, piCond z f ε u i • z i

/-- The facts of `eq:trim-kkt` used by the proof (masses `m`, cap `c = 1/(n(1−α))`). -/
structure TrimKKT {n : ℕ} (f m : Fin n → ℝ) (α : ℝ) : Prop where
  f_nonpos : ∀ i, f i ≤ 0
  m_pos : ∀ i, 0 < m i
  m_sum : ∑ i, m i = 1
  m_cap : ∀ i, m i ≤ 1 / (n * (1 - α))
  binds : ∀ i, f i < 0 → m i = 1 / (n * (1 - α))

namespace Claims

/-- `thm:trimmed` (a), pointwise bound: if `ℓ ≤ nα` (including the boundary case `ℓ = nα`), then for
every contaminated sample, every replaced point `z_k` and every `‖u‖ ≤ D_ν`,
`π(k|u) ≤ exp(−((‖z_k‖ − D_ν)₊² − (D_ν + B)²)/(2ε))`. -/
def trimmed_a_bound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (z : Fin n → E) (f m : Fin n → ℝ) (O : Finset (Fin n)) (α ε Dν B : ℝ),
    0 < α → α < 1 → 0 < ε → 0 ≤ Dν → (O.card : ℝ) ≤ n * α →
    (∀ j ∉ O, ‖z j‖ ≤ B) → TrimKKT f m α →
      ∀ k ∈ O, ∀ u : E, ‖u‖ ≤ Dν →
        piCond z f ε u k ≤
          Real.exp (-((max (‖z k‖ - Dν) 0) ^ 2 - (Dν + B) ^ 2) / (2 * ε))

/-- `thm:trimmed` (a), consequence: `sup_{‖u‖≤D_ν} ‖Q̂(u)‖` is bounded over all contaminations of at
most `ℓ ≤ nα` points, by a constant depending only on `n, α, ε, D_ν, B` — not on the replaced points
nor on the ambient (possibly infinite-dimensional) space. -/
def trimmed_a_bounded : Prop :=
  ∀ (n : ℕ) (α ε Dν B : ℝ), 0 < α → α < 1 → 0 < ε → 0 ≤ Dν → 0 ≤ B →
    ∃ M : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        (z : Fin n → E) (f m : Fin n → ℝ) (O : Finset (Fin n)),
        (O.card : ℝ) ≤ n * α → (∀ j ∉ O, ‖z j‖ ≤ B) → TrimKKT f m α →
          ∀ u : E, ‖u‖ ≤ Dν → ‖Qhat z f ε u‖ ≤ M

end Claims
end StatFormal.OTFDR
