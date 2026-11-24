import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Trimming pairs of a density pair (library, untrusted)

A *trimming pair* of densities `p, q ≥ 0` on `ℝ` about `x₀` at scale `W`: densities `f_P ≤ p`, `f_Q ≤ q` (of the trimmings
`P′ = f_P dx ≤ P`, `Q′ = f_Q dx ≤ Q`) and `h₊, h₋ ≥ 0` carried by `[x₀ − W, x₀ + W]` with `f_P + h₋ = f_Q + h₊` (so that
`P′ − Q′ = h₊dx − h₋dx`), `∫ h₊ + ∫ h₋ ≤ M`, equal moments of order `< N`, and equal masses `∫ f_P = ∫ f_Q = ∫ min(p, q) + e`.
The explicit trimmings of Propositions S4.14 (`N = 1`, `M = 2ε`) and S4.15 (`W = Tw`, `M = 2ℓ₀w²`) of the trimmed-mmd
supplement are trimming pairs; the measure-level consequences (`|ν| ≤ M`, `supp ν ⊆ [x₀ − W, x₀ + W]`, vanishing moments through
the Jordan parts) are drawn once for all trimming pairs.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.MomentTrim

/-- The properties of a trimming pair (see the module docstring). -/
structure IsTrimmingPair (p q : ℝ → ℝ) (x₀ W M : ℝ) (N : ℕ) (fP fQ hp hm : ℝ → ℝ) (e : ℝ) : Prop where
  meas_fP : Measurable fP
  meas_fQ : Measurable fQ
  meas_hp : Measurable hp
  meas_hm : Measurable hm
  fP_nonneg : ∀ x, 0 ≤ fP x
  fQ_nonneg : ∀ x, 0 ≤ fQ x
  hp_nonneg : ∀ x, 0 ≤ hp x
  hm_nonneg : ∀ x, 0 ≤ hm x
  fP_le : ∀ x, fP x ≤ p x
  fQ_le : ∀ x, fQ x ≤ q x
  add_eq : ∀ x, fP x + hm x = fQ x + hp x
  support : ∀ x, x ∉ Icc (x₀ - W) (x₀ + W) → hp x = 0 ∧ hm x = 0
  int_hp : Integrable hp
  int_hm : Integrable hm
  mass_h : (∫ x, hp x) + ∫ x, hm x ≤ M
  moments : ∀ j < N, ∫ x, (x - x₀) ^ j * hp x = ∫ x, (x - x₀) ^ j * hm x
  mass_fP : ∫ x, fP x = (∫ x, min (p x) (q x)) + e
  mass_fQ : ∫ x, fQ x = (∫ x, min (p x) (q x)) + e

end StatFormal.MomentTrim
