import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Jordan parts of a difference of finite measures (library, untrusted)

For finite measures `μ₁, μ₂` and the signed measure `s = μ₁ − μ₂`, the Jordan parts `s⁺ = μ₁ − μ₂` and `s⁻ = μ₂ − μ₁`
(Mathlib's `toJordanDecomposition_toSignedMeasure_sub`, measure subtraction) lie below `μ₁` and `μ₂`, and
`s⁺ + μ₂ = s⁻ + μ₁`. Hence, for every `f` integrable against `μ₁` and `μ₂`, `∫ f ds⁺ − ∫ f ds⁻ = ∫ f dμ₁ − ∫ f dμ₂`, and
`|s| = s⁺ + s⁻ ≤ μ₁ + μ₂` (the minimality of the Jordan decomposition, Halmos, *Measure Theory*, §29, Thm D).

These facts let one compute the moments and the Fourier transform of a signed measure through its Jordan parts from any
representation `s = μ₁ − μ₂` (eq:newmomentdecay and Propositions S4.14–S4.15 of the trimmed-mmd supplement).

* `jordan_posPart_le`, `jordan_negPart_le`: `s⁺ ≤ μ₁`, `s⁻ ≤ μ₂`;
* `jordan_add_eq`: `s⁺ + μ₂ = s⁻ + μ₁`;
* `integral_jordan_sub`: `∫ f ds⁺ − ∫ f ds⁻ = ∫ f dμ₁ − ∫ f dμ₂`;
* `totalVariation_sub_le`: `|μ₁ − μ₂| ≤ μ₁ + μ₂`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.MomentTrim

variable {α : Type*} [MeasurableSpace α]

/-- The positive Jordan part of `μ₁ − μ₂` lies below `μ₁`. -/
theorem jordan_posPart_le (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    (μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.posPart ≤ μ₁ := by
  rw [Measure.toJordanDecomposition_toSignedMeasure_sub]
  exact Measure.sub_le

/-- The negative Jordan part of `μ₁ − μ₂` lies below `μ₂`. -/
theorem jordan_negPart_le (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    (μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.negPart ≤ μ₂ := by
  rw [Measure.toJordanDecomposition_toSignedMeasure_sub]
  exact Measure.sub_le

/-- For a signed measure `s` with Jordan parts `s⁺, s⁻` and `s = μ₁ − μ₂`, `s⁺ + μ₂ = s⁻ + μ₁` as measures. -/
theorem jordan_add_eq' (s : SignedMeasure α) (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hs : s = μ₁.toSignedMeasure - μ₂.toSignedMeasure) :
    s.toJordanDecomposition.posPart + μ₂ = s.toJordanDecomposition.negPart + μ₁ := by
  rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
  have h := s.toSignedMeasure_toJordanDecomposition
  rw [JordanDecomposition.toSignedMeasure] at h
  have h' : s.toJordanDecomposition.posPart.toSignedMeasure =
      s + s.toJordanDecomposition.negPart.toSignedMeasure := by
    rw [← sub_eq_iff_eq_add, h]
  rw [h', hs]; abel

/-- `s⁺ + μ₂ = s⁻ + μ₁` for `s = μ₁ − μ₂`. -/
theorem jordan_add_eq (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    (μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.posPart + μ₂ =
      (μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.negPart + μ₁ :=
  jordan_add_eq' _ μ₁ μ₂ rfl

/-- **Integrals through the Jordan parts.** If `s = μ₁ − μ₂` for finite measures `μ₁, μ₂` and `f` is integrable against
both, then `f` is integrable against `s⁺, s⁻` and `∫ f ds⁺ − ∫ f ds⁻ = ∫ f dμ₁ − ∫ f dμ₂`. -/
theorem integral_jordan_sub' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : SignedMeasure α)
    (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (hs : s = μ₁.toSignedMeasure - μ₂.toSignedMeasure)
    {f : α → E} (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂) :
    ∫ x, f x ∂s.toJordanDecomposition.posPart - ∫ x, f x ∂s.toJordanDecomposition.negPart =
      ∫ x, f x ∂μ₁ - ∫ x, f x ∂μ₂ := by
  subst hs
  have hp : Integrable f (μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.posPart :=
    h₁.mono_measure (jordan_posPart_le μ₁ μ₂)
  have hn : Integrable f (μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.negPart :=
    h₂.mono_measure (jordan_negPart_le μ₁ μ₂)
  have h := congrArg (fun μ => ∫ x, f x ∂μ) (jordan_add_eq μ₁ μ₂)
  rw [integral_add_measure hp h₂, integral_add_measure hn h₁] at h
  rw [sub_eq_sub_iff_add_eq_add, h, add_comm]

/-- `∫ f ds⁺ − ∫ f ds⁻ = ∫ f dμ₁ − ∫ f dμ₂` for `s = μ₁ − μ₂`. -/
theorem integral_jordan_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {f : α → E} (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂) :
    ∫ x, f x ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.posPart -
        ∫ x, f x ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).toJordanDecomposition.negPart =
      ∫ x, f x ∂μ₁ - ∫ x, f x ∂μ₂ :=
  integral_jordan_sub' _ μ₁ μ₂ rfl h₁ h₂

/-- **Minimality of the Jordan decomposition.** If `s = μ₁ − μ₂` for finite measures, `|s| ≤ μ₁ + μ₂`. -/
theorem totalVariation_le_of_eq_sub (s : SignedMeasure α) (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hs : s = μ₁.toSignedMeasure - μ₂.toSignedMeasure) : s.totalVariation ≤ μ₁ + μ₂ := by
  subst hs
  exact add_le_add (jordan_posPart_le μ₁ μ₂) (jordan_negPart_le μ₁ μ₂)

/-- The Jordan parts of `s = μ₁ − μ₂` lie below `μ₁` and `μ₂` (for any presentation of `s`). -/
theorem jordan_parts_le (s : SignedMeasure α) (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hs : s = μ₁.toSignedMeasure - μ₂.toSignedMeasure) :
    s.toJordanDecomposition.posPart ≤ μ₁ ∧ s.toJordanDecomposition.negPart ≤ μ₂ := by
  subst hs
  exact ⟨jordan_posPart_le μ₁ μ₂, jordan_negPart_le μ₁ μ₂⟩

/-- Two presentations of the same difference: `μ₁ + ν₂ = ν₁ + μ₂` gives `μ₁ − μ₂ = ν₁ − ν₂` as signed measures. -/
theorem toSignedMeasure_sub_eq_of_add_eq (μ₁ μ₂ ν₁ ν₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (h : μ₁ + ν₂ = ν₁ + μ₂) :
    μ₁.toSignedMeasure - μ₂.toSignedMeasure = ν₁.toSignedMeasure - ν₂.toSignedMeasure := by
  have h' := Measure.toSignedMeasure_congr h
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at h'
  rw [sub_eq_sub_iff_add_eq_add, h']

end StatFormal.MomentTrim
