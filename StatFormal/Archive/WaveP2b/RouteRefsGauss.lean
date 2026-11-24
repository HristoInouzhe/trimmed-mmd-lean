import StatFormal.Archive.WaveP2b.Statements
import StatFormal.Archive.WaveP2b.RouteGauss

/-!
# Route — otfd A `lem:app-references-Pl` (i) (untrusted)

From the core `gaussian_null` (law level) and Fernique (`IsGaussian.memLp_two_id`) for the second moment.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP2b

open StatFormal.OTFD.Wave1 (PellClass IsLipHyp lipHyp)

lemma isClosed_of_isLipHyp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {S : Set H}
    (hS : IsLipHyp S) : IsClosed S := by
  obtain ⟨w, hw, τ, ⟨L, hτ⟩, rfl⟩ := hS
  exact isClosed_lipHyp hw hτ

lemma lintegral_sq_lt_top_of_memLp {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H]
    {μ : Measure H} (h : MemLp id 2 μ) : ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ < ⊤ := by
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ) (f := id) (p := 2) two_ne_zero
    ENNReal.ofNat_ne_top h.eLpNorm_lt_top
  simpa using this

/-- The law-level form of (i). -/
lemma pell_of_gaussian {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsGaussian μ]
    (hinj : Function.Injective (covarianceBilin μ)) : PellClass μ :=
  ⟨inferInstance, lintegral_sq_lt_top_of_memLp IsGaussian.memLp_two_id,
    fun S hS => gaussian_null μ hinj S hS⟩

theorem refs_Pl_gaussian : Claims.refs_Pl_gaussian := by
  intro H _ _ _ _ _ _ Ω _ P ζ hG hinj
  have := hG.isGaussian_map
  refine ⟨fun S hS => ?_, pell_of_gaussian _ hinj⟩
  have hSm : MeasurableSet S := (isClosed_of_isLipHyp hS).measurableSet
  rw [show {ω | ζ ω ∈ S} = ζ ⁻¹' S from rfl,
    ← Measure.map_apply₀ hG.aemeasurable hSm.nullMeasurableSet]
  exact gaussian_null _ hinj S hS

end StatFormal.WaveP2b
