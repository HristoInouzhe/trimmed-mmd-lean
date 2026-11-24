import TauCeti.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Route (wave P2c): relative-entropy toolkit for `prop:tax`(b) (untrusted)

* `klDiv_map_equiv`: `KL(μ ∘ e⁻¹ ‖ ν ∘ e⁻¹) = KL(μ ‖ ν)` for a measurable equivalence (data processing both ways);
* `klDiv_pi`: tensorization `KL(⊗_k μ_k ‖ ⊗_k ν_k) = Σ_k KL(μ_k ‖ ν_k)` for probability measures on `Fin d → X`
  (induction with `piFinSuccAbove` and Tau Ceti's `klDiv_prod_prod`);
* `klDiv_finsum_le`: joint convexity for finite mixtures, `KL(Σ_i p_i μ_i ‖ Σ_i p_i ν_i) ≤ Σ_i p_i KL(μ_i ‖ ν_i)`
  (data processing for the second marginal and Tau Ceti's conditional chain rule `klDiv_compProd_right`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Finset
open scoped ENNReal

set_option linter.style.longLine false

namespace StatFormal.WaveP2c

section Equiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem klDiv_map_equiv (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rwa [Measure.map_map e.symm.measurable e.measurable, Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id, Measure.map_id] at h

end Equiv

section Pi

variable {X : Type*} [MeasurableSpace X]

theorem klDiv_pi : ∀ (d : ℕ) (μ ν : Fin d → Measure X) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, IsProbabilityMeasure (ν k)],
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ k, klDiv (μ k) (ν k) := by
  intro d
  induction d with
  | zero =>
    intro μ ν _ _
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν, klDiv_self]
    simp
  | succ d ih =>
    intro μ ν _ _
    have hμ := (measurePreserving_piFinSuccAbove μ 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove ν 0).map_eq
    rw [← klDiv_map_equiv (MeasurableEquiv.piFinSuccAbove (fun _ => X) 0), hμ, hν,
      TauCeti.klDiv_prod_prod, ih, Fin.sum_univ_succ]
    rfl

end Pi

section Mixture

variable {ι E : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]

/-- `(κ ∘ₘ Σ_i p_i δ_i) = Σ_i p_i κ_i` for a finitely supported mixing law. -/
lemma bind_finsum (p : ι → ℝ≥0∞) (μ : ι → Measure E) :
    (Measure.bind (∑ i, p i • Measure.dirac i) μ) = ∑ i, p i • μ i := by
  have hμm : Measurable μ := measurable_of_countable μ
  ext A hA
  rw [Measure.bind_apply hA hμm.aemeasurable, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]

/-- **Joint convexity** of relative entropy for finite mixtures. -/
theorem klDiv_finsum_le [MeasurableSpace.CountableOrCountablyGenerated ι E] (p : ι → ℝ≥0∞) (hp : ∀ i, p i ≠ ⊤)
    (μ ν : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (∑ i, p i • μ i) (∑ i, p i • ν i) ≤ ∑ i, p i * klDiv (μ i) (ν i) := by
  set ρ : Measure ι := ∑ i, p i • Measure.dirac i with hρ
  have : IsFiniteMeasure ρ := by
    refine ⟨?_⟩
    simp only [hρ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    exact ENNReal.sum_lt_top.2 fun i _ => (hp i).lt_top
  let κ : Kernel ι E := ⟨μ, measurable_of_countable μ⟩
  let η : Kernel ι E := ⟨ν, measurable_of_countable ν⟩
  have : IsMarkovKernel κ := ⟨fun i => inferInstanceAs (IsProbabilityMeasure (μ i))⟩
  have : IsMarkovKernel η := ⟨fun i => inferInstanceAs (IsProbabilityMeasure (ν i))⟩
  have h1 : (ρ ⊗ₘ κ).snd = ∑ i, p i • μ i := by
    rw [Measure.snd_compProd]
    exact bind_finsum p μ
  have h2 : (ρ ⊗ₘ η).snd = ∑ i, p i • ν i := by
    rw [Measure.snd_compProd]
    exact bind_finsum p ν
  rw [← h1, ← h2]
  refine (klDiv_map_le _ _ measurable_snd).trans ?_
  rw [TauCeti.klDiv_compProd_right, hρ, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  exact le_rfl

end Mixture

end StatFormal.WaveP2c
