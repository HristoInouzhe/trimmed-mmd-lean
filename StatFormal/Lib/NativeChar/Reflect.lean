import StatFormal.Lib.TIKernel.Feature
import StatFormal.Lib.TIKernel.Gram

/-!
# Real functions on the Fourier side: the reflection `G ↦ conj G(−·)` (library, untrusted)

For an even density `ψ ≥ 0`, negation preserves the spectral measure `ψ · vol`, so `R G = conj ∘ G ∘ neg` is a continuous
real-linear map (an isometry) of `L²(ψ · vol; ℂ)`. It fixes every Fourier feature `𝐞(−⟪x, ·⟫)`, hence every element of the
closed real span of the Fourier feature map: such `G` satisfy `G(−ξ) = conj G(ξ)` for `ψ · vol`-a.e. `ξ`, the Fourier-side form
of "the represented function `⟪G, Ψ ·⟫` is the inverse transform of `ψ G`, a real function".

The Gram isometry `U` of two feature maps with the same Gram function maps the closed span of the first into the closed span
of the second (`gramIso_mem_spanCl`); with the above, every function represented in a feature map of a translation-invariant
kernel is represented in the Fourier feature map by a symmetric `G` of no larger norm.
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.NativeChar

open StatFormal.Wave31tp StatFormal.TIKernel

section Range

variable {𝒳 : Type*} {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H'] {φ : 𝒳 → H} {φ' : 𝒳 → H'}

/-- The Gram isometry `U : closure(span φ(𝒳)) → H'` takes values in `closure(span φ'(𝒳))`: it maps `Σ cᵢ φ xᵢ` to
`Σ cᵢ φ' xᵢ`, and the preimage of a closed set under the continuous `U` is closed. -/
theorem gramIso_mem_spanCl (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫) (w : spanCl φ) :
    (gramIso hG w : H') ∈ spanCl φ' := by
  refine (inclCl_dense φ).induction_on (p := fun w => (gramIso hG w : H') ∈ spanCl φ') w
    (IsClosed.preimage (gramIso hG).continuous (Submodule.isClosed_topologicalClosure _)) ?_
  intro v
  obtain ⟨c, rfl⟩ := lcSpan_surj φ v
  change gramExt hG (inclCl φ (lcSpan φ c)) ∈ spanCl φ'
  rw [gramExt_incl, gramSpanMap_lc]
  refine span_le_cl φ' ?_
  rw [← Finsupp.range_linearCombination]
  exact LinearMap.mem_range_self _ c

end Range

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- `conj 𝐞(t) = 𝐞(−t)`. -/
lemma conj_fourierChar (t : ℝ) : conj (𝐞 t : ℂ) = 𝐞 (-t) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- Negation preserves the spectral measure of an even density. -/
theorem specMeas_neg {ψ : V → ℝ} (hψm : Measurable ψ) (hev : ∀ ξ, ψ (-ξ) = ψ ξ) :
    MeasurePreserving (fun ξ : V => -ξ) (specMeas ψ) (specMeas ψ) := by
  refine ⟨measurable_neg, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_neg hA, specMeas, withDensity_apply _ hA, withDensity_apply _ (measurable_neg hA)]
  have h := (Measure.measurePreserving_neg (volume : Measure V)).setLIntegral_comp_preimage hA
    (ENNReal.measurable_ofReal.comp hψm)
  simp only [Function.comp_apply, hev] at h
  exact h

section Reflect

variable {ψ : V → ℝ} (hψ : MeasurePreserving (fun ξ : V => -ξ) (specMeas ψ) (specMeas ψ))

/-- The reflection `R G = conj ∘ G ∘ neg` on `L²(ψ · vol; ℂ)`, a continuous real-linear map. -/
def reflect : Lp ℂ 2 (specMeas ψ) →L[ℝ] Lp ℂ 2 (specMeas ψ) :=
  (ContinuousLinearMap.compLpL 2 (specMeas ψ) (Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : V => -ξ) hψ).toContinuousLinearMap

lemma reflect_ae (G : Lp ℂ 2 (specMeas ψ)) :
    (reflect hψ G : V → ℂ) =ᵐ[specMeas ψ] fun ξ => conj (G (-ξ)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := specMeas ψ) (p := 2) (Complex.conjCLE : ℂ →L[ℝ] ℂ)
    (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : V => -ξ) hψ G)
  have h2 := Lp.coeFn_compMeasurePreserving G hψ
  filter_upwards [h1, h2] with ξ e1 e2
  change (ContinuousLinearMap.compLpL 2 (specMeas ψ) (Complex.conjCLE : ℂ →L[ℝ] ℂ))
    (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : V => -ξ) hψ G) ξ = _
  rw [e1]
  change conj ((Lp.compMeasurePreserving (fun ξ : V => -ξ) hψ G) ξ) = _
  rw [e2]
  rfl

/-- The real subspace of `G` with `R G = G`, i.e. `G(−ξ) = conj G(ξ)` a.e.; it is closed. -/
def symmSub : Submodule ℝ (Lp ℂ 2 (specMeas ψ)) :=
  LinearMap.ker ((reflect hψ - ContinuousLinearMap.id ℝ (Lp ℂ 2 (specMeas ψ)) :
    Lp ℂ 2 (specMeas ψ) →L[ℝ] Lp ℂ 2 (specMeas ψ)) : Lp ℂ 2 (specMeas ψ) →ₗ[ℝ] Lp ℂ 2 (specMeas ψ))

lemma isClosed_symmSub : IsClosed (symmSub hψ : Set (Lp ℂ 2 (specMeas ψ))) :=
  ContinuousLinearMap.isClosed_ker _

lemma mem_symmSub_iff (G : Lp ℂ 2 (specMeas ψ)) : G ∈ symmSub hψ ↔ reflect hψ G = G := by
  simp [symmSub, sub_eq_zero]

/-- The reflection fixes every Fourier feature. -/
lemma reflect_feature (hψi : Integrable ψ) (x : V) : reflect hψ (fourierFeature ψ x) = fourierFeature ψ x := by
  refine Lp.ext ?_
  have h3 : (fun ξ => (fourierFeature ψ x : V → ℂ) (-ξ)) =ᵐ[specMeas ψ] fun ξ => (𝐞 (-⟪x, -ξ⟫) : ℂ) :=
    (fourierFeature_ae ψ hψi x).comp_tendsto hψ.quasiMeasurePreserving.tendsto_ae
  filter_upwards [reflect_ae hψ _, h3, fourierFeature_ae ψ hψi x] with ξ e1 e2 e3
  rw [e1, e2, e3, inner_neg_right, neg_neg, conj_fourierChar]

lemma spanCl_le_symmSub (hψi : Integrable ψ) : spanCl (fourierFeature ψ) ≤ symmSub hψ := by
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) (isClosed_symmSub hψ)
  rintro _ ⟨x, rfl⟩
  exact (mem_symmSub_iff hψ _).mpr (reflect_feature hψ hψi x)

end Reflect

/-- **Symmetry on the closed span of the Fourier feature map.** Every `G` in the closed real span of `x ↦ 𝐞(−⟪x, ·⟫)` in
`L²(ψ · vol; ℂ)` (`ψ ≥ 0` even and integrable) satisfies `G(−ξ) = conj G(ξ)` for `ψ · vol`-a.e. `ξ`. -/
theorem ae_symm_of_mem_spanCl {ψ : V → ℝ} (hψm : Measurable ψ) (hev : ∀ ξ, ψ (-ξ) = ψ ξ) (hψi : Integrable ψ)
    {G : Lp ℂ 2 (specMeas ψ)} (hG : G ∈ spanCl (fourierFeature ψ)) : ∀ᵐ ξ ∂(specMeas ψ), G (-ξ) = conj (G ξ) := by
  have hψ := specMeas_neg hψm hev
  have hR := (mem_symmSub_iff hψ G).mp (spanCl_le_symmSub hψ hψi hG)
  filter_upwards [reflect_ae hψ G] with ξ e
  rw [hR] at e
  rw [e, Complex.conj_conj]

end StatFormal.NativeChar
