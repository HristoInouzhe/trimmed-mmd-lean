import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.OTFD.WaveL3.RouteHilbert
import StatFormal.Archive.OTFD.WaveL1.RouteL2

/-!
# Route — T `prop:equivariance` (supp:814): unitary equivariance of the Brenier maps (untrusted)

`J#P` is again null on Lipschitz hypersurfaces (`J⁻¹(A_w^τ) = A_{J⁻¹w}^{τ∘J}`), has the same second moment, and
`T₀ = J T J⁻¹` is Borel, pushes `J#P` to `J#μ` and is `J#P`-a.e. cyclically monotone (a unitary map preserves the
inner products in the cycle sums). The certified Brenier–GHS uniqueness `OTFD.WaveL3.brenier_uniq_H` identifies the
graph plan of any competitor `T'` with that of `T₀`, whence `T' = T₀` a.e.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24c

open StatFormal.OTFD.WaveL1 (LipNull Mom2 IsCMMapAE CycMon CMConc Graph BrenierUniq)

section Unitary
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup H']
  [InnerProductSpace ℝ H'] [CompleteSpace H'] [SecondCountableTopology H'] [MeasurableSpace H'] [BorelSpace H']

/-- The measurable equivalence underlying `J`. -/
def unitaryME (J : H ≃ₗᵢ[ℝ] H') : H ≃ᵐ H' := J.toHomeomorph.toMeasurableEquiv

lemma unitaryME_coe (J : H ≃ₗᵢ[ℝ] H') : ⇑(unitaryME J) = ⇑J := rfl

lemma map_unitary_apply (J : H ≃ₗᵢ[ℝ] H') (P : Measure H) (S : Set H') : P.map J S = P (J ⁻¹' S) := by
  rw [← unitaryME_coe, MeasurableEquiv.map_apply]

lemma isLipHyp_preimage (J : H ≃ₗᵢ[ℝ] H') {S : Set H'} (hS : StatFormal.OTFD.Wave1.IsLipHyp S) :
    StatFormal.OTFD.Wave1.IsLipHyp (J ⁻¹' S) := by
  obtain ⟨w, hw, τ, ⟨L, hL⟩, rfl⟩ := hS
  refine ⟨J.symm w, by simpa using hw, τ ∘ J, ⟨L * 1, ?_⟩, ?_⟩
  · refine hL.comp (J.lipschitz.lipschitzOnWith (s := {z | ⟪z, J.symm w⟫ = 0})) ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [← J.inner_map_map, J.apply_symm_apply] at hz
    exact hz
  · ext x
    simp only [Set.mem_preimage, StatFormal.OTFD.Wave1.lipHyp, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨z, hz, hx⟩
      refine ⟨J.symm z, ?_, ?_⟩
      · rw [← J.inner_map_map, J.apply_symm_apply, J.apply_symm_apply]; exact hz
      · apply J.injective
        rw [hx]
        simp [map_add, map_smul]
    · rintro ⟨z, hz, hx⟩
      refine ⟨J z, ?_, ?_⟩
      · rw [← J.inner_map_map, J.apply_symm_apply] at hz; exact hz
      · rw [hx, map_add, map_smul, J.apply_symm_apply]

lemma lipNull_map (J : H ≃ₗᵢ[ℝ] H') {P : Measure H} (hP : LipNull P) : LipNull (P.map J) := by
  intro S hS
  rw [map_unitary_apply]
  exact hP _ (isLipHyp_preimage J hS)

lemma mom2_map (J : H ≃ₗᵢ[ℝ] H') (P : Measure H) : Mom2 (P.map J) = Mom2 P := by
  unfold Mom2
  rw [lintegral_map (by fun_prop) J.continuous.measurable]
  congr 1
  funext x
  rw [← ofReal_norm, ← ofReal_norm, J.norm_map]

lemma isCMMapAE_conj (J : H ≃ₗᵢ[ℝ] H') {P : Measure H} {T : H → H} (hT : IsCMMapAE P T) :
    IsCMMapAE (P.map J) (fun y => J (T (J.symm y))) := by
  obtain ⟨S, hS, hS0, hcm⟩ := hT
  refine ⟨J.symm ⁻¹' S, J.symm.continuous.measurable hS, ?_, ?_⟩
  · rw [map_unitary_apply]
    have : J ⁻¹' (J.symm ⁻¹' S)ᶜ = Sᶜ := by
      ext x; simp
    rw [this]; exact hS0
  · intro m z hz
    set x : Fin m → H := fun i => J.symm (z i).1
    have hz' : ∀ i, (x i, T (x i)) ∈ {z : H × H | z.1 ∈ S ∧ z.2 = T z.1} := fun i => ⟨(hz i).1, rfl⟩
    have h := hcm m (fun i => (x i, T (x i))) hz'
    have heq : ∀ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ =
        ⟪T (x i), x (finRotate m i) - x i⟫ := by
      intro i
      have h1 : (z i).2 = J (T (x i)) := (hz i).2
      have h2 : ∀ j, (z j).1 = J (x j) := fun j => by simp [x]
      rw [h1, h2, h2, ← map_sub, J.inner_map_map]
    simpa only [heq] using h

lemma map_conj (J : H ≃ₗᵢ[ℝ] H') {P : Measure H} {T : H → H} (hT : Measurable T) :
    (P.map J).map (fun y => J (T (J.symm y))) = (P.map T).map J := by
  have hm : Measurable (fun y => J (T (J.symm y))) :=
    J.continuous.measurable.comp (hT.comp J.symm.continuous.measurable)
  rw [Measure.map_map hm J.continuous.measurable, Measure.map_map J.continuous.measurable hT]
  congr 1
  funext x
  simp

lemma ae_eq_of_graph_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {P : Measure E} {F G : E → E} (hF : Measurable F) (hG : Measurable G)
    (h : Graph P F = Graph P G) : F =ᵐ[P] G := by
  set A : Set (E × E) := {z | z.2 = G z.1}
  have hA : MeasurableSet A := measurableSet_eq_fun measurable_snd (hG.comp measurable_fst)
  have hGA : Graph P G Aᶜ = 0 := by
    rw [Graph, Measure.map_apply (StatFormal.OTFD.WaveL1.measurable_graph hG) hA.compl]
    convert measure_empty (μ := P)
    ext x; simp [A]
  rw [← h, Graph, Measure.map_apply (StatFormal.OTFD.WaveL1.measurable_graph hF) hA.compl] at hGA
  refine measure_mono_null (fun x hx => ?_) hGA
  simpa [A] using hx

end Unitary

theorem equivariance_unitary : Claims.equivariance_unitary := by
  intro H H' _ _ _ _ _ _ _ _ _ _ _ _ J P μ T T' hP hμ hlip hm2P hm2μ hT hTμ hcm hT' hT'μ hcm'
  set T₀ : H' → H' := fun y => J (T (J.symm y)) with hT₀
  have hT₀m : Measurable T₀ := J.continuous.measurable.comp (hT.comp J.symm.continuous.measurable)
  haveI : IsProbabilityMeasure (P.map J) := inferInstance
  haveI : IsProbabilityMeasure (μ.map J) := inferInstance
  have huniq := StatFormal.OTFD.WaveL3.brenier_uniq_H H' (⟨P.map J, inferInstance⟩ : ProbabilityMeasure H')
    (⟨μ.map J, inferInstance⟩ : ProbabilityMeasure H') T₀
    (lipNull_map J hlip) (by simpa [mom2_map] using hm2P) (by simpa [mom2_map] using hm2μ) hT₀m
    (show (P.map J).map T₀ = μ.map J by rw [hT₀, map_conj J hT, hTμ]) (isCMMapAE_conj J hcm)
  have hgraph : Graph (P.map J) T' = Graph (P.map J) T₀ := by
    refine huniq _ (by unfold Graph; infer_instance)
      (StatFormal.OTFD.WaveL1.graph_fst hT') ?_ (StatFormal.OTFD.WaveL1.cmConc_graph hT' hcm')
    rw [StatFormal.OTFD.WaveL1.graph_snd hT', hT'μ]
    rfl
  have hae : T' =ᵐ[P.map J] T₀ := ae_eq_of_graph_eq hT' hT₀m hgraph
  refine ⟨hae, ?_⟩
  have hae' : ∀ᵐ y ∂(P.map (unitaryME J)), T' y = T₀ y := by rw [unitaryME_coe]; exact hae
  rw [(unitaryME J).measurableEmbedding.ae_map_iff] at hae'
  filter_upwards [hae'] with x hx
  have : T' (J x) = J (T x) := by
    rw [unitaryME_coe] at hx
    simpa [T₀] using hx
  exact ⟨this, by rw [this, J.norm_map]⟩

end StatFormal.Wave24c
