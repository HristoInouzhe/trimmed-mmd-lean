import StatFormal.Archive.OTFD.WaveL8.Statements
import StatFormal.Archive.OTFD.WaveL8.RouteGeneral
import StatFormal.Archive.OTFD.WaveL3.RouteHilbert
import StatFormal.Archive.OTFD.WaveL1.RoutePlanStab
import StatFormal.Archive.Wave24c.RouteEquivT
import StatFormal.Archive.Wave23d.RouteCM

/-!
# Route (wave L8): the uniqueness claims without moments

Untrusted route file. `BrenierUniq` for a Lipschitz-null source and ANY target is `RouteGeneral.brenierUniq_general`
(McCann with extended-valued Rockafellar potentials, library `Foundations/McCannH/Extended`); the exchanged form is
`brenierUniq_swap_general`. With it:
* `brenier_uniq_H`, `brenier_uniq_H_swap`, `brenier_uniq_bdd_source`, `brenier_uniq_fd` (`P ≪ Leb` ⇒ Lipschitz-null,
  the certified wave-L3 `lipnull_of_ac`) directly;
* `plan_stab_fd_a/_b/_b_map`, `plan_stab_w1`: the certified wave-L1 conditional theorems (`plan_stab_a/_b/_b_map`,
  `tendsto_of_cmConc`) with the `BrenierUniq` premise discharged;
* `equivariance_unitary`: the wave-24c route with `brenier_uniq_H` replaced by `brenierUniq_general`;
* `ghs_inverse_H`: no Brenier *existence* is needed for the inverse: the swapped graph plan `(F × Id)#P` is a
  coupling of `(μ, P)` carried by the (swapped, cyclically monotone, hence monotone) graph of `F`, which is
  single-valued `μ`-a.e. since `μ` is Lipschitz-null; so it is a graph plan `(Id × G)#μ` (library
  `exists_eq_graphPlan_of_ae_mem`), and `G` is the a.e. inverse.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL8

open StatFormal.OTFD.WaveL1

theorem brenier_uniq_H : Claims.brenier_uniq_H := by
  intro H _ _ _ _ _ _ P μ F hL hF hmap hcm
  exact brenierUniq_general hL hF hmap hcm

theorem brenier_uniq_H_swap : Claims.brenier_uniq_H_swap := by
  intro H _ _ _ _ _ _ P μ Q hL hQ hmap hcm
  exact brenierUniq_swap_general hL hQ hmap hcm

theorem brenier_uniq_bdd_source : Claims.brenier_uniq_bdd_source := by
  intro H _ _ _ _ _ _ μ P Q M hL _ hQ hmap hcm
  exact brenierUniq_general hL hQ hmap hcm

theorem brenier_uniq_fd : Claims.brenier_uniq_fd := by
  intro d P μ F hac hF hmap hcm
  exact brenierUniq_general (StatFormal.OTFD.WaveL3.lipnull_of_ac d P hac) hF hmap hcm

theorem plan_stab_fd_a : Claims.plan_stab_fd_a := by
  intro d P μ F M α ν π G hac hμM hF hmap hcm hα hν hfst hsnd hcmπ hG
  have hL := StatFormal.OTFD.WaveL3.lipnull_of_ac d P hac
  exact StatFormal.OTFD.WaveL1.plan_stab_a (Euc d) P μ F M α ν π G hL hμM hF
    (brenierUniq_general hL hF hmap hcm) hα hν hfst hsnd hcmπ hG

theorem plan_stab_fd_b : Claims.plan_stab_fd_b := by
  intro d P μ F M ν π hac hF hmap hcm hν hM hfst hsnd hcmπ
  have hL := StatFormal.OTFD.WaveL3.lipnull_of_ac d P hac
  exact StatFormal.OTFD.WaveL1.plan_stab_b (Euc d) P μ F M ν π hL hF
    (brenierUniq_general hL hF hmap hcm) hν hM hfst hsnd hcmπ

theorem plan_stab_fd_b_map : Claims.plan_stab_fd_b_map := by
  intro d P μ F M ν T hac hF hmap hcm hν hM hT hTν hTcm
  have hL := StatFormal.OTFD.WaveL3.lipnull_of_ac d P hac
  exact StatFormal.OTFD.WaveL1.plan_stab_b_map (Euc d) P μ F M ν T hL hF
    (brenierUniq_general hL hF hmap hcm) hν hM hT hTν hTcm

theorem plan_stab_w1 : Claims.plan_stab_w1 := by
  intro H _ _ _ _ _ _ μ P Q M α ν π G hL _ hQ hmap hcm hα hν hfst hsnd hcmπ hG
  exact tendsto_of_cmConc (brenierUniq_general hL hQ hmap hcm) hα hν hfst hsnd hcmπ hG

/-! ### Unitary equivariance (Wave 24c) -/

theorem equivariance_unitary : Claims.equivariance_unitary := by
  intro H H' _ _ _ _ _ _ _ _ _ _ _ _ J P μ T T' hP hμ hlip hT hTμ hcm hT' hT'μ hcm'
  set T₀ : H' → H' := fun y => J (T (J.symm y)) with hT₀
  have hT₀m : Measurable T₀ := J.continuous.measurable.comp (hT.comp J.symm.continuous.measurable)
  have : IsProbabilityMeasure (P.map J) := inferInstance
  have huniq : BrenierUniq (P.map J) (μ.map J) T₀ :=
    brenierUniq_general (StatFormal.Wave24c.lipNull_map J hlip) hT₀m
      (show (P.map J).map T₀ = μ.map J by rw [hT₀, StatFormal.Wave24c.map_conj J hT, hTμ])
      (StatFormal.Wave24c.isCMMapAE_conj J hcm)
  have hgraph : Graph (P.map J) T' = Graph (P.map J) T₀ := by
    refine huniq _ (by unfold Graph; infer_instance)
      (StatFormal.OTFD.WaveL1.graph_fst hT') ?_ (StatFormal.OTFD.WaveL1.cmConc_graph hT' hcm')
    rw [StatFormal.OTFD.WaveL1.graph_snd hT', hT'μ]
  have hae : T' =ᵐ[P.map J] T₀ := StatFormal.Wave24c.ae_eq_of_graph_eq hT' hT₀m hgraph
  refine ⟨hae, ?_⟩
  have hae' : ∀ᵐ y ∂(P.map (StatFormal.Wave24c.unitaryME J)), T' y = T₀ y := by
    rw [StatFormal.Wave24c.unitaryME_coe]; exact hae
  rw [(StatFormal.Wave24c.unitaryME J).measurableEmbedding.ae_map_iff] at hae'
  filter_upwards [hae'] with x hx
  have : T' (J x) = J (T x) := by
    rw [StatFormal.Wave24c.unitaryME_coe] at hx
    simpa [T₀] using hx
  exact ⟨this, by rw [this, J.norm_map]⟩

/-! ### GHS Lemma 4.3 without moments -/

section Inverse

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The a.e. inverse of a cyclically monotone map onto a Lipschitz-null law, with no moment and no existence
theorem: the swapped graph plan is itself a graph plan over `μ`. -/
theorem exists_inverse_general {P μ : Measure H} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (hμ : LipNull μ) {F : H → H} (hF : Measurable F) (hmap : P.map F = μ) (hcm : IsCMMapAE P F) :
    ∃ G : H → H, Measurable G ∧ μ.map G = P ∧ IsCMMapAE μ G ∧
      (∀ᵐ x ∂P, G (F x) = x) ∧ ∀ᵐ u ∂μ, F (G u) = u := by
  obtain ⟨S, hS, hS0, hSc⟩ := hcm
  set Γ : Set (H × H) := {z | z.1 ∈ S ∧ z.2 = F z.1} with hΓdef
  have hΓm : MeasurableSet Γ :=
    (measurable_fst hS).inter (measurableSet_eq_fun measurable_snd (hF.comp measurable_fst))
  set Γ' : Set (H × H) := Prod.swap ⁻¹' Γ with hΓ'def
  have hΓ'm : MeasurableSet Γ' := measurable_swap hΓm
  have hΓ'c : CycMon Γ' := StatFormal.OTFD.WaveL3.cycMon_swap hSc
  set π : Measure (H × H) := (Graph P F).map Prod.swap with hπdef
  have hc : IsCoupling π μ P :=
    ⟨by rw [hπdef, Measure.fst_map_swap, graph_snd hF, hmap], by rw [hπdef, Measure.snd_map_swap, graph_fst hF]⟩
  have hπΓ : π Γ'ᶜ = 0 := by
    rw [hπdef, Measure.map_apply measurable_swap hΓ'm.compl, Graph,
      Measure.map_apply (measurable_graph hF) (measurable_swap hΓ'm.compl)]
    refine measure_mono_null (fun x hx => ?_) hS0
    simp only [hΓ'def, hΓdef, mem_preimage, mem_compl_iff, Prod.swap_swap,
      mem_setOf_eq, and_true] at hx
    exact hx
  have hae : ∀ᵐ z ∂π, z ∈ Γ' := (measure_eq_zero_iff_ae_notMem.1 hπΓ).mono fun _ h => notMem_compl_iff.1 h
  have hM : μ (StatFormal.Potentials.multivaluedSet Γ') = 0 :=
    StatFormal.Potentials.measure_multivaluedSet_eq_zero (StatFormal.OTFD.WaveL3.lipGraph_null hμ)
      (StatFormal.Wave23d.isMonotoneSet_of_cycMon hΓ'c)
  have : IsFiniteMeasure π := by rw [hπdef, Graph]; infer_instance
  obtain ⟨G, hG, hπG, hGΓ⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem hc hΓ'm hae hM
  have hGraphG : Graph μ G = π := hπG.symm
  have hπ : (Graph μ G).map Prod.swap = Graph P F := by
    rw [hGraphG, hπdef, StatFormal.OTFD.WaveL3.map_swap_map_swap]
  have hGmap : μ.map G = P := by
    rw [← graph_snd hG, hGraphG, hc.snd_eq]
  have hGcm : IsCMMapAE μ G := by
    refine ⟨{u | (u, G u) ∈ Γ'}, (measurable_id.prodMk hG) hΓ'm, ?_, ?_⟩
    · exact ae_iff.1 hGΓ
    · refine StatFormal.OTFD.WaveL3.cycMon_mono hΓ'c ?_
      rintro ⟨u, y⟩ ⟨hu, hy⟩
      simp only at hu hy
      rw [hy]; exact hu
  have hD1 : MeasurableSet {p : H × H | G p.2 = p.1} :=
    measurableSet_eq_fun (hG.comp measurable_snd) measurable_fst
  have hD2 : MeasurableSet {p : H × H | F p.1 = p.2} :=
    measurableSet_eq_fun (hF.comp measurable_fst) measurable_snd
  refine ⟨G, hG, hGmap, hGcm, ?_, ?_⟩
  · have h1 : (Graph P F) {p : H × H | G p.2 = p.1}ᶜ = 0 := by
      rw [← hπ, Measure.map_apply measurable_swap hD1.compl, Graph,
        Measure.map_apply (measurable_graph hG) (measurable_swap hD1.compl)]
      convert measure_empty (μ := μ)
      ext u; simp
    rw [Graph, Measure.map_apply (measurable_graph hF) hD1.compl] at h1
    exact measure_eq_zero_iff_ae_notMem.1 h1 |>.mono fun x hx => by simpa using hx
  · have h1 : ((Graph μ G).map Prod.swap) {p : H × H | F p.1 = p.2}ᶜ = 0 := by
      rw [hπ, Graph, Measure.map_apply (measurable_graph hF) hD2.compl]
      convert measure_empty (μ := P)
      ext u; simp
    rw [Measure.map_apply measurable_swap hD2.compl, Graph,
      Measure.map_apply (measurable_graph hG) (measurable_swap hD2.compl)] at h1
    exact measure_eq_zero_iff_ae_notMem.1 h1 |>.mono fun x hx => by simpa using hx

end Inverse

theorem ghs_inverse_H : Claims.ghs_inverse_H := by
  intro H _ _ _ _ _ _ P μ _ _ F _ hμ hF hmap hcm
  exact exists_inverse_general hμ hF hmap hcm

end StatFormal.OTFD.WaveL8
