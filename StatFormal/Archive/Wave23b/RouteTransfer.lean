import StatFormal.Archive.Wave23b.Statements
import StatFormal.Archive.OTFD.Wave4.RouteDepthSign

/-!
# Route — T `prop:transfer-M`(i)–(iii), T `thm:population` (chart part) (untrusted)

Everything is conjugation of the Hilbert-level rank pairs by the fixed Borel charts: almost-everywhere identities are
transported along pushforwards (`ae_of_ae_map`), and the uniqueness in (ii) is the certified `lem:depthsign-rank`
(Wave 4): two `μ_K`-distributed vectors with equal depth and sign coincide a.s.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave23b

open StatFormal.OTFD.Wave8c (IsRankPair)

section Transfer
variable {K : ℕ} {X : Type*} [MeasurableSpace X]

lemma measurableSet_eq_euc {α : Type*} [MeasurableSpace α] {f g : α → Euc K} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {x | f x = g x} := measurableSet_eq_fun hf hg

/-- `Ψ ∘ Φ = Id` almost everywhere for the coefficient law `P.map Ψ`. -/
lemma ae_psi_phi {P : Measure X} {Φ : Euc K → X} {Ψ : X → Euc K} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (h : ∀ᵐ x ∂P, Φ (Ψ x) = x) : ∀ᵐ z ∂(P.map Ψ), Ψ (Φ z) = z := by
  have hset : MeasurableSet {z : Euc K | Ψ (Φ z) = z} := measurableSet_eq_fun (hΨ.comp hΦ) measurable_id
  refine (ae_map_iff hΨ.aemeasurable hset).2 ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The key identity `F_B Ψ_B Φ_B Q_B = Id`, `μ`-a.e. -/
lemma ae_FB_psi_phi_QB {μ : Measure (Euc K)} {PB : Measure X} {ΦB : Euc K → X} {ΨB : X → Euc K}
    {FB QB : Euc K → Euc K} (hΦ : Measurable ΦB) (hΨ : Measurable ΨB) (h : ∀ᵐ x ∂PB, ΦB (ΨB x) = x)
    (hB : IsRankPair μ (PB.map ΨB) FB QB) : ∀ᵐ u ∂μ, FB (ΨB (ΦB (QB u))) = u := by
  obtain ⟨hF, hQ, hQμ, -, hFQ, -⟩ := hB
  have h1 := ae_psi_phi hΦ hΨ h
  rw [← hQμ] at h1
  have h2 := ae_of_ae_map hQ.aemeasurable h1
  filter_upwards [h2, hFQ] with u hu hu'
  rw [hu, hu']

lemma map_rank {μ : Measure (Euc K)} {PA : Measure X} {ΨA : X → Euc K} {FA QA : Euc K → Euc K}
    (hΨ : Measurable ΨA) (hA : IsRankPair μ (PA.map ΨA) FA QA) : PA.map (fun x => FA (ΨA x)) = μ := by
  obtain ⟨hF, -, -, hFν, -, -⟩ := hA
  rw [← hFν, Measure.map_map hF hΨ]
  rfl

end Transfer

theorem transferM_push : Claims.transferM_push := by
  intro K X _ μ PA PB ΦA ΦB ΨA ΨB FA QA FB QB hΦA hΦB hΨA hΨB hA hB rA rB
  have hkey := ae_FB_psi_phi_QB hΦB hΨB hB rB
  have hlaw := map_rank hΨA rA
  obtain ⟨hFA, -, -, -, -, -⟩ := rA
  obtain ⟨-, hQB, hQBμ, -, -, -⟩ := rB
  refine ⟨?_, ?_⟩
  · have hG : Measurable fun x => FA (ΨA x) := hFA.comp hΨA
    have : (fun x => ΦB (QB (FA (ΨA x)))) = ΦB ∘ QB ∘ fun x => FA (ΨA x) := rfl
    rw [this, ← Measure.map_map hΦB (hQB.comp hG), ← Measure.map_map hQB hG, hlaw,
      hQBμ, Measure.map_map hΦB hΨB]
    conv_rhs => rw [← Measure.map_id (μ := PB)]
    exact Measure.map_congr (hB.mono fun x hx => hx)
  · rw [← hlaw] at hkey
    filter_upwards [ae_of_ae_map (hFA.comp hΨA).aemeasurable hkey] with x hx
    simp only [Function.comp_apply] at hx
    exact ⟨hx, by rw [hx], by rw [hx]⟩

theorem transferM_unique : Claims.transferM_unique := by
  intro K X _ μ _ PA PB _ ΦA ΦB ΨA ΨB FA QA FB QB T' hΦA hΦB hΨA hΨB hA hB rA rB hT' hT'law hdepth hsign
  have hlawA := map_rank hΨA rA
  obtain ⟨hFA, -, -, -, -, -⟩ := rA
  obtain ⟨hFB, hQB, -, hFBν, -, hQFB⟩ := rB
  haveI : IsProbabilityMeasure PB := by rw [← hT'law]; infer_instance
  have hlawB : PA.map (fun x => FB (ΨB (T' x))) = μ := by
    rw [← hFBν, Measure.map_map hFB hΨB, ← hT'law, Measure.map_map (hFB.comp hΨB) hT']
    rfl
  have hU := StatFormal.OTFD.Wave4.depthsign_rank (Euc K) X PA μ (fun x => FA (ΨA x)) (fun x => FB (ΨB (T' x)))
    sgnK (hFA.comp hΨA) (hFB.comp (hΨB.comp hT')) hlawA hlawB (fun u _ => rfl) hdepth hsign
  have h1 : ∀ᵐ x ∂PA, ΦB (ΨB (T' x)) = T' x := by
    rw [← hT'law] at hB
    exact ae_of_ae_map hT'.aemeasurable hB
  have h2 : ∀ᵐ x ∂PA, QB (FB (ΨB (T' x))) = ΨB (T' x) := by
    have := ae_of_ae_map hΨB.aemeasurable hQFB
    rw [← hT'law] at this
    exact ae_of_ae_map hT'.aemeasurable this
  filter_upwards [hU, h1, h2] with x hx h1x h2x
  rw [← h1x, ← h2x, hx]

theorem transferM_cocycle : Claims.transferM_cocycle := by
  intro K X _ μ PA PB PC ΦA ΦB ΦC ΨA ΨB ΨC FA QA FB QB FC QC hΦA hΦB hΦC hΨA hΨB hΨC hA hB hC rA rB rC
  have hkey := ae_FB_psi_phi_QB hΦB hΨB hB rB
  have hlaw := map_rank hΨA rA
  obtain ⟨hFA, -, -, -, -, hQFA⟩ := rA
  refine ⟨?_, ?_⟩
  · filter_upwards [hA, ae_of_ae_map hΨA.aemeasurable hQFA] with x hx hx'
    rw [hx', hx]
  · rw [← hlaw] at hkey
    filter_upwards [ae_of_ae_map (hFA.comp hΨA).aemeasurable hkey] with x hx
    simp only [Function.comp_apply] at hx
    rw [hx]

theorem pop_manifold : Claims.pop_manifold := by
  intro H X _ _ _ _ P _ μ _ Em Lm Dr F Q hEm hLm hDr hLE hP rk
  obtain ⟨hF, hQ, hQμ, hFν, hFQ, hQF⟩ := rk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Measure.map_map hF hLm, hFν]
  · rw [← Measure.map_map hEm hQ, hQμ, Measure.map_map hEm hLm]
    conv_rhs => rw [← Measure.map_id (μ := P)]
    exact Measure.map_congr (hP.mono fun x hx => hx.2)
  · filter_upwards [hP, ae_of_ae_map hLm.aemeasurable hQF] with x hx hx'
    rw [hx', hx.2]
  · have hDrν : ∀ᵐ z ∂(P.map Lm), z ∈ Dr := by
      exact (ae_map_iff hLm.aemeasurable (show MeasurableSet {z | z ∈ Dr} from hDr)).2
        (hP.mono fun x hx => hx.1)
    rw [← hQμ] at hDrν
    filter_upwards [ae_of_ae_map hQ.aemeasurable hDrν, hFQ] with u hu hu'
    rw [hLE _ hu, hu']

theorem pop_regions : Claims.pop_regions := by
  intro H X _ _ _ _ _ _ _ _ _ _ _ P _ μ _ Fm Qm hF hQ hFP hQμ hQF hFQ
  have hdX : MeasurableSet {x | Qm (Fm x) = x} :=
    isClosed_diagonal.measurableSet.preimage ((hQ.comp hF).prodMk measurable_id)
  have hdH : MeasurableSet {u | Fm (Qm u) = u} :=
    isClosed_diagonal.measurableSet.preimage ((hF.comp hQ).prodMk measurable_id)
  set ΩP := {x | Qm (Fm x) = x} ∩ Fm ⁻¹' {u | Fm (Qm u) = u}
  set Ωμ := {u | Fm (Qm u) = u} ∩ Qm ⁻¹' {x | Qm (Fm x) = x}
  have hΩP : MeasurableSet ΩP := hdX.inter (hF hdH)
  have hΩμ : MeasurableSet Ωμ := hdH.inter (hQ hdX)
  have hnullX : P {x | Qm (Fm x) = x}ᶜ = 0 := ae_iff.mp hQF
  have hnullH : μ {u | Fm (Qm u) = u}ᶜ = 0 := ae_iff.mp hFQ
  refine ⟨ΩP, Ωμ, hΩP, hΩμ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [compl_inter]
    refine measure_union_null hnullX ?_
    rw [← preimage_compl, ← Measure.map_apply hF hdH.compl, hFP, hnullH]
  · rw [compl_inter]
    refine measure_union_null hnullH ?_
    rw [← preimage_compl, ← Measure.map_apply hQ hdX.compl, hQμ, hnullX]
  · rintro x ⟨hx1, hx2⟩
    refine ⟨⟨hx2, ?_⟩, hx1⟩
    simp only [mem_preimage, mem_setOf_eq] at hx1 ⊢
    rw [hx1, hx1]
  · rintro u ⟨hu1, hu2⟩
    refine ⟨⟨hu2, ?_⟩, hu1⟩
    simp only [mem_preimage, mem_setOf_eq] at hu1 ⊢
    rw [hu1, hu1]
  · intro A hA
    constructor
    · rw [Set.inter_comm, measure_inter_conull ?_, ← Measure.map_apply hF hA, hFP]
      rw [compl_inter]
      refine measure_union_null hnullX ?_
      rw [← preimage_compl, ← Measure.map_apply hF hdH.compl, hFP, hnullH]
    · ext x
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hxA⟩
        exact ⟨Fm x, ⟨⟨hx2, by simp only [mem_preimage, mem_setOf_eq] at hx1 ⊢; rw [hx1, hx1]⟩, hxA⟩, hx1⟩
      · rintro ⟨u, ⟨⟨hu1, hu2⟩, huA⟩, rfl⟩
        refine ⟨⟨hu2, ?_⟩, ?_⟩
        · simp only [mem_preimage, mem_setOf_eq] at hu1 ⊢; rw [hu1]; exact hu1
        · simp only [mem_preimage, mem_setOf_eq] at hu1 ⊢; rw [hu1]; exact huA

end StatFormal.Wave23b
