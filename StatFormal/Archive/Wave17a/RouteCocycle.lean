import StatFormal.Archive.Wave17a.Statements

/-!
# Route: otfd B `prop:rk-transfer-cocycle` (untrusted)

Every null set of a target measure pulls back to a null set along a map pushing the source onto it
(`ae_of_ae_map`); the composites `Q_B∘F_A`, `F_B∘Q_B∘F_A` push `P_{A,K}` onto `P_{B,K}`, `μ_K`.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.Wave17a

open StatFormal.OTFD.Wave8c (IsRankPair)

variable {K : ℕ}

local notation "EK" => EuclideanSpace ℝ (Fin K)

lemma pull {μ P : Measure EK} {F : EK → EK} (hF : Measurable F) (hmap : P.map F = μ) {p : EK → Prop}
    (h : ∀ᵐ u ∂μ, p u) : ∀ᵐ z ∂P, p (F z) := by
  rw [← hmap] at h
  exact ae_of_ae_map hF.aemeasurable h

lemma map_QF {μ PA PB : Measure EK} {FA QA FB QB : EK → EK} (hA : IsRankPair μ PA FA QA)
    (hB : IsRankPair μ PB FB QB) : PA.map (fun z => QB (FA z)) = PB := by
  have : (fun z => QB (FA z)) = QB ∘ FA := rfl
  rw [this, ← Measure.map_map hB.2.1 hA.1, hA.2.2.2.1, hB.2.2.1]

lemma map_FQF {μ PA PB : Measure EK} {FA QA FB QB : EK → EK} (hA : IsRankPair μ PA FA QA)
    (hB : IsRankPair μ PB FB QB) : PA.map (fun z => FB (QB (FA z))) = μ := by
  have hm : Measurable fun z => QB (FA z) := hB.2.1.comp hA.1
  rw [show (fun z => FB (QB (FA z))) = FB ∘ (fun z => QB (FA z)) from rfl, ← Measure.map_map hB.1 hm,
    map_QF hA hB, hB.2.2.2.1]

theorem rk_transfer_cocycle : Claims.rk_transfer_cocycle := by
  intro K μ PA PB PC FA QA FB QB FC QC hA hB hC
  have h1 : ∀ᵐ z ∂PA, QA (FA z) = z := hA.2.2.2.2.2
  have h2 : ∀ᵐ z ∂PA, FB (QB (FA z)) = FA z := pull hA.1 hA.2.2.2.1 hB.2.2.2.2.1
  refine ⟨h1, ?_, ?_⟩
  · filter_upwards [h2] with z hz
    rw [hz]
  · filter_upwards [h1, h2] with z hz1 hz2
    rw [hz2, hz1]

theorem rk_transfer_version : Claims.rk_transfer_version := by
  intro K μ PA PB PC FA QA FB QB FC QC FA' QA' FB' QB' QC' hA hB hC hFA hQA hFB hQB hQC
  have hAm := hA.2.2.2.1
  -- one-step composites
  have one : ∀ {Q Q' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)}, Q' =ᵐ[μ] Q →
      ∀ᵐ z ∂PA, Q' (FA' z) = Q (FA z) := by
    intro Q Q' hQ
    filter_upwards [hFA, pull hA.1 hAm hQ] with z hz1 hz2
    rw [hz1, hz2]
  have hB1 := one hQB
  -- `F_B'` along `Q_B∘F_A`
  have hFB2 : ∀ᵐ z ∂PA, FB' (QB (FA z)) = FB (QB (FA z)) :=
    pull (F := fun z => QB (FA z)) (hB.2.1.comp hA.1) (map_QF hA hB) hFB
  have two : ∀ {Q Q' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)}, Q' =ᵐ[μ] Q →
      ∀ᵐ z ∂PA, Q' (FB' (QB' (FA' z))) = Q (FB (QB (FA z))) := by
    intro Q Q' hQ
    have h3 : ∀ᵐ z ∂PA, Q' (FB (QB (FA z))) = Q (FB (QB (FA z))) :=
      pull (F := fun z => FB (QB (FA z))) (hB.1.comp (hB.2.1.comp hA.1)) (map_FQF hA hB) hQ
    filter_upwards [hB1, hFB2, h3] with z hz1 hz2 hz3
    rw [hz1, hz2, hz3]
  exact ⟨one hQA, hB1, one hQC, two hQC, two hQA⟩

theorem rk_transfer_cocycle_version : Claims.rk_transfer_cocycle_version := by
  intro K μ PA PB PC FA QA FB QB FC QC FA' QA' FB' QB' QC' hA hB hC hFA hQA hFB hQB hQC
  obtain ⟨v1, -, v3, v4, v5⟩ := rk_transfer_version K μ PA PB PC FA QA FB QB FC QC FA' QA' FB' QB' QC'
    hA hB hC hFA hQA hFB hQB hQC
  obtain ⟨c1, c2, c3⟩ := rk_transfer_cocycle K μ PA PB PC FA QA FB QB FC QC hA hB hC
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [v1, c1] with z h1 h2
    rw [h1, h2]
  · filter_upwards [v3, v4, c2] with z h1 h2 h3
    rw [h1, h2, h3]
  · filter_upwards [v5, c3] with z h1 h2
    rw [h1, h2]

end StatFormal.Wave17a
