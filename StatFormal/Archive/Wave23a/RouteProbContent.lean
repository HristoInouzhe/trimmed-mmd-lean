import StatFormal.Archive.Wave23a.Statements

/-!
# Route — otfd B `thm:prob-content` (b), (e) (untrusted)

* (b) `P(F⁻¹B) = (F#P)(B) = μ(B)` for the Borel `B = supp μ ∩ {ρ ≤ τ}`, and `μ(supp μ) = 1` (second countable);
  `c_K(c_K^{-1}(p)) = p`: the sublevel set `{t ∈ [0,1] : c(t) ≥ p}` is closed and contains its infimum `t*`, and
  continuity forbids `c(t*) > p` when `t* > 0` (points just left of `t*` would be in the set).
* (e) The sandwich `F⁻¹A ∩ G' ⊆ Q'(A) ⊆ F⁻¹A ∪ Dᶜ` gives `Q'(A) =ᵐ F⁻¹A`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave23a

variable {K : ℕ}

local notation "Eu" => EuclideanSpace ℝ (Fin K)

lemma measure_support_inter (μ : Measure Eu) (A : Set Eu) : μ ({u | u ∈ μ.support} ∩ A) = μ A := by
  have h : μ (μ.support)ᶜ = 0 := Measure.measure_compl_support
  rw [Set.inter_comm]
  exact measure_inter_conull h

lemma cdfK_inv_spec (μ : Measure Eu) (ρ : Eu → ℝ) (hc : ContinuousOn (cdfK μ ρ) (Icc 0 1))
    (h0 : cdfK μ ρ 0 = 0) (h1 : cdfK μ ρ 1 = 1) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    cdfKInv μ ρ p ∈ Icc (0 : ℝ) 1 ∧ cdfK μ ρ (cdfKInv μ ρ p) = p := by
  set T := {t ∈ Icc (0 : ℝ) 1 | p ≤ cdfK μ ρ t} with hT
  have hTne : T.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by rw [h1]; exact hp.2⟩⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  have hTclosed : IsClosed T := by
    have hTeq : T = Icc 0 1 ∩ (cdfK μ ρ) ⁻¹' Ici p := by
      ext t; simp only [T, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    rw [hTeq]
    exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hmem : sInf T ∈ T := hTclosed.csInf_mem hTne hTbdd
  have hdef : cdfKInv μ ρ p = sInf T := rfl
  rw [hdef]
  refine ⟨hmem.1, le_antisymm ?_ hmem.2⟩
  by_contra hgt
  push Not at hgt
  set ts := sInf T
  rcases eq_or_lt_of_le hmem.1.1 with h | hpos
  · rw [← h, h0] at hgt
    linarith [hp.1]
  · -- points just left of `ts` would lie in `T`
    have hev : ∀ᶠ t in 𝓝[Icc 0 1] ts, p < cdfK μ ρ t :=
      (hc ts hmem.1).eventually (lt_mem_nhds hgt)
    obtain ⟨U, hUo, htsU, hUsub⟩ := mem_nhdsWithin.1 hev
    have hU : U ∈ 𝓝 ts := hUo.mem_nhds htsU
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
    set t := max (ts - δ / 2) (ts / 2)
    have ht_lt : t < ts := max_lt (by linarith) (by linarith)
    have ht_ge : 0 ≤ t := le_max_of_le_right (by linarith)
    have ht_le : t ≤ 1 := ht_lt.le.trans hmem.1.2
    have htU : t ∈ U := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have : ts - δ / 2 ≤ t := le_max_left _ _
        linarith
      · linarith
    have htT : t ∈ T := ⟨⟨ht_ge, ht_le⟩, (hUsub ⟨htU, ⟨ht_ge, ht_le⟩⟩).le⟩
    have := csInf_le hTbdd htT
    linarith

theorem prob_content_b : Claims.prob_content_b := by
  intro K P μ _ _ F ρ hF hmap hρ
  have hB : ∀ τ, MeasurableSet {u : EuclideanSpace ℝ (Fin K) | u ∈ μ.support ∧ ρ u ≤ τ} := fun τ =>
    (Measure.isClosed_support.measurableSet).inter (measurableSet_le hρ measurable_const)
  have hcont : ∀ τ, P.real (F ⁻¹' {u | u ∈ μ.support ∧ ρ u ≤ τ}) = cdfK μ ρ τ := by
    intro τ
    unfold cdfK Measure.real
    rw [← Measure.map_apply hF (hB τ), hmap, Set.ofPred_and, measure_support_inter]
  refine ⟨hcont, fun hc h0 h1 p hp => ?_⟩
  rw [hcont]
  exact (cdfK_inv_spec μ ρ hc h0 h1 hp).2

theorem prob_content_e : Claims.prob_content_e := by
  intro K P μ _ _ F Q' ρ G' D hF hmap hρ hG' hD hPG hPD hinv1 hinv2
  have main : ∀ A : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet A →
      F ⁻¹' A ∩ G' ⊆ Q' '' A ∧ Q' '' A ⊆ F ⁻¹' A ∪ Dᶜ ∧ NullMeasurableSet (Q' '' A) P ∧ P (Q' '' A) = μ A := by
    intro A hA
    have hsub1 : F ⁻¹' A ∩ G' ⊆ Q' '' A := fun z ⟨hzA, hzG⟩ => ⟨F z, hzA, hinv1 z hzG⟩
    have hsub2 : Q' '' A ⊆ F ⁻¹' A ∪ Dᶜ := by
      rintro z ⟨u, huA, rfl⟩
      by_cases hz : Q' u ∈ D
      · left; show F (Q' u) ∈ A; rw [hinv2 u (Q' u) hz rfl]; exact huA
      · right; exact hz
    have hae : Q' '' A =ᵐ[P] F ⁻¹' A := by
      refine ae_eq_set.2 ⟨?_, ?_⟩
      · exact measure_mono_null (fun z ⟨hz1, hz2⟩ => (hsub2 hz1).resolve_left hz2) hPD
      · refine measure_mono_null (fun z ⟨hz1, hz2⟩ => ?_) hPG
        by_contra hzG
        exact hz2 (hsub1 ⟨hz1, not_not.1 hzG⟩)
    refine ⟨hsub1, hsub2, (hF hA).nullMeasurableSet.congr hae.symm, ?_⟩
    rw [measure_congr hae, ← Measure.map_apply hF hA, hmap]
  refine ⟨main, fun τ => ?_⟩
  have hA : MeasurableSet {u : EuclideanSpace ℝ (Fin K) | ρ u ≤ τ ∧ u ∈ μ.support} :=
    (measurableSet_le hρ measurable_const).inter Measure.isClosed_support.measurableSet
  unfold Measure.real cdfK
  rw [(main _ hA).2.2.2, Set.ofPred_and, Set.inter_comm, measure_support_inter]
  rfl

end StatFormal.Wave23a
