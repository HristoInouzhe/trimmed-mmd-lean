import StatFormal.Archive.TrimmedMMD.Lower.Statements

/-!
# Proof route — `cor:lower` (untrusted)

Proves the three draft claims of `TrimmedMMD/Lower/StatementsDraft.lean`.
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped ENNReal

namespace StatFormal.TrimmedMMD.Lower

/-- `t < α̂_lo` (with `t ≥ 0`) iff some fully rejected prefix ends at a level above `t`. -/
theorem lt_alphaLo_iff {J : ℕ} (α : Fin J → ℝ) (rej : Fin J → Prop) {t : ℝ} (ht : 0 ≤ t) :
    t < alphaLo α rej ↔ ∃ j, (∀ i ≤ j, rej i) ∧ t < α j := by
  classical
  unfold alphaLo
  split_ifs with h
  · constructor
    · intro hlt
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' h α
      refine ⟨j, (Finset.mem_filter.1 hj).2, ?_⟩
      rw [← hjeq]; exact hlt
    · rintro ⟨j, hj, hlt⟩
      exact lt_of_lt_of_le hlt (Finset.le_sup' α (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩))
  · constructor
    · intro hlt; exact absurd hlt (not_lt.2 ht)
    · rintro ⟨j, hj, -⟩
      exact absurd ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩ h

/-- A first grid index at or above `t`, whenever some level is `≥ t`. -/
theorem exists_first {J : ℕ} (α : Fin J → ℝ) {t : ℝ} (h : ∃ j, t ≤ α j) :
    ∃ j₀ : Fin J, t ≤ α j₀ ∧ ∀ i < j₀, α i < t := by
  refine ⟨wellFounded_lt.min {i | t ≤ α i} h, wellFounded_lt.min_mem _ h, fun i hi => ?_⟩
  by_contra hc
  exact wellFounded_lt.not_lt_min {i | t ≤ α i} (not_lt.1 hc) hi

theorem downclosed_pathwise : Claims.downclosed_pathwise := by
  intro J α rej t ht hlt
  obtain ⟨j, hpre, hj⟩ := (lt_alphaLo_iff α rej ht).1 hlt
  refine ⟨exists_first α ⟨j, hj.le⟩, ?_⟩
  · intro j₀ hj₀ hfirst
    apply hpre
    by_contra hc
    exact absurd (hfirst j (lt_of_not_ge hc)) (not_lt.2 hj.le)

/-- The bad event as a finite union of finite intersections. -/
theorem badEvent_eq {Ω : Type*} {J : ℕ} (α : Fin J → ℝ) (R : Fin J → Set Ω) {t : ℝ} (ht : 0 ≤ t) :
    {ω | t < alphaLo α (fun j => ω ∈ R j)} =
      ⋃ j : Fin J, ({_ω | t < α j} ∩ ⋂ i : Fin J, ⋂ (_ : i ≤ j), R i) := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
  rw [lt_alphaLo_iff _ _ ht]
  exact ⟨fun ⟨j, h1, h2⟩ => ⟨j, h2, h1⟩, fun ⟨j, h2, h1⟩ => ⟨j, h1, h2⟩⟩

theorem badEvent_measurable {Ω : Type*} [MeasurableSpace Ω] {J : ℕ} (α : Fin J → ℝ)
    (R : Fin J → Set Ω) (hR : ∀ j, MeasurableSet (R j)) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet {ω | t < alphaLo α (fun j => ω ∈ R j)} := by
  rw [badEvent_eq α R ht]
  refine MeasurableSet.iUnion fun j => (MeasurableSet.const _).inter ?_
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hR i

theorem badEvent_subset {Ω : Type*} {J : ℕ} (α : Fin J → ℝ) (R : Fin J → Set Ω) {t : ℝ}
    (ht : 0 ≤ t) (j₀ : Fin J) (hj₀ : t ≤ α j₀) (hfirst : ∀ i < j₀, α i < t) :
    {ω | t < alphaLo α (fun j => ω ∈ R j)} ⊆ R j₀ := fun ω hω =>
  (downclosed_pathwise J α (fun j => ω ∈ R j) t ht hω).2 j₀ hj₀ hfirst

theorem badEvent_empty {Ω : Type*} {J : ℕ} (α : Fin J → ℝ) (R : Fin J → Set Ω) {t : ℝ}
    (ht : 0 ≤ t) (hall : ∀ j, α j < t) :
    {ω | t < alphaLo α (fun j => ω ∈ R j)} = ∅ := by
  ext ω
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hω
  obtain ⟨j, -, hj⟩ := (lt_alphaLo_iff _ _ ht).1 hω
  exact absurd (hall j) (not_lt.2 hj.le)

theorem downclosed_measurable_le : Claims.downclosed_measurable_le := by
  intro Ω _ P J α R t hR ht
  exact ⟨badEvent_measurable α R hR ht,
    fun j₀ hj₀ hfirst => measure_mono (badEvent_subset α R ht j₀ hj₀ hfirst),
    fun hall => badEvent_empty α R ht hall⟩

theorem cor_lower : Claims.cor_lower := by
  intro 𝒳 _ P Q _ _ J α δ Ω _ PN _ R _ _ _ _ hR hlev
  have ht : 0 ≤ StatFormal.Distances.tvDist P Q := StatFormal.Distances.tvDist_nonneg P Q
  refine ⟨fun N => badEvent_measurable α (R N) (hR N) ht, ?_⟩
  by_cases hex : ∃ j, StatFormal.Distances.tvDist P Q ≤ α j
  · obtain ⟨j₀, hj₀, hfirst⟩ := exists_first α hex
    refine le_trans (Filter.limsup_le_limsup (Filter.Eventually.of_forall fun N => ?_)) (hlev j₀ hj₀)
    exact measure_mono (badEvent_subset α (R N) ht j₀ hj₀ hfirst)
  · push Not at hex
    have h0 : (fun N => PN N {ω | StatFormal.Distances.tvDist P Q <
        alphaLo α (fun j => ω ∈ R N j)}) = fun _ => 0 := by
      funext N; rw [badEvent_empty α (R N) ht hex, measure_empty]
    rw [h0, Filter.limsup_const]
    exact bot_le

end StatFormal.TrimmedMMD.Lower
