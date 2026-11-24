import StatFormal.Wave31tj.Statements
import StatFormal.Wave30tv.Proofs
import StatFormal.Archive.TrimmedMMD.Lower.Proofs

set_option linter.style.longLine false

/-!
# Route: wave 31tj, `rem:batch0grid` (untrusted)

Conditional form: for a fixed value `(u, x₀, y₀)` of batch 0 the grid is fixed, `a_j = α_j(u, x₀, y₀)`; freezing batch 0 in the
fractions makes them an `IsBatchBetRule` at level `a_j`, so the certified `Wave30tv.thm_betting_cond` bounds each true null's
rejection by `δ`, and the certified `TrimmedMMD.Lower.downclosed_measurable_le` (the first grid level `≥ TV`) gives the bound for
`α̂_lo`. Unconditional form: slice over `u`, and over batch 0 through the identity
`law((withBatchZero x₀ x, withBatchZero y₀ y)) = P^{⊗n} ⊗ Q^{⊗m}` for independent copies `(x₀,y₀)`, `(x,y)` (`map_wbz_two`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tj

open StatFormal.Wave30tv StatFormal.Wave30tq

variable {𝒳 U : Type*} [MeasurableSpace 𝒳] [MeasurableSpace U] {n m N : ℕ}

/-! ### Batch 0 as an independent copy -/

omit [MeasurableSpace 𝒳] in
lemma wbz_idem {p : ℕ} (l : Fin p → ℕ) (x₀ x : Fin p → 𝒳) :
    withBatchZero l x₀ (withBatchZero l x₀ x) = withBatchZero l x₀ x := by
  funext i; unfold withBatchZero; split_ifs <;> rfl

omit [MeasurableSpace 𝒳] in
lemma wbz_zero {p : ℕ} {l : Fin p → ℕ} (x₀ x : Fin p → 𝒳) : ∀ i, l i = 0 → withBatchZero l x₀ x i = x₀ i := by
  intro i hi; simp [withBatchZero, hi]

lemma measurable_wbz2 {p : ℕ} (l : Fin p → ℕ) :
    Measurable (fun q : (Fin p → 𝒳) × (Fin p → 𝒳) => withBatchZero l q.1 q.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : l i = 0
  · simp only [withBatchZero, h, ite_true]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [withBatchZero, h, ite_false]; exact (measurable_pi_apply i).comp measurable_snd

lemma map_wbz_one {p : ℕ} (P : Measure 𝒳) [IsProbabilityMeasure P] (l : Fin p → ℕ) :
    ((Measure.pi fun _ : Fin p => P).prod (Measure.pi fun _ : Fin p => P)).map
      (fun q => withBatchZero l q.1 q.2) = Measure.pi fun _ : Fin p => P := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_wbz2 l) (MeasurableSet.univ_pi hs)]
  set s₁ : Fin p → Set 𝒳 := fun i => if l i = 0 then s i else univ
  set s₂ : Fin p → Set 𝒳 := fun i => if l i = 0 then univ else s i
  have hpre : (fun q : (Fin p → 𝒳) × (Fin p → 𝒳) => withBatchZero l q.1 q.2) ⁻¹' univ.pi s =
      univ.pi s₁ ×ˢ univ.pi s₂ := by
    ext q
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod, withBatchZero, s₁, s₂]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> by_cases hi : l i = 0 <;> simp [hi] <;> simpa [hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : l i = 0
      · simpa [hi] using h1 i
      · simpa [hi] using h2 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : l i = 0 <;> simp [s₁, s₂, hi]

lemma lintegral_wbz {p : ℕ} (P : Measure 𝒳) [IsProbabilityMeasure P] (l : Fin p → ℕ) {A : Set (Fin p → 𝒳)}
    (hA : MeasurableSet A) :
    ∫⁻ x₀, (Measure.pi fun _ : Fin p => P) {x | withBatchZero l x₀ x ∈ A} ∂(Measure.pi fun _ : Fin p => P) =
      (Measure.pi fun _ : Fin p => P) A := by
  have hm : MeasurableSet ((fun q : (Fin p → 𝒳) × (Fin p → 𝒳) => withBatchZero l q.1 q.2) ⁻¹' A) :=
    measurable_wbz2 l hA
  have h := congrArg (fun μ => μ A) (map_wbz_one P l)
  simp only at h
  rw [Measure.map_apply (measurable_wbz2 l) hA, Measure.prod_apply hm] at h
  exact h

lemma measurable_wbz_pair (lx : Fin n → ℕ) (ly : Fin m → ℕ) :
    Measurable (fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      (withBatchZero lx q.1.1 q.2.1, withBatchZero ly q.1.2 q.2.2)) :=
  ((measurable_wbz2 lx).comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
    ((measurable_wbz2 ly).comp (measurable_fst.snd.prodMk measurable_snd.snd))

lemma map_wbz_two (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (lx : Fin n → ℕ)
    (ly : Fin m → ℕ) :
    (((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).prod
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))).map
      (fun q => (withBatchZero lx q.1.1 q.2.1, withBatchZero ly q.1.2 q.2.2)) =
      (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) := by
  set μx := Measure.pi fun _ : Fin n => P
  set μy := Measure.pi fun _ : Fin m => Q
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
  rw [Measure.map_apply (measurable_wbz_pair lx ly) hAB, Measure.prod_apply (measurable_wbz_pair lx ly hAB)]
  have hslice : ∀ z₀ : (Fin n → 𝒳) × (Fin m → 𝒳),
      (μx.prod μy) (Prod.mk z₀ ⁻¹' ((fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
        (withBatchZero lx q.1.1 q.2.1, withBatchZero ly q.1.2 q.2.2)) ⁻¹' A ×ˢ B)) =
      μx {x | withBatchZero lx z₀.1 x ∈ A} * μy {y | withBatchZero ly z₀.2 y ∈ B} := fun z₀ => by
    rw [← Measure.prod_prod]; rfl
  simp_rw [hslice]
  have hfA : Measurable fun x₀ : Fin n → 𝒳 => μx {x | withBatchZero lx x₀ x ∈ A} :=
    measurable_measure_prodMk_left (ν := μx) (measurable_wbz2 lx hA)
  have hfB : Measurable fun y₀ : Fin m → 𝒳 => μy {y | withBatchZero ly y₀ y ∈ B} :=
    measurable_measure_prodMk_left (ν := μy) (measurable_wbz2 ly hB)
  rw [lintegral_prod_mul (f := fun x₀ => μx {x | withBatchZero lx x₀ x ∈ A})
    (g := fun y₀ => μy {y | withBatchZero ly y₀ y ∈ B}) hfA.aemeasurable hfB.aemeasurable,
    lintegral_wbz P lx hA, lintegral_wbz Q ly hB]

/-! ### Rejection at a level that depends on the data -/

omit [MeasurableSpace 𝒳] in
lemma alphaLo_gt_iff {J : ℕ} (a : Fin J → ℝ) (rej : Fin J → Prop) {t : ℝ} (ht : 0 ≤ t) :
    t < StatFormal.TrimmedMMD.Lower.alphaLo a rej ↔ ∃ j, (∀ i ≤ j, rej i) ∧ t < a j := by
  classical
  unfold StatFormal.TrimmedMMD.Lower.alphaLo
  split_ifs with h
  · rw [Finset.lt_sup'_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · constructor
    · intro h'; linarith
    · rintro ⟨j, hj, -⟩
      exact absurd ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩ h

lemma measurableSet_seqReject_var {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
    {B : Fin N → Finset (Fin m)} {δ : ℝ} {g : ℕ → U → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
    {lam : (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    {α : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) → ℝ} (hα : Measurable α) (hg : IsBatchRule lx ly bat g)
    (hlam : ∀ k : Fin N, Measurable (fun p : (U × ((Fin n → 𝒳) × (Fin m → 𝒳))) × (Fin k → ℝ) =>
      lam k p.1.1 p.1.2.1 p.1.2.2 p.2)) :
    MeasurableSet {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) | seqReject lam g bat A B (α ω) δ ω.1 ω.2.1 ω.2.2} := by
  have hZ : ∀ k : Fin N, Measurable fun ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      seqZ g bat A B ω.1 ω.2.1 ω.2.2 k := fun k => by
    unfold seqZ pairZ blockMean
    refine Measurable.sub (Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _)
      (Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _)
    · exact (hg k).1.comp (measurable_id.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    · exact (hg k).1.comp (measurable_id.prodMk ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hW : ∀ t, Measurable fun ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      wealth (fun k => lam k ω.1 ω.2.1 ω.2.2) (α ω) (seqZ g bat A B ω.1 ω.2.1 ω.2.2) t := fun t => by
    unfold wealth
    refine Finset.measurable_prod _ fun k _ => ?_
    refine measurable_const.add (Measurable.mul ?_ ((hZ k).sub hα))
    exact (hlam k).comp (measurable_id.prodMk (Measurable.of_eval fun i => hZ _))
  unfold seqReject betReject
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun t =>
    (MeasurableSet.const (t ≤ N)).inter (measurableSet_le measurable_const (hW t))

/-! ### The claims -/

theorem batch0grid_cond : Claims.batch0grid_cond := by
  intro 𝒳 U _ _ P Q _ _ n m N J lx ly bat A B α δ c g lam hpair hδ0 hδ1 hc0 hc1 hgrid hg hlam u x₀ y₀
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  set a : Fin J → ℝ := fun j => α j u x₀ y₀ with ha
  have hαfix : ∀ j (ω : (Fin n → 𝒳) × (Fin m → 𝒳)),
      α j u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) = a j := fun j ω =>
    (hgrid j).2.2 u _ _ _ _ (wbz_zero x₀ ω.1) (wbz_zero y₀ ω.2)
  set R : Fin J → Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := fun j =>
    {ω | seqReject (lam j) (g j) bat A B (a j) δ u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} with hR
  have hset : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | StatFormal.Distances.tvDist P Q < StatFormal.TrimmedMMD.Lower.alphaLo
        (fun j => α j u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2))
        (fun j => seqReject (lam j) (g j) bat A B (α j u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)) δ u
          (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2))} =
      {ω | StatFormal.Distances.tvDist P Q < StatFormal.TrimmedMMD.Lower.alphaLo a (fun j => ω ∈ R j)} := by
    ext ω
    have h := fun j => hαfix j ω
    simp only [mem_setOf_eq, h]
    rfl
  rw [hset]
  -- the fractions with batch 0 frozen are an `IsBatchBetRule` at level `a j`
  have hφ : Measurable fun p : (U × ((Fin n → 𝒳) × (Fin m → 𝒳))) =>
      ((u, withBatchZero lx x₀ p.2.1, withBatchZero ly y₀ p.2.2) : U × ((Fin n → 𝒳) × (Fin m → 𝒳))) :=
    measurable_const.prodMk (((measurable_withBatchZero lx x₀).comp measurable_snd.fst).prodMk
      ((measurable_withBatchZero ly y₀).comp measurable_snd.snd))
  set L : Fin J → (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ :=
    fun j k _ x y z => lam j k u (withBatchZero lx x₀ x) (withBatchZero ly y₀ y) z with hL
  have hLrule : ∀ j, IsBatchBetRule lx ly bat (a j) c (L j) := fun j k => by
    refine ⟨((hlam j k).1).comp ((hφ.comp measurable_fst).prodMk measurable_snd), fun u' x y z => ?_,
      fun u' x x' y y' hx hy => ?_⟩
    · have h := (hlam j k).2.1 u (withBatchZero lx x₀ x) (withBatchZero ly y₀ y) z
      rw [hαfix j (x, y)] at h
      exact h
    · exact (hlam j k).2.2 u _ _ _ _ (withBatchZero_agree hx) (withBatchZero_agree hy)
  have hRL : ∀ j, R j = {ω | seqReject (L j) (g j) bat A B (a j) δ u (withBatchZero lx x₀ ω.1)
      (withBatchZero ly y₀ ω.2)} := fun j => by
    ext ω
    simp only [hR, hL, mem_setOf_eq, seqReject, wbz_idem]
  have hRm : ∀ j, MeasurableSet (R j) := fun j => by
    rw [hRL j]
    have hS := measurableSet_seqReject (A := A) (B := B) (δ := δ) (hg j) (hLrule j)
    exact hS.preimage (measurable_const.prodMk (((measurable_withBatchZero lx x₀).comp measurable_fst).prodMk
      ((measurable_withBatchZero ly y₀).comp measurable_snd)))
  have hRle : ∀ j, StatFormal.Distances.tvDist P Q ≤ a j → μ (R j) ≤ ENNReal.ofReal δ := fun j hj => by
    rw [hRL j]
    exact StatFormal.Wave30tv.thm_betting_cond 𝒳 U P Q n m N lx ly bat A B (a j) δ c (g j) (L j) hpair
      ((hgrid j).2.1 u x₀ y₀) hδ0 hδ1 hc0 hc1 (hg j) (hLrule j) hj u x₀ y₀
  set t := StatFormal.Distances.tvDist P Q with ht
  have ht0 : 0 ≤ t := StatFormal.Distances.tvDist_nonneg P Q
  have hD := StatFormal.TrimmedMMD.Lower.downclosed_measurable_le _ μ J a R t hRm ht0
  by_cases hex : ∃ j, t ≤ a j
  · classical
    set s := Finset.univ.filter (fun j : Fin J => t ≤ a j) with hs
    have hsne : s.Nonempty := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
    set j₀ := s.min' hsne with hj₀
    have hj₀mem : t ≤ a j₀ := (Finset.mem_filter.1 (s.min'_mem hsne)).2
    have hmin : ∀ i < j₀, a i < t := fun i hi => by
      by_contra hcon
      push Not at hcon
      have : j₀ ≤ i := s.min'_le i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
      exact absurd hi (not_lt.2 this)
    exact (hD.2.1 j₀ hj₀mem hmin).trans (hRle j₀ hj₀mem)
  · push Not at hex
    rw [hD.2.2 hex, measure_empty]
    exact zero_le

theorem batch0grid : Claims.batch0grid := by
  intro 𝒳 U _ _ P Q _ _ ν _ n m N J lx ly bat A B α δ c g lam hpair hδ0 hδ1 hc0 hc1 hgrid hg hlam
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  set t := StatFormal.Distances.tvDist P Q with ht
  have ht0 : 0 ≤ t := StatFormal.Distances.tvDist_nonneg P Q
  set S := {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) | t < StatFormal.TrimmedMMD.Lower.alphaLo
      (fun j => α j ω.1 ω.2.1 ω.2.2)
      (fun j => seqReject (lam j) (g j) bat A B (α j ω.1 ω.2.1 ω.2.2) δ ω.1 ω.2.1 ω.2.2)} with hSdef
  have hRm : ∀ j, MeasurableSet {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
      seqReject (lam j) (g j) bat A B (α j ω.1 ω.2.1 ω.2.2) δ ω.1 ω.2.1 ω.2.2} := fun j =>
    measurableSet_seqReject_var (hgrid j).1 (hg j) fun k => (hlam j k).1
  have hSm : MeasurableSet S := by
    have : S = ⋃ j : Fin J, ((⋂ i : Fin J, ⋂ (_ : i ≤ j), {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
        seqReject (lam i) (g i) bat A B (α i ω.1 ω.2.1 ω.2.2) δ ω.1 ω.2.1 ω.2.2}) ∩
        {ω | t < α j ω.1 ω.2.1 ω.2.2}) := by
      ext ω
      simp only [hSdef, mem_setOf_eq, alphaLo_gt_iff _ _ ht0, mem_iUnion, mem_inter_iff, mem_iInter]
    rw [this]
    exact MeasurableSet.iUnion fun j => (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hRm i).inter
      (measurableSet_lt measurable_const (hgrid j).1)
  refine prod_le_of_slices ν μ hSm fun u => ?_
  have hSu : MeasurableSet (Prod.mk u ⁻¹' S) := measurable_prodMk_left hSm
  have hmap := map_wbz_two P Q lx ly
  rw [hμ, ← hmap, Measure.map_apply (measurable_wbz_pair lx ly) hSu]
  refine prod_le_of_slices μ μ (measurable_wbz_pair lx ly hSu) fun z₀ => ?_
  exact batch0grid_cond 𝒳 U P Q n m N J lx ly bat A B α δ c g lam hpair hδ0 hδ1 hc0 hc1 hgrid hg hlam u z₀.1 z₀.2

end StatFormal.Wave31tj
