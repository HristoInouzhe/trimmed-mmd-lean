import StatFormal.Wave30tv.RouteSeq
import StatFormal.Wave30tq.RouteLemmas
import StatFormal.Wave30tq.RouteLower

/-!
# Wave 30tv route: the frozen claims (untrusted)

* `slice_level`: `core_level` for the rules evaluated at a fixed `u`;
* `thm_betting_cond_route` (every batch-0 value: the rules composed with `withBatchZero`; the blocks lie outside
  batch 0, so the pair statistics are unchanged), `thm_betting_route` (Fubini over `u`, 30tq `prod_le_of_slices`),
  `thm_betting_condexp_route` (`P(reject ∩ S) ≤ δ P(S)` for every `S ∈ σ(u, batch 0)` by slicing, then the
  set-integral characterisation of the conditional expectation on the trimmed measure);
* `cor_lower_route` (as `cor:lower`: only the first grid level `j₀` with `TV ≤ α_{j₀}` enters), `lem_ramp_iii_route`,
  `single_split_route` (instantiation: fold one as `u`, every label `1`, batch 0 empty).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tv

open StatFormal.Wave30tq StatFormal.Betting

variable {𝒳 U : Type*} [MeasurableSpace 𝒳] [MeasurableSpace U] {n m N : ℕ}

lemma measurable_withBatchZero {p : ℕ} (l : Fin p → ℕ) (x₀ : Fin p → 𝒳) :
    Measurable (withBatchZero l x₀) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : l i = 0
  · simp only [withBatchZero, h, ite_true]; exact measurable_const
  · simp only [withBatchZero, h, ite_false]; exact measurable_pi_apply i

omit [MeasurableSpace 𝒳] in
lemma withBatchZero_of_ne {p : ℕ} {l : Fin p → ℕ} {x₀ x : Fin p → 𝒳} {i : Fin p} (h : l i ≠ 0) :
    withBatchZero l x₀ x i = x i := by simp [withBatchZero, h]

omit [MeasurableSpace 𝒳] in
lemma withBatchZero_agree {p : ℕ} {l : Fin p → ℕ} {b : ℕ} {x₀ x x' : Fin p → 𝒳}
    (h : ∀ i, l i < b → x i = x' i) : ∀ i, l i < b → withBatchZero l x₀ x i = withBatchZero l x₀ x' i := by
  intro i hi
  unfold withBatchZero
  split_ifs
  · rfl
  · exact h i hi

lemma measurable_batchZero (lx : Fin n → ℕ) (ly : Fin m → ℕ) :
    Measurable (batchZero (𝒳 := 𝒳) (U := U) lx ly) := by
  unfold batchZero
  fun_prop

omit [MeasurableSpace 𝒳] [MeasurableSpace U] in
lemma depOn_before {β : Type*} {lx : Fin n → ℕ} {ly : Fin m → ℕ} {b : ℕ}
    {F : (Fin n → 𝒳) → (Fin m → 𝒳) → β}
    (hF : ∀ x x' y y', (∀ i, lx i < b → x i = x' i) → (∀ j, ly j < b → y j = y' j) → F x y = F x' y') :
    DepOn (before lx ly b) (fun ω => F ω.1 ω.2) :=
  fun ω ω' h => hF _ _ _ _ (fun i hi => h (Sum.inl i) hi) (fun j hj => h (Sum.inr j) hj)

variable {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
  {B : Fin N → Finset (Fin m)}

/-- The level bound at a fixed `u`, for every event `s` of batch 0. -/
theorem slice_level (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α δ c : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hc1 : c ≤ 1)
    {g : ℕ → U → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
    {lam : (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hg : IsBatchRule lx ly bat g) (hlam : IsBatchBetRule lx ly bat α c lam)
    (hTV : StatFormal.Distances.tvDist P Q ≤ α) (u : U)
    {s : Set ((Fin n → 𝒳) × (Fin m → 𝒳))} (hs : MeasurableSet s)
    (hsd : DepOn (before lx ly 1) (fun ω => ω ∈ s)) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real
        ({ω | seqReject lam g bat A B α δ u ω.1 ω.2} ∩ s) ≤
      δ * ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real s :=
  core_level P Q hpair hα hδ hc1 (fun b ω => g b u ω.1 ω.2)
    (fun k => (hg k).1.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    (fun k ω z => (hg k).2.1 u ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => g (bat k) u x y) fun x x' y y' hx hy => (hg k).2.2 u x x' y y' hx hy)
    (fun k ω z => lam k u ω.1 ω.2 z)
    (fun k => (hlam k).1.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    (fun k ω z => (hlam k).2.1 u ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => lam k u x y) fun x x' y y' hx hy => (hlam k).2.2 u x x' y y' hx hy)
    hTV hs hsd

/-- The rejection event is measurable. -/
lemma measurableSet_seqReject {α δ c : ℝ} {g : ℕ → U → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
    {lam : (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hg : IsBatchRule lx ly bat g) (hlam : IsBatchBetRule lx ly bat α c lam) :
    MeasurableSet {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) | seqReject lam g bat A B α δ ω.1 ω.2.1 ω.2.2} := by
  have hZ : ∀ k : Fin N, Measurable fun ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      seqZ g bat A B ω.1 ω.2.1 ω.2.2 k := fun k => by
    unfold seqZ pairZ blockMean
    refine Measurable.sub (Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _)
      (Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _)
    · exact (hg k).1.comp (measurable_id.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    · exact (hg k).1.comp (measurable_id.prodMk ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hW : ∀ t, Measurable fun ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      wealth (fun k => lam k ω.1 ω.2.1 ω.2.2) α (seqZ g bat A B ω.1 ω.2.1 ω.2.2) t := fun t => by
    unfold wealth
    refine Finset.measurable_prod _ fun k _ => ?_
    refine measurable_const.add (Measurable.mul ?_ ((hZ k).sub_const α))
    exact (hlam k).1.comp (measurable_id.prodMk (Measurable.of_eval fun i => hZ _))
  unfold seqReject betReject
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun t =>
    (MeasurableSet.const (t ≤ N)).inter (measurableSet_le measurable_const (hW t))

/-- `thm:betting` (v2 seq), for every value of batch 0. -/
theorem thm_betting_cond_route : Claims.thm_betting_cond := by
  intro 𝒳 U _ _ P Q _ _ n m N lx ly bat A B α δ c g lam hpair hα hδ0 _ _ hc1 hg hlam hTV u x₀ y₀
  set G : ℕ → (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ :=
    fun b ω => g b u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) with hG
  set Lam : (k : ℕ) → (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin k → ℝ) → ℝ :=
    fun k ω => lam k u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) with hLam
  have hφ : Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) =>
      (withBatchZero lx x₀ ω.1, withBatchZero ly y₀ ω.2) :=
    ((measurable_withBatchZero lx x₀).comp measurable_fst).prodMk
      ((measurable_withBatchZero ly y₀).comp measurable_snd)
  have h := core_level P Q hpair hα hδ0 hc1 G
    (fun k => (hg k).1.comp ((measurable_const.prodMk (hφ.comp measurable_fst)).prodMk measurable_snd))
    (fun k ω z => (hg k).2.1 _ _ _ z)
    (fun k ω ω' hω => (hg k).2.2 u _ _ _ _ (withBatchZero_agree fun i hi => hω (Sum.inl i) hi)
      (withBatchZero_agree fun j hj => hω (Sum.inr j) hj))
    Lam
    (fun k => (hlam k).1.comp ((measurable_const.prodMk (hφ.comp measurable_fst)).prodMk measurable_snd))
    (fun k ω z => (hlam k).2.1 _ _ _ z)
    (fun k ω ω' hω => (hlam k).2.2 u _ _ _ _ (withBatchZero_agree fun i hi => hω (Sum.inl i) hi)
      (withBatchZero_agree fun j hj => hω (Sum.inr j) hj))
    hTV (s := Set.univ) MeasurableSet.univ (fun _ _ _ => rfl)
  rw [Set.inter_univ, probReal_univ, mul_one] at h
  have hset : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
      seqReject lam g bat A B α δ u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} =
      {ω | betReject (fun k => Lam k ω) α δ (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k)} := by
    ext ω
    have hZ : seqZ g bat A B u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) =
        fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k := funext fun k => by
      unfold seqZ
      refine pairZ_congr k (fun i hi => withBatchZero_of_ne ?_) (fun j hj => withBatchZero_of_ne ?_)
      · rw [hpair.2.2.2.1 k i hi]; have := hpair.2.2.1 k; omega
      · rw [hpair.2.2.2.2 k j hj]; have := hpair.2.2.1 k; omega
    change seqReject lam g bat A B α δ u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) ↔
      betReject (fun k => Lam k ω) α δ (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k)
    unfold seqReject
    rw [hZ]
  rw [hset, ← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- `thm:betting` (v2 seq), "Hence": the unconditional level bound. -/
theorem thm_betting_route : Claims.thm_betting := by
  intro 𝒳 U _ _ P Q _ _ ν _ n m N lx ly bat A B α δ c g lam hpair hα hδ0 _ _ hc1 hg hlam hTV
  have hS := measurableSet_seqReject (A := A) (B := B) (δ := δ) hg hlam
  refine prod_le_of_slices ν _ hS fun u => ?_
  have h := slice_level (A := A) (B := B) P Q hpair hα hδ0 hc1 hg hlam hTV u (s := Set.univ)
    MeasurableSet.univ (fun _ _ _ => rfl)
  rw [Set.inter_univ, probReal_univ, mul_one] at h
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- `thm:betting` (v2 seq), the conditional display: `P(reject | σ(u, batch 0)) ≤ δ` a.s. -/
theorem thm_betting_condexp_route : Claims.thm_betting_condexp := by
  intro 𝒳 U _ _ P Q _ _ ν _ n m N lx ly bat A B α δ c g lam hpair hα hδ0 _ _ hc1 hg hlam hTV
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  set μt := ν.prod μ with hμt
  set R := {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) | seqReject lam g bat A B α δ ω.1 ω.2.1 ω.2.2} with hRdef
  have hR : MeasurableSet R := measurableSet_seqReject hg hlam
  refine ⟨hR, ?_⟩
  have hm : MeasurableSpace.comap (batchZero (𝒳 := 𝒳) (U := U) lx ly) inferInstance ≤
      (inferInstance : MeasurableSpace (U × ((Fin n → 𝒳) × (Fin m → 𝒳)))) :=
    (measurable_batchZero (𝒳 := 𝒳) (U := U) lx ly).comap_le
  -- `P(R ∩ S) ≤ δ P(S)` for every `S ∈ σ(u, batch 0)`
  have hkey : ∀ S, MeasurableSet[MeasurableSpace.comap (batchZero (𝒳 := 𝒳) (U := U) lx ly) inferInstance] S →
      μt.real (S ∩ R) ≤ μt.real S * δ := by
    rintro _ ⟨T, hT, rfl⟩
    have hS : MeasurableSet (batchZero lx ly ⁻¹' T) := measurable_batchZero lx ly hT
    have hsl : ∀ u, μ (Prod.mk u ⁻¹' (batchZero lx ly ⁻¹' T ∩ R)) ≤
        ENNReal.ofReal δ * μ (Prod.mk u ⁻¹' (batchZero lx ly ⁻¹' T)) := by
      intro u
      have hsu : MeasurableSet (Prod.mk u ⁻¹' (batchZero (𝒳 := 𝒳) lx ly ⁻¹' T)) :=
        measurable_prodMk_left hS
      have hsud : DepOn (before lx ly 1)
          (fun ω => ω ∈ Prod.mk u ⁻¹' (batchZero (𝒳 := 𝒳) lx ly ⁻¹' T)) := fun ω ω' h => by
        have hb : batchZero lx ly (u, ω) = batchZero lx ly (u, ω') := by
          simp only [batchZero]
          congr 2
          · funext i
            exact h (Sum.inl i.1) (show lx i.1 < 1 by rw [i.2]; omega)
          · funext j
            exact h (Sum.inr j.1) (show ly j.1 < 1 by rw [j.2]; omega)
        change (batchZero lx ly (u, ω) ∈ T) = (batchZero lx ly (u, ω') ∈ T)
        rw [hb]
      have h := slice_level (A := A) (B := B) P Q hpair hα hδ0 hc1 hg hlam hTV u hsu hsud
      have hset : Prod.mk u ⁻¹' (batchZero lx ly ⁻¹' T ∩ R) =
          {ω | seqReject lam g bat A B α δ u ω.1 ω.2} ∩ Prod.mk u ⁻¹' (batchZero lx ly ⁻¹' T) := by
        rw [Set.preimage_inter, Set.inter_comm]
        rfl
      rw [hset, ← ofReal_measureReal (measure_ne_top _ _),
        ← ofReal_measureReal (measure_ne_top μ (Prod.mk u ⁻¹' (batchZero lx ly ⁻¹' T))),
        ← ENNReal.ofReal_mul hδ0.le]
      exact ENNReal.ofReal_le_ofReal h
    have hmeas : μt (batchZero lx ly ⁻¹' T ∩ R) ≤ ENNReal.ofReal δ * μt (batchZero lx ly ⁻¹' T) := by
      rw [hμt, Measure.prod_apply (hS.inter hR), Measure.prod_apply hS,
        ← lintegral_const_mul _ (measurable_measure_prodMk_left hS)]
      exact lintegral_mono hsl
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hmeas
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0.le] at this
    rw [measureReal_def, measureReal_def, mul_comm]
    exact this
  -- the set-integral characterisation on the trimmed measure
  have hfint : Integrable (R.indicator fun _ => (1 : ℝ)) μt := (integrable_const (1 : ℝ)).indicator hR
  refine ae_le_of_ae_le_trim (hm := hm) ?_
  refine ae_le_of_forall_setIntegral_le (integrable_condExp.trim hm stronglyMeasurable_condExp)
    (integrable_const δ) fun S hS _ => ?_
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hS, ← setIntegral_trim hm stronglyMeasurable_const hS,
    setIntegral_condExp hm hfint hS, setIntegral_indicator hR, setIntegral_const, setIntegral_const,
    smul_eq_mul, smul_eq_mul, mul_one]
  have hSR : μt.real (S ∩ R) ≤ μt.real S * δ := hkey S hS
  simpa [measureReal_restrict_apply_univ] using hSR

/-- `cor:lower` (v2 seq), finite-sample clause. -/
theorem cor_lower_route : Claims.cor_lower := by
  intro 𝒳 U _ _ P Q _ _ ν _ n m N J lx ly bat A B α δ c g lam hpair hδ0 hδ1 hc0 hc1 hα hg hlam
  set μt := ν.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) with hμt
  set R : Fin J → Set (U × ((Fin n → 𝒳) × (Fin m → 𝒳))) := fun j =>
    {ω | seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2} with hR
  have hRm : ∀ j, MeasurableSet (R j) := fun j => measurableSet_seqReject (hg j) (hlam j)
  have hRle : ∀ j, StatFormal.Distances.tvDist P Q ≤ α j → μt (R j) ≤ ENNReal.ofReal δ := fun j hj =>
    thm_betting_route 𝒳 U P Q ν n m N lx ly bat A B (α j) δ c (g j) (lam j) hpair (hα j) hδ0 hδ1 hc0 hc1
      (hg j) (hlam j) hj
  set t := StatFormal.Distances.tvDist P Q with ht
  have ht0 : 0 ≤ t := StatFormal.Distances.tvDist_nonneg P Q
  have hD := StatFormal.TrimmedMMD.Lower.downclosed_measurable_le _ μt J α R t hRm ht0
  change μt {ω | t < StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => ω ∈ R j)} ≤ ENNReal.ofReal δ
  by_cases hex : ∃ j, t ≤ α j
  · classical
    set s := Finset.univ.filter (fun j : Fin J => t ≤ α j) with hs
    have hsne : s.Nonempty := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
    set j₀ := s.min' hsne with hj₀
    have hj₀mem : t ≤ α j₀ := (Finset.mem_filter.1 (s.min'_mem hsne)).2
    have hmin : ∀ i < j₀, α i < t := fun i hi => by
      by_contra hcon
      push Not at hcon
      have : j₀ ≤ i := s.min'_le i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
      exact absurd hi (not_lt.2 this)
    exact (hD.2.1 j₀ hj₀mem hmin).trans (hRle j₀ hj₀mem)
  · push Not at hex
    rw [hD.2.2 hex, measure_empty]
    exact zero_le

/-- `lem:ramp` (iii) (v2 seq). -/
theorem lem_ramp_iii_route : Claims.lem_ramp_iii := by
  intro 𝒳 _ P Q _ _ f s s' hf hss
  have hm : Measurable (ramp f s s') := by
    show Measurable fun x => (min (max (f x) s') s - s') / (s - s')
    exact (((hf.max measurable_const).min measurable_const).sub_const _).div_const _
  have h01 := (lem2_1_route 𝒳 P Q 0 f s s' hf le_rfl zero_lt_one hss).1
  exact ⟨hm, h01, delta_le_tv P Q hm h01⟩

/-- With no batch 0, `σ(u, batch 0) = σ(u)`. -/
lemma comap_batchZero_one :
    MeasurableSpace.comap (batchZero (𝒳 := 𝒳) (U := U) (fun _ : Fin n => 1) (fun _ : Fin m => 1)) inferInstance
      = MeasurableSpace.comap (Prod.fst : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) → U) inferInstance := by
  apply le_antisymm
  · rintro s ⟨t, ht, rfl⟩
    have hsub : Subsingleton (({i : Fin n // (fun _ : Fin n => 1) i = 0} → 𝒳) ×
        ({j : Fin m // (fun _ : Fin m => 1) j = 0} → 𝒳)) := by
      constructor; intro a b
      ext ⟨i, hi⟩ <;> simp at hi
    let c : (({i : Fin n // (fun _ : Fin n => 1) i = 0} → 𝒳) × ({j : Fin m // (fun _ : Fin m => 1) j = 0} → 𝒳)) :=
      (fun i => absurd i.2 (by simp), fun j => absurd j.2 (by simp))
    refine ⟨(fun u => (u, c)) ⁻¹' t, measurable_prodMk_right ht, ?_⟩
    ext ω
    simp only [Set.mem_preimage, batchZero]
    rw [Subsingleton.elim (fun i => ω.2.1 i.1, fun j => ω.2.2 j.1) c]
  · rintro s ⟨t, ht, rfl⟩
    exact ⟨Prod.fst ⁻¹' t, measurable_fst ht, rfl⟩

/-- "The single split is the case `B = 1`": the 30tq single-split claims are instances. -/
theorem single_split_route : Claims.single_split := by
  refine ⟨?_, ?_, ?_⟩
  · intro h 𝒳 _ P Q _ _ n m N A B α δ c g lam hAB hα hδ hδ1 hc hc1 hg hg01 hlam hTV
    obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
    have := h 𝒳 Unit P Q n m N (fun _ => 1) (fun _ => 1) (fun _ => 1) A B α δ c
      (fun _ _ _ _ z => g z) (fun k _ _ _ z => lam k z)
      ⟨hAB, monotone_const, fun _ => le_rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩ hα hδ hδ1 hc hc1
      (fun k => ⟨hg.comp measurable_snd, fun u x y z => hg01 z, fun _ _ _ _ _ _ _ => rfl⟩)
      (fun k => ⟨(hlam k k.isLt).1.comp measurable_snd, fun u x y z => (hlam k k.isLt).2 z,
        fun _ _ _ _ _ _ _ => rfl⟩) hTV
      () (fun _ => x0) (fun _ => x0)
    have hw : ∀ {p : ℕ} (x₀ x : Fin p → 𝒳), withBatchZero (fun _ => 1) x₀ x = x := by
      intro p x₀ x; funext i; simp [withBatchZero]
    simp only [hw] at this
    exact this
  · intro h 𝒳 Ω₁ _ _ P Q _ _ μ₁ _ n m N A B α δ c g lam hAB hα hδ hδ1 hc hc1 hg hg01 hlam hTV
    obtain ⟨hS, hce⟩ := h 𝒳 Ω₁ P Q μ₁ n m N (fun _ => 1) (fun _ => 1) (fun _ => 1) A B α δ c
      (fun _ u _ _ z => g u z) (fun k u _ _ z => lam u k z)
      ⟨hAB, monotone_const, fun _ => le_rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩ hα hδ hδ1 hc hc1
      (fun k => ⟨hg.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd), fun u x y z => hg01 u z,
        fun _ _ _ _ _ _ _ => rfl⟩)
      (fun k => ⟨(hlam k k.isLt).1.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd),
        fun u x y z => (hlam k k.isLt).2 u z, fun _ _ _ _ _ _ _ => rfl⟩) hTV
    rw [comap_batchZero_one] at hce
    exact ⟨hS, hce⟩
  · intro h 𝒳 Ω₁ _ _ P Q _ _ μ₁ _ n m N A B α δ c g lam hAB hα hδ hδ1 hc hc1 hg hg01 hlam hTV
    exact h 𝒳 Ω₁ P Q μ₁ n m N (fun _ => 1) (fun _ => 1) (fun _ => 1) A B α δ c
      (fun _ u _ _ z => g u z) (fun k u _ _ z => lam u k z)
      ⟨hAB, monotone_const, fun _ => le_rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩ hα hδ hδ1 hc hc1
      (fun k => ⟨hg.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd), fun u x y z => hg01 u z,
        fun _ _ _ _ _ _ _ => rfl⟩)
      (fun k => ⟨(hlam k k.isLt).1.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd),
        fun u x y z => (hlam k k.isLt).2 u z, fun _ _ _ _ _ _ _ => rfl⟩) hTV

end StatFormal.Wave30tv
