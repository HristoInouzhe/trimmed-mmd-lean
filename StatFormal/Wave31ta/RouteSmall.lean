import StatFormal.Wave31ta.Statements
import StatFormal.Archive.Wave18b.Proofs
import StatFormal.Archive.Wave17a.Proofs
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs
import StatFormal.Wave30tv.Proofs

/-!
# Wave 31ta routes (untrusted): `continuity_v2`, `distmax`, `uniform_event`, `cor_lower_v2`

* `continuity_v2`: the certified `Wave18b.continuity_lip` at `η = 1 − ᾱ` for `ᾱ > 0`; `ᾱ = 0` forces `α = α' = 0`.
* `distmax`: the certified `Wave17a.separation`, `separation_nearest_exists`, `separation_attained`, and `sep(0; A, B) = 0`.
* `uniform_event`: the named event equals the countable-supremum event of the certified concentration proof
  (`TrimmedMMD/Concentration/Proofs.lean`, `exists_good_event`), and the deterministic reduction `hausdorffDist_le_rn`.
* `cor_lower_v2`: pathwise, the event equals `⋃_{j : TV ≤ α_j} ⋂_{i ≤ j} R_i` (strictly increasing grid, `α_j ≥ 0`), which lies in the
  rejection event of the first grid level `≥ TV`; its probability is bounded by the certified `Wave30tv.thm_betting`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31ta

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

/-! ### `lem:continuity (v2 short)` -/

theorem continuity_v2 : Claims.continuity_v2 := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ ab α α' hφ hκ hab0 hab1 hα hα'
  rcases hab0.eq_or_lt with h0 | hpos
  · have h1 : α = 0 := le_antisymm (h0 ▸ hα.2) hα.1
    have h2 : α' = 0 := le_antisymm (h0 ▸ hα'.2) hα'.1
    subst h1 h2
    simp
  · have hη : (1 : ℝ) - (1 - ab) = ab := by ring
    have h := StatFormal.Wave18b.continuity_lip 𝒳 H P Q φ κ (1 - ab) α α' hφ hκ (by linarith) (by linarith)
      ⟨hα.1, by rw [hη]; exact hα.2⟩ ⟨hα'.1, by rw [hη]; exact hα'.2⟩
    exact h

/-! ### `eq:distmax (v2 short)` -/

theorem sepVal_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A B : Set H}
    (hA : A.Nonempty) (hB : B.Nonempty) : StatFormal.Wave17a.sepVal 0 A B = 0 := by
  unfold StatFormal.Wave17a.sepVal
  simp only [inner_zero_left, EReal.coe_zero]
  rw [biInf_const hA, biSup_const hB, sub_zero]

theorem setDist_nonneg' {H : Type*} [NormedAddCommGroup H] (A B : Set H) : 0 ≤ setDist A B := by
  unfold setDist
  apply Real.sInf_nonneg
  rintro r ⟨a, -, b, -, rfl⟩
  exact norm_nonneg _

theorem distmax : Claims.distmax := by
  intro H _ _ _ A B hA hB hcA hcB hkA hkB
  have hzero := sepVal_zero hA hB
  have hd0 := setDist_nonneg' A B
  refine ⟨⟨?_, ?_⟩, fun h0 => by rw [hzero, h0]; rfl, fun a ha b hb hpos hab =>
    (StatFormal.Wave17a.separation_attained H A B a b hcA hcB hkA hkB hpos ha hb hab).2⟩
  · rcases hd0.eq_or_lt with h0 | hpos
    · exact ⟨0, Metric.mem_closedBall_self zero_le_one, by show StatFormal.Wave17a.sepVal 0 A B = _; rw [hzero, ← h0]; rfl⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := StatFormal.Wave17a.separation_nearest_exists H A B hA hB hkA hkB
      obtain ⟨hn, hv⟩ := StatFormal.Wave17a.separation_attained H A B a b hcA hcB hkA hkB hpos ha hb hab
      exact ⟨_, mem_closedBall_zero_iff.2 hn.le, hv⟩
  · rintro y ⟨f, hf, rfl⟩
    exact StatFormal.Wave17a.separation H A B f hA hB (mem_closedBall_zero_iff.1 hf)

/-! ### `cor:uniform (v2 short)` -/

theorem gDev_eq {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure 𝒳) (φ : 𝒳 → H) (κ : ℝ) {n : ℕ} (x : Fin n → 𝒳) :
    gDev P φ κ x = ⨆ p : StatFormal.Concentration.tmParams H κ,
      |StatFormal.Concentration.empDev P (StatFormal.Concentration.gTM φ) n x p.1| := rfl

theorem uniform_event : Claims.uniform_event := by
  intro 𝒳 H _ _ _ _ _ P _ φ κ δ n hφ hκ hn hδ0 hδ1
  set bnd := 4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n) with hbnd
  have hκ0 : 0 ≤ κ := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ y)
  have h0 : ((0 : H), (0 : ℝ)) ∈ StatFormal.Concentration.tmParams H κ := ⟨by simp, by simp [hκ0]⟩
  haveI : Nonempty (StatFormal.Concentration.tmParams H κ) := ⟨⟨_, h0⟩⟩
  have hdet : ∀ x : Fin n → 𝒳, gDev P φ κ x ≤ bnd → ∀ α, 0 ≤ α → α < 1 →
      Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤ rn κ α δ n := by
    intro x hx α hα0 hα1
    rw [gDev_eq] at hx
    exact StatFormal.TrimmedMMD.Concentration.hausdorffDist_le_rn P hφ hκ hα0 hα1 hn x hx
  rcases hκ0.eq_or_lt with hκe | hκpos
  · -- `κ = 0`: the class is `{0}`, the event is everything.
    subst hκe
    have hφ0 : ∀ y, φ y = 0 := fun y => norm_le_zero_iff.1 (hκ y)
    have hall : ∀ x : Fin n → 𝒳, gDev P φ 0 x ≤ bnd := by
      intro x
      rw [gDev_eq]
      have hb : bnd = 0 := by rw [hbnd]; simp
      rw [hb]
      refine ciSup_le fun p => ?_
      have hp2 : p.1.2 = 0 := abs_nonpos_iff.1 p.2.2
      have hg : ∀ y, StatFormal.Concentration.gTM φ p.1 y = 0 := fun y => by
        simp [StatFormal.Concentration.gTM, hφ0, hp2]
      simp [StatFormal.Concentration.empDev, hg]
    have hset : {x : Fin n → 𝒳 | gDev P φ 0 x ≤ bnd} = univ := eq_univ_of_forall hall
    refine ⟨by rw [hset]; exact MeasurableSet.univ, by rw [hset, probReal_univ]; linarith, hdet⟩
  · obtain ⟨T₀, hT₀, hcount, hdense⟩ :=
      (TopologicalSpace.IsSeparable.of_separableSpace (StatFormal.Concentration.tmParams H κ)).exists_countable_dense_subset
    have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense h0⟩
    haveI : Nonempty T₀ := hne.to_subtype
    haveI : Countable T₀ := hcount.to_subtype
    have hset : {x : Fin n → 𝒳 | gDev P φ κ x ≤ bnd} =
        {x | ⨆ q : T₀, |StatFormal.Concentration.empDev P (fun q : T₀ => StatFormal.Concentration.gTM φ q.1) n x q|
          ≤ bnd} := by
      ext x
      show gDev P φ κ x ≤ bnd ↔ _
      rw [gDev_eq, StatFormal.Concentration.iSup_tmParams_eq P hφ hκ T₀ hT₀ hdense x]
      exact Iff.rfl
    refine ⟨?_, ?_, hdet⟩
    · rw [hset]
      exact measurableSet_le (Measurable.iSup fun q => continuous_abs.measurable.comp
        (StatFormal.Concentration.measurable_empDev P
          (fun q : T₀ => StatFormal.Concentration.measurable_gTM hφ q.1) n q)) measurable_const
    · rw [hset]
      exact StatFormal.Concentration.tm_concentration_countable P T₀ hT₀ hφ hκ hκpos hn hδ0 hδ1

/-! ### `cor:lower (v2 short)` -/

section Lower

open StatFormal.TrimmedMMD.Lower

/-- The pathwise identity for a strictly increasing grid of nonnegative levels:
`{(∃ j, α̂_lo = α_j ∧ rej_j) ∧ t ≤ α̂_lo} = ∃ j, t ≤ α_j ∧ ∀ i ≤ j, rej_i`. -/
theorem lower_event_iff {J : ℕ} {α : Fin J → ℝ} (hα : StrictMono α) (hα0 : ∀ j, 0 ≤ α j) (rej : Fin J → Prop)
    (t : ℝ) :
    ((∃ j, alphaLo α rej = α j ∧ rej j) ∧ t ≤ alphaLo α rej) ↔ ∃ j, t ≤ α j ∧ ∀ i ≤ j, rej i := by
  classical
  set S := Finset.univ.filter fun j : Fin J => ∀ i ≤ j, rej i with hS
  constructor
  · rintro ⟨⟨j, hj, hrj⟩, ht⟩
    by_cases hne : S.Nonempty
    · have hlo : alphaLo α rej = S.sup' hne α := by
        unfold alphaLo; rw [dif_pos hne]
      obtain ⟨j', hj'S, hj'⟩ := Finset.exists_mem_eq_sup' hne α
      have hjj : j = j' := hα.injective (by rw [← hj, hlo, hj'])
      subst hjj
      refine ⟨j, by rw [← hj]; exact ht, (Finset.mem_filter.1 hj'S).2⟩
    · exfalso
      have hlo : alphaLo α rej = 0 := by unfold alphaLo; rw [dif_neg hne]
      apply hne
      refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => ?_⟩⟩
      rcases hi.lt_or_eq with hlt | heq
      · have := hα hlt
        rw [← hj, hlo] at this
        exact absurd this (not_lt.2 (hα0 i))
      · exact heq ▸ hrj
  · rintro ⟨j, ht, hrj⟩
    have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hrj⟩
    have hne : S.Nonempty := ⟨j, hjS⟩
    have hlo : alphaLo α rej = S.sup' hne α := by
      unfold alphaLo; rw [dif_pos hne]
    obtain ⟨j', hj'S, hj'⟩ := Finset.exists_mem_eq_sup' hne α
    refine ⟨⟨j', by rw [hlo, hj'], (Finset.mem_filter.1 hj'S).2 j' le_rfl⟩, ?_⟩
    rw [hlo]
    exact ht.trans (Finset.le_sup' α hjS)

theorem cor_lower_v2 : Claims.cor_lower_v2 := by
  intro 𝒳 U _ _ P Q _ _ ν _ n m N J lx ly bat A B α δ c g lam hpair hδ0 hδ1 hc0 hc1 hmono hα0 hrule hbet
  classical
  set μ := ν.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) with hμ
  set rej : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) → Fin J → Prop := fun ω j =>
    StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2 with hrej
  set R : Fin J → Set (U × ((Fin n → 𝒳) × (Fin m → 𝒳))) := fun j => {ω | rej ω j} with hR
  -- measurability of each rejection event (it does not depend on the laws: use `P` for both samples)
  have hRm : ∀ j, MeasurableSet (R j) := fun j =>
    (StatFormal.Wave30tv.thm_betting_condexp 𝒳 U P P ν n m N lx ly bat A B (α j) δ c (g j) (lam j) hpair
      (hα0 j) hδ0 hδ1 hc0 hc1 (hrule j) (hbet j) (by rw [StatFormal.Distances.tvDist_self]; exact hα0 j)).1
  have hE : {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
      (∃ j, alphaLo α (rej ω) = α j ∧ rej ω j) ∧ StatFormal.Distances.tvDist P Q ≤ alphaLo α (rej ω)} =
      ⋃ j ∈ Finset.univ.filter (fun j : Fin J => StatFormal.Distances.tvDist P Q ≤ α j), ⋂ i ∈ Finset.Iic j, R i := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iic, exists_prop, hR]
    rw [lower_event_iff hmono hα0 (rej ω)]
  have hEm : MeasurableSet {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
      (∃ j, alphaLo α (rej ω) = α j ∧ rej ω j) ∧ StatFormal.Distances.tvDist P Q ≤ alphaLo α (rej ω)} := by
    rw [hE]
    exact Finset.measurableSet_biUnion _ fun j _ => Finset.measurableSet_biInter _ fun i _ => hRm i
  refine ⟨hEm, ?_, StatFormal.Wave30tv.cor_lower 𝒳 U P Q ν n m N J lx ly bat A B α δ c g lam hpair hδ0 hδ1 hc0
    hc1 hα0 hrule hbet⟩
  rw [hE]
  by_cases hex : (Finset.univ.filter (fun j : Fin J => StatFormal.Distances.tvDist P Q ≤ α j)).Nonempty
  · set i0 := (Finset.univ.filter (fun j : Fin J => StatFormal.Distances.tvDist P Q ≤ α j)).min' hex with hi0
    have hi0mem := Finset.min'_mem _ hex
    rw [← hi0] at hi0mem
    have hsub : (⋃ j ∈ Finset.univ.filter (fun j : Fin J => StatFormal.Distances.tvDist P Q ≤ α j),
        ⋂ i ∈ Finset.Iic j, R i) ⊆ R i0 := by
      intro ω hω
      simp only [mem_iUnion, mem_iInter, exists_prop, Finset.mem_Iic] at hω
      obtain ⟨j, hj, hω⟩ := hω
      exact hω i0 (Finset.min'_le _ _ hj)
    have hlev := StatFormal.Wave30tv.thm_betting 𝒳 U P Q ν n m N lx ly bat A B (α i0) δ c (g i0) (lam i0)
      hpair (hα0 i0) hδ0 hδ1 hc0 hc1 (hrule i0) (hbet i0) (Finset.mem_filter.1 hi0mem).2
    exact (measure_mono hsub).trans hlev
  · rw [Finset.not_nonempty_iff_eq_empty] at hex
    rw [hex]
    simp

end Lower

end StatFormal.Wave31ta
