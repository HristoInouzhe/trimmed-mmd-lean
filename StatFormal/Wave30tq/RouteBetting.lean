import StatFormal.Wave30tq.RouteIndep

/-!
# Wave 30tq route: Theorem 1 (the betting certificate) — untrusted

* `pairFiltration`: `𝒢_t = σ(Z_i : i < t)` on fold two;
* `bet_level`: per fold, if `Δ = E_P g − E_Q g ≤ α` then `P(max_{t ≤ N} K_t ≥ 1/δ) ≤ δ` (library
  `Betting.betting_ville`: the wealth is a nonnegative supermartingale, Ville's inequality on a finite horizon);
* `measurableSet_betReject`: the rejection event is measurable when the rules are jointly measurable in `D_1`;
* `prod_le_of_slices`, `condExp_indicator_le_of_slices`: Fubini and the conditional probability given the first
  factor of a product space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tq

open StatFormal.Betting

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}

/-- The filtration `𝒢_t = σ(Z_i : i < t)` of the pair statistics. -/
def pairFiltration {g : 𝒳 → ℝ} (hg : Measurable g) (A : Fin N → Finset (Fin n))
    (B : Fin N → Finset (Fin m)) :
    Filtration ℕ (inferInstance : MeasurableSpace ((Fin n → 𝒳) × (Fin m → 𝒳))) where
  seq t := ⨆ i ∈ {i : Fin N | (i : ℕ) < t},
    MeasurableSpace.comap (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => pairZ g A B ω.1 ω.2 i) inferInstance
  mono' _ _ hst := biSup_mono fun _ hi => lt_of_lt_of_le hi hst
  le' _ := iSup₂_le fun i _ => (measurable_pairZ hg A B i).comap_le

lemma measurable_pairZ_filt {g : 𝒳 → ℝ} (hg : Measurable g) (A : Fin N → Finset (Fin n))
    (B : Fin N → Finset (Fin m)) (i : Fin N) {t : ℕ} (hit : (i : ℕ) < t) :
    Measurable[pairFiltration hg A B t] (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => pairZ g A B ω.1 ω.2 i) :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun j (_ : j ∈ {i : Fin N | (i : ℕ) < t}) =>
    MeasurableSpace.comap (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => pairZ g A B ω.1 ω.2 j) inferInstance) i hit)

/-- **Theorem 1, one fold**: if `Δ = E_P g − E_Q g ≤ α`, the betting test rejects with probability at most `δ`. -/
theorem bet_level (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {α δ c : ℝ} {g : 𝒳 → ℝ} (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)} (hAB : IsBlockPairing A B)
    (hα : 0 ≤ α) (hδ : 0 < δ) (hc1 : c ≤ 1) {lam : (k : ℕ) → (Fin k → ℝ) → ℝ}
    (hlam : IsBetRule N α c lam) (hΔ : (∫ x, g x ∂P) - (∫ y, g y ∂Q) ≤ α) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
      {ω | betReject lam α δ (pairZ g A B ω.1 ω.2)} ≤ ENNReal.ofReal δ := by
  set ν := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hν
  set 𝒢 := pairFiltration hg A B with h𝒢
  set Z : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => pairZ g A B ω.1 ω.2 k with hZ
  set Y : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => Z k ω - α with hYdef
  set Λ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => lam k (past (fun i => Z i ω) k)
    with hΛdef
  have h1α : 0 < 1 + α := by linarith
  have hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k) := fun k =>
    (measurable_pairZ_filt hg A B k (Nat.lt_succ_self k)).sub_const α
  have hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k) := fun k => by
    refine (hlam k k.isLt).1.comp (@Measurable.of_eval _ _ _ (𝒢 k) _ _ fun i => ?_)
    exact measurable_pairZ_filt hg A B (Fin.castLE k.isLt.le i) (by simp)
  have hind : ∀ k : Fin N, Indep (MeasurableSpace.comap (Y k) inferInstance) (𝒢 k) ν := fun k => by
    have h := indep_pairZ_past P Q hg hAB k
    refine indep_of_indep_of_le_left h ?_
    exact ((comap_measurable (Z k)).sub_const α).comap_le
  have hZb : ∀ k ω, Z k ω ∈ Icc (-1 : ℝ) 1 := fun k ω => pairZ_mem hg01 hAB k ω.1 ω.2
  have hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ c / (1 + α) := fun k ω => (hlam k k.isLt).2 _
  have hYb : ∀ k ω, |Y k ω| ≤ 1 + α := fun k ω => by
    have := hZb k ω
    rw [abs_le]; constructor <;> simp only [hYdef] <;> linarith [this.1, this.2]
  have hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω := fun k ω => by
    have hYlo : -(1 + α) ≤ Y k ω := by
      have := hZb k ω; simp only [hYdef]; linarith [this.1]
    have hl := hΛb k ω
    have hcap : Λ k ω * (1 + α) ≤ c := by
      have := mul_le_mul_of_nonneg_right hl.2 h1α.le
      rwa [div_mul_cancel₀ c h1α.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left hYlo hl.1]
  have hmean : ∀ k, ∫ ω, Y k ω ∂ν ≤ 0 := fun k => by
    have hZi : Integrable (Z k) ν :=
      Integrable.of_mem_Icc (-1) 1 (measurable_pairZ hg A B k).aemeasurable (ae_of_all _ (hZb k))
    simp only [hYdef]
    rw [integral_sub hZi (integrable_const α), integral_const, probReal_univ, one_smul]
    have := integral_pairZ P Q hg hg01 hAB k
    simp only [hZ] at this ⊢
    rw [this]; linarith
  have hV := betting_ville 𝒢 Λ Y hY hΛ hind hΛb hYb hfac hmean (a := 1 / δ) (by positivity)
  rw [one_div_one_div] at hV
  exact hV

/-- The rejection event of the betting test is measurable when the rules are jointly measurable. -/
lemma measurableSet_betReject {Ω₁ : Type*} [MeasurableSpace Ω₁] {g : Ω₁ → 𝒳 → ℝ}
    (hg : Measurable fun p : Ω₁ × 𝒳 => g p.1 p.2) {lam : Ω₁ → (k : ℕ) → (Fin k → ℝ) → ℝ}
    (hlam : ∀ k < N, Measurable fun p : Ω₁ × (Fin k → ℝ) => lam p.1 k p.2)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α δ : ℝ) :
    MeasurableSet {ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
      betReject (lam ω.1) α δ (pairZ (g ω.1) A B ω.2.1 ω.2.2)} := by
  have hZ : ∀ k : Fin N, Measurable fun ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      pairZ (g ω.1) A B ω.2.1 ω.2.2 k := fun k => by
    unfold pairZ blockMean
    refine Measurable.sub (Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _)
      (Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _)
    · exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    · exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hW : ∀ t, Measurable fun ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      wealth (lam ω.1) α (pairZ (g ω.1) A B ω.2.1 ω.2.2) t := fun t => by
    unfold wealth
    refine Finset.measurable_prod _ fun k _ => ?_
    refine measurable_const.add (Measurable.mul ?_ ((hZ k).sub_const α))
    exact (hlam k k.isLt).comp (measurable_fst.prodMk (Measurable.of_eval fun i => hZ _))
  unfold betReject
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun t =>
    (MeasurableSet.const (t ≤ N)).inter (measurableSet_le measurable_const (hW t))

/-- Fubini bound: if every slice of a measurable set has `ν`-measure at most `b`, so does the set. -/
lemma prod_le_of_slices {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (μ₁ : Measure Ω₁)
    [IsProbabilityMeasure μ₁] (ν : Measure Ω₂) [SFinite ν] {S : Set (Ω₁ × Ω₂)} (hS : MeasurableSet S)
    {b : ℝ≥0∞} (h : ∀ d, ν (Prod.mk d ⁻¹' S) ≤ b) : (μ₁.prod ν) S ≤ b := by
  rw [Measure.prod_apply hS]
  calc ∫⁻ d, ν (Prod.mk d ⁻¹' S) ∂μ₁ ≤ ∫⁻ _, b ∂μ₁ := lintegral_mono h
    _ = b := by simp

/-- Conditional probability given the first factor: if every slice has `ν`-probability at most `δ`, then
`P(S | σ(first factor)) ≤ δ` almost surely. -/
lemma condExp_indicator_le_of_slices {Ω₁ Ω₂ : Type*} [mΩ₁ : MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (ν : Measure Ω₂) [IsProbabilityMeasure ν]
    {S : Set (Ω₁ × Ω₂)} (hS : MeasurableSet S) {δ : ℝ} (h : ∀ d, ν.real (Prod.mk d ⁻¹' S) ≤ δ) :
    condExp (MeasurableSpace.comap Prod.fst mΩ₁) (μ₁.prod ν) (S.indicator fun _ => (1 : ℝ))
      ≤ᵐ[μ₁.prod ν] fun _ => δ := by
  set μ := μ₁.prod ν with hμ
  have hm : MeasurableSpace.comap Prod.fst mΩ₁ ≤ (inferInstance : MeasurableSpace (Ω₁ × Ω₂)) :=
    measurable_fst.comap_le
  set h₁ : Ω₁ → ℝ := fun d => ν.real (Prod.mk d ⁻¹' S) with hh₁
  have hh₁m : Measurable h₁ := (measurable_measure_prodMk_left hS).ennreal_toReal
  set F : Ω₁ × Ω₂ → ℝ := fun ω => h₁ ω.1 with hF
  have hFm : Measurable[MeasurableSpace.comap Prod.fst mΩ₁] F := by
    rw [measurable_iff_comap_le]
    have : MeasurableSpace.comap F inferInstance =
        MeasurableSpace.comap Prod.fst (MeasurableSpace.comap h₁ inferInstance) := by
      rw [MeasurableSpace.comap_comp]; rfl
    rw [this]
    exact MeasurableSpace.comap_mono hh₁m.comap_le
  have hFb : ∀ ω, F ω ∈ Icc (0 : ℝ) 1 := fun ω =>
    ⟨measureReal_nonneg, by simp only [hF, hh₁]; exact measureReal_le_one⟩
  have hFint : Integrable F μ :=
    Integrable.of_mem_Icc 0 1 (hFm.mono hm le_rfl).aemeasurable (ae_of_all _ hFb)
  have hfint : Integrable (S.indicator fun _ => (1 : ℝ)) μ := (integrable_const (1 : ℝ)).indicator hS
  have hEq : F =ᵐ[μ] condExp (MeasurableSpace.comap Prod.fst mΩ₁) μ (S.indicator fun _ => (1 : ℝ)) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hfint (fun s _ _ => hFint.integrableOn)
      (fun s hs _ => ?_) hFm.stronglyMeasurable.aestronglyMeasurable
    obtain ⟨Bs, hBs, rfl⟩ := hs
    -- left side: `∫_{fst⁻¹ Bs} F = ∫_{Bs} ν(S_d) dμ₁`
    have hL : ∫ ω in Prod.fst ⁻¹' Bs, F ω ∂μ = ∫ d, Bs.indicator h₁ d ∂μ₁ := by
      rw [← integral_indicator (measurable_fst hBs)]
      have : (Prod.fst ⁻¹' Bs).indicator F = fun ω : Ω₁ × Ω₂ => Bs.indicator h₁ ω.1 := by
        funext ω; by_cases hω : ω.1 ∈ Bs <;> simp [hω, hF]
      rw [this, hμ, integral_fun_fst (fun d => Bs.indicator h₁ d), probReal_univ, one_smul]
    -- right side: `∫_{fst⁻¹ Bs} 1_S = μ(S ∩ fst⁻¹ Bs) = ∫_{Bs} ν(S_d) dμ₁`
    have hR : ∫ ω in Prod.fst ⁻¹' Bs, S.indicator (fun _ => (1 : ℝ)) ω ∂μ =
        μ.real (S ∩ Prod.fst ⁻¹' Bs) := by
      rw [integral_indicator_const _ hS, measureReal_restrict_apply hS, smul_eq_mul, mul_one]
    have hmeasS : MeasurableSet (S ∩ Prod.fst ⁻¹' Bs) := hS.inter (measurable_fst hBs)
    have hslice : ∀ d, ν (Prod.mk d ⁻¹' (S ∩ Prod.fst ⁻¹' Bs)) =
        Bs.indicator (fun d => ν (Prod.mk d ⁻¹' S)) d := fun d => by
      by_cases hd : d ∈ Bs
      · have he : Prod.mk d ⁻¹' S ∩ Prod.mk d ⁻¹' (Prod.fst ⁻¹' Bs) = Prod.mk d ⁻¹' S := by
          ext y; simp [hd]
        rw [Set.preimage_inter, he, Set.indicator_of_mem hd]
      · have he : Prod.mk d ⁻¹' S ∩ Prod.mk d ⁻¹' (Prod.fst ⁻¹' Bs) = ∅ := by
          ext y; simp [hd]
        rw [Set.preimage_inter, he, measure_empty, Set.indicator_of_notMem hd]
    have hμS : μ (S ∩ Prod.fst ⁻¹' Bs) = ∫⁻ d, Bs.indicator (fun d => ν (Prod.mk d ⁻¹' S)) d ∂μ₁ := by
      rw [hμ, Measure.prod_apply hmeasS]
      exact lintegral_congr fun d => hslice d
    rw [hL, hR, measureReal_def, hμS]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun d => ?_)
      ((hh₁m.indicator hBs).aestronglyMeasurable)]
    · congr 1
      refine lintegral_congr fun d => ?_
      by_cases hd : d ∈ Bs
      · simp [hd, hh₁, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      · simp [hd]
    · by_cases hd : d ∈ Bs
      · simp [hd, hh₁, measureReal_nonneg]
      · simp [hd]
  filter_upwards [hEq] with ω hω
  rw [← hω]
  exact h ω.1


/-- Section of a jointly measurable fold-one rule at a fixed fold-one outcome. -/
lemma measurable_section {Ω₁ β : Type*} [MeasurableSpace Ω₁] [MeasurableSpace β] {h : Ω₁ → β → ℝ}
    (hh : Measurable fun p : Ω₁ × β => h p.1 p.2) (d : Ω₁) : Measurable (h d) :=
  hh.comp (measurable_const.prodMk measurable_id)

/-- The rule at a fixed fold-one outcome is a predictable betting rule. -/
lemma isBetRule_section {Ω₁ : Type*} [MeasurableSpace Ω₁] {α c : ℝ}
    {lam : Ω₁ → (k : ℕ) → (Fin k → ℝ) → ℝ}
    (hlam : ∀ k < N, Measurable (fun p : Ω₁ × (Fin k → ℝ) => lam p.1 k p.2) ∧
      ∀ d z, 0 ≤ lam d k z ∧ lam d k z ≤ c / (1 + α)) (d : Ω₁) : IsBetRule N α c (lam d) :=
  fun k hk => ⟨measurable_section (h := fun d' z => lam d' k z) (hlam k hk).1 d, fun z => (hlam k hk).2 d z⟩

/-- Theorem 1, fold one fixed. -/
theorem thm1_cond_route : Claims.thm1_cond := by
  intro 𝒳 _ P Q _ _ n m N A B α δ c g lam hAB hα hδ0 _ _ hc1 hg hg01 hlam hTV
  exact bet_level P Q hg hg01 hAB hα hδ0 hc1 hlam ((delta_le_tv P Q hg hg01).trans hTV)

/-- Theorem 1, the conditional form `P(· | D_1) ≤ δ` a.s. -/
theorem thm1_condexp_route : Claims.thm1_condexp := by
  intro 𝒳 Ω₁ _ _ P Q _ _ μ₁ _ n m N A B α δ c g lam hAB hα hδ0 _ _ hc1 hg hg01 hlam hTV
  have hS := measurableSet_betReject hg (fun k hk => (hlam k hk).1) A B α δ
  refine ⟨hS, condExp_indicator_le_of_slices μ₁ _ hS fun d => ?_⟩
  have hgd := measurable_section hg d
  have h := bet_level P Q hgd (hg01 d) hAB hα hδ0 hc1 (isBetRule_section hlam d)
    ((delta_le_tv P Q hgd (hg01 d)).trans hTV)
  exact ENNReal.toReal_le_of_le_ofReal hδ0.le h

/-- Theorem 1, unconditional: `sup_{H_{0,α}} P(reject) ≤ δ`. -/
theorem thm1_route : Claims.thm1 := by
  intro 𝒳 Ω₁ _ _ P Q _ _ μ₁ _ n m N A B α δ c g lam hAB hα hδ0 _ _ hc1 hg hg01 hlam hTV
  have hS := measurableSet_betReject hg (fun k hk => (hlam k hk).1) A B α δ
  refine prod_le_of_slices μ₁ _ hS fun d => ?_
  have hgd := measurable_section hg d
  exact bet_level P Q hgd (hg01 d) hAB hα hδ0 hc1 (isBetRule_section hlam d)
    ((delta_le_tv P Q hgd (hg01 d)).trans hTV)

end StatFormal.Wave30tq
