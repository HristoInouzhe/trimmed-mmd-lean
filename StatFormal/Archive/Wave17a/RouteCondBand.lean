import StatFormal.Archive.Wave17a.Statements

/-!
# Route: otfd C `prop:conditional-pop-content`, `prop:net-inner-band` (untrusted)

* Content: every point `y` of the support of `ν = Q#(μ_K|_A)` satisfies `⟨v,y⟩ ≤ h^pop(v)` for **all** `v` at once
  (an open half-space beyond the essential supremum is `ν`-null); `ν` is carried by its support, so
  `P_{K,x}(band) ≥ ν(supp ν) = μ_K(A) ≥ p`. The band is closed.
* Net band: Step 1 maximises `⟨v,Q⟩` on the compact `A`, pushes the maximiser along `v` to the last point of `A`
  (a frontier point) and uses the two subgradient inequalities; Steps 2–4 as in the paper.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.Wave17a

variable {K : ℕ}


/-! ### Content -/

lemma le_hPop_of_mem_support {μ : Measure (EuclideanSpace ℝ (Fin K))} {A : Set (EuclideanSpace ℝ (Fin K))} {Q : (EuclideanSpace ℝ (Fin K)) → (EuclideanSpace ℝ (Fin K))} (hQ : Measurable Q) {y : (EuclideanSpace ℝ (Fin K))}
    (hy : y ∈ ((μ.restrict A).map Q).support) (v : (EuclideanSpace ℝ (Fin K))) : ((⟪v, y⟫ : ℝ) : EReal) ≤ hPop μ A Q v := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hae : ∀ᵐ u ∂μ.restrict A, ((⟪v, Q u⟫ : ℝ) : EReal) < c := ae_lt_of_essSup_lt hc1
  set U : Set (EuclideanSpace ℝ (Fin K)) := {w | c < ⟪v, w⟫}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hpos := (Measure.mem_support_iff_forall y).1 hy U (hU.mem_nhds (EReal.coe_lt_coe_iff.1 hc2))
  rw [Measure.map_apply hQ hU.measurableSet] at hpos
  have : (μ.restrict A) (Q ⁻¹' U) = 0 := by
    rw [← compl_mem_ae_iff]
    filter_upwards [hae] with u hu
    simp only [mem_compl_iff, mem_preimage, mem_setOf_eq, U, not_lt]
    exact (EReal.coe_lt_coe_iff.1 hu).le
  exact hpos.ne' this

lemma isClosed_popBand {T : Type*} (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K))) (Q : (EuclideanSpace ℝ (Fin K)) → (EuclideanSpace ℝ (Fin K))) (m : T → ℝ) (e : T → (EuclideanSpace ℝ (Fin K))) :
    IsClosed {z | InPopBand μ A Q m e z} := by
  have : {z | InPopBand μ A Q m e z} = ⋂ t, ({z : (EuclideanSpace ℝ (Fin K)) | (m t : EReal) - hPop μ A Q (-e t) ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal)} ∩
      {z : (EuclideanSpace ℝ (Fin K)) | ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ (m t : EReal) + hPop μ A Q (e t)}) := by
    ext z; simp [InPopBand]
  rw [this]
  refine isClosed_iInter fun t => IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const
      (continuous_coe_real_ereal.comp (continuous_const.add (continuous_const.inner continuous_id)))
  · exact isClosed_le (continuous_coe_real_ereal.comp (continuous_const.add (continuous_const.inner continuous_id)))
      continuous_const

theorem conditional_pop_content : Claims.conditional_pop_content := by
  intro K T μ Px Q A p m e _ hQ hPx hA hp
  have hcl := isClosed_popBand μ A Q m e
  refine ⟨hcl.measurableSet, ?_⟩
  set ν := (μ.restrict A).map Q
  have hsub : ν.support ⊆ {z | InPopBand μ A Q m e z} := by
    intro y hy t
    have h1 := le_hPop_of_mem_support hQ hy (-e t)
    have h2 := le_hPop_of_mem_support hQ hy (e t)
    rw [inner_neg_left] at h1
    constructor
    · calc (m t : EReal) - hPop μ A Q (-e t) ≤ (m t : EReal) - ((-⟪e t, y⟫ : ℝ) : EReal) :=
            EReal.sub_le_sub le_rfl h1
        _ = ((m t + ⟪e t, y⟫ : ℝ) : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
    · rw [EReal.coe_add]; exact add_le_add_right h2 _
  have hmeasS : MeasurableSet ν.support := Measure.isClosed_support.measurableSet
  calc ENNReal.ofReal p ≤ μ A := hp
    _ = ν univ := by rw [Measure.map_apply hQ MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
    _ ≤ ν ν.support + ν ν.supportᶜ := measure_univ_le_add_compl _
    _ = ν ν.support := by rw [Measure.measure_compl_support, add_zero]
    _ ≤ ν {z | InPopBand μ A Q m e z} := measure_mono hsub
    _ = (μ.restrict A) (Q ⁻¹' {z | InPopBand μ A Q m e z}) := Measure.map_apply hQ hcl.measurableSet
    _ ≤ μ (Q ⁻¹' {z | InPopBand μ A Q m e z}) := Measure.restrict_apply_le _ _
    _ = Px {z | InPopBand μ A Q m e z} := by rw [← hPx, Measure.map_apply hQ hcl.measurableSet]

/-! ### Net band -/

section Net
variable {μ : Measure (EuclideanSpace ℝ (Fin K))} {A S O : Set (EuclideanSpace ℝ (Fin K))} {χ : (EuclideanSpace ℝ (Fin K)) → EReal} {Q Qb T : (EuclideanSpace ℝ (Fin K)) → (EuclideanSpace ℝ (Fin K))} {ω η h : ℝ} {N : Finset (EuclideanSpace ℝ (Fin K))}

lemma NetSetting.sub_AO (hs : NetSetting μ A S O χ Q Qb T ω η h N) : A ⊆ O := hs.subset_AS.trans hs.subset_SO

lemma NetSetting.contQ (hs : NetSetting μ A S O χ Q Qb T ω η h N) (v : (EuclideanSpace ℝ (Fin K))) :
    ContinuousOn (fun u => ⟪v, Q u⟫) A :=
  (continuous_const.inner continuous_id).comp_continuousOn (hs.cont_Q.mono hs.sub_AO)

lemma NetSetting.bddQ (hs : NetSetting μ A S O χ Q Qb T ω η h N) (v : (EuclideanSpace ℝ (Fin K))) :
    BddAbove ((fun u => ⟪v, Q u⟫) '' A) :=
  (hs.compact_A.image_of_continuousOn (hs.contQ v)).bddAbove

lemma NetSetting.le_supQ (hs : NetSetting μ A S O χ Q Qb T ω η h N) (v : (EuclideanSpace ℝ (Fin K))) {u : (EuclideanSpace ℝ (Fin K))} (hu : u ∈ A) :
    ⟪v, Q u⟫ ≤ supOn A Q v :=
  le_csSup (hs.bddQ v) ⟨u, hu, rfl⟩

lemma NetSetting.T_le (hs : NetSetting μ A S O χ Q Qb T ω η h N) (v : (EuclideanSpace ℝ (Fin K))) {u : (EuclideanSpace ℝ (Fin K))} (hu : u ∈ S) :
    ⟪v, T u⟫ ≤ ⟪v, Q u⟫ + ‖v‖ * η := by
  have h1 : ⟪v, T u⟫ - ⟪v, Q u⟫ ≤ ‖v‖ * η := by
    rw [← inner_sub_right]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hs.approx u hu) (norm_nonneg _))
  linarith

lemma NetSetting.le_T (hs : NetSetting μ A S O χ Q Qb T ω η h N) (v : (EuclideanSpace ℝ (Fin K))) {u : (EuclideanSpace ℝ (Fin K))} (hu : u ∈ S) :
    ⟪v, Q u⟫ - ‖v‖ * η ≤ ⟪v, T u⟫ := by
  have h1 : ⟪v, Q u⟫ - ⟪v, T u⟫ ≤ ‖v‖ * η := by
    rw [← inner_sub_right]
    refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_sub_rev]; exact hs.approx u hu
  linarith

lemma NetSetting.supT_le (hs : NetSetting μ A S O χ Q Qb T ω η h N) (hA : A.Nonempty) (v : (EuclideanSpace ℝ (Fin K))) :
    supOn A T v ≤ supOn A Q v + ‖v‖ * η := by
  refine csSup_le (hA.image _) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact (hs.T_le v (hs.subset_AS hu)).trans (by linarith [hs.le_supQ v hu])

lemma NetSetting.bddT (hs : NetSetting μ A S O χ Q Qb T ω η h N) (v : (EuclideanSpace ℝ (Fin K))) :
    BddAbove ((fun u => ⟪v, T u⟫) '' A) :=
  ⟨supOn A Q v + ‖v‖ * η, by
    rintro _ ⟨u, hu, rfl⟩
    exact (hs.T_le v (hs.subset_AS hu)).trans (by linarith [hs.le_supQ v hu])⟩

lemma NetSetting.omega_nonneg (hs : NetSetting μ A S O χ Q Qb T ω η h N) {u : (EuclideanSpace ℝ (Fin K))} (hu : u ∈ S) : 0 ≤ ω := by
  have := hs.modulus u hu u hu (by simp [hs.nonneg_h])
  simpa using this

lemma NetSetting.eta_nonneg (hs : NetSetting μ A S O χ Q Qb T ω η h N) {u : (EuclideanSpace ℝ (Fin K))} (hu : u ∈ S) : 0 ≤ η :=
  (norm_nonneg _).trans (hs.approx u hu)

/-- Step 1. -/
lemma NetSetting.attained (hs : NetSetting μ A S O χ Q Qb T ω η h N) (hA : A.Nonempty) {v : (EuclideanSpace ℝ (Fin K))} (hv : v ≠ 0) :
    ∃ u ∈ A ∩ frontier A, ⟪v, Q u⟫ = supOn A Q v := by
  obtain ⟨u₀, hu₀, hmax⟩ := hs.compact_A.exists_isMaxOn hA (hs.contQ v)
  have hM : ⟪v, Q u₀⟫ = supOn A Q v :=
    le_antisymm (hs.le_supQ v hu₀) (csSup_le (hA.image _) (by rintro _ ⟨u, hu, rfl⟩; exact hmax hu))
  set Ts : Set ℝ := {t | 0 ≤ t ∧ u₀ + t • v ∈ A}
  have hAc := hs.compact_A
  have hTs_closed : IsClosed Ts :=
    isClosed_Ici.inter (hAc.isClosed.preimage (continuous_const.add (continuous_id.smul continuous_const)))
  obtain ⟨R, hR⟩ := hAc.isBounded.subset_closedBall 0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hTs_bdd : Bornology.IsBounded Ts := by
    refine (Metric.isBounded_Icc (0 : ℝ) ((R + ‖u₀‖) / ‖v‖)).subset ?_
    rintro t ⟨ht0, htA⟩
    refine ⟨ht0, ?_⟩
    rw [le_div_iff₀ hvpos]
    have h1 : ‖u₀ + t • v‖ ≤ R := by simpa using hR htA
    have h2 : ‖t • v‖ ≤ ‖u₀ + t • v‖ + ‖u₀‖ := by
      calc ‖t • v‖ = ‖(u₀ + t • v) - u₀‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg ht0] at h2
    linarith
  obtain ⟨t₁, ⟨ht₁0, ht₁A⟩, ht₁max⟩ :=
    (Metric.isCompact_of_isClosed_isBounded hTs_closed hTs_bdd).exists_isGreatest ⟨0, le_rfl, by simpa using hu₀⟩
  set u₁ := u₀ + t₁ • v
  have hfr : u₁ ∈ frontier A := by
    refine ⟨subset_closure ht₁A, fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    set s := ε / (2 * ‖v‖)
    have hs0 : 0 < s := div_pos hε (by positivity)
    have hmem : u₁ + s • v ∈ A := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
      have : s * ‖v‖ = ε / 2 := by simp only [s]; field_simp
      linarith
    have : t₁ + s ∈ Ts := ⟨by linarith, by simpa [u₁, add_smul, add_assoc] using hmem⟩
    linarith [ht₁max this]
  refine ⟨u₁, ⟨ht₁A, hfr⟩, le_antisymm (hs.le_supQ v ht₁A) ?_⟩
  rw [← hM]
  -- the two subgradient inequalities
  have g₀ := hs.subgrad u₀ (hs.sub_AO hu₀)
  have g₁ := hs.subgrad u₁ (hs.sub_AO ht₁A)
  simp only [TauCeti.mem_subdifferential_iff, innerₗ_apply_apply] at g₀ g₁
  obtain ⟨b₀, t₀', g₀⟩ := g₀
  obtain ⟨b₁, t₁', g₁⟩ := g₁
  have e₀ := g₀ u₁
  have e₁ := g₁ u₀
  rw [← EReal.coe_toReal t₀' b₀, ← EReal.coe_toReal t₁' b₁] at e₀ e₁
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at e₀ e₁
  have hsum : ⟪u₁ - u₀, Q u₀⟫ + ⟪u₀ - u₁, Q u₁⟫ ≤ 0 := by linarith
  have hd : u₁ - u₀ = t₁ • v := by simp [u₁]
  have hd' : u₀ - u₁ = -(t₁ • v) := by rw [← hd, neg_sub]
  rw [hd, hd', inner_neg_left, real_inner_smul_left, real_inner_smul_left] at hsum
  rcases ht₁0.lt_or_eq with hpos | hzero
  · by_contra hcon
    push Not at hcon
    have := mul_pos hpos (sub_pos.2 hcon)
    linarith
  · simp [u₁, ← hzero]

lemma NetSetting.netMax_le (hs : NetSetting μ A S O χ Q Qb T ω η h N) (hN : N.Nonempty) (v : (EuclideanSpace ℝ (Fin K))) :
    netMax N hN T v ≤ supOn A T v :=
  Finset.sup'_le hN _ fun u hu => le_csSup (hs.bddT v) ⟨u, hs.net_sub hu, rfl⟩

lemma NetSetting.hPop_le (hs : NetSetting μ A S O χ Q Qb T ω η h N) (v : (EuclideanSpace ℝ (Fin K))) :
    hPop μ A Qb v ≤ (supOn A Q v : EReal) := by
  refine essSup_le_of_ae_le _ ?_
  have hAm : MeasurableSet A := hs.compact_A.isClosed.measurableSet
  filter_upwards [ae_restrict_mem hAm, ae_restrict_of_ae hs.version] with u hu hver
  rw [hver (hs.sub_AO hu)]
  exact EReal.coe_le_coe_iff.2 (hs.le_supQ v hu)

lemma NetSetting.lower (hs : NetSetting μ A S O χ Q Qb T ω η h N) (hN : N.Nonempty) (v : (EuclideanSpace ℝ (Fin K))) :
    supOn A Q v - ‖v‖ * (ω + η) ≤ netMax N hN T v := by
  obtain ⟨w₀, hw₀⟩ := hN
  have hA : A.Nonempty := ⟨w₀, hs.net_sub hw₀⟩
  by_cases hv : v = 0
  · subst hv
    have h1 : supOn A Q 0 = 0 := by
      simp only [supOn, inner_zero_left]
      rw [hA.image_const]; exact csSup_singleton 0
    have h2 : netMax N ⟨w₀, hw₀⟩ T 0 = 0 := by simp only [netMax, inner_zero_left]; exact Finset.sup'_const _ _
    simp [h1, h2]
  obtain ⟨u, ⟨huA, hufr⟩, hu⟩ := hs.attained hA hv
  obtain ⟨w, hwN, hw⟩ := hs.net_cover u hufr
  have hwS := hs.subset_AS (hs.net_sub hwN)
  have huS := hs.subset_AS huA
  have h1 := hs.le_T v hwS
  have h2 : ⟪v, Q u⟫ - ⟪v, Q w⟫ ≤ ‖v‖ * ω := by
    rw [← inner_sub_right]
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hs.modulus u huS w hwS hw) (norm_nonneg _))
  have h3 : ⟪v, T w⟫ ≤ netMax N ⟨w₀, hw₀⟩ T v := Finset.le_sup' (fun u => ⟪v, T u⟫) hwN
  rw [← hu]
  nlinarith

lemma NetSetting.hPop_eq (hs : NetSetting μ A S O χ Q Qb T ω η h N) (hsupp : (μ.restrict A).support = A)
    (hA : A.Nonempty) (v : (EuclideanSpace ℝ (Fin K))) : hPop μ A Qb v = (supOn A Q v : EReal) := by
  refine le_antisymm (hs.hPop_le v) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hc2' : c < supOn A Q v := EReal.coe_lt_coe_iff.1 hc2
  obtain ⟨u₀, hu₀, hmax⟩ := hs.compact_A.exists_isMaxOn hA (hs.contQ v)
  have hM : ⟪v, Q u₀⟫ = supOn A Q v :=
    le_antisymm (hs.le_supQ v hu₀) (csSup_le (hA.image _) (by rintro _ ⟨u, hu, rfl⟩; exact hmax hu))
  have hcont : ContinuousAt (fun u => ⟪v, Q u⟫) u₀ :=
    (continuous_const.inner continuous_id).continuousAt.comp
      (hs.cont_Q.continuousAt (hs.isOpen_O.mem_nhds (hs.sub_AO hu₀)))
  have hev : ∀ᶠ u in 𝓝 u₀, c < ⟪v, Q u⟫ := hcont.eventually (lt_mem_nhds (by show c < ⟪v, Q u₀⟫; rw [hM]; exact hc2'))
  have hpos := (Measure.mem_support_iff_forall u₀).1 (hsupp.symm ▸ hu₀) _ hev
  have hae : ∀ᵐ u ∂μ.restrict A, ((⟪v, Qb u⟫ : ℝ) : EReal) < c := ae_lt_of_essSup_lt hc1
  have hAm : MeasurableSet A := hs.compact_A.isClosed.measurableSet
  have hzero : (μ.restrict A) {u | c < ⟪v, Q u⟫} = 0 := by
    rw [← compl_mem_ae_iff]
    filter_upwards [hae, ae_restrict_mem hAm, ae_restrict_of_ae hs.version] with u hu huA hver
    simp only [mem_compl_iff, mem_setOf_eq, not_lt]
    rw [← hver (hs.sub_AO huA)]
    exact (EReal.coe_lt_coe_iff.1 hu).le
  exact hpos.ne' hzero

end Net

theorem net_inner_band_attained : Claims.net_inner_band_attained := by
  intro K μ A S O χ Q Qb T ω η h N v hs hA hv
  obtain ⟨u, hu, hval⟩ := hs.attained hA hv
  exact ⟨u, hu, hval, fun u' hu' => hs.le_supQ v hu'⟩

theorem net_inner_band_i : Claims.net_inner_band_i := by
  intro K μ A S O χ Q Qb T ω η h N hN v hs
  obtain ⟨w, hw⟩ := hN
  exact ⟨hs.netMax_le _ v, hs.supT_le ⟨w, hs.net_sub hw⟩ v⟩

theorem net_inner_band_ii : Claims.net_inner_band_ii := by
  intro K μ A S O χ Q Qb T ω η h N hN v hs
  exact ⟨hs.lower hN v, hs.hPop_le v⟩

theorem net_inner_band_iii : Claims.net_inner_band_iii := by
  intro K μ A S O χ Q Qb T ω η h N hN v hs
  obtain ⟨w, hw⟩ := hN
  have h1 := hs.netMax_le ⟨w, hw⟩ v
  have h2 := hs.supT_le ⟨w, hs.net_sub hw⟩ v
  have h3 := hs.lower ⟨w, hw⟩ v
  constructor <;> nlinarith

theorem net_inner_band_iv : Claims.net_inner_band_iv := by
  intro K μ A S O χ Q Qb T ω η h N hN v hs hsupp
  obtain ⟨w, hw⟩ := hN
  have hA : A.Nonempty := ⟨w, hs.net_sub hw⟩
  have hS := hs.subset_AS (hs.net_sub hw)
  have h1 := hs.netMax_le ⟨w, hw⟩ v
  have h2 := hs.supT_le hA v
  have h3 := hs.lower ⟨w, hw⟩ v
  have hω := hs.omega_nonneg hS
  have hvω : 0 ≤ ‖v‖ * ω := mul_nonneg (norm_nonneg _) hω
  refine ⟨hs.hPop_eq hsupp hA v, abs_le.2 ⟨by linarith, by nlinarith⟩⟩

theorem net_inner_band_edges : Claims.net_inner_band_edges := by
  intro K μ A S O χ Q Qb T ω η h N hN 𝒯 m e Eb hs hE
  obtain ⟨w, hw⟩ := hN
  have hA : A.Nonempty := ⟨w, hs.net_sub hw⟩
  have hS := hs.subset_AS (hs.net_sub hw)
  have hωη : 0 ≤ ω + η := add_nonneg (hs.omega_nonneg hS) (hs.eta_nonneg hS)
  have hb : ∀ t, ‖e t‖ * (ω + η) ≤ Eb * (ω + η) := fun t => mul_le_mul_of_nonneg_right (hE t) hωη
  have hb' : ∀ t, ‖-e t‖ * (ω + η) ≤ Eb * (ω + η) := fun t => by rw [norm_neg]; exact hb t
  refine ⟨fun t => ⟨by linarith [hs.netMax_le ⟨w, hw⟩ (e t)], by linarith [hs.netMax_le ⟨w, hw⟩ (-e t)]⟩,
    fun t => ⟨?_, ?_⟩, fun hsupp t => ⟨?_, ?_, hs.hPop_eq hsupp hA _, hs.hPop_eq hsupp hA _⟩⟩
  · have h1 := hs.hPop_le (e t)
    have h2 := hs.lower ⟨w, hw⟩ (e t)
    have h3 : (supOn A Q (e t) : EReal) ≤ ((netMax N ⟨w, hw⟩ T (e t) + Eb * (ω + η) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 (by linarith [hb t])
    calc (m t : EReal) + hPop μ A Qb (e t) ≤ (m t : EReal) + ((netMax N ⟨w, hw⟩ T (e t) + Eb * (ω + η) : ℝ) : EReal) :=
          add_le_add_right (h1.trans h3) _
      _ = _ := by rw [← EReal.coe_add]; congr 1; ring
  · have h1 := hs.hPop_le (-e t)
    have h2 := hs.lower ⟨w, hw⟩ (-e t)
    have h3 : (supOn A Q (-e t) : EReal) ≤ ((netMax N ⟨w, hw⟩ T (-e t) + Eb * (ω + η) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 (by linarith [hb' t])
    calc ((m t - netMax N ⟨w, hw⟩ T (-e t) - Eb * (ω + η) : ℝ) : EReal)
        = (m t : EReal) - ((netMax N ⟨w, hw⟩ T (-e t) + Eb * (ω + η) : ℝ) : EReal) := by
          rw [← EReal.coe_sub]; congr 1; ring
      _ ≤ (m t : EReal) - hPop μ A Qb (-e t) := EReal.sub_le_sub le_rfl (h1.trans h3)
  · have h1 := hs.netMax_le ⟨w, hw⟩ (e t)
    have h2 := hs.supT_le hA (e t)
    have h3 := hs.lower ⟨w, hw⟩ (e t)
    have hη := hs.eta_nonneg hS
    have hω := hs.omega_nonneg hS
    have : ‖e t‖ * η ≤ ‖e t‖ * (ω + η) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    rw [abs_le]; constructor <;> linarith [hb t]
  · have h1 := hs.netMax_le ⟨w, hw⟩ (-e t)
    have h2 := hs.supT_le hA (-e t)
    have h3 := hs.lower ⟨w, hw⟩ (-e t)
    have hη := hs.eta_nonneg hS
    have hω := hs.omega_nonneg hS
    have : ‖-e t‖ * η ≤ ‖-e t‖ * (ω + η) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    rw [abs_le]; constructor <;> linarith [hb' t]

end StatFormal.Wave17a
