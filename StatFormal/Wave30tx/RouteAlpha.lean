import StatFormal.Wave30tx.RouteBasic
import StatFormal.Archive.Wave11b.RouteAttain
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs
import StatFormal.Wave30tu.RouteConsistency

/-!
# Route: `prop:alphahat (v2)` (untrusted proof material)

Given `lem:contact (v2)` (the frozen `Claims.contact`, as a hypothesis):
* on the product `E` of the two `cor:uniform` events at level `δ'`, for every level `a ≤ α*` and every minimiser `(w,v)` of
  `eq:qp`, `â = Σ w_iφ(X_i)` is within `r_n(a,δ') ≤ r_n(α*,δ')` of `𝒞_a(P) ⊆ 𝒞_{α*}(P)`; its nearest point `a'` (closed convex
  region, Hilbert projection) is within `r_n + D̂_a + r_m` of `𝒞_{α*}(Q)`, so `‖a' − μ_{R*}‖ ≤ ω_c(D̂_a + r_n + r_m)`;
* `α̂`: `Wave30tu.consistency_i` (probability), `Wave30tu.crossing` (`D̂_{α̂} ≤ τ(α̂+)`), `Wave30tu.tauRight_spec` at `α̂ = α*`,
  `Wave30tu.crossing_meas` (measurability);
* the schedule: `δ' = δ_i`, `Wave30tu.tau_sched`, `r_n ≤ τ_{n,m}` and the monotonicity of `ω_c` below `ε₀`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace Pointwise

namespace StatFormal.Wave30tx.RAlpha

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.TrimmedMMD.ZeroSet StatFormal.Distances

section Helpers

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem contactLaw_comm (P Q : Measure 𝒳) :
    StatFormal.Wave30tx.contactLaw Q P = StatFormal.Wave30tx.contactLaw P Q := by
  simp only [StatFormal.Wave30tx.contactLaw, tvDist_comm Q P, inf_comm]

theorem region_mono {φ : 𝒳 → H} {P : Measure 𝒳} {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    region φ a P ⊆ region φ b P := by
  rintro z ⟨g, hg, hgb, hg1, rfl⟩
  refine ⟨g, hg, fun x => ⟨(hgb x).1, (hgb x).2.trans ?_⟩, hg1, rfl⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem rn_mono_alpha {κ a b δ : ℝ} (hκ : 0 ≤ κ) (hab : a ≤ b) (hb : b < 1) (n : ℕ) :
    rn κ a δ n ≤ rn κ b δ n := by
  unfold rn
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact div_le_div_of_nonneg_left hκ (by linarith) (by linarith)

theorem rn_le_tau {κ α d : ℝ} (hκ : 0 ≤ κ) (hα : α < 1) (hd : 0 < d) (n m : ℕ) :
    rn κ α d n ≤ tau κ α d n m := by
  unfold tau
  have h1 : rn κ α d n ≤ rn κ α (d / 2) n := by
    unfold rn
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.sqrt_le_sqrt ?_))
      (div_nonneg hκ (by linarith))
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (by norm_num)
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (by norm_num) hd.le
  have h2 : 0 ≤ rn κ α (d / 2) m := by unfold rn; have : 0 < 1 - α := by linarith
                                       positivity
  linarith

theorem rn_le_tau_right {κ α d : ℝ} (hκ : 0 ≤ κ) (hα : α < 1) (hd : 0 < d) (n m : ℕ) :
    rn κ α d m ≤ tau κ α d n m := by
  have h := rn_le_tau (m := n) hκ hα hd m
  unfold tau at h ⊢
  linarith

theorem integral_wEmp [CompleteSpace H] {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (x : Fin n → 𝒳) :
    ∫ y, φ y ∂(StatFormal.Wave30tx.wEmp w x) = ∑ i, w i • φ (x i) := by
  unfold StatFormal.Wave30tx.wEmp
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac' _ _ hφ, ENNReal.toReal_ofReal (hw i)]
  · intro i _
    exact (Integrable.of_bound hφ.aestronglyMeasurable κ (ae_of_all _ hκ)).smul_measure ENNReal.ofReal_ne_top

theorem ofReal_le_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (_hS : MeasurableSet S) (hT : MeasurableSet T) {a b : ℝ}
    (ha : ENNReal.ofReal a ≤ μ S) (hb : ENNReal.ofReal b ≤ μ T) : ENNReal.ofReal (a + b - 1) ≤ μ (S ∩ T) := by
  have ha' : a ≤ μ.real S := by
    by_cases h : a ≤ 0
    · exact h.trans measureReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 ha
  have hb' : b ≤ μ.real T := by
    by_cases h : b ≤ 0
    · exact h.trans measureReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hb
  have hu := measureReal_union_add_inter (μ := μ) (s := S) hT
  have h1 : μ.real (S ∪ T) ≤ 1 := measureReal_le_one
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  change a + b - 1 ≤ μ.real (S ∩ T)
  linarith

end Helpers

section Main

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Bounded above: the set defining `ω_c`. -/
theorem bdd_omega (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (htv : tvDist P Q < 1) (ε : ℝ) :
    BddAbove {r | ∃ a ∈ region φ (tvDist P Q) P,
      Metric.infDist a (region φ (tvDist P Q) Q) ≤ ε ∧ r = ‖a - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖} := by
  refine ⟨κ + ‖∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖, ?_⟩
  rintro r ⟨a, ha, -, rfl⟩
  have := StatFormal.Wave11b.attain_bounded 𝒳 H P φ κ (tvDist P Q) hφ hκ (tvDist_nonneg P Q) htv a ha
  exact (norm_sub_le _ _).trans (by linarith)

theorem le_omegaC (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (htv : tvDist P Q < 1) {a : H}
    (ha : a ∈ region φ (tvDist P Q) P) {ε : ℝ} (hd : Metric.infDist a (region φ (tvDist P Q) Q) ≤ ε) :
    ‖a - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤ StatFormal.Wave30tx.omegaC φ P Q ε :=
  le_csSup (bdd_omega P Q hφ hκ htv ε) ⟨a, ha, hd, rfl⟩

theorem omegaC_mono (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (htv : tvDist P Q < 1) {ε ε' : ℝ} (h : ε ≤ ε') :
    StatFormal.Wave30tx.omegaC φ P Q ε ≤ StatFormal.Wave30tx.omegaC φ P Q ε' := by
  refine Real.sSup_le ?_ (Real.sSup_nonneg fun r ⟨a, _, _, hr⟩ => hr ▸ norm_nonneg _)
  rintro r ⟨a, ha, hd, rfl⟩
  exact le_omegaC P Q hφ hκ htv ha (hd.trans h)

/-- A nearest point in a region. -/
theorem exists_near (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ α : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (u : H) :
    ∃ v ∈ region φ α P, ‖u - v‖ = Metric.infDist u (region φ α P) := by
  have hne : (region φ α P).Nonempty := ⟨_, StatFormal.Wave30tl.one_mem_region P φ hα0 hα1⟩
  obtain ⟨v, hv, hvn⟩ := exists_norm_eq_iInf_of_complete_convex hne
    (StatFormal.Wave11b.attain_closed 𝒳 H P φ κ α hφ hκ hα0 hα1).isComplete
    (StatFormal.Wave11b.attain_convex 𝒳 H P φ κ α hφ hκ hα0 hα1) u
  refine ⟨v, hv, ?_⟩
  rw [hvn, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]

/-- On the `cor:uniform` event, the empirical point is within `r_n(α,δ')` of the population region. -/
theorem infDist_le_rn (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ α δ' : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ} (hn : 1 ≤ n)
    (x : Fin n → 𝒳) (hx : Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤ rn κ α δ' n)
    {w : Fin n → ℝ} (hw : w ∈ capped n α) :
    Metric.infDist (∑ i, w i • φ (x i)) (region φ α P) ≤ rn κ α δ' n := by
  have := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hn) x
  have hmem : ∑ i, w i • φ (x i) ∈ region φ α (empirical x) := by
    rw [StatFormal.Wave8a.georep_empirical 𝒳 H φ α n x hφ hα0 hα1 (by omega)]
    exact ⟨w, hw, rfl⟩
  have hb : ∀ (R : Measure 𝒳) [IsProbabilityMeasure R], Bornology.IsBounded (region φ α R) := by
    intro R _
    exact (Metric.isBounded_iff_subset_closedBall 0).2 ⟨κ, fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact StatFormal.Wave11b.attain_bounded 𝒳 H R φ κ α hφ hκ hα0 hα1 z hz⟩
  have hfin := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    ⟨_, StatFormal.Wave30tl.one_mem_region (empirical x) φ hα0 hα1⟩
    ⟨_, StatFormal.Wave30tl.one_mem_region P φ hα0 hα1⟩ (hb (empirical x)) (hb P)
  exact (Metric.infDist_le_hausdorffDist_of_mem hmem hfin).trans hx

/-- The deterministic bound on the `cor:uniform` events, at every level `a ∈ [0, α*]`. -/
theorem bound_on_event (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ δ' : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (htv : tvDist P Q < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳))
    (hzx : ∀ α ∈ Ico (0 : ℝ) 1, Metric.hausdorffDist (region φ α (empirical z.1)) (region φ α P) ≤ rn κ α δ' n)
    (hzy : ∀ α ∈ Ico (0 : ℝ) 1, Metric.hausdorffDist (region φ α (empirical z.2)) (region φ α Q) ≤ rn κ α δ' m)
    {a : ℝ} (ha : a ∈ Icc 0 (tvDist P Q)) {pr : (Fin n → ℝ) × (Fin m → ℝ)} (hpr : pr ∈ capped n a ×ˢ capped m a)
    (hmin : IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n a ×ˢ capped m a) pr) :
    ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.1 z.1) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤
        rn κ (tvDist P Q) δ' n + StatFormal.Wave30tx.omegaC φ P Q
          (Demp φ z.1 z.2 a + rn κ (tvDist P Q) δ' n + rn κ (tvDist P Q) δ' m) ∧
      ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.2 z.2) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤
        rn κ (tvDist P Q) δ' m + StatFormal.Wave30tx.omegaC φ Q P
          (Demp φ z.1 z.2 a + rn κ (tvDist P Q) δ' n + rn κ (tvDist P Q) δ' m) := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := StatFormal.Wave30tl.kappa_nonneg_of hκ x₀
  set T := tvDist P Q with hT
  have ha1 : a < 1 := lt_of_le_of_lt ha.2 htv
  have htv' : tvDist Q P < 1 := by rwa [tvDist_comm]
  set rN := rn κ T δ' n
  set rM := rn κ T δ' m
  set ah := ∑ i, pr.1 i • φ (z.1 i) with hah
  set bh := ∑ j, pr.2 j • φ (z.2 j) with hbh
  have hA : ∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.1 z.1) = ah :=
    integral_wEmp hφ hκ pr.1 (fun i => (hpr.1.1 i).1) z.1
  have hB : ∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.2 z.2) = bh :=
    integral_wEmp hφ hκ pr.2 (fun j => (hpr.2.1 j).1) z.2
  have hdX : Metric.infDist ah (region φ a P) ≤ rN :=
    (infDist_le_rn P hφ hκ ha.1 ha1 hn z.1 (hzx a ⟨ha.1, ha1⟩) hpr.1).trans (rn_mono_alpha hκ0 ha.2 htv n)
  have hdY : Metric.infDist bh (region φ a Q) ≤ rM :=
    (infDist_le_rn Q hφ hκ ha.1 ha1 hm z.2 (hzy a ⟨ha.1, ha1⟩) hpr.2).trans (rn_mono_alpha hκ0 ha.2 htv m)
  obtain ⟨a', ha', ha'd⟩ := exists_near P hφ hκ ha.1 ha1 ah
  obtain ⟨b', hb', hb'd⟩ := exists_near Q hφ hκ ha.1 ha1 bh
  have ha'T : a' ∈ region φ T P := region_mono ha.2 htv ha'
  have hb'T : b' ∈ region φ T Q := region_mono ha.2 htv hb'
  have hD : Demp φ z.1 z.2 a = ‖ah - bh‖ :=
    StatFormal.Wave30tx.RBasic.Demp_eq_norm hφ ha.1 ha1 hn hm z.1 z.2 hpr hmin
  have hab : ‖a' - b'‖ ≤ Demp φ z.1 z.2 a + rN + rM := by
    have e : a' - b' = (a' - ah) + (ah - bh) + (bh - b') := by abel
    rw [e, hD]
    have h3 := norm_add₃_le (a := a' - ah) (b := ah - bh) (c := bh - b')
    have h4 : ‖a' - ah‖ = ‖ah - a'‖ := norm_sub_rev _ _
    linarith
  refine ⟨?_, ?_⟩
  · have h1 : Metric.infDist a' (region φ T Q) ≤ Demp φ z.1 z.2 a + rN + rM :=
      (Metric.infDist_le_dist_of_mem hb'T).trans (by rw [dist_eq_norm]; exact hab)
    have h2 := le_omegaC P Q hφ hκ htv ha'T h1
    rw [hA]
    calc ‖ah - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖
        ≤ ‖ah - a'‖ + ‖a' - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ rN + StatFormal.Wave30tx.omegaC φ P Q (Demp φ z.1 z.2 a + rN + rM) := add_le_add (by linarith) h2
  · have hb'T' : b' ∈ region φ (tvDist Q P) Q := by rw [tvDist_comm]; exact hb'T
    have ha'T' : a' ∈ region φ (tvDist Q P) P := by rw [tvDist_comm]; exact ha'T
    have h1 : Metric.infDist b' (region φ (tvDist Q P) P) ≤ Demp φ z.1 z.2 a + rN + rM :=
      (Metric.infDist_le_dist_of_mem ha'T').trans (by rw [dist_eq_norm, norm_sub_rev]; exact hab)
    have h2 := le_omegaC Q P hφ hκ htv' hb'T' h1
    rw [contactLaw_comm] at h2
    rw [hB]
    calc ‖bh - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖
        ≤ ‖bh - b'‖ + ‖b' - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ rM + StatFormal.Wave30tx.omegaC φ Q P (Demp φ z.1 z.2 a + rN + rM) := add_le_add (by linarith) h2

end Main

theorem alphahat_of (hc : StatFormal.Wave30tx.Claims.contact) : StatFormal.Wave30tx.Claims.alphahat := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ δ' τ n m hφ hκ hchar htv0 htv1 hδ0 hδ1 hδ'0 hδ'1 hn hm hvalid hcont hne
  intro αs rN rM Bound
  obtain ⟨-, -, -, -, -, hω⟩ := hc 𝒳 H P Q φ κ hφ hκ hchar htv1
  refine ⟨hω, ?_⟩
  obtain ⟨EX, hEXm, hEXp, hEX⟩ :=
    StatFormal.TrimmedMMD.Concentration.uniform_alpha 𝒳 H P φ κ δ' n hφ hκ hn hδ'0 hδ'1
  obtain ⟨EY, hEYm, hEYp, hEY⟩ :=
    StatFormal.TrimmedMMD.Concentration.uniform_alpha 𝒳 H Q φ κ δ' m hφ hκ hm hδ'0 hδ'1
  set E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := EX ×ˢ EY with hEdef
  have hEm : MeasurableSet E := hEXm.prod hEYm
  have hEp : ENNReal.ofReal (1 - 2 * δ') ≤ StatFormal.Wave30tp.sampleLaw P Q n m E := by
    rw [StatFormal.Wave30tp.sampleLaw, hEdef, Measure.prod_prod]
    have h1 : ENNReal.ofReal (1 - δ') ≤ (Measure.pi fun _ : Fin n => P) EX :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hEXp
    have h2 : ENNReal.ofReal (1 - δ') ≤ (Measure.pi fun _ : Fin m => Q) EY :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hEYp
    calc ENNReal.ofReal (1 - 2 * δ') ≤ ENNReal.ofReal ((1 - δ') * (1 - δ')) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal (1 - δ') * ENNReal.ofReal (1 - δ') := ENNReal.ofReal_mul (by linarith)
      _ ≤ _ := mul_le_mul' h1 h2
  have hEz : ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1,
      Metric.hausdorffDist (region φ α (empirical z.1)) (region φ α P) ≤ rn κ α δ' n ∧
        Metric.hausdorffDist (region φ α (empirical z.2)) (region φ α Q) ≤ rn κ α δ' m :=
    fun z hz α hα => ⟨hEX hz.1 α hα.1 hα.2, hEY hz.2 α hα.1 hα.2⟩
  have hBound : ∀ z ∈ E, ∀ a ∈ Icc (0 : ℝ) αs, Bound z a := by
    intro z hz a ha pr hpr hmin
    exact bound_on_event P Q hφ hκ htv1 hn hm z (fun α hα => (hEz z hz α hα).1) (fun α hα => (hEz z hz α hα).2)
      ha hpr hmin
  obtain ⟨E1, hE1m, hE1p, hE1⟩ :=
    StatFormal.Wave30tu.consistency_i 𝒳 H P Q φ κ δ τ n m hφ hκ htv1 hδ0 hδ1 hn hm hvalid
  have hmeas := (StatFormal.Wave30tu.crossing_meas 𝒳 H φ κ τ n m hφ hκ hn hm hvalid.1 hvalid.2.1 hcont hne).2
  have hAm : MeasurableSet {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) τ ≤ αs} :=
    measurableSet_le hmeas measurable_const
  refine ⟨E, hEm, hEp, hEz, hBound, hAm, ?_, ?_⟩
  · have : IsProbabilityMeasure (StatFormal.Wave30tp.sampleLaw P Q n m) := by
      unfold StatFormal.Wave30tp.sampleLaw; infer_instance
    have h := ofReal_le_inter (StatFormal.Wave30tp.sampleLaw P Q n m) hEm hE1m hEp hE1p
    rw [show 1 - 2 * δ' + (1 - δ) - 1 = 1 - δ - 2 * δ' by ring] at h
    exact h.trans (measure_mono (inter_subset_inter_right _ fun z hz => (hE1 hz).1))
  · rintro z ⟨hzE, hzA⟩
    have hah0 : 0 ≤ alphaHat (Demp φ z.1 z.2) τ := alphaHat_nonneg (hne z.1 z.2)
    refine ⟨?_, hBound z hzE _ ⟨hah0, hzA⟩⟩
    obtain ⟨-, -, hcr, -⟩ := StatFormal.Wave30tu.crossing 𝒳 H φ κ τ n m hφ hκ hn hm hvalid.1 hvalid.2.1 hcont
      z.1 z.2 (hne z.1 z.2)
    refine hcr.trans ?_
    rcases (show alphaHat (Demp φ z.1 z.2) τ ≤ αs from hzA).lt_or_eq with hlt | heq
    · unfold StatFormal.Wave30tu.tauRight
      refine csInf_le ⟨0, ?_⟩ ⟨αs, ⟨hlt, htv1⟩, rfl⟩
      rintro _ ⟨b, hb, rfl⟩
      exact hvalid.1 b ⟨hah0.trans hb.1.le, hb.2⟩
    · rw [heq]
      exact ((StatFormal.Wave30tu.tauRight_spec τ αs hvalid.1 hvalid.2.1 htv0.le htv1).2.2 htv0 hcont).le

theorem alphahat_schedule_of (hc : StatFormal.Wave30tx.Claims.contact) :
    StatFormal.Wave30tx.Claims.alphahat_schedule := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ τ ι l n m δ hφ hκ hchar htv0 htv1 hfam hn hm hδ0 hδ hrate e he
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 := StatFormal.Wave30tl.kappa_nonneg_of hκ x₀
  set T := tvDist P Q with hTdef
  have htv1' : tvDist Q P < 1 := by rwa [tvDist_comm]
  have hωPQ := (hc 𝒳 H P Q φ κ hφ hκ hchar htv1).2.2.2.2.2
  have hωQP := (hc 𝒳 H Q P φ κ hφ hκ hchar htv1').2.2.2.2.2
  obtain ⟨d1, hd1, h1⟩ := Metric.tendsto_nhdsWithin_nhds.1 hωPQ (e / 2) (half_pos he)
  obtain ⟨d2, hd2, h2⟩ := Metric.tendsto_nhdsWithin_nhds.1 hωQP (e / 2) (half_pos he)
  set ε₀ := min d1 d2 / 2 with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  have hε₀1 : ε₀ < d1 := by
    have := min_le_left d1 d2; rw [hε₀]; linarith
  have hε₀2 : ε₀ < d2 := by
    have := min_le_right d1 d2; rw [hε₀]; linarith
  have hdε : dist ε₀ 0 = ε₀ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε₀0]
  have hωP : StatFormal.Wave30tx.omegaC φ P Q ε₀ < e / 2 := by
    have := h1 (show ε₀ ∈ Ioi 0 from hε₀0) (by rw [hdε]; exact hε₀1)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hωQ : StatFormal.Wave30tx.omegaC φ Q P ε₀ < e / 2 := by
    have := h2 (show ε₀ ∈ Ioi 0 from hε₀0) (by rw [hdε]; exact hε₀2)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  set Cnd : ι → Prop := fun i => δ i < 1 ∧ tau κ T (δ i) (n i) (m i) ≤ e / 2 ∧
    3 * tau κ T (δ i) (n i) (m i) ≤ ε₀ with hCnd
  have key' : ∀ i, ∃ F : Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), MeasurableSet F ∧
      F ⊆ {z | let ah := alphaHat (Demp φ z.1 z.2) (τ (n i) (m i) (δ i))
        ∀ pr ∈ capped (n i) ah ×ˢ capped (m i) ah,
          IsMinOn (qp (fun k => φ (z.1 k)) (fun k => φ (z.2 k))) (capped (n i) ah ×ˢ capped (m i) ah) pr →
            ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.1 z.1) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤ e ∧
              ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.2 z.2) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤ e} ∧
      (Cnd i → ENNReal.ofReal (1 - 3 * δ i) ≤ StatFormal.Wave30tp.sampleLaw P Q (n i) (m i) F) := by
    intro i
    by_cases hi : Cnd i
    · obtain ⟨hv, hcont, hne, hle⟩ := hfam (n i) (m i) (hn i) (hm i) (δ i) (hδ0 i) hi.1
      obtain ⟨-, E, hEm, hEp, -, -, hAm, hEAp, hEA⟩ := alphahat_of hc 𝒳 H P Q φ κ (δ i) (δ i)
        (τ (n i) (m i) (δ i)) (n i) (m i) hφ hκ hchar htv0 htv1 (hδ0 i) hi.1 (hδ0 i) hi.1 (hn i) (hm i) hv hcont hne
      refine ⟨_, hEm.inter hAm, ?_, fun _ => ?_⟩
      · intro z hz
        obtain ⟨hD, hB⟩ := hEA z hz
        intro pr hpr hmin
        obtain ⟨hb1, hb2⟩ := hB pr hpr hmin
        set ta := tau κ T (δ i) (n i) (m i)
        have hrN : rn κ T (δ i) (n i) ≤ ta := rn_le_tau hκ0 htv1 (hδ0 i) _ _
        have hrM : rn κ T (δ i) (m i) ≤ ta := rn_le_tau_right hκ0 htv1 (hδ0 i) _ _
        have hDle : Demp φ z.1 z.2 (alphaHat (Demp φ z.1 z.2) (τ (n i) (m i) (δ i))) ≤ ta :=
          hD.trans (hle T ⟨htv0.le, htv1⟩)
        have harg : Demp φ z.1 z.2 (alphaHat (Demp φ z.1 z.2) (τ (n i) (m i) (δ i))) +
            rn κ T (δ i) (n i) + rn κ T (δ i) (m i) ≤ ε₀ := by linarith [hi.2.2]
        have hmP := omegaC_mono P Q hφ hκ htv1 harg
        have hmQ := omegaC_mono Q P hφ hκ htv1' harg
        constructor
        · linarith [hi.2.1]
        · linarith [hi.2.1]
      · rw [show 1 - 3 * δ i = 1 - δ i - 2 * δ i by ring]
        exact hEAp
    · exact ⟨∅, MeasurableSet.empty, empty_subset _, fun h' => absurd h' hi⟩
  choose F hFm hFs hFp using key'
  have ht := StatFormal.Wave30tu.tau_sched κ T htv1 hκ0 hn hm hδ0 hδ hrate
  have hev : ∀ᶠ i in l, Cnd i := by
    have hpos : 0 < min (e / 2) (ε₀ / 3) := lt_min (half_pos he) (by positivity)
    filter_upwards [hδ.eventually (gt_mem_nhds one_pos), ht.eventually (gt_mem_nhds hpos)] with i hi1 hi2
    refine ⟨hi1, (hi2.le.trans (min_le_left _ _)), ?_⟩
    have := hi2.le.trans (min_le_right _ _)
    linarith
  refine ⟨F, hFm, hFs, ?_⟩
  have hlow : Tendsto (fun i => ENNReal.ofReal (1 - 3 * δ i)) l (𝓝 1) := by
    have : Tendsto (fun i => 1 - 3 * δ i) l (𝓝 (1 - 3 * 0)) := tendsto_const_nhds.sub (hδ.const_mul 3)
    rw [mul_zero, sub_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  have hprob : ∀ i, IsProbabilityMeasure (StatFormal.Wave30tp.sampleLaw P Q (n i) (m i)) := fun i => by
    unfold StatFormal.Wave30tp.sampleLaw; infer_instance
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun i => by have := hprob i; exact prob_le_one)
  filter_upwards [hev] with i hi
  exact hFp i hi

end StatFormal.Wave30tx.RAlpha
