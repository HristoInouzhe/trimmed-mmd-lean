import StatFormal.Wave31tf.Statements
import StatFormal.Wave31td.RouteClaims
import StatFormal.Wave31ta.Proofs
import StatFormal.Wave30tu.Full.Route
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

set_option linter.style.longLine false

/-!
# Route: wave 31tf, the short claims (untrusted)

* `linear_margin` (G3a): `TV = ⅓` is the certified `Wave31td.linear_tv`, and `D_{⅓−ε} = max((3/2)ε, 0) = 3ε/2` on `[0,⅓]` is the certified
  `Wave31td.linear_D` (it includes both endpoints); `ω(ε) = 3ε/2` is strictly increasing, continuous, `0` at `0`, nonnegative on `[0,⅓]`.
* `gamma_ge_one` (G4): `D_{α⋆} = 0` (certified `zero_of_tv_le`, no (A3)) and the Lipschitz bound of the path (certified
  `Wave31ta.continuity_v2`, constant `4κ(1−α⋆)⁻²`) give `c₀ ε^γ ≤ L ε` on `(0,α⋆]`; if `γ < 1`, `L ε^{1−γ} → 0` as `ε ↓ 0`, a contradiction.
* `delta_schedule`, `consistency_schedule`, `consistency_schedule_full`, `consistency_schedule_cpl` (G5): `1/(n∧m) → 0` and
  `log(n∧m)/(n∧m) → 0` as `n∧m → ∞` (`Real.isLittleO_log_id_atTop`); then the certified `Wave30tu.cor_consistency` (generic), its instance
  `Wave30tu.Full.cor_consistency_full` (`tauFull`), and the generic corollary at `tauV2Cpl` (valid by the certified `Wave31ta.tauV2Cpl_facts`, `≤ tau`
  when `D ≤ 2κ`; `τ^A` a lower tool by `tauA_lower`, `≤ tau` by `tauNM_le_tau`).
* `n_of_a_generic` (G7a): for `n ≤ N` the thresholds `τ_n(a) ≥ τ_n(0) ≥ c := min_{n ≤ N} τ_n(0) > 0`, while `D(a) < c` near `α⋆` by continuity
  and `D(α⋆) = 0`; so no `n ∈ [1,N]` has `τ_n(a) < D(a)`, i.e. `n(a) ≥ N + 1`.
* `no_uniform_accuracy`, `no_uniform_rate` (G8): from the certified `Wave31ta.impossible_two` applied to `Û = T̂ + r` (`{|T̂ − TV| ≤ r} ⊆ {TV ≤ Û}`):
  `P_{u,u}(T̂ + r ≥ 1) ≥ 1 − δ`, while accuracy at the uniform pair (`TV = 0`) gives `P_{u,u}(|T̂| ≤ r) ≥ 1 − δ`; the two events are disjoint
  for `r < ½` and the sum of their probabilities exceeds `1` for `δ < ½`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tf

open StatFormal.TrimmedMMD.Unconditional

/-! ### G3a -/

theorem linear_margin : Claims.linear_margin := by
  have htv : StatFormal.Distances.tvDist StatFormal.Wave31td.Plin StatFormal.Wave31td.Qlin = 1 / 3 :=
    StatFormal.Wave31td.linear_tv
  refine ⟨htv, ?_⟩
  obtain ⟨hD, -⟩ := StatFormal.Wave31td.linear_D
  unfold StatFormal.Wave30tu.Margin
  rw [htv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a _ b _ hab
    show 3 * a / 2 < 3 * b / 2
    linarith
  · exact (by fun_prop : Continuous fun ε : ℝ => 3 * ε / 2).continuousOn
  · simp
  · intro e he
    show 0 ≤ 3 * e / 2
    linarith [he.1]
  · intro e he
    have h := (hD (1 / 3 - e) (by linarith [he.2]) (by linarith [he.1])).1
    rw [h]
    show 3 * e / 2 ≤ max (3 / 2 * (1 / 3 - (1 / 3 - e))) 0
    have : 3 / 2 * (1 / 3 - (1 / 3 - e)) = 3 * e / 2 := by ring
    rw [this]
    exact le_max_left _ _

/-! ### G4 -/

theorem gamma_ge_one : Claims.gamma_ge_one := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ c₀ γ hφ hκ htv0 htv1 hc₀ hγ hmar
  by_contra hlt
  push Not at hlt
  set a := StatFormal.Distances.tvDist P Q with ha
  have hD0 : Dpop φ P Q a = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ a hφ hκ htv0.le htv1 le_rfl
  have hLip : ∀ ε ∈ Icc (0 : ℝ) a, Dpop φ P Q (a - ε) ≤ 4 * κ / (1 - a) ^ 2 * ε := by
    intro ε hε
    have h := StatFormal.Wave31ta.continuity_v2 𝒳 H P Q φ κ a (a - ε) a hφ hκ htv0.le htv1
      ⟨by linarith [hε.2], by linarith [hε.1]⟩ ⟨htv0.le, le_rfl⟩
    rw [hD0, sub_zero] at h
    have h2 : |a - ε - a| = ε := by
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hε.1]
    rw [h2] at h
    exact le_trans (le_abs_self _) h
  set L := 4 * κ / (1 - a) ^ 2 with hL
  have key : ∀ ε ∈ Icc (0 : ℝ) a, c₀ * ε ^ γ ≤ L * ε := fun ε hε => (hmar ε hε).trans (hLip ε hε)
  have hs : 0 < 1 - γ := by linarith
  have hcont : Tendsto (fun ε : ℝ => L * ε ^ (1 - γ)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ (1 - γ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const (0 : ℝ) (1 - γ) (Or.inr hs.le)).tendsto
      rw [Real.zero_rpow hs.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    simpa using h1.const_mul L
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), L * ε ^ (1 - γ) < c₀ := hcont.eventually (gt_mem_nhds hc₀)
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioc 0 a := Ioc_mem_nhdsGT htv0
  obtain ⟨ε, h1, h2⟩ := (hev1.and hev2).exists
  have hεpos : 0 < ε := h2.1
  have hk := key ε ⟨h2.1.le, h2.2⟩
  have hε' : ε ^ γ * ε ^ (1 - γ) = ε := by
    rw [← Real.rpow_add hεpos]; simp
  have hpos : 0 < ε ^ γ := Real.rpow_pos_of_pos hεpos γ
  have h3 : c₀ * ε ^ γ ≤ (L * ε ^ (1 - γ)) * ε ^ γ := by
    calc c₀ * ε ^ γ ≤ L * ε := hk
      _ = L * (ε ^ γ * ε ^ (1 - γ)) := by rw [hε']
      _ = (L * ε ^ (1 - γ)) * ε ^ γ := by ring
  have h4 : c₀ ≤ L * ε ^ (1 - γ) := le_of_mul_le_mul_right h3 hpos
  linarith

/-! ### G5 -/

theorem delta_schedule : Claims.delta_schedule := by
  refine ⟨fun n m hn hm => ?_, fun ι l n m hlim => ?_⟩
  · have h2 : (2 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast le_min hn hm
    unfold deltaSched
    constructor
    · have : (0 : ℝ) < ((min n m : ℕ) : ℝ) := by linarith
      positivity
    · rw [div_lt_one (by linarith)]
      linarith
  · have hcast : Tendsto (fun i => ((min (n i) (m i) : ℕ) : ℝ)) l atTop :=
      tendsto_natCast_atTop_atTop.comp hlim
    constructor
    · refine hcast.inv_tendsto_atTop.congr (fun i => ?_)
      simp [deltaSched, one_div]
    · have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      refine (hlog.comp hcast).congr' ?_
      filter_upwards [hcast.eventually_ge_atTop 1] with i hi
      simp [deltaSched, one_div]

theorem consistency_schedule : Claims.consistency_schedule := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ τ τA ι l n m hφ hκ hchar htv hτ hn hm hlim e he
  obtain ⟨hd1, hd2⟩ := delta_schedule
  obtain ⟨hδ, hrate⟩ := hd2 ι l n m hlim
  exact StatFormal.Wave30tu.cor_consistency 𝒳 H P Q φ κ τ τA ι l n m (fun i => deltaSched (n i) (m i))
    hφ hκ hchar htv hτ (fun i => le_trans (by norm_num) (hn i)) (fun i => le_trans (by norm_num) (hm i))
    (fun i => (hd1 (n i) (m i) (hn i) (hm i)).1) hδ hrate e he

theorem consistency_schedule_full : Claims.consistency_schedule_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D ι l n m hφ hκ hD h2κ hchar htv hn hm hlim e he
  obtain ⟨hd1, hd2⟩ := delta_schedule
  obtain ⟨hδ, hrate⟩ := hd2 ι l n m hlim
  exact StatFormal.Wave30tu.Full.cor_consistency_full 𝒳 H P Q φ κ D ι l n m (fun i => deltaSched (n i) (m i))
    hφ hκ hD h2κ hchar htv (fun i => le_trans (by norm_num) (hn i)) (fun i => le_trans (by norm_num) (hm i))
    (fun i => (hd1 (n i) (m i) (hn i) (hm i)).1) hδ hrate e he

theorem consistency_schedule_cpl : Claims.consistency_schedule_cpl := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D ι l n m hφ hκ hD h2κ hk0 hdiag hchar htv hn hm hlim e he
  obtain ⟨hd1, hd2⟩ := delta_schedule
  obtain ⟨hδ, hrate⟩ := hd2 ι l n m hlim
  exact StatFormal.Wave30tu.cor_consistency 𝒳 H P Q φ κ
    (fun n m d α => StatFormal.Wave31ta.tauV2Cpl κ D α d n m)
    (fun n m d α => StatFormal.Wave30tr.tauA κ D α d n m) ι l n m (fun i => deltaSched (n i) (m i))
    hφ hκ hchar htv
    (fun n m hn hm d hd0 hd1 =>
      ⟨(StatFormal.Wave31ta.tauV2Cpl_facts 𝒳 H φ κ D d n m (nonempty_of_isProbabilityMeasure P) hφ hκ hD hk0 hdiag
          hd0 hd1 hn hm).1,
        (StatFormal.Wave31ta.tauV2Cpl_facts 𝒳 H φ κ D d n m (nonempty_of_isProbabilityMeasure P) hφ hκ hD hk0 hdiag
          hd0 hd1 hn hm).2.2.1 h2κ,
        (StatFormal.Wave30tu.Instance.tauA_lower P Q hφ hκ hD hd0 hd1 hn hm).2,
        (StatFormal.Wave30tu.Instance.tauNM_le_tau P hκ hD h2κ hd0 hd1 hn hm).1⟩)
    (fun i => le_trans (by norm_num) (hn i)) (fun i => le_trans (by norm_num) (hm i))
    (fun i => (hd1 (n i) (m i) (hn i) (hm i)).1) hδ hrate e he

/-! ### G7, the generic reason -/

theorem n_of_a_generic : Claims.n_of_a_generic := by
  intro τ D αs hα0 hα1 hmono hpos hcont hD N
  have hev : ∀ n ∈ Finset.Icc 1 N, ∀ᶠ a in 𝓝[<] αs, D a < τ n 0 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hc : ContinuousWithinAt D (Icc 0 αs) αs := hcont αs ⟨hα0.le, le_rfl⟩
    have ht : Tendsto D (𝓝[Ioo 0 αs] αs) (𝓝 (D αs)) :=
      hc.tendsto.mono_left (nhdsWithin_mono _ (fun x hx => ⟨hx.1.le, hx.2.le⟩))
    rw [nhdsWithin_Ioo_eq_nhdsLT hα0, hD] at ht
    exact ht.eventually (gt_mem_nhds (hpos n hn1))
  have hall : ∀ᶠ a in 𝓝[<] αs, ∀ n ∈ Finset.Icc 1 N, D a < τ n 0 := (Filter.eventually_all_finset _).2 hev
  have hlt : ∀ᶠ a in 𝓝[<] αs, a ∈ Ioo 0 αs := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hα0]
    exact self_mem_nhdsWithin
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hall.and hlt)
  have hl' : l < αs := hl
  set l0 := max l 0 with hl0
  have hl0lt : l0 < αs := max_lt hl' hα0
  refine ⟨(l0 + αs) / 2, ⟨by have := le_max_right l 0; linarith, by linarith⟩, ?_⟩
  intro a ha
  have haI : a ∈ Ioo l αs := ⟨by have := le_max_left l 0; linarith [ha.1], ha.2⟩
  obtain ⟨hDa, ha0⟩ := hsub haI
  have hN1 : ((N + 1 : ℕ) : ℕ∞) ≤ sizeNeeded τ D a := by
    unfold sizeNeeded
    refine le_iInf₂ fun n hn => ?_
    obtain ⟨hn1, hlt'⟩ := hn
    by_contra hcon
    have hnN : n ≤ N := by
      have : ¬ ((N + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := hcon
      by_contra h2
      exact this (by exact_mod_cast Nat.succ_le_of_lt (not_le.1 h2))
    have h1 := hDa n (Finset.mem_Icc.2 ⟨hn1, hnN⟩)
    have h2 : τ n 0 ≤ τ n a := hmono n hn1 ⟨le_refl 0, by norm_num⟩ ⟨ha0.1.le, by linarith [ha0.2]⟩ ha0.1.le
    linarith
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) hN1

/-! ### G8 -/

/-- The uniform law on `[0,1]` belongs to `𝒫₂`. -/
lemma density2_unif : StatFormal.Wave31ta.Density2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  refine ⟨⟨?_⟩, ?_⟩
  · rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp
  · refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left zero_le (by norm_num)

/-- `Density2` pairs give probability data laws. -/
lemma dataLaw_prob (n m : ℕ) {Ξ : Type} [MeasurableSpace Ξ] (R : Measure Ξ) [IsProbabilityMeasure R]
    {P Q : Measure ℝ} (hP : StatFormal.Wave31ta.Density2 P) (hQ : StatFormal.Wave31ta.Density2 Q) :
    IsProbabilityMeasure (StatFormal.TrimmedMMD.Impossible.dataLaw n m P Q R) := by
  haveI := hP.1
  haveI := hQ.1
  unfold StatFormal.TrimmedMMD.Impossible.dataLaw
  infer_instance

theorem no_uniform_accuracy : Claims.no_uniform_accuracy := by
  intro n m δ r Ξ _ R _ T hn hm hδ0 hδ1 hr hT hall
  have hPu2 := density2_unif
  have himp := StatFormal.Wave31ta.impossible_two n m δ Ξ R (fun z => T z + r) hn hm hδ0 (by linarith)
    (hT.add_const r) (by
      intro P Q hP hQ
      haveI := dataLaw_prob n m R hP hQ
      refine le_trans (hall P Q hP hQ) (measureReal_mono ?_)
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have := (abs_le.1 hz).1
      linarith)
  have h2 := hall _ _ hPu2 hPu2
  rw [StatFormal.Distances.tvDist_self] at h2
  haveI := dataLaw_prob n m R hPu2 hPu2
  set μ := StatFormal.TrimmedMMD.Impossible.dataLaw n m (volume.restrict (Set.Icc (0 : ℝ) 1))
    (volume.restrict (Set.Icc (0 : ℝ) 1)) R with hμ
  have hBm : MeasurableSet {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | |T z - 0| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hdisj : Disjoint {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | 1 ≤ T z + r} {z | |T z - 0| ≤ r} := by
    refine Set.disjoint_left.2 fun z hzA hzB => ?_
    simp only [Set.mem_ofPred_eq] at hzA hzB
    have := (abs_le.1 hzB).2
    linarith
  have hU := measureReal_union (μ := μ) hdisj hBm
  have hle : μ.real ({z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | 1 ≤ T z + r} ∪ {z | |T z - 0| ≤ r}) ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  linarith

theorem no_uniform_rate : Claims.no_uniform_rate := by
  intro δ r hδ0 hδ1 hr
  have hev : ∀ᶠ p : ℕ × ℕ in atTop, r p.1 p.2 < 1 / 2 :=
    (hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨⟨N1, N2⟩, hN⟩ := eventually_atTop.1 hev
  refine ⟨max N1 N2, fun n m hNn hNm hn hm Ξ _ R _ T hT => ?_⟩
  have hlt : r n m < 1 / 2 := hN (n, m) ⟨le_trans (le_max_left _ _) hNn, le_trans (le_max_right _ _) hNm⟩
  have hacc := no_uniform_accuracy n m δ (r n m) Ξ R T hn hm hδ0 hδ1 hlt hT
  refine ⟨hacc, fun hall => hacc ?_⟩
  intro P Q hP hQ
  refine hall P Q ⟨hP.1, ?_⟩ ⟨hQ.1, ?_⟩
  · -- `P ≤ 2 • volume.restrict (Icc 0 1)` gives `P (Icc 0 1)ᶜ = 0`
    have h := hP.2 (Set.Icc (0 : ℝ) 1)ᶜ
    rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_Icc.compl)] at h
    simp at h
    exact h
  · have h := hQ.2 (Set.Icc (0 : ℝ) 1)ᶜ
    rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_Icc.compl)] at h
    simp at h
    exact h

end StatFormal.Wave31tf
