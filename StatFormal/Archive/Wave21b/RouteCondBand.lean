import StatFormal.Archive.Wave21b.Statements
import StatFormal.Archive.Gaps1.RouteSupport
import StatFormal.Archive.Wave17a.RouteCondBand

/-!
# Route — otfd C `thm:conditional-band-limits` (deterministic cores), `cor:conditional-test-coverage`
(untrusted)

* two-sided: `ess sup_A ⟨v,Q⟩ = sup_A ⟨v,Q⟩` (certified `lem:full-support-region`(i), `Gaps1`), attained on the compact
  `A`, and `|⟨v,T⟩ − ⟨v,Q⟩| ≤ ‖v‖ η` on `A ⊆ S`;
* one-sided: a finite `a`-net of the (bounded) essential range made of images of convergence points;
* coverage: the certified population content (`prop:conditional-pop-content`, Wave 17a) and edge comparison in `EReal`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave21b

open StatFormal.Wave17a (hPop InPopBand)

theorem cond_band_two_sided : Claims.cond_band_two_sided := by
  intro K 𝒯 μ A S Q T e δ η EK hQ hT he hA p hp hp1 t v hv
  obtain ⟨hcpt, hcvx, hint, hsupp, hAS⟩ := hA p hp hp1
  have hvn : ‖v‖ ≤ EK := by
    rcases hv with rfl | hv
    · exact he t
    · rw [Set.mem_singleton_iff] at hv; rw [hv, norm_neg]; exact he t
  set g : EuclideanSpace ℝ (Fin K) → ℝ := fun u => ⟪v, Q u⟫
  have hg : ContinuousOn g (A p) := (continuousOn_const.inner (hQ.mono hAS))
  have hfs := (StatFormal.Gaps1.full_support_region K μ (A p) hcpt.isClosed hcvx hint hsupp).2.2.2 g hg
  obtain ⟨u0, hu0, hmax⟩ := hcpt.exists_isMaxOn (hint.mono interior_subset) hg
  have hsupQ : (⨆ u ∈ A p, ((g u : ℝ) : EReal)) = ((g u0 : ℝ) : EReal) := by
    refine le_antisymm (iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 (hmax hu)) (le_iSup₂_of_le u0 hu0 le_rfl)
  have hη : 0 ≤ η := (norm_nonneg _).trans (hT u0 (hAS hu0))
  have hclose : ∀ u ∈ A p, |⟪v, T u⟫ - ⟪v, Q u⟫| ≤ EK * η := by
    intro u hu
    rw [← inner_sub_right]
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul hvn (hT u (hAS hu)) (norm_nonneg _) ((norm_nonneg _).trans hvn)
  have hup : supE (A p) T v ≤ ((g u0 + EK * η : ℝ) : EReal) := by
    refine iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 ?_
    have h1 := (abs_le.1 (hclose u hu)).2
    have h2 : ⟪v, Q u⟫ ≤ ⟪v, Q u0⟫ := hmax hu
    simp only [g]
    linarith
  have hlo : ((⟪v, T u0⟫ : ℝ) : EReal) ≤ supE (A p) T v := le_iSup₂_of_le u0 hu0 le_rfl
  have hne_top : supE (A p) T v ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  have hne_bot : supE (A p) T v ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo
  refine ⟨g u0, (supE (A p) T v).toReal, by rw [StatFormal.Wave17a.hPop, hfs, hsupQ],
    (EReal.coe_toReal hne_top hne_bot).symm, ?_⟩
  have h1 : (supE (A p) T v).toReal ≤ g u0 + EK * η := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne_top hne_bot]; exact hup
  have h2 : ⟪v, T u0⟫ ≤ (supE (A p) T v).toReal := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne_top hne_bot]; exact hlo
  have h3 := (abs_le.1 (hclose u0 hu0)).1
  rw [abs_le]; constructor <;> simp only [g] at * <;> linarith

theorem cond_band_one_sided : Claims.cond_band_one_sided := by
  intro K 𝒯 μ A Q Qn e R EK hA hR hconv he η hη
  set D : Set (EuclideanSpace ℝ (Fin K)) :=
    {u | u ∈ A ∧ ‖Q u‖ ≤ R ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))}
  have hD : ∀ᵐ u ∂μ.restrict A, u ∈ D := by
    filter_upwards [ae_restrict_mem hA, hR, hconv] with u h1 h2 h3 using ⟨h1, h2, h3⟩
  set a : ℝ := η / (2 * (|EK| + 1))
  have ha : 0 < a := by positivity
  have htb : TotallyBounded (Q '' D) := by
    refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin K)) R).totallyBounded.subset ?_
    rintro _ ⟨u, hu, rfl⟩
    simpa using hu.2.1
  obtain ⟨F, hFsub, hFfin, hFcov⟩ := Metric.finite_approx_of_totallyBounded htb a ha
  have hpre : ∀ y ∈ F, ∃ u ∈ D, Q u = y := fun y hy => hFsub hy
  choose! uy huyD huyQ using hpre
  have hev : ∀ᶠ n in atTop, ∀ y ∈ F, ‖Qn n (uy y) - Q (uy y)‖ < a := by
    refine (hFfin.eventually_all).2 fun y hy => ?_
    have := (huyD y hy).2.2
    have := (tendsto_iff_norm_sub_tendsto_zero.1 this).eventually (gt_mem_nhds ha)
    exact this
  filter_upwards [hev] with n hn
  intro t
  have key : ∀ v : EuclideanSpace ℝ (Fin K), ‖v‖ ≤ EK → hPop μ A Q v ≤ supE A (Qn n) v + η := by
    intro v hv
    have hv' : ‖v‖ ≤ |EK| := hv.trans (le_abs_self _)
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hD] with u hu
    obtain ⟨y, hyF, hyb⟩ := Set.mem_iUnion₂.1 (hFcov ⟨u, hu, rfl⟩)
    rw [Metric.mem_ball] at hyb
    have hu' := huyQ y hyF
    have hc1 : ⟪v, Q u⟫ ≤ ⟪v, Qn n (uy y)⟫ + η := by
      have hd : ‖Q u - Qn n (uy y)‖ ≤ 2 * a := by
        have h1 : ‖Q u - Q (uy y)‖ < a := by rw [hu', ← dist_eq_norm]; exact hyb
        have h2 := hn y hyF
        rw [norm_sub_rev] at h2
        calc ‖Q u - Qn n (uy y)‖ ≤ ‖Q u - Q (uy y)‖ + ‖Q (uy y) - Qn n (uy y)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * a := by linarith
      have hi : ⟪v, Q u⟫ - ⟪v, Qn n (uy y)⟫ ≤ ‖v‖ * ‖Q u - Qn n (uy y)‖ := by
        rw [← inner_sub_right]; exact real_inner_le_norm _ _
      have hb : ‖v‖ * ‖Q u - Qn n (uy y)‖ ≤ |EK| * (2 * a) :=
        mul_le_mul hv' hd (norm_nonneg _) (abs_nonneg _)
      have hfin : |EK| * (2 * a) ≤ η := by
        simp only [a]
        rw [show |EK| * (2 * (η / (2 * (|EK| + 1)))) = η * (|EK| / (|EK| + 1)) by field_simp]
        have : |EK| / (|EK| + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        nlinarith
      linarith
    have hc2 : ((⟪v, Qn n (uy y)⟫ : ℝ) : EReal) ≤ supE A (Qn n) v :=
      le_iSup₂_of_le (uy y) (huyD y hyF).1 le_rfl
    calc ((⟪v, Q u⟫ : ℝ) : EReal) ≤ ((⟪v, Qn n (uy y)⟫ + η : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hc1
      _ = ((⟪v, Qn n (uy y)⟫ : ℝ) : EReal) + (η : EReal) := EReal.coe_add _ _
      _ ≤ supE A (Qn n) v + η := add_le_add hc2 le_rfl
  exact ⟨key _ (he t), key _ (by rw [norm_neg]; exact he t)⟩

lemma ereal_sub_add_cancel_aux (m η : ℝ) (h : EReal) :
    (m : EReal) - (h + η) + η = (m : EReal) - h := by
  induction h using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub]
    congr 1; ring

theorem cond_test_coverage_inflated : Claims.cond_test_coverage_inflated := by
  intro K 𝒯 μ _ Q A p κ m e U L hQ hA hpA hκ hdef
  obtain ⟨hmeas, hcont⟩ := StatFormal.Wave17a.conditional_pop_content K 𝒯 μ (μ.map Q) Q A p m e inferInstance hQ rfl
    hA hpA
  filter_upwards [hdef κ hκ] with n hn
  refine ⟨_, hmeas, fun z hz t => ?_, hcont⟩
  obtain ⟨h1, h2⟩ := hz t
  obtain ⟨h3, h4⟩ := hn t
  constructor
  · calc L n t - κ ≤ ((m t : EReal) - hPop μ A Q (-e t) + κ) - κ := EReal.sub_le_sub h4 le_rfl
      _ = (m t : EReal) - hPop μ A Q (-e t) := EReal.add_sub_cancel_right
      _ ≤ _ := h1
  · exact h2.trans h3

theorem cond_test_coverage_nested : Claims.cond_test_coverage_nested := by
  intro K 𝒯 μ _ Q A p m e U L hQ hA hpA hnest hdef p' hp' hp'p
  obtain ⟨η, hη, hηt⟩ := hnest p' hp' hp'p
  obtain ⟨hmeas, hcont⟩ := StatFormal.Wave17a.conditional_pop_content K 𝒯 μ (μ.map Q) Q (A p') p' m e
    inferInstance hQ rfl (hA p') (hpA p' hp' hp'p.le)
  filter_upwards [hdef η hη] with n hn
  refine ⟨_, hmeas, fun z hz t => ?_, hcont⟩
  obtain ⟨h1, h2⟩ := hz t
  obtain ⟨h3, h4⟩ := hn t
  obtain ⟨h5, h6⟩ := hηt t
  constructor
  · calc L n t ≤ (m t : EReal) - hPop μ (A p) Q (-e t) + η := h4
      _ ≤ (m t : EReal) - (hPop μ (A p') Q (-e t) + η) + η := by
          gcongr
          exact EReal.sub_le_sub le_rfl h6
      _ = (m t : EReal) - hPop μ (A p') Q (-e t) := ereal_sub_add_cancel_aux _ _ _
      _ ≤ _ := h1
  · refine h2.trans ?_
    have : (m t : EReal) + hPop μ (A p') Q (e t) + η ≤ U n t + η := by
      calc (m t : EReal) + hPop μ (A p') Q (e t) + η = (m t : EReal) + (hPop μ (A p') Q (e t) + η) := by
            rw [add_assoc]
        _ ≤ (m t : EReal) + hPop μ (A p) Q (e t) := add_le_add le_rfl h5
        _ ≤ U n t + η := h3
    calc (m t : EReal) + hPop μ (A p') Q (e t) = (m t : EReal) + hPop μ (A p') Q (e t) + η - η :=
          EReal.add_sub_cancel_right.symm
      _ ≤ U n t + η - η := EReal.sub_le_sub this le_rfl
      _ = U n t := EReal.add_sub_cancel_right

end StatFormal.Wave21b
