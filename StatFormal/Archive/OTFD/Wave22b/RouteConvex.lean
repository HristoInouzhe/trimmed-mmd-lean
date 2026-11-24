import StatFormal.Archive.OTFD.Wave22b.Statements
import StatFormal.Archive.OTFD.Wave19a.RouteSubgrad
import StatFormal.Archive.Wave21b.RouteCondBand
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Measure

/-!
# Route — B `thm:band-consistency`, C band limits from potentials, C `prop:cond-transfer-consistency` (untrusted)

* Rademacher: a convex function on an open set is locally Lipschitz (`ConvexOn.locallyLipschitzOn`), hence
  differentiable Lebesgue-a.e. there (countable cover by balls, `ae_differentiableWithinAt_of_mem`); with
  `Convex.addHaar_frontier`, `μ ≪ Leb` carried by a convex `U` charges only `int U`.
* The gradient of a convex function is continuous where it is differentiable (certified Wave 19a
  `subgrad_conv_point` applied to the constant sequence).
* Two-sided: Wave 19a `subgrad_conv_unif` gives `sup_S ‖T_n − ∇χ‖ ≤ ε` eventually; Wave 21b `cond_band_two_sided`
  then bounds the edges. One-sided: Wave 19a `subgrad_conv_point` at a.e. point, then Wave 21b `cond_band_one_sided`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.Wave22b

open StatFormal.OTFD.Wave19a (extTop grad_mem_subdiff mem_subdiff_extTop)
open StatFormal.Wave12b (Euc)
open StatFormal.Wave17a (hPop)
open StatFormal.Wave21b (supE)

variable {K : ℕ}

/-- Rademacher for convex functions on open sets. -/
lemma ae_differentiableAt_of_convexOn {C : Set (Euc K)} {χ : Euc K → ℝ} (hC : IsOpen C) (hχ : ConvexOn ℝ C χ) :
    ∀ᵐ u ∂(volume : Measure (Euc K)), u ∈ C → DifferentiableAt ℝ χ u := by
  have hL := hχ.locallyLipschitzOn hC
  have hex : ∀ x : C, ∃ r : ℝ, 0 < r ∧ ∃ L, LipschitzOnWith L χ (Metric.ball (x : Euc K) r) := by
    rintro ⟨x, hx⟩
    obtain ⟨L, t, ht, hLt⟩ := hL hx
    rw [nhdsWithin_eq_nhds.2 (hC.mem_nhds hx)] at ht
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
    exact ⟨r, hr, L, hLt.mono hrt⟩
  choose r hr L hLip using hex
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : C => Metric.ball (x : Euc K) (r x)) (fun _ => Metric.isOpen_ball)
  have hT : ∀ i ∈ T, ∀ᵐ u ∂(volume : Measure (Euc K)),
      u ∈ Metric.ball (i : Euc K) (r i) → DifferentiableAt ℝ χ u := by
    intro i _
    filter_upwards [(hLip i).ae_differentiableWithinAt_of_mem (μ := volume)] with u hu hmem
    exact (hu hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  have hall := (ae_ball_iff hTc).2 hT
  filter_upwards [hall] with u hu huC
  have hmem : u ∈ ⋃ i ∈ T, Metric.ball (i : Euc K) (r i) := by
    rw [hTU]; exact mem_iUnion.2 ⟨⟨u, huC⟩, Metric.mem_ball_self (hr _)⟩
  obtain ⟨i, hi, hmem⟩ := mem_iUnion₂.1 hmem
  exact hu i hi hmem

/-- The constant sequence converges uniformly. -/
lemma tendstoUniformlyOn_const_seq (χ : Euc K → ℝ) (S : Set (Euc K)) :
    TendstoUniformlyOn (fun _ : ℕ => χ) χ atTop S :=
  Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by simpa using hε

/-- The gradient of a convex function is continuous at interior differentiability points of an open set where it is
differentiable. -/
lemma continuousAt_gradient {C O : Set (Euc K)} {χ : Euc K → ℝ} (hC : IsOpen C) (hCc : Convex ℝ C)
    (hχ : ConvexOn ℝ C χ) (hO : IsOpen O) (hOC : O ⊆ C) (hd : ∀ u ∈ O, DifferentiableAt ℝ χ u) {u : Euc K}
    (hu : u ∈ O) : ContinuousAt (gradient χ) u := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro us hus
  have hev : ∀ᶠ n in atTop, us n ∈ O := hus (hO.mem_nhds hu)
  exact StatFormal.OTFD.Wave19a.subgrad_conv_point K C (fun _ => χ) χ u us (fun n => gradient χ (us n)) hC hCc
    (fun _ => hχ) hχ (fun S _ _ => tendstoUniformlyOn_const_seq χ S) (hOC hu) (hd u hu) hus
    (hev.mono fun n hn => grad_mem_subdiff hχ (hOC hn) (hd _ hn))

lemma hPop_congr {μ : Measure (Euc K)} {A : Set (Euc K)} {Q Q' : Euc K → Euc K} (h : Q =ᵐ[μ.restrict A] Q')
    (v : Euc K) : hPop μ A Q v = hPop μ A Q' v := by
  unfold hPop
  exact essSup_congr_ae (h.mono fun u hu => by simp only [hu])

lemma ae_restrict_eq_grad {μ : Measure (Euc K)} {A O : Set (Euc K)} {Q : Euc K → Euc K} {χ : Euc K → ℝ}
    (hA : MeasurableSet A) (hAO : A ⊆ O) (hQ : ∀ᵐ u ∂μ, u ∈ O → Q u = gradient χ u) :
    Q =ᵐ[μ.restrict A] gradient χ := by
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae hQ] with u hu h using h (hAO hu)

theorem band_consistency : Claims.band_consistency := by
  intro K 𝒯 μ A C O χ g Q T e δ EK hC hCc hχ hg hunif hO hAO hOC hdiff hQ hAc hA hT he η hη
  set S := A (1 - δ)
  set E' := max EK 0
  set ε := η / (E' + 1) with hεdef
  have hE' : 0 ≤ E' := le_max_right _ _
  have hε : 0 < ε := div_pos hη (by linarith)
  have hconv := StatFormal.OTFD.Wave19a.subgrad_conv_unif K C g χ O S hC hCc hg hχ hunif hO hOC hdiff hAO hAc ε hε
  have hcont : ContinuousOn (gradient χ) S := fun u hu =>
    (continuousAt_gradient hC hCc hχ hO hOC hdiff (hAO hu)).continuousWithinAt
  filter_upwards [hconv] with n hn
  intro p hp hp1 t v hv
  have hTS : ∀ u ∈ S, ‖T n u - gradient χ u‖ ≤ ε := fun u hu => hn u hu (T n u) (hT n u hu)
  obtain ⟨r, s, hr, hs, hrs⟩ := StatFormal.Wave21b.cond_band_two_sided K 𝒯 μ A S (gradient χ) (T n) e δ ε E' hcont hTS
    (fun t => (he t).trans (le_max_left _ _))
    (fun p hp hp1 => let h := hA p hp hp1; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) p hp hp1 t v hv
  obtain ⟨hcpt, -, -, -, hAS⟩ := hA p hp hp1
  refine ⟨r, s, ?_, hs, ?_⟩
  · rw [← hr]; exact hPop_congr (ae_restrict_eq_grad hcpt.isClosed.measurableSet (hAS.trans hAO) hQ) v
  · calc |s - r| ≤ E' * ε := hrs
      _ ≤ η := by
        rw [hεdef, mul_div_assoc']
        rw [div_le_iff₀ (by linarith)]
        nlinarith

/-- `μ ≪ Leb` carried by a convex `U` charges only `int U`. -/
lemma ae_mem_interior {μ : Measure (Euc K)} {U : Set (Euc K)} (hac : μ ≪ volume) (hU : Convex ℝ U)
    (hUc : μ Uᶜ = 0) : ∀ᵐ u ∂μ, u ∈ interior U := by
  have hfr : μ (frontier U) = 0 := hac (hU.addHaar_frontier volume)
  have h1 : ∀ᵐ u ∂μ, u ∈ U := measure_eq_zero_iff_ae_notMem.1 hUc |>.mono fun u hu => by simpa using hu
  have h2 : ∀ᵐ u ∂μ, u ∉ frontier U := measure_eq_zero_iff_ae_notMem.1 hfr
  filter_upwards [h1, h2] with u hu1 hu2
  rw [← self_sdiff_frontier]; exact ⟨hu1, hu2⟩

/-- The good set of points: interior, differentiability, `Q = ∇χ`. -/
lemma ae_good {μ : Measure (Euc K)} {U : Set (Euc K)} {χ : Euc K → ℝ} {Q : Euc K → Euc K} (hac : μ ≪ volume)
    (hU : Convex ℝ U) (hUc : μ Uᶜ = 0) (hχ : ConvexOn ℝ (interior U) χ) (hQ : Q =ᵐ[μ] gradient χ) :
    ∀ᵐ u ∂μ, u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Q u = gradient χ u := by
  have hd := hac.ae_le (ae_differentiableAt_of_convexOn isOpen_interior hχ)
  filter_upwards [ae_mem_interior hac hU hUc, hd, hQ] with u h1 h2 h3 using ⟨h1, h2 h1, h3⟩

theorem cond_maps_ae : Claims.cond_maps_ae := by
  intro K μ U χ g Q Qn hac hU hUc hχ hg hunif hQ hQn
  filter_upwards [ae_good hac hU hUc hχ hQ] with u ⟨hu, hdu, hQu⟩
  refine ⟨hu, hdu, ?_⟩
  rw [hQu]
  exact StatFormal.OTFD.Wave19a.subgrad_conv_point K (interior U) g χ u (fun _ => u) (fun n => Qn n u) isOpen_interior
    hU.interior hg hχ hunif hu hdu tendsto_const_nhds (Eventually.of_forall fun n => hQn n u hu)

theorem cond_band_one_sided_potentials : Claims.cond_band_one_sided_potentials := by
  intro K 𝒯 μ U A χ g Q Qn e R EK hac hU hUc hχ hg hunif hQ hQn hA hR he η hη
  have hconv := cond_maps_ae K μ U χ g Q Qn hac hU hUc hχ hg hunif hQ hQn
  exact StatFormal.Wave21b.cond_band_one_sided K 𝒯 μ A Q Qn e R EK hA hR
    (ae_restrict_of_ae (hconv.mono fun u hu => hu.2.2)) he η hη

theorem cond_transfer_consistency : Claims.cond_transfer_consistency := by
  intro K Ω _ P μ U DF Z F Fh χ' g Q' Qh hac hU hUc hZ hF hmap hZD hrank hχ' hQ' hpot hQh
  have hgood := ae_good hac hU hUc hχ' hQ'
  rw [← hmap] at hgood
  have hgoodP := ae_of_ae_map (hF.comp hZ).aemeasurable hgood
  filter_upwards [hgoodP, hZD, hrank, hpot] with ω hG hz hr hp
  obtain ⟨hint, hdiff, hQe⟩ := hG
  simp only [Function.comp_apply] at hint hdiff hQe
  refine ⟨hint, hdiff, hQe, ?_⟩
  have hus : Tendsto (fun n => Fh n ω (Z ω)) atTop (𝓝 (F (Z ω))) := hr (Z ω) hz
  have hev : ∀ᶠ n in atTop, Fh n ω (Z ω) ∈ interior U := hus (isOpen_interior.mem_nhds hint)
  rw [hQe]
  exact StatFormal.OTFD.Wave19a.subgrad_conv_point K (interior U) (fun n => g n ω) χ' (F (Z ω))
    (fun n => Fh n ω (Z ω)) (fun n => Qh n ω (Fh n ω (Z ω))) isOpen_interior hU.interior hp.1 hχ' hp.2 hint hdiff
    hus (hev.mono fun n hn => hQh n ω _ hn)

theorem cond_transfer_consistency_prob : Claims.cond_transfer_consistency_prob := by
  intro K Ω _ P _ μ U DF Z F Fh χ' g Q' Qh hac hU hUc hZ hF hmap hZD hrank hχ' hQ' hpot hQh hmeas
  have h := cond_transfer_consistency K Ω P μ U DF Z F Fh χ' g Q' Qh hac hU hUc hZ hF hmap hZD hrank hχ' hQ' hpot hQh
  exact tendstoInMeasure_of_tendsto_ae hmeas (h.mono fun ω hω => hω.2.2.2)

theorem cert_band_consistency : Claims.cert_band_consistency := by
  intro K 𝒯 μ A S C O χ g gh Q T e EK xbar slack hC hCc hχ hg hgh hunif hunifh hO hSO hOC hdiff hQ hSc hAc hAcv
    hAint hAsupp hAS hT he hsq hslack η hη
  set E' := max EK 0 with hE'def
  have hE' : 0 ≤ E' := le_max_right _ _
  set ε := η / (2 * (E' + 1)) with hεdef
  have hε : 0 < ε := div_pos hη (by linarith)
  have hEε : E' * ε ≤ η / 2 := by
    rw [hεdef, mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have he' : ∀ t, ‖e t‖ ≤ E' := fun t => (he t).trans (le_max_left _ _)
  have hcont : ContinuousOn (gradient χ) S := fun u hu =>
    (continuousAt_gradient hC hCc hχ hO hOC hdiff (hSO hu)).continuousWithinAt
  have h1 := StatFormal.OTFD.Wave19a.subgrad_conv_unif K C g χ O S hC hCc hg hχ hunif hO hOC hdiff hSO hSc ε hε
  have h2 := StatFormal.OTFD.Wave19a.subgrad_conv_unif K C gh χ O S hC hCc hgh hχ hunifh hO hOC hdiff hSO hSc ε hε
  have h3 := hslack (η / 2) (by linarith)
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
  intro t
  have hTS : ∀ u ∈ S, ‖T n u - gradient χ u‖ ≤ ε := fun u hu => hn2 u hu (T n u) (hT n u hu)
  obtain ⟨r, s, hr, hs, hrs⟩ := StatFormal.Wave21b.cond_band_two_sided K 𝒯 μ (fun _ => A) S (gradient χ) (T n) e 0 ε E'
    hcont hTS he' (fun _ _ _ => ⟨hAc, hAcv, hAint, hAsupp, hAS⟩) 1 one_pos (by norm_num) t (e t) (by simp)
  have hrQ : hPop μ A Q (e t) = r :=
    (hPop_congr (ae_restrict_eq_grad hAc.isClosed.measurableSet (hAS.trans hSO) hQ) (e t)).trans hr
  refine ⟨r, hrQ, ?_⟩
  have hgc : ContinuousOn (fun u => ⟪e t, gradient χ u⟫) A := continuousOn_const.inner (hcont.mono hAS)
  have hfs := (StatFormal.Gaps1.full_support_region K μ A hAc.isClosed hAcv hAint hAsupp).2.2.2 _ hgc
  have hsup : supSub C A (g n) (e t) ≤ ((r + E' * ε : ℝ) : EReal) := by
    refine iSup₂_le fun u hu => iSup₂_le fun ξ hξ => ?_
    have hξ' := hn1 u (hAS hu) ξ hξ
    have hle : ((⟪e t, gradient χ u⟫ : ℝ) : EReal) ≤ (r : EReal) := by
      rw [← hr]
      change _ ≤ essSup (fun u => ((⟪e t, gradient χ u⟫ : ℝ) : EReal)) (μ.restrict A)
      rw [hfs]
      exact le_iSup₂_of_le u hu le_rfl
    have hle' : ⟪e t, gradient χ u⟫ ≤ r := EReal.coe_le_coe_iff.1 hle
    have hi : ⟪e t, ξ⟫ - ⟪e t, gradient χ u⟫ ≤ ‖e t‖ * ‖ξ - gradient χ u‖ := by
      rw [← inner_sub_right]; exact real_inner_le_norm _ _
    have hb : ‖e t‖ * ‖ξ - gradient χ u‖ ≤ E' * ε := mul_le_mul (he' t) hξ' (norm_nonneg _) hE'
    exact EReal.coe_le_coe_iff.2 (by linarith)
  obtain ⟨hlo, hhi⟩ := hsq n t
  rw [hs] at hlo
  have hlo' : s ≤ xbar n t := EReal.coe_le_coe_iff.1 hlo
  have hhi' : xbar n t ≤ r + E' * ε + slack n t := by
    have := hhi.trans (add_le_add_left hsup _)
    rw [← EReal.coe_add] at this; exact EReal.coe_le_coe_iff.1 this
  have hrs' := (abs_le.1 hrs).1
  have := hn3 t
  rw [abs_le]; constructor <;> nlinarith

lemma ereal_sub_le_aux (m η : ℝ) {h s : EReal} (hle : h ≤ s + η) :
    (m : EReal) - s ≤ (m : EReal) - h + η := by
  induction s using EReal.rec with
  | bot =>
    have : h = ⊥ := by simpa using hle
    subst this; simp
  | top => simp
  | coe s =>
    induction h using EReal.rec with
    | bot => simp
    | top => exact absurd hle (by rw [← EReal.coe_add]; exact not_le.2 (EReal.coe_lt_top _))
    | coe h =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hle
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith

theorem cond_test_coverage_potentials : Claims.cond_test_coverage_potentials := by
  intro K 𝒯 μ _ U A χ g Q Qn m e Ue Le R EK p κ hac hU hUc hχ hg hunif hQ hQn hQm hA hR he hp hκ hband
  have hone := cond_band_one_sided_potentials K 𝒯 μ U A χ g Q Qn e R EK hac hU hUc hχ hg hunif hQ hQn hA hR he
  refine StatFormal.Wave21b.cond_test_coverage_inflated K 𝒯 μ Q A p κ m e Ue Le hQm hA hp hκ fun η hη => ?_
  filter_upwards [hone η hη] with n hn
  intro t
  obtain ⟨h1, h2⟩ := hn t
  obtain ⟨hU1, hL1⟩ := hband n t
  refine ⟨?_, hL1.trans (ereal_sub_le_aux (m t) η h2)⟩
  calc (m t : EReal) + hPop μ A Q (e t) ≤ (m t : EReal) + (supE A (Qn n) (e t) + η) := add_le_add le_rfl h1
    _ = (m t : EReal) + supE A (Qn n) (e t) + η := (add_assoc _ _ _).symm
    _ ≤ Ue n t + η := add_le_add hU1 le_rfl

end StatFormal.OTFD.Wave22b
