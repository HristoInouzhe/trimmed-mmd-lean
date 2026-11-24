import StatFormal.Archive.Wave23b.Statements
import StatFormal.Archive.OTFD.WaveL1.RoutePlanStab
import StatFormal.Archive.OTFD.Wave8b.RouteNaive
import StatFormal.Archive.OTFD.WaveL3.RouteHilbert
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Route — A `cor:convergent-references` (untrusted)

(a) The sieve map `T_K = ι_K F_K Π_K` is `P`-a.e. cyclically monotone in `H` (`⟨ι_K y, h⟩ = ⟨y, Π_K h⟩`) and pushes `P`
to `ι_K#ν_K`, carried by `B̄(0, M)` (`ι_K` is an isometry); the certified plan stability (WaveL1 `plan_stab_b_map`,
CONDITIONAL on `BrenierUniq`) gives `L²` convergence, and portmanteau on the closed ball gives `supp μ ⊆ B̄(0, M)`.
(b) Convergence in probability implies convergence in distribution (Mathlib); the limit is identified by (a) and
uniqueness of limits in probability.
Spherical references: a weak limit `μ` would satisfy `∫ g dμ = g(0)` for weakly continuous bounded `g` (certified
`naive_weak_tendsto`), hence `μ = δ₀` (separability), contradicting the certified `naive_norm_no_weak`.
Coherent truncations: `ι_K Π_K x → x` for a Hilbert basis, and dominated convergence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave23b

open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave8b (embed proj embLaw)
open StatFormal.OTFD.WaveL1 (LipNull BrenierUniq IsCMMapAE CycMon CMConc)

section Sieve
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma truncK_eq_proj (e : ℕ → H) (K : ℕ) : truncK e K = proj e K := rfl

lemma continuous_truncK (e : ℕ → H) (K : ℕ) : Continuous (truncK e K) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_const.inner continuous_id)

lemma truncK_sub (e : ℕ → H) (K : ℕ) (a b : H) : truncK e K (a - b) = truncK e K a - truncK e K b := by
  ext k; simp [truncK, inner_sub_right]

lemma cycMon_sieve (e : ℕ → H) (K : ℕ) (F : Euc K → Euc K) (S : Set (Euc K))
    (h : CycMon {z : Euc K × Euc K | z.1 ∈ S ∧ z.2 = F z.1}) :
    CycMon {z : H × H | z.1 ∈ truncK e K ⁻¹' S ∧ z.2 = embed e K (F (truncK e K z.1))} := by
  intro m z hz
  have hw : ∀ i, ((truncK e K (z i).1, F (truncK e K (z i).1)) : Euc K × Euc K) ∈
      {z : Euc K × Euc K | z.1 ∈ S ∧ z.2 = F z.1} := fun i => ⟨(hz i).1, rfl⟩
  have := h m (fun i => (truncK e K (z i).1, F (truncK e K (z i).1))) hw
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) this
  rw [(hz i).2, StatFormal.OTFD.Wave8b.inner_embed, ← truncK_eq_proj, truncK_sub]

end Sieve

theorem convref_a : Claims.convref_a := by
  intro H _ _ _ _ _ _ P μ e M ν F νH Fμ he hLip hνM hFm hFlaw hCM hνH hconv hFμm hBU
  have hT : ∀ K, Measurable fun x => embed e K (F K (truncK e K x)) := fun K =>
    (StatFormal.OTFD.Wave8b.continuous_embed e).measurable.comp ((hFm K).comp (continuous_truncK e K).measurable)
  have hlaw : ∀ K, (P : Measure H).map (fun x => embed e K (F K (truncK e K x))) = νH K := by
    intro K
    rw [hνH K, ← hFlaw K, Measure.map_map (hFm K) (continuous_truncK e K).measurable,
      Measure.map_map (StatFormal.OTFD.Wave8b.continuous_embed e).measurable
        ((hFm K).comp (continuous_truncK e K).measurable)]
    rfl
  have hball : ∀ K, (νH K : Measure H) (Metric.closedBall 0 M)ᶜ = 0 := by
    intro K
    rw [hνH K, Measure.map_apply (StatFormal.OTFD.Wave8b.continuous_embed e).measurable
      Metric.isClosed_closedBall.measurableSet.compl]
    have hsub : embed e K ⁻¹' (Metric.closedBall (0 : H) M)ᶜ ⊆ (Metric.closedBall 0 M)ᶜ := by
      intro z hz hzM
      apply hz
      simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right] at hzM ⊢
      rw [StatFormal.OTFD.Wave8b.norm_embed e he]
      exact hzM
    exact measure_mono_null hsub (hνM K)
  have hCM' : ∀ K, IsCMMapAE (P : Measure H) fun x => embed e K (F K (truncK e K x)) := by
    intro K
    obtain ⟨S, hS, hS0, hcyc⟩ := hCM K
    refine ⟨truncK e K ⁻¹' S, (continuous_truncK e K).measurable hS, ?_, cycMon_sieve e K (F K) S hcyc⟩
    rw [← preimage_compl, ← Measure.map_apply (continuous_truncK e K).measurable hS.compl, hS0]
  refine ⟨?_, StatFormal.OTFD.WaveL1.plan_stab_b_map H P μ Fμ M νH (fun K x => embed e K (F K (truncK e K x)))
    hLip hFμm hBU hconv hball hT hlaw hCM'⟩
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
    (Metric.isClosed_closedBall (x := (0 : H)) (ε := M))
  have h1 : ∀ K, (νH K : Measure H) (Metric.closedBall 0 M) = 1 := fun K => by
    rw [← prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet]; exact hball K
  simp only [h1, limsup_const] at hlim
  rw [prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet]
  exact le_antisymm prob_le_one hlim

theorem convref_b : Claims.convref_b := by
  intro H Ω _ _ _ _ _ _ _ Pr _ X Y e M ν F νH μY hX hY he hLip hνM hFm hFlaw hCM hνH hμY hconv
  set YK : ℕ → Ω → H := fun K ω => embed e K (F K (truncK e K (X ω))) with hYK
  have hYKm : ∀ K, Measurable (YK K) := fun K =>
    (StatFormal.OTFD.Wave8b.continuous_embed e).measurable.comp
      ((hFm K).comp ((continuous_truncK e K).measurable.comp hX))
  have hlaw : ∀ K, Pr.map (YK K) = (νH K : Measure H) := by
    intro K
    rw [hνH K, ← hFlaw K, Measure.map_map (hFm K) (continuous_truncK e K).measurable,
      Measure.map_map ((hFm K).comp (continuous_truncK e K).measurable) hX,
      Measure.map_map (StatFormal.OTFD.Wave8b.continuous_embed e).measurable
        ((hFm K).comp (continuous_truncK e K).measurable |>.comp hX)]
    rfl
  have hdist := hconv.tendstoInDistribution fun K => (hYKm K).aemeasurable
  have htend : Tendsto νH atTop (𝓝 μY) := by
    have h1 := hdist.tendsto
    have e1 : (fun K => (⟨Pr.map (YK K), inferInstance⟩ : ProbabilityMeasure H)) = νH := by
      funext K; exact Subtype.ext (hlaw K)
    have e2 : (⟨Pr.map Y, inferInstance⟩ : ProbabilityMeasure H) = μY := Subtype.ext hμY.symm
    rw [e1, e2] at h1
    exact h1
  refine ⟨htend, fun Fμ hFμm hBU => ?_⟩
  set P : ProbabilityMeasure H := ⟨Pr.map X, inferInstance⟩ with hP
  have ha := convref_a H P μY e M ν F νH Fμ he hLip hνM hFm hFlaw hCM hνH htend hFμm hBU
  have hL2 : Tendsto (fun K => ∫⁻ ω, ‖YK K ω - Fμ (X ω)‖ₑ ^ 2 ∂Pr) atTop (𝓝 0) := by
    refine ha.2.congr fun K => ?_
    show ∫⁻ x, ‖embed e K (F K (truncK e K x)) - Fμ x‖ₑ ^ 2 ∂(Pr.map X) = _
    rw [lintegral_map _ hX]
    exact (((StatFormal.OTFD.Wave8b.continuous_embed e).measurable.comp
      ((hFm K).comp (continuous_truncK e K).measurable)).sub hFμm).enorm.pow_const 2
  have hmeasF : TendstoInMeasure Pr YK atTop (fun ω => Fμ (X ω)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ?_
    have : ∀ K, eLpNorm (YK K - fun ω => Fμ (X ω)) 2 Pr = (∫⁻ ω, ‖YK K ω - Fμ (X ω)‖ₑ ^ 2 ∂Pr) ^ (1 / 2 : ℝ) := by
      intro K
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := YK K - fun ω => Fμ (X ω)) two_ne_zero
        ENNReal.ofNat_ne_top ((hYKm K).sub (hFμm.comp hX)).aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat, Pi.sub_apply]
      congr 1
      refine lintegral_congr fun ω => ?_
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    simp_rw [this]
    have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    exact hc.comp hL2
  exact tendstoInMeasure_ae_unique hconv hmeasF

/-! ### Unconditional (a), (b): `BrenierUniq` from the certified WaveL3 `brenier_uniq_H_bdd` -/

/-- Portmanteau on the closed ball: a weak limit of laws carried by `B̄(0, M)` is carried by it. -/
lemma support_of_tendsto {H : Type} [NormedAddCommGroup H] [MeasurableSpace H] [OpensMeasurableSpace H]
    {M : ℝ} {νH : ℕ → ProbabilityMeasure H} {μ : ProbabilityMeasure H} (hconv : Tendsto νH atTop (𝓝 μ))
    (hball : ∀ K, (νH K : Measure H) (Metric.closedBall 0 M)ᶜ = 0) :
    (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 := by
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
    (Metric.isClosed_closedBall (x := (0 : H)) (ε := M))
  have h1 : ∀ K, (νH K : Measure H) (Metric.closedBall 0 M) = 1 := fun K => by
    rw [← prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet]; exact hball K
  simp only [h1, limsup_const] at hlim
  rw [prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet]
  exact le_antisymm prob_le_one hlim

lemma embLaw_ball {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    {e : ℕ → H} (he : Orthonormal ℝ e) {M : ℝ} {ν : ∀ K, Measure (Euc K)} {νH : ℕ → ProbabilityMeasure H}
    (hνM : ∀ K, ν K (Metric.closedBall 0 M)ᶜ = 0) (hνH : ∀ K, (νH K : Measure H) = (ν K).map (embed e K)) :
    ∀ K, (νH K : Measure H) (Metric.closedBall 0 M)ᶜ = 0 := by
  intro K
  rw [hνH K, Measure.map_apply (StatFormal.OTFD.Wave8b.continuous_embed e).measurable
    Metric.isClosed_closedBall.measurableSet.compl]
  have hsub : embed e K ⁻¹' (Metric.closedBall (0 : H) M)ᶜ ⊆ (Metric.closedBall 0 M)ᶜ := by
    intro z hz hzM
    apply hz
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right] at hzM ⊢
    rw [StatFormal.OTFD.Wave8b.norm_embed e he]
    exact hzM
  exact measure_mono_null hsub (hνM K)

theorem convref_a_uncond : Claims.convref_a_uncond := by
  intro H _ _ _ _ _ _ P μ e M ν F νH Fμ he hLip hP1 hνM hFm hFlaw hCM hνH hconv hFμm hFμlaw hFμcm
  have hsupp := support_of_tendsto hconv (embLaw_ball he hνM hνH)
  exact convref_a H P μ e M ν F νH Fμ he hLip hνM hFm hFlaw hCM hνH hconv hFμm
    (StatFormal.OTFD.WaveL3.brenier_uniq_H_bdd H P μ Fμ M hLip hP1 hsupp hFμm hFμlaw hFμcm)

theorem convref_b_uncond : Claims.convref_b_uncond := by
  intro H Ω _ _ _ _ _ _ _ Pr _ X Y e M ν F νH μY hX hY he hLip hP1 hνM hFm hFlaw hCM hνH hμY hconv
  obtain ⟨htend, hid⟩ := convref_b H Ω Pr X Y e M ν F νH μY hX hY he hLip hνM hFm hFlaw hCM hνH hμY hconv
  refine ⟨htend, fun Fμ hFμm hFμlaw hFμcm => hid Fμ hFμm ?_⟩
  have hsupp := support_of_tendsto htend (embLaw_ball he hνM hνH)
  exact StatFormal.OTFD.WaveL3.brenier_uniq_H_bdd H ⟨Pr.map X, inferInstance⟩ μY Fμ M hLip hP1 hsupp hFμm
    hFμlaw hFμcm

section Weak
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma weak_inner_cont (h : H) : Continuous fun y : WeakSpace ℝ H => ⟪h, (toWeakSpace ℝ H).symm y⟫ := by
  exact WeakBilin.eval_continuous (topDualPairing ℝ H).flip (innerSL ℝ h)

end Weak

theorem convref_spherical : Claims.convref_spherical := by
  intro H _ _ _ _ _ _ e L c C he hc hcL hC hCL
  rintro ⟨μ, hμ, hlim⟩
  have hweak := StatFormal.OTFD.Wave8b.naive_weak_tendsto H e L c he hc hcL
  have hval : ∀ g : H →ᵇ ℝ, Continuous (fun y : WeakSpace ℝ H => g ((toWeakSpace ℝ H).symm y)) →
      ∫ x, g x ∂μ = g 0 := fun g hg =>
    tendsto_nhds_unique (hlim g) (hweak g hg ⟨‖g‖, fun x => by
      simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x⟩)
  have hcoord : ∀ h : H, μ {x | ⟪h, x⟫ ≠ 0} = 0 := by
    intro h
    have hn : ∀ n : ℕ, μ {x | 1 / ((n : ℝ) + 1) ≤ |⟪h, x⟫|} = 0 := by
      intro n
      set g : H →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => min 1 (((n : ℝ) + 1) * |⟪h, x⟫|)) (by fun_prop) 1 (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]; exact min_le_left _ _)
        with hg
      have hgw : Continuous (fun y : WeakSpace ℝ H => g ((toWeakSpace ℝ H).symm y)) := by
        simp only [hg, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        have := weak_inner_cont h
        fun_prop
      have h0 := hval g hgw
      simp only [hg, BoundedContinuousFunction.coe_ofNormedAddCommGroup, inner_zero_right, abs_zero,
        mul_zero, min_eq_right zero_le_one] at h0
      have hint : Integrable (fun x => min 1 (((n : ℝ) + 1) * |⟪h, x⟫|)) μ :=
        Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]; exact min_le_left _ _)
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => le_min zero_le_one (by positivity)) hint).1 h0
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
      simp only [mem_setOf_eq, Pi.zero_apply] at hx ⊢
      intro hzero
      have : 1 ≤ ((n : ℝ) + 1) * |⟪h, x⟫| := by
        rw [div_le_iff₀ (by positivity)] at hx; linarith
      rw [min_eq_left this] at hzero
      exact one_ne_zero hzero
    have hU : {x | ⟪h, x⟫ ≠ 0} = ⋃ n : ℕ, {x | 1 / ((n : ℝ) + 1) ≤ |⟪h, x⟫|} := by
      ext x
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 hx)
        exact ⟨n, hn.le⟩
      · rintro ⟨n, hn⟩ h0
        rw [h0, abs_zero] at hn
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [hU]
    exact measure_iUnion_null hn
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  have hzero : μ {x | x ≠ 0} = 0 := by
    have hsub : {x : H | x ≠ 0} ⊆ ⋃ n, {x | ⟪d n, x⟫ ≠ 0} := by
      intro x hx
      obtain ⟨n, hn⟩ := hd.exists_dist_lt x (norm_pos_iff.2 hx)
      refine mem_iUnion.2 ⟨n, fun h0 => ?_⟩
      have h1 : ⟪x, x⟫ = ⟪x - d n, x⟫ := by rw [inner_sub_left, real_inner_comm, h0, sub_zero]
      rw [real_inner_self_eq_norm_sq] at h1
      have h2 := real_inner_le_norm (x - d n) x
      rw [dist_eq_norm] at hn
      have hxpos := norm_pos_iff.2 hx
      nlinarith
    exact measure_mono_null hsub (measure_iUnion_null fun n => hcoord (d n))
  apply StatFormal.OTFD.Wave8b.naive_norm_no_weak H e L C he hC hCL
  intro f hf hB
  obtain ⟨B, hB⟩ := hB
  set g : H →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hf B (fun x => by
    rw [Real.norm_eq_abs]; exact hB x) with hg
  have h1 := hlim g
  have h2 : ∫ x, g x ∂μ = f 0 := by
    have hae : ∀ᵐ x ∂μ, x = 0 := by
      rw [ae_iff]; simpa using hzero
    have : (fun x => g x) =ᵐ[μ] fun _ => f 0 := by
      filter_upwards [hae] with x hx
      simp [hg, hx]
    rw [integral_congr_ae this, integral_const]
    simp
  rw [h2] at h1
  simpa [hg] using h1

theorem convref_coherent : Claims.convref_coherent := by
  intro H _ _ _ _ _ μ _ b f
  have hP : ∀ x, Tendsto (fun K => embed (fun k => b k) K (truncK (fun k => b k) K x)) atTop (𝓝 x) := by
    intro x
    have hs := (b.hasSum_repr x).tendsto_sum_nat
    refine hs.congr fun K => ?_
    simp only [embed, truncK, PiLp.toLp_apply, HilbertBasis.repr_apply_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => ⟪b k, x⟫ • b k) K]
  have hT : ∀ K, Measurable fun x => embed (fun k => b k) K (truncK (fun k => b k) K x) := fun K =>
    (StatFormal.OTFD.Wave8b.continuous_embed _).measurable.comp (continuous_truncK _ K).measurable
  have hmap : ∀ K, ∫ x, f x ∂((μ.map (truncK (fun k => b k) K)).map (embed (fun k => b k) K)) =
      ∫ x, f (embed (fun k => b k) K (truncK (fun k => b k) K x)) ∂μ := by
    intro K
    rw [Measure.map_map (StatFormal.OTFD.Wave8b.continuous_embed _).measurable (continuous_truncK _ K).measurable,
      integral_map ((StatFormal.OTFD.Wave8b.continuous_embed _).measurable.comp
        (continuous_truncK _ K).measurable).aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  simp_rw [hmap]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun K => (f.continuous.measurable.comp
    (hT K)).aestronglyMeasurable) (integrable_const _) (fun K => ae_of_all _ fun x => f.norm_coe_le_norm _)
    (ae_of_all _ fun x => (f.continuous.tendsto x).comp (hP x))

end StatFormal.Wave23b
