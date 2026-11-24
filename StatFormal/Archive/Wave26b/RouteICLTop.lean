import StatFormal.Archive.Wave26b.RouteICLObj
import StatFormal.Archive.Wave20a.RoutePhiKL
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Route — ICL `cor:iid-consistency`, the pool-to-population approximation (untrusted)

* `R^iid` is weakly continuous on `𝒫(𝒵)` (`μ ↦ μ^{⊗M}` is continuous, Mathlib `ProbabilityMeasure.continuous_pi`;
  dominated convergence in the query; `Φ` by the frozen `lem:phi`(iv)), `𝒫(supp P₀)` is closed in the compact
  `𝒫(𝒵)` (Prokhorov), so `R^{iid⋆}` is attained at some `μ⋆`.
* An i.i.d. `P₀` pool lies in `supp P₀` and is eventually `δ`-dense in it for every `δ > 0`, almost surely
  (finite ball covers centred in the support; each ball is hit with probability one).
* Quantisation: on a `δ`-dense pool, the cells `A_i = B(z_i, δ) \ ⋃_{j<i} B(z_j, δ)` give weights
  `w_i = μ⋆(A_i)` with `|∫ f dμ_w − ∫ f dμ⋆| ≤ η` whenever `f` oscillates by at most `η` on `δ`-balls; hence
  `μ_w → μ⋆` weakly and `min_w R^iid(μ_w) → R^{iid⋆}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave26b

open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.ICL.Joint (ProbVec)

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-! ### Weak continuity and the minimiser -/

lemma continuous_riskIid {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} {BL Kmin Kmax : ℝ} (lcov : ℝ)
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] :
    Continuous fun μ : ProbabilityMeasure Z => riskIid L Kk lcov P₀ (μ : Measure Z) := by
  unfold riskIid
  refine Continuous.add ?_ (continuous_const.mul ?_)
  · -- the risk term
    have hpi : Continuous fun μ : ProbabilityMeasure Z => ProbabilityMeasure.pi fun _ : Fin M => μ :=
      ProbabilityMeasure.continuous_pi.comp (continuous_pi fun _ => continuous_id)
    have hz : ∀ z, Continuous fun μ : ProbabilityMeasure Z => gIid L (μ : Measure Z) z := by
      intro z
      have hf : Continuous fun t : Fin M → Z => L z t := hL.comp (Continuous.prodMk continuous_const continuous_id)
      have := (ProbabilityMeasure.continuous_integral_continuousMap (X := Fin M → Z)
        (⟨fun t => L z t, hf⟩ : C(Fin M → Z, ℝ))).comp hpi
      exact this
    refine continuous_of_dominated (bound := fun _ => BL) (fun μ => ?_) (fun μ => ?_) (integrable_const _)
      (Eventually.of_forall hz)
    · exact (continuous_gIid hL hLb (μ : Measure Z)).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (gIid_mem hL hLb (μ : Measure Z) z).1]
      exact (gIid_mem hL hLb (μ : Measure Z) z).2
  · exact (StatFormal.Wave20a.phi_continuous Z Kk Kmin Kmax P₀
      ⟨hKmin, hK.measurable, hKb⟩ hK).1

lemma support_nonempty (P₀ : Measure Z) [IsProbabilityMeasure P₀] : P₀.support.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have := P₀.measure_compl_support
  rw [h, Set.compl_empty, measure_univ] at this
  exact one_ne_zero this

/-- The probability laws carried by `supp P₀` form a closed set in `𝒫(𝒵)`. -/
lemma isClosed_carried (P₀ : Measure Z) [IsProbabilityMeasure P₀] :
    IsClosed {μ : ProbabilityMeasure Z | (μ : Measure Z) P₀.supportᶜ = 0} := by
  set S := P₀.support with hS
  have hSc : IsClosed S := Measure.isClosed_support
  have hSne : S.Nonempty := support_nonempty P₀
  set g : C(Z, ℝ) := ⟨fun x => Metric.infDist x S, Metric.continuous_infDist_pt S⟩ with hg
  have hset : {μ : ProbabilityMeasure Z | (μ : Measure Z) Sᶜ = 0} =
      (fun μ : ProbabilityMeasure Z => ∫ x, g x ∂(μ : Measure Z)) ⁻¹' {0} := by
    ext μ
    show _ ↔ ∫ x, g x ∂(μ : Measure Z) = 0
    have hint : Integrable (fun x => g x) (μ : Measure Z) := integrable_of_continuous_bdd _ g.continuous
    show (μ : Measure Z) Sᶜ = 0 ↔ _
    rw [integral_eq_zero_iff_of_nonneg (f := fun x => g x) (fun x => Metric.infDist_nonneg) hint]
    have : {x | g x ≠ 0} = Sᶜ := by
      ext x
      simp only [mem_setOf_eq, mem_compl_iff, hg, ContinuousMap.coe_mk]
      rw [hSc.notMem_iff_infDist_pos hSne]
      exact ⟨fun h => lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h), fun h => h.ne'⟩
    rw [Filter.EventuallyEq, ae_iff]
    simp only [Pi.zero_apply]
    rw [this]
  rw [hset]
  exact (isClosed_singleton).preimage (ProbabilityMeasure.continuous_integral_continuousMap g)

lemma exists_minimiser {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} {BL Kmin Kmax : ℝ} (lcov : ℝ)
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] :
    ∃ μs : ProbabilityMeasure Z, (μs : Measure Z) P₀.supportᶜ = 0 ∧
      IsLeast {r | ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ μ P₀.supportᶜ = 0 ∧ r = riskIid L Kk lcov P₀ μ}
        (riskIid L Kk lcov P₀ (μs : Measure Z)) := by
  set C := {μ : ProbabilityMeasure Z | (μ : Measure Z) P₀.supportᶜ = 0} with hC
  have hCc : IsCompact C := (isClosed_carried P₀).isCompact
  have hCne : C.Nonempty := ⟨⟨P₀, inferInstance⟩, P₀.measure_compl_support⟩
  obtain ⟨μs, hμs, hmin⟩ := hCc.exists_isMinOn hCne
    (continuous_riskIid lcov hL hLb hK hKmin hKb P₀).continuousOn
  refine ⟨μs, hμs, ⟨⟨μs, inferInstance, hμs, rfl⟩, ?_⟩⟩
  rintro _ ⟨μ, hμ, hμS, rfl⟩
  exact hmin (show (⟨μ, hμ⟩ : ProbabilityMeasure Z) ∈ C from hμS)

/-! ### The almost-sure pool event -/

lemma ae_exists_mem {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {P₀ : Measure Z} [IsProbabilityMeasure P₀] {Zs : ℕ → Ω₀ → Z}
    (hm : ∀ i, Measurable (Zs i)) (hind : iIndepFun Zs Q) (hlaw : ∀ i, Q.map (Zs i) = P₀) {U : Set Z}
    (hU : MeasurableSet U) (hpos : 0 < P₀ U) : ∀ᵐ ω ∂Q, ∃ i, Zs i ω ∈ U := by
  rw [ae_iff]
  have hlt : P₀ Uᶜ < 1 := by
    rw [prob_compl_eq_one_sub hU]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  have hbound : ∀ N : ℕ, Q {ω | ¬∃ i, Zs i ω ∈ U} ≤ P₀ Uᶜ ^ N := by
    intro N
    calc Q {ω | ¬∃ i, Zs i ω ∈ U} ≤ Q (⋂ i ∈ Finset.range N, Zs i ⁻¹' Uᶜ) := by
          refine measure_mono fun ω hω => ?_
          simp only [mem_iInter, Set.mem_preimage, mem_compl_iff]
          intro i _ hi
          exact hω ⟨i, hi⟩
      _ = ∏ i ∈ Finset.range N, Q (Zs i ⁻¹' Uᶜ) :=
          hind.measure_inter_preimage_eq_mul _ fun i _ => hU.compl
      _ = P₀ Uᶜ ^ N := by
          rw [Finset.prod_congr rfl fun i _ => by rw [← Measure.map_apply (hm i) hU.compl, hlaw i]]
          simp
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hbound) bot_le

lemma exists_bound_of_finite {ι : Type*} {t : Set ι} (ht : t.Finite) {p : ι → ℕ → Prop}
    (h : ∀ c ∈ t, ∃ i, p c i) : ∃ N, ∀ c ∈ t, ∃ i < N, p c i := by
  classical
  choose! F hF using h
  refine ⟨ht.toFinset.sup F + 1, fun c hc => ⟨F c, ?_, hF c hc⟩⟩
  have := Finset.le_sup (f := F) (ht.mem_toFinset.2 hc)
  omega

/-- The pool event: almost surely every pool point lies in `supp P₀`, and for every `δ > 0` the first `N` points
form a `δ`-net of `supp P₀` for some `N`. -/
lemma ae_pool_dense {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {P₀ : Measure Z} [IsProbabilityMeasure P₀] {Zs : ℕ → Ω₀ → Z}
    (hm : ∀ i, Measurable (Zs i)) (hind : iIndepFun Zs Q) (hlaw : ∀ i, Q.map (Zs i) = P₀) :
    ∀ᵐ ω ∂Q, (∀ i, Zs i ω ∈ P₀.support) ∧
      ∀ δ > 0, ∃ N, ∀ x ∈ P₀.support, ∃ i < N, dist x (Zs i ω) < δ := by
  set S := P₀.support with hS
  have hSk : IsCompact S := Measure.isClosed_support.isCompact
  have hcov : ∀ k : ℕ, ∃ t ⊆ S, t.Finite ∧ S ⊆ ⋃ x ∈ t, Metric.ball x (1 / (k + 1)) :=
    fun k => finite_cover_balls_of_compact hSk (by positivity)
  choose t htS htf htcov using hcov
  have hin : ∀ᵐ ω ∂Q, ∀ i, Zs i ω ∈ S := by
    rw [ae_all_iff]
    intro i
    have : Q (Zs i ⁻¹' Sᶜ) = 0 := by
      rw [← Measure.map_apply (hm i) Measure.isClosed_support.measurableSet.compl, hlaw i]
      exact P₀.measure_compl_support
    rw [ae_iff]
    exact this
  have hhit : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ c ∈ t k, ∃ i, Zs i ω ∈ Metric.ball c (1 / (k + 1)) := by
    rw [ae_all_iff]
    intro k
    rw [(htf k).eventually_all]
    intro c hc
    refine ae_exists_mem hm hind hlaw measurableSet_ball ?_
    exact (Measure.mem_support_iff_forall c).1 (htS k hc) _ (Metric.ball_mem_nhds c (by positivity))
  filter_upwards [hin, hhit] with ω h1 h2
  refine ⟨h1, fun δ hδ => ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / δ)
  have hk' : 2 / ((k : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hk
    nlinarith
  obtain ⟨N, hN⟩ := exists_bound_of_finite (htf k) (h2 k)
  refine ⟨N, fun x hx => ?_⟩
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (htcov k hx)
  obtain ⟨i, hi, hic⟩ := hN c hc
  refine ⟨i, hi, ?_⟩
  have := dist_triangle x c (Zs i ω)
  rw [Metric.mem_ball] at hxc hic
  rw [dist_comm] at hic
  have : dist x (Zs i ω) < 2 / ((k : ℝ) + 1) := by
    have h2' : 2 / ((k : ℝ) + 1) = 1 / (k + 1) + 1 / (k + 1) := by ring
    linarith
  linarith

/-! ### Quantisation on a dense pool -/

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] in
lemma measurableSet_disjointed_fin {N : ℕ} {f : Fin N → Set Z} (hf : ∀ i, MeasurableSet (f i)) (i : Fin N) :
    MeasurableSet (disjointed f i) := by
  unfold disjointed
  refine (hf i).diff ?_
  rw [Finset.sup_set_eq_biUnion]
  exact Finset.measurableSet_biUnion _ fun j _ => hf j

lemma exists_pool_weights (μ : Measure Z) [IsProbabilityMeasure μ] {S : Set Z} (hμS : μ Sᶜ = 0) {N : ℕ}
    (z : Fin N → Z) {δ : ℝ} (hcov : ∀ x ∈ S, ∃ i, dist x (z i) < δ) :
    ∃ w : Fin N → ℝ, ProbVec w ∧ ∀ f : Z → ℝ, Continuous f → ∀ η : ℝ,
      (∀ x y, dist x y < δ → |f x - f y| ≤ η) → |∫ x, f x ∂(poolLaw z w) - ∫ x, f x ∂μ| ≤ η := by
  classical
  set B : Fin N → Set Z := fun i => Metric.ball (z i) δ with hB
  set A : Fin N → Set Z := disjointed B with hA
  have hAm : ∀ i, MeasurableSet (A i) := measurableSet_disjointed_fin fun i => measurableSet_ball
  have hAd : Pairwise (Function.onFun Disjoint A) := disjoint_disjointed B
  have hAB : ⋃ i, A i = ⋃ i, B i := iUnion_disjointed
  have hfull : μ (⋃ i, A i)ᶜ = 0 := by
    refine measure_mono_null ?_ hμS
    intro x hx
    rw [mem_compl_iff] at hx ⊢
    intro hxS
    obtain ⟨i, hi⟩ := hcov x hxS
    exact hx (hAB ▸ mem_iUnion.2 ⟨i, Metric.mem_ball.2 hi⟩)
  have hunion : μ (⋃ i, A i) = 1 := by
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hAm)]
    exact hfull
  set w : Fin N → ℝ := fun i => μ.real (A i) with hw
  have hwsum : ∑ i, w i = 1 := by
    have := measure_iUnion (μ := μ) hAd hAm
    rw [tsum_fintype, hunion] at this
    simp only [hw, Measure.real]
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _), ← this, ENNReal.toReal_one]
  have hw0 : ∀ i, 0 ≤ w i := fun i => measureReal_nonneg
  refine ⟨w, ⟨hw0, hwsum⟩, fun f hf η hη => ?_⟩
  have hfi : Integrable f μ := integrable_of_continuous_bdd μ hf
  have h1 : ∫ x, f x ∂μ = ∑ i, ∫ x in A i, f x ∂μ := by
    rw [← integral_iUnion_fintype hAm hAd fun i => hfi.integrableOn]
    have hae : ∀ᵐ x ∂μ, x ∈ ⋃ i, A i := mem_ae_iff.2 hfull
    rw [Measure.restrict_eq_self_of_ae_mem hae]
  have h2 : ∫ x, f x ∂(poolLaw z w) = ∑ i, ∫ x in A i, f (z i) ∂μ := by
    rw [integral_poolLaw z hw0 hf.measurable]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setIntegral_const, smul_eq_mul]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  have hcell : ∀ i, |∫ x in A i, f (z i) ∂μ - ∫ x in A i, f x ∂μ| ≤ η * w i := by
    intro i
    rw [← integral_sub (integrable_const _) hfi.integrableOn]
    have hb : ∀ x ∈ A i, ‖f (z i) - f x‖ ≤ η := by
      intro x hx
      have hxB : x ∈ B i := disjointed_subset B i hx
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hη x (z i) (Metric.mem_ball.1 hxB)
    have := norm_setIntegral_le_of_norm_le_const (measure_lt_top μ (A i)) hb
    rw [Real.norm_eq_abs] at this
    calc _ ≤ η * μ.real (A i) := this
      _ = η * w i := rfl
  calc |∑ i, (∫ x in A i, f (z i) ∂μ - ∫ x in A i, f x ∂μ)|
      ≤ ∑ i, |∫ x in A i, f (z i) ∂μ - ∫ x in A i, f x ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, η * w i := Finset.sum_le_sum fun i _ => hcell i
    _ = η := by rw [← Finset.mul_sum, hwsum, mul_one]

end StatFormal.Wave26b
