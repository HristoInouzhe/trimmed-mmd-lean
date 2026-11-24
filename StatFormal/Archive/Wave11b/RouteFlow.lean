import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.Wave9b.RoutePareto

/-!
# Route: SB `thm:flow` (i)–(iii), and (iv) with the ODE as a hypothesis

(i)–(iii) are the certified `pareto_flow`, `pareto_weak` (wave 9b) transported to the random-variable form
`𝓛(· | S = s)`; optimality is Tau Ceti's `isOptimalCoupling_quantileCoupling` through `graphPlan_flowMap`.
(iv): a non-decreasing `Φ` with `Φ_#R = μ` satisfies `F_μ(Φ(u)) ≥ F_R(u)`, hence `Ψ ≤ Φ` on `{0 < F_R < 1}`;
two random variables with `Ψ ≤ Φ` and the same law agree a.s. (compare `{· ≤ q}`, `q ∈ ℚ`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set Filter
open scoped ENNReal NNReal

namespace StatFormal.Wave11b

open StatFormal.Wave9b

theorem flow_mixture_prob : Claims.flow_mixture_prob := by
  intro ε t π hπ
  unfold StatFormal.Wave4b.endpointMixture1
  infer_instance

lemma condLaw_isProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Ω → Fin 2} {s : Fin 2} (hs : P (S ⁻¹' {s}) ≠ 0) {W : Ω → ℝ} (hW : Measurable W) :
    IsProbabilityMeasure (condLaw P S s W) := by
  have := cond_isProbabilityMeasure (μ := P) hs
  unfold condLaw; infer_instance

theorem flow_push : Claims.flow_push := by
  intro Ω _ P S U s μ hP hS hU hs hμ hR
  have := condLaw_isProb hs hU
  have h := (pareto_flow (condLaw P S s U) μ inferInstance hμ hR).1
  refine Eq.trans ?_ h
  change (P[|S ⁻¹' {s}]).map (flowMap (condLaw P S s U) μ ∘ U) = ((P[|S ⁻¹' {s}]).map U).map _
  rw [Measure.map_map (measurable_flowMap _ _) hU]

lemma cdf_mem_Ioo_ae (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R] :
    R {u | 0 < cdf R u ∧ cdf R u < 1}ᶜ = 0 := by
  have hm : Measurable (cdf R) := (cdf R).mono.measurable
  have hset : {u | 0 < cdf R u ∧ cdf R u < 1}ᶜ = cdf R ⁻¹' (Ioo (0 : ℝ) 1)ᶜ := by
    ext u; simp [mem_Ioo]
  rw [hset, ← Measure.map_apply hm measurableSet_Ioo.compl, Measure.cdf_map_eq_volume_restrict,
    Measure.restrict_apply measurableSet_Ioo.compl]
  have hsub : (Ioo (0 : ℝ) 1)ᶜ ∩ Icc 0 1 ⊆ {0, 1} := by
    intro x ⟨hx1, hx2⟩
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hx1
    rcases hx1 with h | h
    · left; exact le_antisymm h hx2.1
    · right; exact le_antisymm hx2.2 h
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

theorem flow_monotone : Claims.flow_monotone := by
  intro R μ hR hRa
  refine ⟨?_, cdf_mem_Ioo_ae R⟩
  rintro u ⟨hu0, hu1⟩ v ⟨hv0, hv1⟩ huv
  exact Measure.monotoneOn_quantile μ ⟨hu0, hu1⟩ ⟨hv0, hv1⟩ ((cdf R).mono huv)

theorem flow_optimal : Claims.flow_optimal := by
  intro R μ hR hμ hRa
  rw [graphPlan_flowMap R μ]
  exact Measure.isOptimalCoupling_quantileCoupling R μ (by norm_num)

theorem flow_cost : Claims.flow_cost := by
  intro Ω _ P S U s μ hP hS hU hs hμ hR
  have := condLaw_isProb hs hU
  have h := (pareto_flow (condLaw P S s U) μ inferInstance hμ hR).2
  have hf : Measurable fun u : ℝ => edist u (flowMap (condLaw P S s U) μ u) ^ (2 : ℝ) :=
    (continuous_cost2.measurable).comp (measurable_id.prodMk (measurable_flowMap _ _))
  have e : ∫⁻ u, edist u (flowMap (condLaw P S s U) μ u) ^ (2 : ℝ) ∂(condLaw P S s U) =
      ∫⁻ ω, edist (U ω) (flowMap (condLaw P S s U) μ (U ω)) ^ (2 : ℝ) ∂(P[|S ⁻¹' {s}]) :=
    lintegral_map hf hU
  rw [← h, e]
  refine lintegral_congr fun ω => ?_
  rw [edist_comm]

theorem flow_minimal : Claims.flow_minimal := by
  intro Ω _ P S U V s μ hP hS hU hV hs hVμ
  set Pc := P[|S ⁻¹' {s}]
  have hUV : Measurable fun ω => (U ω, V ω) := hU.prodMk hV
  have hcpl : IsCoupling (Pc.map fun ω => (U ω, V ω)) (condLaw P S s U) μ := by
    refine ⟨?_, ?_⟩
    · rw [Measure.fst, Measure.map_map measurable_fst hUV]; rfl
    · rw [Measure.snd, Measure.map_map measurable_snd hUV, ← hVμ]; rfl
  refine (pareto_weak _ _ _ hcpl).trans_eq ?_
  unfold qcost
  rw [lintegral_map continuous_cost2.measurable hUV]
  refine lintegral_congr fun ω => ?_
  rw [edist_comm]

/-- Two real random variables with `f ≤ g` a.e. and the same law agree a.e. -/
lemma ae_eq_of_le_of_map_eq {R : Measure ℝ} [IsFiniteMeasure R] {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hle : f ≤ᵐ[R] g) (hmap : R.map f = R.map g) : f =ᵐ[R] g := by
  have hq : ∀ q : ℚ, R ({u | f u ≤ q} \ {u | g u ≤ q}) = 0 := by
    intro q
    have h1 : R {u | f u ≤ q} = R {u | g u ≤ q} := by
      have := congrArg (fun ν : Measure ℝ => ν (Iic (q : ℝ))) hmap
      rwa [Measure.map_apply hf measurableSet_Iic, Measure.map_apply hg measurableSet_Iic] at this
    have hsub : {u | g u ≤ q} ≤ᵐ[R] {u | f u ≤ q} := by
      filter_upwards [hle] with u hu h
      exact (hu.trans h : f u ≤ q)
    have heq : {u | g u ≤ q} =ᵐ[R] {u | f u ≤ q} :=
      ae_eq_of_ae_subset_of_measure_ge hsub h1.le
        (measurableSet_le hg measurable_const).nullMeasurableSet (measure_ne_top _ _)
    exact ae_le_set.mp heq.symm.le
  have hnull : R {u | f u < g u} = 0 := by
    refine measure_mono_null (fun u (hu : f u < g u) => ?_) (measure_iUnion_null hq)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu
    exact mem_iUnion.2 ⟨q, hq1.le, fun h : g u ≤ q => absurd hq2 (not_lt.2 h)⟩
  have hae : ∀ᵐ u ∂R, ¬ f u < g u := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hle, hae] with u h1 h2
  exact le_antisymm h1 (not_lt.1 h2)

theorem flow_ode_unique : Claims.flow_ode_unique := by
  intro R μ Φ hR hμ hRa hΦ hmap
  have hΦm : Measurable Φ := hΦ.measurable
  have hle : flowMap R μ ≤ᵐ[R] Φ := by
    have hG := cdf_mem_Ioo_ae R
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hG] with u hu
    simp only [mem_compl_iff, not_not, mem_ofPred_eq] at hu
    unfold flowMap
    rw [Measure.quantile_le_iff μ hu.1 hu.2, cdf_eq_real, cdf_eq_real, ← hmap,
      map_measureReal_apply hΦm measurableSet_Iic]
    exact measureReal_mono (fun v (hv : v ≤ u) => (hΦ hv : Φ v ≤ Φ u))
  have hmapΨ := (pareto_flow R μ hR hμ hRa).1
  exact (ae_eq_of_le_of_map_eq (measurable_flowMap R μ) hΦm hle (hmapΨ.trans hmap.symm)).symm

end StatFormal.Wave11b
