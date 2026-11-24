import StatFormal.Archive.Wave9b.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement
import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Route: SB `prop:pareto` (with `thm:flow`(i)–(iii))

1. For atomless `R`, the graph plan of `Ψ = q_μ ∘ F_R` is the monotone (quantile) coupling
   (`F_R ∘ q_R = id` a.e. on `(0,1)`, Tau Ceti `cdf_quantile_ae`), which is optimal
   (`isOptimalCoupling_quantileCoupling`): `Ψ_#R = μ` and the cost of `Ψ` is `W₂²`.
2. **Uniqueness of the optimal plan, in the form used.** An optimal plan `σ` of finite cost has a
   cyclically monotone support `S` (Tau Ceti), i.e. `(u − u')(y − y') ≥ 0` on `S`. The set `B` of
   `u` whose section of `S` has two points is countable (disjoint open intervals, one rational each),
   hence `R`-null, so `G = S ∩ (Bᶜ × ℝ)` is a `σ`-full set with at most one point per section.
3. A non-degenerate kernel cannot be carried by such a `G`; neither can the bridge plan, whose
   sections are translates of a Gaussian (atomless). Hence the strict inequality.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set Filter
open scoped ENNReal NNReal Topology

namespace StatFormal.Wave9b

lemma edist_rpow_two (a b : ℝ) : edist a b ^ (2 : ℝ) = ENNReal.ofReal ((a - b) ^ 2) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

lemma continuous_cost2 : Continuous fun z : ℝ × ℝ => edist z.1 z.2 ^ (2 : ℝ) :=
  (ENNReal.continuous_rpow_const).comp (continuous_fst.edist continuous_snd)

lemma w2_sq_eq_transportCost (R μ : Measure ℝ) :
    wassersteinEDist 2 R μ ^ (2 : ℝ) =
      transportCost (fun z : ℝ × ℝ => edist z.1 z.2 ^ (2 : ℝ)) R μ := by
  have := wassersteinEDist_rpow_eq_transportCost (X := ℝ) measurable_edist (p := 2) two_ne_zero
    ENNReal.ofNat_ne_top R μ
  simpa using this

theorem pareto_weak : Claims.pareto_weak := by
  intro R μ σ hσ
  rw [w2_sq_eq_transportCost]
  exact transportCost_le_lintegral hσ _

theorem pareto_atomless : Claims.pareto_atomless := by
  intro R ν π hπ hac
  refine ⟨fun a => ?_⟩
  rw [← hπ.measure_prod_univ (measurableSet_singleton a)]
  refine hac ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-! ### The flow map -/

lemma measurable_flowMap (R μ : Measure ℝ) : Measurable (flowMap R μ) :=
  (Measure.measurable_quantile μ).comp (cdf R).mono.measurable

lemma graphPlan_flowMap (R μ : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R] :
    graphPlan (flowMap R μ) R = Measure.quantileCoupling R μ := by
  have hR := Measure.map_quantile_volume_Ioo R
  have hq := Measure.measurable_quantile R
  rw [graphPlan_def, Measure.quantileCoupling_def]
  have e : R.map (fun x => (x, flowMap R μ x)) =
      ((volume.restrict (Ioo (0 : ℝ) 1)).map R.quantile).map (fun x => (x, flowMap R μ x)) := by
    rw [hR]
  rw [e, Measure.map_map (measurable_id'.prodMk (measurable_flowMap R μ)) hq]
  refine Measure.map_congr ?_
  have hae := Measure.cdf_quantile_ae R
  have hae' : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), cdf R (R.quantile u) = u :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hae
  filter_upwards [hae'] with u hu
  simp [flowMap, hu]

theorem pareto_flow : Claims.pareto_flow := by
  intro R μ hR hμ hRa
  have hg := graphPlan_flowMap R μ
  have hc := Measure.isCoupling_quantileCoupling R μ
  refine ⟨?_, ?_⟩
  · rw [← snd_graphPlan (measurable_flowMap R μ).aemeasurable, hg]
    exact hc.snd_eq
  · have hopt := Measure.isOptimalCoupling_quantileCoupling R μ (p := 2) (by norm_num)
    rw [w2_sq_eq_transportCost, ← hopt.lintegral_eq, ← hg, graphPlan_def,
      lintegral_map continuous_cost2.measurable
        (measurable_id'.prodMk (measurable_flowMap R μ))]

/-! ### Optimal plans are carried by graphs -/

lemma monotone_of_mem {σ : Measure (ℝ × ℝ)}
    (hcm : IsCyclicallyMonotone (fun z : ℝ × ℝ => edist z.1 z.2 ^ (2 : ℝ)) σ.support)
    {u y u' y' : ℝ} (h : (u, y) ∈ σ.support) (h' : (u', y') ∈ σ.support) :
    0 ≤ (u - u') * (y - y') := by
  have := hcm.add_le_add_swap h h'
  simp only [edist_rpow_two] at this
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  nlinarith

lemma opt_graph {R μ : Measure ℝ} [IsProbabilityMeasure R] [IsProbabilityMeasure μ]
    [NullSingletonClass R] {σ : Measure (ℝ × ℝ)} (hσ : IsCoupling σ R μ)
    (hW : wassersteinEDist 2 R μ ≠ ⊤) (heq : qcost σ = wassersteinEDist 2 R μ ^ (2 : ℝ)) :
    ∃ G : Set (ℝ × ℝ), MeasurableSet G ∧ σ Gᶜ = 0 ∧
      ∀ u y y', (u, y) ∈ G → (u, y') ∈ G → y = y' := by
  set c : ℝ × ℝ → ℝ≥0∞ := fun z => edist z.1 z.2 ^ (2 : ℝ)
  have hopt : IsOptimalCoupling c σ R μ :=
    { toIsCoupling := hσ
      lintegral_eq := by rw [← w2_sq_eq_transportCost]; exact heq }
  have hfin : transportCost c R μ ≠ ⊤ := by
    rw [← w2_sq_eq_transportCost]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hW
  have hcm := hopt.isCyclicallyMonotone_support continuous_cost2 hfin
  set S := σ.support
  set B := {u : ℝ | ∃ y y', y < y' ∧ (u, y) ∈ S ∧ (u, y') ∈ S}
  have key : ∀ u ∈ B, ∃ (y y' : ℝ) (q : ℚ), (u, y) ∈ S ∧ (u, y') ∈ S ∧ y < q ∧ (q : ℝ) < y' := by
    rintro u ⟨y, y', hyy, hy, hy'⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hyy
    exact ⟨y, y', q, hy, hy', hq1, hq2⟩
  choose! yl yr q hq using key
  have hinj : InjOn q B := by
    intro u₁ h₁ u₂ h₂ he
    by_contra hne
    have aux : ∀ {a b}, a ∈ B → b ∈ B → a < b → (q a : ℝ) < q b := fun {a b} ha hb hab => by
      obtain ⟨-, hra, -, hqa⟩ := hq a ha
      obtain ⟨hlb, -, hqb, -⟩ := hq b hb
      have hm := monotone_of_mem hcm hlb hra
      have : yr a ≤ yl b := by nlinarith
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd (congrArg (fun r : ℚ => (r : ℝ)) he) (aux h₁ h₂ hlt).ne
    · exact absurd (congrArg (fun r : ℚ => (r : ℝ)) he).symm (aux h₂ h₁ hlt).ne
  have hBc : B.Countable :=
    (mapsTo_univ q B).countable_of_injOn hinj countable_univ
  have hBm : MeasurableSet B := hBc.measurableSet
  have hRB : R B = 0 := hBc.measure_zero R
  have hSm : MeasurableSet S := by
    simpa using (Measure.isOpen_compl_support (μ := σ)).measurableSet.compl
  refine ⟨S ∩ (Bᶜ ×ˢ univ), hSm.inter (hBm.compl.prod .univ), ?_, ?_⟩
  · have hsub : (S ∩ (Bᶜ ×ˢ univ))ᶜ ⊆ Sᶜ ∪ (B ×ˢ univ) := by
      intro z hz
      by_cases hzS : z ∈ S
      · right; exact ⟨by by_contra h; exact hz ⟨hzS, h, trivial⟩, trivial⟩
      · left; exact hzS
    refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
    rw [Measure.measure_compl_support, hσ.measure_prod_univ hBm, hRB, add_zero]
  · rintro u y y' ⟨hy, hu, -⟩ ⟨hy', -, -⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hu ⟨y, y', hlt, hy, hy'⟩
    · exact hu ⟨y', y, hlt, hy', hy⟩

lemma eq_dirac_of_compl {m : Measure ℝ} [IsProbabilityMeasure m] {y : ℝ} (h : m {y}ᶜ = 0) :
    m = Measure.dirac y := by
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases hy : y ∈ s
  · rw [indicator_of_mem hy, Pi.one_apply]
    rw [← prob_compl_eq_zero_iff hs]
    exact measure_mono_null (compl_subset_compl.2 (singleton_subset_iff.2 hy)) h
  · rw [indicator_of_notMem hy]
    exact measure_mono_null (fun z hz => by rintro rfl; exact hy hz) h

lemma w2_ne_top {R μ : Measure ℝ} [IsProbabilityMeasure R] [IsProbabilityMeasure μ]
    (hR : HasFiniteMoment 2 R) (hμ : HasFiniteMoment 2 μ) : wassersteinEDist 2 R μ ≠ ⊤ :=
  (hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist hR).1 hμ

theorem pareto_strict : Claims.pareto_strict := by
  intro R μ K hR hμ hK hRa hR2 hμ2 hsnd ⟨A, hAm, hApos, hA⟩
  have hσ : IsCoupling (R ⊗ₘ K) R μ := ⟨Measure.fst_compProd R K, hsnd⟩
  have hW := w2_ne_top hR2 hμ2
  by_contra hlt
  push Not at hlt
  have heq := le_antisymm hlt (pareto_weak R μ _ hσ)
  obtain ⟨G, hGm, hG0, hGs⟩ := opt_graph hσ hW heq
  rw [Measure.compProd_apply hGm.compl] at hG0
  have hae : ∀ᵐ u ∂R, K u (Prod.mk u ⁻¹' Gᶜ) = 0 :=
    (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hGm.compl)).1 hG0
  have hnot : ∀ᵐ u ∂R, u ∉ A := by
    filter_upwards [hae] with u hu huA
    have hsec : MeasurableSet (Prod.mk u ⁻¹' G) := measurable_prodMk_left hGm
    rw [preimage_compl, prob_compl_eq_zero_iff hsec] at hu
    obtain ⟨y₀, hy₀⟩ : (Prod.mk u ⁻¹' G).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      rw [hem, measure_empty] at hu
      exact zero_ne_one hu
    refine hA u huA y₀ (eq_dirac_of_compl ?_)
    rw [← prob_compl_eq_zero_iff hsec] at hu
    exact measure_mono_null (show ({y₀}ᶜ : Set ℝ) ⊆ (Prod.mk u ⁻¹' G)ᶜ from
      fun y hy hyG => hy (hGs u y y₀ hyG hy₀)) hu
  exact hApos.ne' (measure_eq_zero_iff_ae_notMem.2 hnot)

/-! ### The bridge realisation -/

section Bridge

variable {ε t : ℝ} {R ν : Measure ℝ} {π : Measure (ℝ × ℝ)}

/-- The variance `εt(1−t)` of the bridge noise. -/
def bvar (ε t : ℝ) : ℝ≥0 := (ε * t * (1 - t)).toNNReal

/-- `(X₀, X₁, Z) ↦ (X₀, X_t)`. -/
def bmap (t : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (q.1.1, (1 - t) * q.1.1 + t * q.1.2 + q.2)

lemma measurable_bmap (t : ℝ) : Measurable (bmap t) := by unfold bmap; fun_prop

lemma stoPlan_eq (ε t : ℝ) (π : Measure (ℝ × ℝ)) :
    stoPlan ε t π = (π.prod (gaussianReal 0 (bvar ε t))).map (bmap t) := rfl

lemma map_fst_fst [IsProbabilityMeasure π] (hπ : IsCoupling π R ν) :
    (π.prod (gaussianReal 0 (bvar ε t))).map (fun q => q.1.1) = R := by
  rw [show (fun q : (ℝ × ℝ) × ℝ => q.1.1) = Prod.fst ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  exact hπ.fst_eq

lemma map_fst_snd [IsProbabilityMeasure π] (hπ : IsCoupling π R ν) :
    (π.prod (gaussianReal 0 (bvar ε t))).map (fun q => q.1.2) = ν := by
  rw [show (fun q : (ℝ × ℝ) × ℝ => q.1.2) = Prod.snd ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_snd measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  exact hπ.snd_eq

lemma stoPlan_coupling [IsProbabilityMeasure π] (hπ : IsCoupling π R ν) :
    IsCoupling (stoPlan ε t π) R (StatFormal.Wave4b.endpointMixture1 ε t π) := by
  constructor
  · rw [stoPlan_eq, Measure.fst, Measure.map_map measurable_fst (measurable_bmap t)]
    exact map_fst_fst hπ
  · have hL : Measurable fun p : ℝ × ℝ => (1 - t) * p.1 + t * p.2 := by fun_prop
    have hpm := Measure.map_prod_map π (gaussianReal 0 (bvar ε t)) hL measurable_id
    rw [Measure.map_id] at hpm
    rw [stoPlan_eq, Measure.snd, Measure.map_map measurable_snd (measurable_bmap t),
      StatFormal.Wave4b.endpointMixture1, Measure.conv]
    change _ = Measure.map _ ((Measure.map _ π).prod (gaussianReal 0 (bvar ε t)))
    rw [hpm, Measure.map_map (by fun_prop) (hL.prodMap measurable_id)]
    rfl

lemma qcost_stoPlan_lt_top [IsProbabilityMeasure π] (hπ : IsCoupling π R ν)
    (hR2 : HasFiniteMoment 2 R) (hν2 : HasFiniteMoment 2 ν) :
    qcost (stoPlan ε t π) < ∞ := by
  have hR : IsProbabilityMeasure R := hπ.fst_eq ▸ inferInstance
  have hν : IsProbabilityMeasure ν := hπ.snd_eq ▸ inferInstance
  set μP := π.prod (gaussianReal 0 (bvar ε t))
  have m1 : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => q.1.1) μP R :=
    ⟨by fun_prop, map_fst_fst hπ⟩
  have m2 : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => q.1.2) μP ν :=
    ⟨by fun_prop, map_fst_snd hπ⟩
  have m3 : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => q.2) μP (gaussianReal 0 (bvar ε t)) :=
    measurePreserving_snd
  have h1 : MemLp (fun q : (ℝ × ℝ) × ℝ => q.1.1) 2 μP := hR2.memLp_id.comp_measurePreserving m1
  have h2 : MemLp (fun q : (ℝ × ℝ) × ℝ => q.1.2) 2 μP := hν2.memLp_id.comp_measurePreserving m2
  have h3 : MemLp (fun q : (ℝ × ℝ) × ℝ => q.2) 2 μP :=
    (memLp_id_gaussianReal' 2 (by norm_num)).comp_measurePreserving m3
  have hD : MemLp (fun q : (ℝ × ℝ) × ℝ => t * q.1.1 - t * q.1.2 - q.2) 2 μP :=
    ((h1.const_mul t).sub (h2.const_mul t)).sub h3
  rw [qcost, stoPlan_eq, lintegral_map continuous_cost2.measurable (measurable_bmap t)]
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
    hD.eLpNorm_lt_top
  refine lt_of_eq_of_lt (lintegral_congr fun q => ?_) (by simpa using hlt)
  simp only [bmap, edist_eq_enorm_sub]
  rw [show q.1.1 - ((1 - t) * q.1.1 + t * q.1.2 + q.2) = t * q.1.1 - t * q.1.2 - q.2 by ring]
  simp

lemma stoPlan_strict (hε : 0 < ε) (ht : t ∈ Ioo (0 : ℝ) 1) [IsProbabilityMeasure π]
    (hπ : IsCoupling π R ν) [NullSingletonClass R] (hR2 : HasFiniteMoment 2 R)
    (hν2 : HasFiniteMoment 2 ν) :
    wassersteinEDist 2 R (StatFormal.Wave4b.endpointMixture1 ε t π) ^ (2 : ℝ) <
      qcost (stoPlan ε t π) := by
  have hR : IsProbabilityMeasure R := hπ.fst_eq ▸ inferInstance
  have hc := stoPlan_coupling (ε := ε) (t := t) hπ
  have hμ := hc.isProbabilityMeasure_right
  have hfin := qcost_stoPlan_lt_top (ε := ε) (t := t) hπ hR2 hν2
  have hv : bvar ε t ≠ 0 := by
    simp only [bvar, ne_eq, Real.toNNReal_eq_zero, not_le]
    have := ht.1; have := ht.2
    have : 0 < 1 - t := by linarith
    positivity
  have hN : NullSingletonClass (gaussianReal 0 (bvar ε t)) := nullSingletonClass_gaussianReal hv
  by_contra hlt
  push Not at hlt
  have heq := le_antisymm hlt (pareto_weak _ _ _ hc)
  have hW : wassersteinEDist 2 R (StatFormal.Wave4b.endpointMixture1 ε t π) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at heq
    exact hfin.ne heq
  obtain ⟨G, hGm, hG0, hGs⟩ := opt_graph hc hW heq
  have hP : IsProbabilityMeasure (stoPlan ε t π) := hc.isProbabilityMeasure
  rw [prob_compl_eq_zero_iff hGm, stoPlan_eq, Measure.map_apply (measurable_bmap t) hGm,
    Measure.prod_apply (measurable_bmap t hGm)] at hG0
  have hzero : ∀ p : ℝ × ℝ,
      gaussianReal 0 (bvar ε t) (Prod.mk p ⁻¹' (bmap t ⁻¹' G)) = 0 := fun p => by
    refine Set.Subsingleton.measure_zero ?_ _
    intro z hz z' hz'
    have := hGs p.1 _ _ hz hz'
    linarith
  simp only [hzero, lintegral_zero] at hG0
  exact zero_ne_one hG0

end Bridge

theorem pareto_bridge : Claims.pareto_bridge := by
  intro ε t R ν π hε ht hR hπ hRa hR2 hν2
  have := hπ.isProbabilityMeasure
  exact ⟨stoPlan_coupling hπ, qcost_stoPlan_lt_top hπ hR2 hν2, stoPlan_strict hε ht hπ hR2 hν2⟩

theorem pareto : Claims.pareto := by
  intro ε t p R ν π hε ht hp hp1 hR hπ hRa hR2 hν2
  have hπp : ∀ s, IsProbabilityMeasure (π s) := fun s => (hπ s).isProbabilityMeasure
  have hc : ∀ s, IsCoupling (stoPlan ε t (π s)) (R s)
      (StatFormal.Wave4b.endpointMixture1 ε t (π s)) := fun s => stoPlan_coupling (hπ s)
  have hflow : ∀ s, (R s).map (flowMap (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s))) =
      StatFormal.Wave4b.endpointMixture1 ε t (π s) ∧
      ∫⁻ u, edist u (flowMap (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s)) u) ^ (2 : ℝ)
        ∂(R s) = wassersteinEDist 2 (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s)) ^ (2 : ℝ) :=
    fun s => pareto_flow _ _ (hR s) (hc s).isProbabilityMeasure_right (hRa s)
  have hstrict : ∀ s, wassersteinEDist 2 (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s)) ^
      (2 : ℝ) < qcost (stoPlan ε t (π s)) := fun s => by
    have := hRa s
    exact stoPlan_strict hε ht (hπ s) (hR2 s) hν2
  have hfin : ∀ s, qcost (stoPlan ε t (π s)) < ∞ := fun s => qcost_stoPlan_lt_top (hπ s) (hR2 s) hν2
  refine ⟨fun s => ⟨(hflow s).1, (hc s).snd_eq⟩, fun α Φ => by
    rw [(hflow 0).1, (hflow 1).1, (hc 0).snd_eq, (hc 1).snd_eq], ?_, ?_⟩
  · exact Finset.sum_congr rfl fun s _ => by rw [(hflow s).2]
  · rw [Fin.sum_univ_two] at hp1 ⊢
    rw [Fin.sum_univ_two]
    have hW : ∀ s, ENNReal.ofReal (p s) *
        wassersteinEDist 2 (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s)) ^ (2 : ℝ) ≠ ⊤ :=
      fun s => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((hstrict s).trans (hfin s)).ne
    rcases lt_or_ge 0 (p 0) with h0 | h0
    · refine ENNReal.add_lt_add_of_lt_of_le (hW 1) ?_ ?_
      · rw [mul_comm (ENNReal.ofReal _), mul_comm (ENNReal.ofReal _)]
        exact ENNReal.mul_lt_mul_left (by simpa using h0) ENNReal.ofReal_ne_top (hstrict 0)
      · gcongr; exact (hstrict 1).le
    · have h1 : 0 < p 1 := by linarith [hp 0]
      rw [add_comm, add_comm (ENNReal.ofReal (p 0) * _)]
      refine ENNReal.add_lt_add_of_lt_of_le (hW 0) ?_ ?_
      · rw [mul_comm (ENNReal.ofReal _), mul_comm (ENNReal.ofReal _)]
        exact ENNReal.mul_lt_mul_left (by simpa using h1) ENNReal.ofReal_ne_top (hstrict 1)
      · gcongr; exact (hstrict 0).le

end StatFormal.Wave9b
