import StatFormal.Archive.OTFD.WaveL1.RouteCM
import StatFormal.Lib.OTLimits.GraphL2

/-!
# Route (wave L1): mean-square plan stability with a fixed source

Untrusted route file. Weak convergence of cyclically monotone plans (`RouteCM`) plus convergence of
second moments of the moving targets gives `∫ ‖y − F(x)‖² dπ_K → 0` (library
`OTLimits.tendsto_lintegral_enorm_sub_sq_of_tendsto_graphPlan`). Bounded supports give the moment
convergence by the portmanteau theorem.
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.OTFD.WaveL1

section Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

theorem measurable_graph {F : E → E} (hF : Measurable F) : Measurable fun x => (x, F x) :=
  measurable_id.prodMk hF

theorem graph_snd {P : Measure E} {F : E → E} (hF : Measurable F) :
    (Graph P F).snd = P.map F := by
  rw [Graph, Measure.snd, Measure.map_map measurable_snd (measurable_graph hF)]
  rfl

theorem graph_fst {P : Measure E} {F : E → E} (hF : Measurable F) :
    (Graph P F).fst = P := by
  rw [Graph, Measure.fst, Measure.map_map measurable_fst (measurable_graph hF)]
  exact Measure.map_id

theorem measurable_enorm_sq : Measurable fun y : E => ‖y‖ₑ ^ 2 := by fun_prop

theorem lintegral_snd_enorm_sq (π : Measure (E × E)) :
    ∫⁻ z, ‖z.2‖ₑ ^ 2 ∂π = Mom2 π.snd := by
  rw [Mom2, Measure.snd, lintegral_map measurable_enorm_sq measurable_snd]

theorem lintegral_map_enorm_sq {P : Measure E} {F : E → E} (hF : Measurable F) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂P = Mom2 (P.map F) := by
  rw [Mom2, lintegral_map measurable_enorm_sq hF]

theorem memLp_of_mom2 {P : Measure E} {F : E → E} (hF : Measurable F)
    (h : Mom2 (P.map F) ≠ ∞) : MemLp F 2 P := by
  have hlt : eLpNorm F 2 P < ∞ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      hF.aestronglyMeasurable]
    simpa [ENNReal.rpow_two, lintegral_map_enorm_sq hF] using h.lt_top
  exact hlt

/-- The graph plan of a `P`-a.e. cyclically monotone map is concentrated on a Borel cyclically
monotone set. -/
theorem cmConc_graph {P : Measure E} {T : E → E} (hT : Measurable T) (h : IsCMMapAE P T) :
    CMConc (Graph P T) := by
  obtain ⟨S, hS, hS0, hcm⟩ := h
  refine ⟨{z : E × E | z.1 ∈ S ∧ z.2 = T z.1}, ?_, hcm, ?_⟩
  · exact (measurable_fst hS).inter (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst))
  · rw [Graph, Measure.map_apply (measurable_graph hT)]
    · refine measure_mono_null (fun x hx => ?_) hS0
      simp only [mem_preimage, mem_compl_iff, Set.mem_ofPred_eq, and_true] at hx
      exact hx
    · exact ((measurable_fst hS).inter
        (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst))).compl

end Graph

section L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- **Core mean-square theorem** (otfd A `lem:plan-stability-H`(b), R `lem:plan-w2`(b)). -/
theorem tendsto_L2_of_cmConc {P μ : ProbabilityMeasure E} {F : E → E}
    {ν : ℕ → ProbabilityMeasure E} {π : ℕ → ProbabilityMeasure (E × E)}
    (hF : Measurable F) (huniq : BrenierUniq (P : Measure E) μ F)
    (hν : Tendsto ν atTop (𝓝 μ))
    (hmom : Tendsto (fun K => Mom2 (ν K : Measure E)) atTop (𝓝 (Mom2 (μ : Measure E))))
    (hμ2 : Mom2 (μ : Measure E) ≠ ∞)
    (hfst : ∀ K, (π K : Measure (E × E)).fst = P)
    (hsnd : ∀ K, (π K : Measure (E × E)).snd = ν K)
    (hcm : ∀ K, CMConc (π K : Measure (E × E))) :
    Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (E × E))) atTop (𝓝 0) := by
  set G : ProbabilityMeasure (E × E) := P.map fun x => (x, F x) with hGdef
  have hconv : Tendsto π atTop (𝓝 G) :=
    tendsto_of_cmConc huniq tendsto_const_nhds hν hfst hsnd hcm rfl
  have hcoupG : IsCoupling (G : Measure (E × E)) P μ :=
    isCoupling_of_tendsto (Eventually.of_forall fun K => ⟨hfst K, hsnd K⟩) hconv
      tendsto_const_nhds hν
  have hmap : (P : Measure E).map F = μ := by
    rw [← graph_snd hF]; exact hcoupG.snd_eq
  have hTL : MemLp F 2 (P : Measure E) := memLp_of_mom2 hF (by rw [hmap]; exact hμ2)
  refine StatFormal.OTLimits.tendsto_lintegral_enorm_sub_sq_of_tendsto_graphPlan hTL
    (Eventually.of_forall hfst) hconv ?_
  rw [lintegral_map_enorm_sq hF, hmap]
  refine hmom.congr fun K => ?_
  rw [lintegral_snd_enorm_sq, hsnd K]

/-- Uniformly bounded supports give convergence of second moments and a bounded limit support. -/
theorem tendsto_mom2_of_bounded {ν : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E} {M : ℝ}
    (hν : Tendsto ν atTop (𝓝 μ)) (hM : ∀ K, (ν K : Measure E) (Metric.closedBall 0 M)ᶜ = 0) :
    (μ : Measure E) (Metric.closedBall 0 M)ᶜ = 0 ∧
      Tendsto (fun K => Mom2 (ν K : Measure E)) atTop (𝓝 (Mom2 (μ : Measure E))) := by
  have hμM : (μ : Measure E) (Metric.closedBall 0 M)ᶜ = 0 := by
    have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν
      (Metric.isClosed_closedBall (x := (0 : E)) (ε := M))
    have h1 : ∀ K, (ν K : Measure E) (Metric.closedBall 0 M) = 1 := fun K =>
      (prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet).1 (hM K)
    simp only [h1, limsup_const] at hlim
    exact (prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet).2
      (le_antisymm prob_le_one hlim)
  refine ⟨hμM, ?_⟩
  set m : ℝ≥0 := M.toNNReal
  let g0 : C(E, ℝ≥0) := ⟨fun y => (min ‖y‖₊ m) ^ 2, by fun_prop⟩
  let g : E →ᵇ ℝ≥0 := BoundedContinuousFunction.mkOfBound g0 (m ^ 2) fun x y => by
    have hx : g0 x ≤ m ^ 2 := pow_le_pow_left₀ bot_le (min_le_right _ _) 2
    have hy : g0 y ≤ m ^ 2 := pow_le_pow_left₀ bot_le (min_le_right _ _) 2
    rw [NNReal.dist_eq]
    have h0x : (0 : ℝ) ≤ g0 x := (g0 x).2
    have h0y : (0 : ℝ) ≤ g0 y := (g0 y).2
    have hx' : (g0 x : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hx
    have hy' : (g0 y : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hy
    rw [abs_le]; constructor <;> linarith
  have hcongr : ∀ ρ : Measure E, ρ (Metric.closedBall 0 M)ᶜ = 0 →
      Mom2 ρ = ∫⁻ y, (g y : ℝ≥0∞) ∂ρ := by
    intro ρ hρ
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ y ∂ρ, y ∉ (Metric.closedBall (0 : E) M)ᶜ := measure_eq_zero_iff_ae_notMem.1 hρ
    filter_upwards [hae] with y hy
    rw [Set.notMem_compl_iff] at hy
    have hy' : ‖y‖₊ ≤ m := by
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hy.trans (Real.le_coe_toNNReal M)
    change ‖y‖ₑ ^ 2 = (((min ‖y‖₊ m) ^ 2 : ℝ≥0) : ℝ≥0∞)
    rw [min_eq_left hy', ENNReal.coe_pow, enorm_eq_nnnorm]
  rw [hcongr _ hμM]
  exact (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hν g).congr
    fun K => (hcongr _ (hM K)).symm

end L2

end StatFormal.OTFD.WaveL1
