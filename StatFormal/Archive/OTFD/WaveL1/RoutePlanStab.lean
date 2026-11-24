import StatFormal.Archive.OTFD.WaveL1.RouteL2

/-!
# Route (wave L1): A `lem:plan-stability-H` and R `lem:plan-w2` in a separable Hilbert space

Untrusted route file; the uniqueness of the cyclically monotone coupling of the limit marginals is
the declared hypothesis `BrenierUniq`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL1

section Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- A probability law carried by a closed ball has a finite second moment. -/
theorem mom2_ne_top_of_bounded {ρ : Measure E} [IsProbabilityMeasure ρ] {M : ℝ}
    (hρ : ρ (Metric.closedBall 0 M)ᶜ = 0) : Mom2 ρ ≠ ∞ := by
  have hae : ∀ᵐ y ∂ρ, y ∉ (Metric.closedBall (0 : E) M)ᶜ := measure_eq_zero_iff_ae_notMem.1 hρ
  have hle : Mom2 ρ ≤ ∫⁻ _, ((M.toNNReal : ℝ≥0∞)) ^ 2 ∂ρ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with y hy
    rw [Set.notMem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hy
    gcongr
    rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
    exact hy.trans (Real.le_coe_toNNReal M)
  refine ne_top_of_le_ne_top ?_ hle
  simp [lintegral_const]

/-- From the plan form of (b) to the map form: graph plans of `P`-a.e. cyclically monotone maps. -/
theorem tendsto_L2_map {P : ProbabilityMeasure E} {F : E → E} {ν : ℕ → ProbabilityMeasure E}
    {T : ℕ → E → E} (hF : Measurable F) (hT : ∀ K, Measurable (T K))
    (hTν : ∀ K, (P : Measure E).map (T K) = ν K) (hTcm : ∀ K, IsCMMapAE (P : Measure E) (T K))
    (hplan : ∀ π : ℕ → ProbabilityMeasure (E × E),
      (∀ K, (π K : Measure (E × E)).fst = P) → (∀ K, (π K : Measure (E × E)).snd = ν K) →
      (∀ K, CMConc (π K : Measure (E × E))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (E × E))) atTop (𝓝 0)) :
    Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure E)) atTop (𝓝 0) := by
  have h := hplan (fun K => P.map fun x => (x, T K x)) (fun K => graph_fst (hT K))
    (fun K => (graph_snd (hT K)).trans (hTν K)) (fun K => cmConc_graph (hT K) (hTcm K))
  refine h.congr fun K => ?_
  change ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(Graph (P : Measure E) (T K)) = _
  rw [Graph, lintegral_map _ (measurable_graph (hT K))]
  exact ((measurable_snd.sub (hF.comp measurable_fst)).enorm.pow_const 2)

end Aux

/-! ### A `lem:plan-stability-H` -/

theorem plan_stab_a : Claims.plan_stab_a := by
  intro H _ _ _ _ _ _ P μ F M α ν π G _ _ _ huniq hα hν hfst hsnd hcm hG
  exact tendsto_of_cmConc huniq hα hν hfst hsnd hcm hG

theorem plan_stab_b : Claims.plan_stab_b := by
  intro H _ _ _ _ _ _ P μ F M ν π _ hF huniq hν hM hfst hsnd hcm
  obtain ⟨hμM, hmom⟩ := tendsto_mom2_of_bounded hν hM
  exact tendsto_L2_of_cmConc hF huniq hν hmom (mom2_ne_top_of_bounded hμM) hfst hsnd hcm

theorem plan_stab_b_map : Claims.plan_stab_b_map := by
  intro H _ _ _ _ _ _ P μ F M ν T hP hF huniq hν hM hT hTν hTcm
  exact tendsto_L2_map hF hT hTν hTcm fun π hfst hsnd hcm =>
    plan_stab_b H P μ F M ν π hP hF huniq hν hM hfst hsnd hcm

/-! ### R `lem:plan-w2` -/

theorem plan_w2_a : Claims.plan_w2_a := by
  intro H _ _ _ _ _ _ P μ F α ν π G _ _ _ huniq hα hν hfst hsnd hcm hG
  exact tendsto_of_cmConc huniq hα.1 hν.1 hfst hsnd hcm hG

theorem plan_w2_b : Claims.plan_w2_b := by
  intro H _ _ _ _ _ _ P μ F ν π _ hμ2 hF huniq hν hfst hsnd hcm
  exact tendsto_L2_of_cmConc hF huniq hν.1 hν.2 hμ2 hfst hsnd hcm

theorem plan_w2_b_map : Claims.plan_w2_b_map := by
  intro H _ _ _ _ _ _ P μ F ν T hP hμ2 hF huniq hν hT hTν hTcm
  exact tendsto_L2_map hF hT hTν hTcm fun π hfst hsnd hcm =>
    plan_w2_b H P μ F ν π hP hμ2 hF huniq hν hfst hsnd hcm

end StatFormal.OTFD.WaveL1
