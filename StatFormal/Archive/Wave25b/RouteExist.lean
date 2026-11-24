import StatFormal.Archive.Wave25b.RouteHardMain
import StatFormal.Lib.Potentials.HilbertUniqueness
import TauCeti.MeasureTheory.OptimalTransport.Brenier

/-!
# Route (wave 25b): A `thm:app-ghs-existence` (GHS Thm 2.3), any target (untrusted)

Truncate the target, `Q_n = T_n#Q` with `T_n y = y` on `‖y‖ ≤ n` and `0` elsewhere (bounded, `Q_n ⇀ Q`). The frozen
`brenier_exists_H` gives cyclically monotone maps `F_n` from `P` to `Q_n`; their graph plans have converging
marginals, so a refinement converges (Prokhorov for couplings, Tau Ceti) to a coupling `σ` of `(P, Q)` whose support
`S` is cyclically monotone (weak limits). Rockafellar's theorem (Tau Ceti) puts `S` inside `∂ψ`, `ψ = g⋆` proper,
convex, lower semicontinuous. The graph of `∂ψ` is monotone, so `P`-a.e. point carries at most one subgradient
(Lipschitz-hypersurface cover, library), `σ` is a graph plan `(Id × F)#P` (library), `F#P = Q`, and `∂ψ(x) = {F x}`
for `P`-a.e. `x`. No moment of `Q` is used.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave25b

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph LipNull Mom2 Euc cmConc_graph cmConc_of_tendsto
  cycMon_support_of_tendsto graph_fst graph_snd)
open StatFormal.OTFD.Wave1 (PellClass)

section Exist
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Truncation at radius `n`. -/
def trunc (n : ℕ) (y : H) : H := if ‖y‖ ≤ n then y else 0

theorem measurable_trunc (n : ℕ) : Measurable (trunc (H := H) n) :=
  Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const) measurable_id measurable_const

theorem norm_trunc_le (n : ℕ) (y : H) : ‖trunc n y‖ ≤ n := by
  unfold trunc
  split_ifs with h
  · exact h
  · simp

theorem tendsto_map_trunc (Q : ProbabilityMeasure H) :
    Tendsto (fun n : ℕ => Q.map (trunc n)) atTop (𝓝 Q) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro f
  simp only [ProbabilityMeasure.toMeasure_map]
  have hfm : Measurable fun y : H => (f y : ℝ≥0∞) := by fun_prop
  simp_rw [lintegral_map hfm (measurable_trunc _)]
  refine tendsto_lintegral_of_dominated_convergence (fun _ => (nndist f 0 : ℝ≥0∞))
    (fun n => hfm.comp (measurable_trunc n)) (fun n => Eventually.of_forall fun y => ?_)
    (by simp) (Eventually.of_forall fun y => ?_)
  · exact ENNReal.coe_le_coe.2 (BoundedContinuousFunction.NNReal.upper_bound f _)
  · refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have : ‖y‖ ≤ n := hN.trans (by exact_mod_cast hn)
    simp [trunc, this]

theorem map_trunc_ball (Q : ProbabilityMeasure H) (n : ℕ) :
    ((Q.map (trunc n) : ProbabilityMeasure H) : Measure H) (Metric.closedBall 0 n)ᶜ = 0 := by
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (measurable_trunc n)
    Metric.isClosed_closedBall.measurableSet.compl]
  have : trunc n ⁻¹' (Metric.closedBall (0 : H) n)ᶜ = ∅ := by
    ext y; simp [norm_trunc_le n y]
  rw [this, measure_empty]

end Exist

theorem app_ghs_existence : Claims.app_ghs_existence := by
  intro H _ _ _ _ _ _ P Q hPell
  have hLip : LipNull (P : Measure H) := hPell.2.2
  have hP2 : Mom2 (P : Measure H) ≠ ∞ := hPell.2.1.ne
  -- maps onto the truncated targets
  have hex : ∀ n : ℕ, ∃ G : H → H, Measurable G ∧ (P : Measure H).map G = Q.map (trunc n) ∧
      IsCMMapAE (P : Measure H) G := fun n =>
    StatFormal.OTFD.WaveL3.brenier_exists_H H P (Q.map (trunc n)) hLip hP2
      (StatFormal.OTFD.WaveL1.mom2_ne_top_of_bounded (map_trunc_ball Q n))
  choose G hGm hGpush hGcm using hex
  set π : ℕ → ProbabilityMeasure (H × H) := fun n => P.map fun x => (x, G n x) with hπ
  have hπG : ∀ n, (π n : Measure (H × H)) = Graph (P : Measure H) (G n) := fun n => rfl
  have hcoup : ∀ n, IsCoupling (π n : Measure (H × H)) (P : Measure H) (Q.map (trunc n) : ProbabilityMeasure H) :=
    fun n => by rw [hπG]; exact ⟨graph_fst (hGm n), (graph_snd (hGm n)).trans (hGpush n)⟩
  have hQn := tendsto_map_trunc Q
  obtain ⟨l', σ, hne, hle, hconv, hσ⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := atTop) (μs := fun _ : ℕ => P) (νs := fun n => Q.map (trunc n)) (πs := π)
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto (tendsto_const_nhds (x := P))).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hQn).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    tendsto_const_nhds hQn (Eventually.of_forall hcoup)
  haveI := hne
  have hcmπ : ∀ n, CMConc (π n : Measure (H × H)) := fun n => by rw [hπG]; exact cmConc_graph (hGm n) (hGcm n)
  set S := (σ : Measure (H × H)).support with hS
  have hcycS : CycMon S := cycMon_support_of_tendsto hconv hcmπ
  -- Rockafellar
  obtain ⟨g, hg⟩ := ((StatFormal.OTFD.WaveL3.cycmon_iff H S).1 hcycS).exists_fenchelConjugate_innerₗ_subset_subdifferential
  set ψ := fenchelConjugate (innerₗ H) g with hψ
  have hSne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h0 := Measure.measure_compl_support (μ := (σ : Measure (H × H)))
    rw [← hS, h, compl_empty, measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨z, hz⟩ := hSne
  -- the graph of `∂ψ` is monotone, so a.e. single-valued
  set Γ : Set (H × H) := {p | p.2 ∈ subdifferential (innerₗ H) ψ p.1} with hΓ
  have hmonoΓ : StatFormal.Potentials.IsMonotoneSet Γ :=
    StatFormal.Potentials.isMonotoneSet_of_subset_subdifferential (u := ψ) subset_rfl
  have hnull : (P : Measure H) (StatFormal.Potentials.multivaluedSet Γ) = 0 :=
    StatFormal.Potentials.measure_multivaluedSet_eq_zero (StatFormal.OTFD.WaveL3.lipGraph_null hLip) hmonoΓ
  have hnullS : (P : Measure H) (StatFormal.Potentials.multivaluedSet S) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro x ⟨y₁, y₂, h1, h2, hne⟩
    exact ⟨y₁, y₂, hg h1, hg h2, hne⟩
  obtain ⟨T, hT, hσT, hTS⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem hσ
    Measure.isClosed_support.measurableSet Measure.support_mem_ae hnullS
  refine ⟨ψ, T, convex_epigraph_fenchelConjugate (innerₗ H) g, lowerSemicontinuous_fenchelConjugate_innerₗ g,
    apply_ne_bot_of_mem_subdifferential (innerₗ H) (hg hz), ⟨z.1, ne_top_of_mem_subdifferential (innerₗ H) (hg hz)⟩,
    hT, ?_, ?_⟩
  · have h1 := hσ.snd_eq
    rw [hσT, graphPlan_def] at h1
    rw [← graph_snd hT]
    exact h1
  · filter_upwards [hTS, measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
    ext y
    simp only [mem_singleton_iff]
    constructor
    · intro hy
      by_contra hne
      exact hxM ⟨y, T x, hy, hg hx, hne⟩
    · rintro rfl
      exact hg hx

end StatFormal.Wave25b
