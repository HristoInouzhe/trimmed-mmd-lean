import StatFormal.Archive.Wave25b.RouteExist

/-!
# Route (wave P3c), part 1: McCann existence in the `IsCMMapAE` form (untrusted)

The certified wave-25b `app_ghs_existence` (GHS Thm 2.3, any target, no moment of the target) gives a proper convex
lower semicontinuous `ψ : H → EReal` and a Borel `F` with `F#P = Q` and `∂ψ(x) = {F x}` for `P`-a.e. `x`. The graph
of `∂ψ` is cyclically monotone (Tau Ceti), so the graph of `F` over a Borel conull set is cyclically monotone: `F` is
a McCann map in the frozen `IsCMMapAE` sense consumed by C's claims.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP3c

open StatFormal.OTFD.WaveL1 (CycMon IsCMMapAE LipNull Mom2 Euc)
open StatFormal.OTFD.Wave1 (PellClass)

section H
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- A map that is `P`-a.e. the unique subgradient of an extended-valued function is a McCann map. -/
theorem isCMMapAE_of_ae_subdifferential {P : Measure H} {ψ : H → EReal} {F : H → H}
    (h : ∀ᵐ x ∂P, subdifferential (innerₗ H) ψ x = {F x}) : IsCMMapAE P F := by
  set N := toMeasurable P {x | ¬ subdifferential (innerₗ H) ψ x = {F x}} with hN
  have hN0 : P N = 0 := by rw [hN, measure_toMeasurable]; exact ae_iff.1 h
  refine ⟨Nᶜ, (measurableSet_toMeasurable _ _).compl, by rwa [compl_compl], ?_⟩
  have hΓ : CycMon {p : H × H | p.2 ∈ subdifferential (innerₗ H) ψ p.1} :=
    (StatFormal.OTFD.WaveL3.cycmon_iff H _).2 (isCyclicallyMonotone_norm_sub_sq_div_two_subdifferential ψ)
  refine StatFormal.OTFD.WaveL3.cycMon_mono hΓ ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only at hx hy
  subst hy
  have hx' : x ∉ {x | ¬ subdifferential (innerₗ H) ψ x = {F x}} := fun h' => hx (subset_toMeasurable _ _ h')
  simp only [mem_setOf_eq, not_not] at hx'
  show F x ∈ subdifferential (innerₗ H) ψ x
  rw [hx']; exact mem_singleton _

/-- **McCann existence in `H`** (from GHS Thm 2.3): for `P ∈ 𝒫^ℓ(H)` and ANY target `Q`. -/
theorem exists_isCMMapAE_of_pell (P Q : ProbabilityMeasure H) (hP : PellClass (P : Measure H)) :
    ∃ F : H → H, Measurable F ∧ (P : Measure H).map F = Q ∧ IsCMMapAE (P : Measure H) F := by
  obtain ⟨ψ, F, -, -, -, -, hF, hmap, hsub⟩ := StatFormal.Wave25b.app_ghs_existence H P Q hP
  exact ⟨F, hF, hmap, isCMMapAE_of_ae_subdifferential hsub⟩

/-! ### Moment-free existence: truncate the source too -/

/-- Closed balls of radius `n + N` exhaust `H`. -/
theorem iUnion_closedBall_add (N : ℕ) : (⋃ n : ℕ, Metric.closedBall (0 : H) (n + N)) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact ⟨n, by simpa using hn.trans (by linarith : (n : ℝ) ≤ n + N)⟩

theorem monotone_closedBall_add (N : ℕ) : Monotone fun n : ℕ => Metric.closedBall (0 : H) (n + N) :=
  fun _ _ h => Metric.closedBall_subset_closedBall (by gcongr)

/-- The conditioned law `P[· | B(0, n + N)]`. -/
def condBall (P : ProbabilityMeasure H) (N : ℕ)
    (hne : ∀ n : ℕ, (P : Measure H) (Metric.closedBall 0 (n + N)) ≠ 0) (n : ℕ) : ProbabilityMeasure H :=
  ⟨(P : Measure H)[|Metric.closedBall 0 (n + N)], cond_isProbabilityMeasure (hne n)⟩

theorem coe_condBall (P : ProbabilityMeasure H) (N : ℕ)
    (hne : ∀ n : ℕ, (P : Measure H) (Metric.closedBall 0 (n + N)) ≠ 0) (n : ℕ) :
    (condBall P N hne n : Measure H) = (P : Measure H)[|Metric.closedBall 0 (n + N)] := rfl

/-- The conditioned laws `P[· | B(0, n + N)]` converge weakly to `P`. -/
theorem tendsto_cond_closedBall (P : ProbabilityMeasure H) (N : ℕ)
    (hne : ∀ n : ℕ, (P : Measure H) (Metric.closedBall 0 (n + N)) ≠ 0) :
    Tendsto (condBall P N hne) atTop (𝓝 P) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro f
  set s : ℕ → Set H := fun n => Metric.closedBall (0 : H) (n + N) with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n => Metric.isClosed_closedBall.measurableSet
  have hfm : Measurable fun y : H => (f y : ℝ≥0∞) := by fun_prop
  simp only [coe_condBall]
  have heq : ∀ n, ∫⁻ x, (f x : ℝ≥0∞) ∂((P : Measure H)[|s n]) =
      ((P : Measure H) (s n))⁻¹ * ((P : Measure H).withDensity fun y => (f y : ℝ≥0∞)) (s n) := by
    intro n
    rw [ProbabilityTheory.cond, lintegral_smul_measure, withDensity_apply _ (hsm n), smul_eq_mul]
  show Tendsto (fun n => ∫⁻ x, (f x : ℝ≥0∞) ∂((P : Measure H)[|s n])) atTop _
  simp_rw [heq]
  have h1 : Tendsto (fun n => (P : Measure H) (s n)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := (P : Measure H)) (monotone_closedBall_add N)
    rw [iUnion_closedBall_add, measure_univ] at this
    exact this
  have h1' : Tendsto (fun n => ((P : Measure H) (s n))⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_inv_iff.2 h1
  have h2 : Tendsto (fun n => ((P : Measure H).withDensity fun y => (f y : ℝ≥0∞)) (s n)) atTop
      (𝓝 (∫⁻ x, (f x : ℝ≥0∞) ∂(P : Measure H))) := by
    have := tendsto_measure_iUnion_atTop (μ := ((P : Measure H).withDensity fun y => (f y : ℝ≥0∞)))
      (monotone_closedBall_add N)
    rw [iUnion_closedBall_add, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  simpa using ENNReal.Tendsto.mul h1' (Or.inl one_ne_zero) h2 (Or.inr ENNReal.one_ne_top)

/-- **GHS Thm 2.3 / McCann (1995) with NO moment at all**: for `P` null on Lipschitz hypersurfaces and ANY target. -/
theorem exists_ghs_of_lipNull (P Q : ProbabilityMeasure H) (hLip : LipNull (P : Measure H)) :
    ∃ (ψ : H → EReal) (F : H → H), Convex ℝ {p : H × ℝ | ψ p.1 ≤ p.2} ∧ LowerSemicontinuous ψ ∧
      (∀ x, ψ x ≠ ⊥) ∧ (∃ x, ψ x ≠ ⊤) ∧ Measurable F ∧ (P : Measure H).map F = Q ∧
      ∀ᵐ x ∂(P : Measure H), TauCeti.subdifferential (innerₗ H) ψ x = {F x} := by
  -- a radius carrying positive mass
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (P : Measure H) (Metric.closedBall 0 N) ≠ 0 := by
    by_contra h
    push Not at h
    have := tendsto_measure_iUnion_atTop (μ := (P : Measure H)) (monotone_closedBall_add 0)
    rw [iUnion_closedBall_add, measure_univ] at this
    have h0 : ((P : Measure H) ∘ fun n : ℕ => Metric.closedBall (0 : H) (n + (0 : ℕ))) = fun _ => 0 := by
      funext n; simpa using h n
    rw [h0] at this
    exact one_ne_zero (tendsto_nhds_unique this tendsto_const_nhds)
  have hne : ∀ n : ℕ, (P : Measure H) (Metric.closedBall 0 (n + N)) ≠ 0 := fun n h0 =>
    hN (measure_mono_null (Metric.closedBall_subset_closedBall (by linarith [Nat.cast_nonneg (α := ℝ) n])) h0)
  set Pn : ℕ → ProbabilityMeasure H := condBall P N hne with hPn
  have hPnP := tendsto_cond_closedBall P N hne
  have hPnLip : ∀ n, LipNull (Pn n : Measure H) := fun n S hS =>
    ProbabilityTheory.cond_absolutelyContinuous (hLip S hS)
  have hPnBall : ∀ n, (Pn n : Measure H) (Metric.closedBall 0 (n + N))ᶜ = 0 := fun n => by
    rw [hPn, coe_condBall, cond_apply Metric.isClosed_closedBall.measurableSet, inter_compl_self, measure_empty, mul_zero]
  have hex : ∀ n : ℕ, ∃ G : H → H, Measurable G ∧ (Pn n : Measure H).map G = Q.map (StatFormal.Wave25b.trunc n) ∧
      IsCMMapAE (Pn n : Measure H) G := fun n =>
    StatFormal.OTFD.WaveL3.brenier_exists_H H (Pn n) (Q.map (StatFormal.Wave25b.trunc n)) (hPnLip n)
      (StatFormal.OTFD.WaveL1.mom2_ne_top_of_bounded (hPnBall n))
      (StatFormal.OTFD.WaveL1.mom2_ne_top_of_bounded (StatFormal.Wave25b.map_trunc_ball Q n))
  choose G hGm hGpush hGcm using hex
  set π : ℕ → ProbabilityMeasure (H × H) := fun n => (Pn n).map fun x => (x, G n x) with hπ
  have hπG : ∀ n, (π n : Measure (H × H)) = StatFormal.OTFD.WaveL1.Graph (Pn n : Measure H) (G n) := fun n => rfl
  have hcoup : ∀ n, IsCoupling (π n : Measure (H × H)) (Pn n : Measure H)
      (Q.map (StatFormal.Wave25b.trunc n) : ProbabilityMeasure H) := fun n => by
    rw [hπG]
    exact ⟨StatFormal.OTFD.WaveL1.graph_fst (hGm n), (StatFormal.OTFD.WaveL1.graph_snd (hGm n)).trans (hGpush n)⟩
  have hQn := StatFormal.Wave25b.tendsto_map_trunc Q
  obtain ⟨l', σ, hne', hle, hconv, hσ⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := atTop) (μs := Pn) (νs := fun n => Q.map (StatFormal.Wave25b.trunc n)) (πs := π)
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hPnP).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hQn).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    hPnP hQn (Eventually.of_forall hcoup)
  have := hne'
  have hcmπ : ∀ n, StatFormal.OTFD.WaveL1.CMConc (π n : Measure (H × H)) := fun n => by
    rw [hπG]; exact StatFormal.OTFD.WaveL1.cmConc_graph (hGm n) (hGcm n)
  set S := (σ : Measure (H × H)).support with hS
  have hcycS : CycMon S := StatFormal.OTFD.WaveL1.cycMon_support_of_tendsto hconv hcmπ
  obtain ⟨g, hg⟩ :=
    ((StatFormal.OTFD.WaveL3.cycmon_iff H S).1 hcycS).exists_fenchelConjugate_innerₗ_subset_subdifferential
  set ψ := fenchelConjugate (innerₗ H) g with hψ
  have hSne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h0 := Measure.measure_compl_support (μ := (σ : Measure (H × H)))
    rw [← hS, h, compl_empty, measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨z, hz⟩ := hSne
  set Γ : Set (H × H) := {p | p.2 ∈ subdifferential (innerₗ H) ψ p.1} with hΓ
  have hmonoΓ : StatFormal.Potentials.IsMonotoneSet Γ :=
    StatFormal.Potentials.isMonotoneSet_of_subset_subdifferential (u := ψ) subset_rfl
  have hnull : (P : Measure H) (StatFormal.Potentials.multivaluedSet Γ) = 0 :=
    StatFormal.Potentials.measure_multivaluedSet_eq_zero (StatFormal.OTFD.WaveL3.lipGraph_null hLip) hmonoΓ
  have hnullS : (P : Measure H) (StatFormal.Potentials.multivaluedSet S) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro x ⟨y₁, y₂, h1, h2, hne⟩
    exact ⟨y₁, y₂, hg h1, hg h2, hne⟩
  have hσfst : (σ : Measure (H × H)).fst = (P : Measure H) := hσ.fst_eq
  obtain ⟨T, hT, hσT, hTS⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem hσ
    Measure.isClosed_support.measurableSet Measure.support_mem_ae hnullS
  refine ⟨ψ, T, convex_epigraph_fenchelConjugate (innerₗ H) g, lowerSemicontinuous_fenchelConjugate_innerₗ g,
    apply_ne_bot_of_mem_subdifferential (innerₗ H) (hg hz), ⟨z.1, ne_top_of_mem_subdifferential (innerₗ H) (hg hz)⟩,
    hT, ?_, ?_⟩
  · have h1 := hσ.snd_eq
    rw [hσT, graphPlan_def] at h1
    rw [← StatFormal.OTFD.WaveL1.graph_snd hT]
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

/-- **McCann existence in `H`, no moment**: `P` null on Lipschitz hypersurfaces, ANY target. -/
theorem exists_isCMMapAE_of_lipNull (P Q : ProbabilityMeasure H) (hP : LipNull (P : Measure H)) :
    ∃ F : H → H, Measurable F ∧ (P : Measure H).map F = Q ∧ IsCMMapAE (P : Measure H) F := by
  obtain ⟨ψ, F, -, -, -, -, hF, hmap, hsub⟩ := exists_ghs_of_lipNull P Q hP
  exact ⟨F, hF, hmap, isCMMapAE_of_ae_subdifferential hsub⟩

end H

end StatFormal.WaveP3c
