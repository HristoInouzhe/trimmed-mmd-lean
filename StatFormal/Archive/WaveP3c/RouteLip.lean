import StatFormal.Archive.WaveP3c.RouteMcCann
import StatFormal.Archive.WaveP3c.Statements
import StatFormal.Lib.GhosalSen.LipschitzPotential

/-!
# Route (wave P3c), part 4: Lipschitz potentials for bounded targets; the semi-discrete estimator exists (untrusted)

* `exists_lipschitz_potential`: `P` Lipschitz-null (no moment), `Q` carried by `B(0, M)`: the moment-free GHS map `F`
  and potential `ψ` (RouteMcCann), and the bounded piece `{(x, F x) : ∂ψ(x) = {F x}, ‖F x‖ ≤ M}` of the graph of
  `∂ψ` regularised by `Foundations/GhosalSen/LipschitzPotential` (A `cor:app-ghs-lipschitz`).
* `exists_semidiscrete`: reference `μ` Lipschitz-null in `B(0, M)`, ANY law `α` (e.g. an empirical measure): the
  McCann map `T` from `μ` to `α`, the swapped graph `{(T u, u)}` (cyclically monotone), Rockafellar (Tau Ceti) and the
  regularisation give an `M`-Lipschitz convex `ψ̂` whose (closed) subgradient graph carries `(T × id)#μ`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP3c

open StatFormal.OTFD.WaveL1 (CycMon IsCMMapAE LipNull Euc)
open StatFormal.OTFD.Wave22a (IsSubgrad)

section H
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem ae_norm_le_of_map {P : Measure H} {F : H → H} (hF : Measurable F) {Q : Measure H} (hmap : P.map F = Q)
    {M : ℝ} (hQ : Q (Metric.closedBall 0 M)ᶜ = 0) : ∀ᵐ x ∂P, ‖F x‖ ≤ M := by
  have h0 : P (F ⁻¹' (Metric.closedBall (0 : H) M)ᶜ) = 0 := by
    rw [← Measure.map_apply hF Metric.isClosed_closedBall.measurableSet.compl, hmap, hQ]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
  simpa using hx

/-- **Lipschitz potential for a bounded target** (A `cor:app-ghs-lipschitz` with the existence of GHS Thm 2.3, no
moment). -/
theorem exists_lipschitz_potential (P Q : ProbabilityMeasure H) (M : ℝ) (hP : LipNull (P : Measure H))
    (hQ : (Q : Measure H) (Metric.closedBall 0 M)ᶜ = 0) :
    ∃ (ψ : H → ℝ) (F : H → H), ConvexOn ℝ univ ψ ∧ (∀ x x', |ψ x - ψ x'| ≤ M * ‖x - x'‖) ∧
      Measurable F ∧ (P : Measure H).map F = Q ∧ ∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x) := by
  obtain ⟨ψ₀, F, -, -, -, -, hFm, hmap, hsub⟩ := exists_ghs_of_lipNull P Q hP
  have hb := ae_norm_le_of_map hFm hmap hQ
  set G : Set H := {x | subdifferential (innerₗ H) ψ₀ x = {F x} ∧ ‖F x‖ ≤ M} with hG
  have hGae : ∀ᵐ x ∂(P : Measure H), x ∈ G := by
    filter_upwards [hsub, hb] with x h1 h2 using ⟨h1, h2⟩
  set C : Set (H × H) := (fun x => (x, F x)) '' G with hC
  have hCsub : C ⊆ {p | p.2 ∈ subdifferential (innerₗ H) ψ₀ p.1} := by
    rintro - ⟨x, hx, rfl⟩
    show F x ∈ subdifferential (innerₗ H) ψ₀ x
    rw [hx.1]; exact mem_singleton _
  have hCM : ∀ p ∈ C, ‖p.2‖ ≤ M := by
    rintro - ⟨x, hx, rfl⟩; exact hx.2
  haveI : (ae (P : Measure H)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨x₀, hx₀⟩ := hGae.exists
  obtain ⟨φ, hφc, hφL, hφs⟩ :=
    StatFormal.GhosalSen.exists_lipschitz_of_subset_subdifferential hCsub hCM ⟨_, ⟨x₀, hx₀, rfl⟩⟩
  refine ⟨φ, F, hφc, hφL, hFm, hmap, ?_⟩
  filter_upwards [hGae] with x hx using hφs (x, F x) ⟨x, hx, rfl⟩

theorem isClosed_subgradGraph {f : H → ℝ} (hf : Continuous f) : IsClosed {p : H × H | IsSubgrad f p.1 p.2} := by
  have : {p : H × H | IsSubgrad f p.1 p.2} = ⋂ z, {p : H × H | f p.1 + ⟪p.2, z - p.1⟫ ≤ f z} := by
    ext p; simp [IsSubgrad]
  rw [this]
  exact isClosed_iInter fun z => isClosed_le (by fun_prop) continuous_const

/-- **The semi-discrete estimator exists**: for a Lipschitz-null reference `μ` carried by `B(0, M)` and ANY law `α`,
an `M`-Lipschitz convex potential `ψ̂` and a coupling of `α` and `μ` carried by the subgradient graph of `ψ̂`. -/
theorem exists_semidiscrete (α μ : ProbabilityMeasure H) (M : ℝ) (hμ : LipNull (μ : Measure H))
    (hμM : (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0) :
    ∃ (ψh : H → ℝ) (γ : ProbabilityMeasure (H × H)), ConvexOn ℝ univ ψh ∧
      (∀ x x', |ψh x - ψh x'| ≤ M * ‖x - x'‖) ∧ (γ : Measure (H × H)).fst = α ∧ (γ : Measure (H × H)).snd = μ ∧
      (γ : Measure (H × H)).support ⊆ {p | IsSubgrad ψh p.1 p.2} := by
  obtain ⟨T, hTm, hTmap, S, hSm, hS0, hcyc⟩ := exists_isCMMapAE_of_lipNull μ α hμ
  set S' : Set H := S ∩ Metric.closedBall 0 M with hS'
  have hS'0 : (μ : Measure H) S'ᶜ = 0 := by
    rw [hS', compl_inter]; exact measure_union_null hS0 hμM
  set C : Set (H × H) := {p | p.2 ∈ S' ∧ p.1 = T p.2} with hC
  have hCcyc : CycMon C := by
    refine StatFormal.OTFD.WaveL3.cycMon_mono (StatFormal.OTFD.WaveL3.cycMon_swap hcyc) ?_
    rintro ⟨x, u⟩ ⟨hu, hx⟩
    simp only at hu hx
    exact ⟨hu.1, hx⟩
  obtain ⟨g, hg⟩ :=
    ((StatFormal.OTFD.WaveL3.cycmon_iff H C).1 hCcyc).exists_fenchelConjugate_innerₗ_subset_subdifferential
  have hCM : ∀ p ∈ C, ‖p.2‖ ≤ M := fun p hp => by simpa using hp.1.2
  have hS'ne : S'.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hS'0
    exact one_ne_zero hS'0
  obtain ⟨u₀, hu₀⟩ := hS'ne
  obtain ⟨φ, hφc, hφL, hφs⟩ :=
    StatFormal.GhosalSen.exists_lipschitz_of_subset_subdifferential hg hCM ⟨(T u₀, u₀), hu₀, rfl⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hCM (T u₀, u₀) ⟨hu₀, rfl⟩)
  have hφcont : Continuous φ := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨M, hM⟩) fun x x' => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]; exact hφL x x'
  have hmeas : Measurable fun u : H => (T u, u) := hTm.prodMk measurable_id
  set γ : ProbabilityMeasure (H × H) := μ.map (fun u => (T u, u)) with hγ
  have hγm : (γ : Measure (H × H)) = (μ : Measure H).map fun u => (T u, u) := by
    rw [hγ, ProbabilityMeasure.toMeasure_map]
  refine ⟨φ, γ, hφc, hφL, ?_, ?_, ?_⟩
  · rw [hγm, Measure.fst_map_prodMk (Y := fun u : H => u) hTm measurable_id, hTmap]
  · rw [hγm, Measure.snd_map_prodMk (Y := fun u : H => u) hTm measurable_id, Measure.map_id']
  · have hcl := isClosed_subgradGraph hφcont
    refine Measure.support_subset_of_isClosed hcl ?_
    rw [mem_ae_iff, hγm, Measure.map_apply hmeas hcl.measurableSet.compl]
    refine measure_mono_null (fun u hu => ?_) hS'0
    by_contra hu'
    exact hu (hφs (T u, u) ⟨not_not.1 hu', rfl⟩)

end H

end StatFormal.WaveP3c

namespace StatFormal.WaveP3c

theorem ghs_lipschitz_exists : Claims.ghs_lipschitz_exists :=
  fun _ _ _ _ _ _ _ P Q M hP hQ => exists_lipschitz_potential P Q M hP hQ

theorem semidiscrete_exists : Claims.semidiscrete_exists :=
  fun _ _ _ _ _ _ _ α μ M hμ hμM => exists_semidiscrete α μ M hμ hμM

end StatFormal.WaveP3c
