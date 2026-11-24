import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Convergence

/-!
# From convergence of transport plans to convergence of transport maps

Library component (OT limit theory, part 2). Untrusted library code; no frozen statement is
touched.

Let `μ` be a probability measure on `X` and `T : X → Y` an (a.e.-measurable) map into a
second-countable pseudo-emetric space. Tau Ceti proves
(`TauCeti.tendsto_map_prodMk_self_iff_tendstoInMeasure`) that, for *graph* plans over the same
`μ`, weak convergence `(id × Tₙ)#μ → (id × T)#μ` is equivalent to `Tₙ → T` in `μ`-measure. This
file removes the requirement that the approximating plans be graph plans: it only asks that they
have first marginal `μ`, and concludes that they concentrate on the graph of `T`.

## Main results

* `tendsto_measure_edist_ge_of_tendsto_graphPlan`: if plans `πᵢ` with first marginal `μ`
  converge weakly to `(id × T)#μ` (along any filter), then for every `ε > 0`,
  `πᵢ {(x, y) | ε ≤ d(y, T x)} → 0`. (Lusin + portmanteau, Ambrosio–Gigli–Savaré Lemma 5.4.1.)
* `tendstoInMeasure_of_tendsto_of_ae_eq_graph`: if moreover each `πᵢ` is concentrated on the
  graph of a map `Tᵢ`, then `Tᵢ → T` in `μ`-measure (along any filter) — the plan-to-map step of
  Villani, *Optimal Transport: Old and New*, Corollary 5.23.
* `tendsto_measure_edist_ge_of_tendsto_graphPlan_of_continuous`: when `T` is *continuous*, the
  first marginals of the `πᵢ` may move: `πᵢ → (id × T)#μ` alone forces
  `πᵢ {ε ≤ d(y, T x)} → 0`.

## Why the first marginal is fixed in general

For a discontinuous `T` the conclusion fails with moving first marginals: on `ℝ` let `μ` be
Lebesgue measure on `[0, 1]`, `T = 0` off `ℚ` and `T = 1` on `ℚ`, and let `μₙ` be uniform on the
rationals `k / n`. The plans `(id × 0)#μₙ` converge to `(id × 0)#μ = (id × T)#μ`, yet each of them
gives mass one to `{(x, y) | 1/2 ≤ |y - T x|}`.
-/

open Filter MeasureTheory Set TauCeti
open scoped ENNReal Topology

namespace StatFormal.OTLimits

variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace X]
  [OpensMeasurableSpace X] [PseudoEMetricSpace Y] [SecondCountableTopology Y]
  [OpensMeasurableSpace Y] [HasOuterApproxClosed (X × Y)]
  {μ : ProbabilityMeasure X} {T : X → Y}

/-- **Plans converging to a continuous graph plan concentrate on the graph.** Let `T : X → Y` be
continuous and let probability measures `πᵢ` on `X × Y` (with arbitrary first marginals) converge
weakly, along any filter, to the graph plan `(id × T)#μ`. Then for every `ε > 0`,
`πᵢ {(x, y) | ε ≤ edist y (T x)} → 0`.

The set is closed and null for the limit, so this is the closed-set half of the portmanteau
theorem. Continuity of `T` cannot be dropped when the first marginals move (module docstring). -/
theorem tendsto_measure_edist_ge_of_tendsto_graphPlan_of_continuous [BorelSpace Y]
    {l : Filter ι} {πs : ι → ProbabilityMeasure (X × Y)} (hT : Continuous T)
    (h : Tendsto πs l (𝓝 (μ.map fun x ↦ (x, T x)))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ (πs i).toMeasure {z | ε ≤ edist z.2 (T z.1)}) l (𝓝 0) := by
  have hC : IsClosed {z : X × Y | ε ≤ edist z.2 (T z.1)} :=
    isClosed_le continuous_const (continuous_snd.edist (hT.comp continuous_fst))
  have hlim : ((μ.map fun x ↦ (x, T x) : ProbabilityMeasure (X × Y)) : Measure (X × Y))
      {z | ε ≤ edist z.2 (T z.1)} = 0 := by
    have hempty : {x | (x, T x) ∈ {z : X × Y | ε ≤ edist z.2 (T z.1)}} = ∅ := by
      ext x; simp [hε.ne']
    rw [toMeasure_map_prodMk_self, graphPlan_apply hT.measurable.aemeasurable hC.measurableSet,
      hempty, measure_empty]
  refine tendsto_of_le_liminf_of_limsup_le zero_le ?_
  rw [← hlim]
  exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hC

variable [(μ : Measure X).WeaklyRegular]

/-- **Plans with a fixed first marginal converging to a graph plan concentrate on the graph.**
Let `μ` be a weakly regular probability measure on `X` (automatic on pseudo-metrizable Borel
spaces), `T : X → Y` a.e.-measurable into a second-countable pseudo-emetric space, and `πᵢ`
probability measures on `X × Y` whose first marginal is eventually `μ`. If `πᵢ → (id × T)#μ`
weakly along a filter `l`, then for every `ε > 0`,
`πᵢ {(x, y) | ε ≤ edist y (T x)} → 0` along `l`.

The `πᵢ` need not be graph plans. Proof: Lusin's theorem makes `T` continuous on a closed `F`
with `μ Fᶜ < δ/2`; `C = (F × Y) ∩ {ε ≤ d(y, T x)}` is closed and null for the limit, so the
portmanteau theorem gives `πᵢ C < δ/2` eventually, while the rest of the set lies in `Fᶜ × Y`,
of `πᵢ`-mass `μ Fᶜ`. Source: Ambrosio–Gigli–Savaré, *Gradient Flows*, Lemma 5.4.1. -/
theorem tendsto_measure_edist_ge_of_tendsto_graphPlan {l : Filter ι}
    {πs : ι → ProbabilityMeasure (X × Y)} (hT : AEMeasurable T μ)
    (hfst : ∀ᶠ i in l, (πs i).toMeasure.fst = μ)
    (h : Tendsto πs l (𝓝 (μ.map fun x ↦ (x, T x)))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ (πs i).toMeasure {z | ε ≤ edist z.2 (T z.1)}) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨F, -, hF, hFμ, hFcont⟩ := hT.exists_isClosed_measure_sdiff_lt_continuousOn
    MeasurableSet.univ (measure_ne_top _ _) hδ2.ne'
  rw [← compl_eq_univ_sdiff] at hFμ
  set C : Set (X × Y) := F ×ˢ univ ∩ {z | ε ≤ edist z.2 (T z.1)} with hC
  have hCclosed : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed (t := Ici ε) ?_ (hF.prod isClosed_univ)
      isClosed_Ici
    exact continuous_edist.comp_continuousOn
      (continuous_snd.continuousOn.prodMk (hFcont.comp continuous_fst.continuousOn fun z hz ↦ hz.1))
  have hlim : ((μ.map fun x ↦ (x, T x) : ProbabilityMeasure (X × Y)) : Measure (X × Y)) C = 0 := by
    have hempty : {x | (x, T x) ∈ C} = ∅ := by ext x; simp [hC, hε.ne']
    rw [toMeasure_map_prodMk_self, graphPlan_apply hT hCclosed.measurableSet, hempty,
      measure_empty]
  have hCn : Tendsto (fun i ↦ (πs i).toMeasure C) l (𝓝 0) := by
    refine tendsto_of_le_liminf_of_limsup_le zero_le ?_
    rw [← hlim]
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hCclosed
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hCn (δ / 2) hδ2, hfst] with i hi hfi
  have hFc : (πs i).toMeasure (Fᶜ ×ˢ univ) = (μ : Measure X) Fᶜ := by
    rw [← hfi, Measure.fst_apply hF.isOpen_compl.measurableSet, prod_univ]
  calc (πs i).toMeasure {z | ε ≤ edist z.2 (T z.1)}
      ≤ (πs i).toMeasure (C ∪ Fᶜ ×ˢ univ) := by
        refine measure_mono fun z hz ↦ ?_
        by_cases hzF : z.1 ∈ F
        · exact Or.inl ⟨⟨hzF, mem_univ _⟩, hz⟩
        · exact Or.inr ⟨hzF, mem_univ _⟩
    _ ≤ (πs i).toMeasure C + (πs i).toMeasure (Fᶜ ×ˢ univ) := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hi (hFc ▸ hFμ.le)
    _ = δ := ENNReal.add_halves δ

/-- **Plan convergence implies map convergence** (Villani, *Optimal Transport: Old and New*,
Corollary 5.23, plan-to-map step). Let `μ` be a weakly regular probability measure on `X`,
`T : X → Y` and `Tᵢ : X → Y` a.e.-measurable maps into a second-countable pseudo-emetric space,
and `πᵢ` probability measures on `X × Y` that eventually have first marginal `μ` and are
concentrated on the graph of `Tᵢ` (`y = Tᵢ x` for `πᵢ`-a.e. `(x, y)`). If `πᵢ → (id × T)#μ`
weakly along a filter `l`, then `Tᵢ → T` in `μ`-measure along `l`. -/
theorem tendstoInMeasure_of_tendsto_of_ae_eq_graph {l : Filter ι}
    {πs : ι → ProbabilityMeasure (X × Y)} {Ts : ι → X → Y} (hT : AEMeasurable T μ)
    (hTs : ∀ᶠ i in l, AEMeasurable (Ts i) μ)
    (hfst : ∀ᶠ i in l, (πs i).toMeasure.fst = μ)
    (hgraph : ∀ᶠ i in l, ∀ᵐ z ∂(πs i).toMeasure, z.2 = Ts i z.1)
    (h : Tendsto πs l (𝓝 (μ.map fun x ↦ (x, T x)))) :
    TendstoInMeasure (μ : Measure X) Ts l T := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_measure_edist_ge_of_tendsto_graphPlan hT hfst h hε)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hTs, hfst, hgraph] with i hTi hfi hgi
  have hπ : (πs i).toMeasure = graphPlan (Ts i) μ := by
    rw [eq_graphPlan_of_ae_snd_eq (hfi ▸ hTi) hgi, hfi]
  rw [hπ, graphPlan_def]
  exact Measure.le_map_apply (aemeasurable_prodMk_self hTi) {z : X × Y | ε ≤ edist z.2 (T z.1)}

end StatFormal.OTLimits
