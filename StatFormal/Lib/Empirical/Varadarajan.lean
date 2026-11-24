import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Empirical
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Varadarajan's theorem and `W_p`-consistency of the empirical measure (pairwise independence)

For a sequence `X 0, X 1, …` of random points with common law `μ`, the empirical measure of the
first `n + 1` points is `TauCeti.Probability.empiricalMeasure (fun i ↦ X i ω) n
= (n + 1)⁻¹ ∑_{i ≤ n} δ_{X i ω}` (a `ProbabilityMeasure`; the successor indexing makes it a
probability measure for every `n`, and is irrelevant for limits).

Tau Ceti already proves, under *mutual* independence (`iIndepFun`):
* `TauCeti.Probability.ConditionallyIIDWith.tendsto_empiricalMeasure_ae` (weak convergence, via
  the conditionally i.i.d. formalism), and
* `TauCeti.tendsto_wassersteinEDist_empiricalMeasure_ae` (`W_p` convergence under a finite
  `p`-th moment).

This file proves both statements under the weaker hypothesis of **pairwise** independence, using
Etemadi's strong law in Mathlib (`ProbabilityTheory.strong_law_ae_real`), and records the
mutually independent forms as corollaries.

## Main results
* `StatFormal.Empirical.tendsto_empiricalMeasure_ae` — Varadarajan's theorem (pairwise iid).
* `StatFormal.Empirical.tendsto_empiricalMeasure_ae_of_iIndepFun` — the same, mutual independence.
* `StatFormal.Empirical.tendsto_wassersteinEDist_empiricalMeasure_ae` — `W_p(μ̂ₙ, μ) → 0` a.s.
  under a finite `p`-th moment, pairwise iid, separable pseudometric space.

## References
* V. S. Varadarajan, *On the convergence of sample probability distributions*, Sankhyā 19 (1958),
  23–26.
* R. M. Dudley, *Real Analysis and Probability*, Thm 11.4.1.
* N. Etemadi, *An elementary proof of the strong law of large numbers*, Z. Wahrsch. 55 (1981).
* C. Villani, *Optimal Transport: Old and New*, Thm 6.9 (W_p convergence = weak + moments).
-/

open Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Topology

namespace StatFormal.Empirical

open TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {P : Measure Ω} {X : ℕ → Ω → α} {μ : ProbabilityMeasure α}

/-- **Setwise strong law for empirical frequencies** (pairwise independence). If the `X i` are
pairwise independent with common law `μ`, then for a fixed measurable set `B`, almost surely the
empirical frequency `μ̂ₙ(B)` converges to `μ(B)`. Source: Etemadi's SLLN applied to `1_B ∘ X i`. -/
theorem tendsto_empiricalMeasure_apply_ae
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) P)
    (hlaw : ∀ i, HasLaw (X i) (μ : Measure α) P) {B : Set α} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ ((empiricalMeasure (fun i ↦ X i ω) n : Measure α) B).toReal) atTop
      (𝓝 ((μ : Measure α) B).toReal) := by
  have hP : IsProbabilityMeasure P := (hlaw 0).isProbabilityMeasure
  set f : α → ℝ := B.indicator 1 with hf_def
  have hf : Measurable f := measurable_one.indicator hB
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i ↦ (hlaw i).identDistrib (hlaw 0)
  have hfint : Integrable (f ∘ X 0) P := by
    refine (hlaw 0).integrable_comp ?_
    exact (integrable_const (1 : ℝ)).indicator hB
  have hslln := strong_law_ae_real (fun i ↦ f ∘ X i) hfint
    (fun i j hij ↦ (hindep hij).comp hf hf) (fun i ↦ (hident i).comp hf)
  have hmean : P[f ∘ X 0] = ((μ : Measure α) B).toReal := by
    rw [(hlaw 0).integral_comp hf.aestronglyMeasurable, hf_def, integral_indicator_one hB,
      measureReal_def]
  filter_upwards [hslln] with ω hω
  rw [← hmean]
  refine (hω.comp (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
  rw [empiricalMeasure_apply_toReal hB]
  simp only [Function.comp_apply, hf_def]
  push_cast
  rw [div_eq_inv_mul]

variable [TopologicalSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]

/-- **Varadarajan's theorem** (pairwise independent form). Let `α` be a second-countable
topological space whose open sets are measurable (e.g. a separable metric space with its Borel
σ-algebra), and let `X 0, X 1, …` be pairwise independent random points of `α`, each with law
`μ`. Then almost surely the empirical measures `(n + 1)⁻¹ ∑_{i ≤ n} δ_{X i ω}` converge to `μ` in
the topology of weak convergence on `ProbabilityMeasure α`.

Proof: the finite intersections of a countable basis form a countable π-system generating
arbitrarily small neighbourhoods; the setwise strong law holds simultaneously on all of them,
and Mathlib's `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` upgrades that to weak
convergence. Source: Varadarajan (1958); Dudley, *Real Analysis and Probability*, Thm 11.4.1. -/
theorem tendsto_empiricalMeasure_ae
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) P)
    (hlaw : ∀ i, HasLaw (X i) (μ : Measure α) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ empiricalMeasure (fun i ↦ X i ω) n) atTop (𝓝 μ) := by
  obtain ⟨B, hB⟩ := exists_seq_basis α
  set T : Finset ℕ → Set α := fun s ↦ ⋂ i ∈ s, B i with hT
  have hBopen : ∀ i, IsOpen (B i) := fun i ↦ hB.isOpen (Set.mem_range_self i)
  have hTmeas : ∀ s, MeasurableSet (T s) := fun s ↦
    s.measurableSet_biInter fun i _ ↦ (hBopen i).measurableSet
  have hpi : IsPiSystem (Set.range T) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ -
    exact ⟨s ∪ t, by
      simp only [hT, ← Finset.set_biInter_coe, Finset.coe_union, Set.biInter_union]⟩
  have hall : ∀ᵐ ω ∂P, ∀ s : Finset ℕ, Tendsto
      (fun n : ℕ ↦ ((empiricalMeasure (fun i ↦ X i ω) n : Measure α) (T s)).toReal) atTop
      (𝓝 ((μ : Measure α) (T s)).toReal) :=
    ae_all_iff.2 fun s ↦ tendsto_empiricalMeasure_apply_ae hindep hlaw (hTmeas s)
  filter_upwards [hall] with ω hω
  refine hpi.tendsto_probabilityMeasure_of_tendsto_of_mem ?_ (fun u hu x hxu ↦ ?_) ?_
  · rintro _ ⟨s, rfl⟩
    exact hTmeas s
  · obtain ⟨-, ⟨i, rfl⟩, hxi, hiu⟩ := hB.exists_subset_of_mem_open hxu hu
    exact ⟨T {i}, Set.mem_range_self _, by simpa [hT] using (hBopen i).mem_nhds hxi,
      by simpa [hT] using hiu⟩
  · rintro _ ⟨s, rfl⟩
    exact NNReal.tendsto_coe.1 <| by
      simpa only [← ProbabilityMeasure.measureReal_eq_coe_coeFn, measureReal_def] using hω s

/-- **Varadarajan's theorem**, i.i.d. form with mutual independence (`iIndepFun`): almost surely
the empirical measures of an i.i.d. `μ`-sample in a second-countable space with measurable open
sets converge weakly to `μ`. Corollary of `tendsto_empiricalMeasure_ae`. -/
theorem tendsto_empiricalMeasure_ae_of_iIndepFun (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μ : Measure α) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ empiricalMeasure (fun i ↦ X i ω) n) atTop (𝓝 μ) :=
  tendsto_empiricalMeasure_ae (fun _ _ hij ↦ hindep.indepFun hij) hlaw

section Wasserstein

open TauCeti

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [SeparableSpace Y] {Z : ℕ → Ω → Y} {ν : ProbabilityMeasure Y} {p : ℝ≥0∞}

/-- **Almost-sure `W_p`-consistency of the empirical measure** (pairwise independent form). Let
`Y` be a separable pseudometric space with measurable open sets, `0 < p < ∞`, and let
`Z 0, Z 1, …` be pairwise independent random points of `Y` with common law `ν`, where `ν` has a
finite `p`-th moment (`TauCeti.HasFiniteMoment p ν`). Then almost surely the `p`-Wasserstein
distance `W_p(μ̂ₙ, ν)` between the empirical measure of `Z 0, …, Z n` and `ν` tends to `0`.

Proof: weak convergence from `tendsto_empiricalMeasure_ae` (Varadarajan), convergence of `p`-th
moments from Etemadi's SLLN applied to `d(x₀, Z i)^p`, and Tau Ceti's characterisation of
`W_p`-convergence (weak convergence plus convergence of `p`-th moments,
`tendsto_wassersteinEDist_of_tendsto_probabilityMeasure_of_tendsto_lintegral`; Villani, Optimal
Transport, Thm 6.9). Strengthens `TauCeti.tendsto_wassersteinEDist_empiricalMeasure_ae`
(mutual independence) to pairwise independence. -/
theorem tendsto_wassersteinEDist_empiricalMeasure_ae (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hν : HasFiniteMoment p (ν : Measure Y))
    (hindep : Pairwise fun i j ↦ IndepFun (Z i) (Z j) P)
    (hlaw : ∀ i, HasLaw (Z i) (ν : Measure Y) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ wassersteinEDist p (empiricalMeasure (fun i ↦ Z i ω) n : Measure Y) ν) atTop
      (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨x, hx⟩ := hasFiniteMoment_def.mp hν
  have hmom : ∫⁻ y, edist x y ^ p.toReal ∂(ν : Measure Y) ≠ ∞ := by
    simpa only [enorm_eq_self] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hx.eLpNorm_lt_top).ne
  set f : Y → ℝ := fun y ↦ dist x y ^ p.toReal with hf_def
  have hf : Measurable f := (continuous_const.dist continuous_id).measurable.pow_const _
  have hfe : ∀ y, edist x y ^ p.toReal = ENNReal.ofReal (f y) := fun y ↦ by
    rw [hf_def, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq.le]
  have hfint : Integrable f (ν : Measure Y) := by
    refine ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y ↦ by positivity)).2 ?_⟩
    rw [← lintegral_congr hfe]
    exact hmom.lt_top
  have := (hlaw 0).isProbabilityMeasure
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i ↦ (hlaw i).identDistrib (hlaw 0)
  have hweak := tendsto_empiricalMeasure_ae hindep hlaw
  have hslln := strong_law_ae (fun i ↦ f ∘ Z i) ((hlaw 0).integrable_comp hfint)
    (fun i j hij ↦ (hindep hij).comp hf hf) (fun i ↦ (hident i).comp hf)
  filter_upwards [hweak, hslln] with ω hωw hωs
  refine tendsto_wassersteinEDist_of_tendsto_probabilityMeasure_of_tendsto_lintegral hp0 hp
    hωw x hmom ?_
  rw [lintegral_congr fun y ↦ hfe y, ← ofReal_integral_eq_lintegral_ofReal hfint
    (Eventually.of_forall fun y ↦ by positivity), ← (hlaw 0).integral_comp hf.aestronglyMeasurable]
  refine ((ENNReal.continuous_ofReal.tendsto _).comp
    (hωs.comp (tendsto_add_atTop_nat 1))).congr fun n ↦ ?_
  have hnonneg : ∀ i, 0 ≤ f (Z i ω) := fun i ↦ by positivity
  simp only [Function.comp_apply, smul_eq_mul, lintegral_empiricalMeasure (hf.ennreal_ofReal),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹),
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hnonneg i,
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)),
    ENNReal.ofReal_natCast, hfe]

end Wasserstein

end StatFormal.Empirical
