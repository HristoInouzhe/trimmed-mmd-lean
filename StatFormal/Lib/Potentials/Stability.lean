import StatFormal.Lib.Potentials.Uniqueness
import StatFormal.Lib.OTLimits.PlanStability
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Stability of Kantorovich / Brenier potentials

Library component (potential-level OT limit theory, part 2). Untrusted library code; no frozen
statement is touched.

For the quadratic cost on a finite-dimensional real inner product space `E`, a (source-side)
*potential* of a plan `π` over an open set `U` is a function `u` convex on `U` such that every
point `(x, y)` of the support of `π` with `x ∈ U` has `y` as a `U`-subgradient of `u` at `x`:
`u x + ⟪y, x' − x⟫ ≤ u x'` for `x' ∈ U` (`IsPotentialOn U u π`). Optimal plans have such
potentials (Rockafellar / Knott–Smith; Tau Ceti's
`TauCeti.IsOptimalCoupling.exists_support_subset_subdifferential`; with bounded target support a
globally Lipschitz one, `Potentials/Existence.lean`), and the Brenier map is their gradient.

This file proves that potentials converge whenever plans do. Everything is stated along an
arbitrary filter, and no compactness of the supports is assumed: what replaces Arzelà–Ascoli is
pointwise eventual boundedness on `U`, ultrafilter compactness of closed intervals, and the
uniform convergence of convex functions on compacta (`StatFormal.Convex`).

## Main results

* `isPotentialOn_of_ae`: the support condition follows from its `π`-a.e. version (continuity).
* `isPotentialOn_of_tendsto`: **closedness** — if `πᵢ → π` weakly, `uᵢ` are convex potentials of
  `πᵢ` over `U` and `uᵢ → u` pointwise on `U`, then `u` is a potential of `π` over `U`.
* `ae_gradient_eq_of_isPotentialOn`: two potentials of the same plan `π`, with first marginal
  `μ ≪ Leb` and `μ Uᶜ = 0`, have equal gradients `μ`-a.e. on `U` (both equal the plan's second
  coordinate; the Brenier map).
* `exists_eq_add_const_of_isPotentialOn`: if moreover `U` is convex with `U ⊆ supp μ`, two
  potentials of `π` differ by a constant on `U`.
* `tendsto_of_tendsto_plan`: **stability of potentials** — `πᵢ → π` weakly, `uᵢ` convex
  potentials of `πᵢ` over `U`, pointwise eventually bounded on `U`, normalised by
  `uᵢ x₀ → a` (`x₀ ∈ U`); `φ` any potential of `π`. Then `uᵢ → φ − φ x₀ + a` pointwise on `U`.
* `tendstoLocallyUniformlyOn_of_tendsto_plan`: the same convergence is locally uniform on `U`
  (uniform on compact subsets of `U`).
* `ae_tendsto_gradient_of_tendsto_plan`: along a sequence, `∇uₙ → ∇φ` Lebesgue-a.e. on `U`.

## References

* C. Villani, *Optimal Transport: Old and New*, Theorem 5.20 and its proof (stability of
  `c`-concave potentials), and Corollary 5.23.
* R. T. Rockafellar, R. J.-B. Wets, *Variational Analysis*, Theorem 7.17 (convex functions:
  pointwise convergence on an open set implies uniform convergence on compacta).
* R. J. McCann, Duke Math. J. 80 (1995) — uniqueness of the Brenier potential.
* otfd-C supplement, `prop:conditional-potentials` (identification steps).
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology Gradient InnerProductSpace

namespace StatFormal.Potentials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `u` is a (quadratic-cost, source-side) **potential of the plan `π` over `U`**: every point
`(x, y)` of the topological support of `π` with `x ∈ U` has `y` as a `U`-subgradient of `u` at
`x`, i.e. `u x + ⟪y, x' − x⟫ ≤ u x'` for all `x' ∈ U`. For `U = univ` and convex `u` this says
that `supp π` lies in the subdifferential graph `∂u`. -/
def IsPotentialOn (U : Set E) (u : E → ℝ) (π : Measure (E × E)) : Prop :=
  ∀ z ∈ π.support, z.1 ∈ U → ∀ x ∈ U, u z.1 + ⟪z.2, x - z.1⟫_ℝ ≤ u x

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The support condition from its almost-everywhere version.** If `u` is continuous on the
open set `U` and, for `π`-a.e. `(x, y)` with `x ∈ U`, `y` is a `U`-subgradient of `u` at `x`, then
`u` is a potential of `π` over `U` (the subgradient inequality is a closed condition). -/
theorem isPotentialOn_of_ae {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContinuousOn u U)
    {π : Measure (E × E)}
    (hae : ∀ᵐ z ∂π, z.1 ∈ U → ∀ x ∈ U, u z.1 + ⟪z.2, x - z.1⟫_ℝ ≤ u x) : IsPotentialOn U u π := by
  intro z hz hzU x hx
  by_contra hlt
  rw [not_le] at hlt
  set F : E × E → ℝ := fun w => u w.1 + ⟪w.2, x - w.1⟫_ℝ with hF
  have hcont : ContinuousAt F z :=
    ((hu.continuousAt (hU.mem_nhds hzU)).comp continuousAt_fst).add
      (continuous_snd.inner (continuous_const.sub continuous_fst)).continuousAt
  have hN : {w | u x < F w} ∩ Prod.fst ⁻¹' U ∈ 𝓝 z :=
    inter_mem (hcont.eventually (isOpen_Ioi.mem_nhds hlt))
      (continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hzU))
  have hpos := (Measure.mem_support_iff_forall z).1 hz _ hN
  have hzero : π ({w | u x < F w} ∩ Prod.fst ⁻¹' U) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with w hw hmem
    exact (hw hmem.2 x hx).not_gt hmem.1
  exact hpos.ne' hzero

omit [MeasurableSpace E] [BorelSpace E] in
/-- At a differentiability point, the gradient of a convex function is a subgradient relative to
`U` (Rockafellar, *Convex Analysis*, Thm 25.1). -/
theorem add_inner_gradient_le {U : Set E} {f : E → ℝ} (hf : ConvexOn ℝ U f) {x : E} (hx : x ∈ U)
    (hd : DifferentiableAt ℝ f x) {x' : E} (hx' : x' ∈ U) :
    f x + ⟪∇ f x, x' - x⟫_ℝ ≤ f x' := by
  have := StatFormal.Convex.add_fderiv_le_of_hasFDerivAt hf hx hd.hasFDerivAt hx'
  have he : ⟪∇ f x, x' - x⟫_ℝ = fderiv ℝ f x (x' - x) := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rwa [he]

omit [MeasurableSpace E] [BorelSpace E] in
/-- At a differentiability point of a convex function on an open set, the only `U`-subgradient is
the gradient (Rockafellar, *Convex Analysis*, Thm 25.1). -/
theorem eq_gradient_of_subgradient {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ConvexOn ℝ U f)
    {x : E} (hx : x ∈ U) (hd : DifferentiableAt ℝ f x) {y : E}
    (hy : ∀ x' ∈ U, f x + ⟪y, x' - x⟫_ℝ ≤ f x') : y = ∇ f x := by
  have h := StatFormal.Convex.tendsto_subgradient_inner (l := (atTop : Filter ℕ))
    (F := fun _ => f) (f := f) hU (Eventually.of_forall fun _ => hf)
    (fun _ _ => tendsto_const_nhds) hx hd.hasGradientAt (xs := fun _ => x) tendsto_const_nhds
    (g := fun _ => y) (Eventually.of_forall fun _ => hy)
  exact tendsto_const_nhds_iff.1 h

/-- **Limits of potentials are potentials of the limit plan** (closedness of the
plan–potential relation; the potential step of Villani, *Optimal Transport*, proof of
Thm 5.20). Let `U ⊆ E` be open, `l` a nontrivial filter, `πᵢ → π` weakly (probability measures on
`E × E`), `uᵢ` eventually convex on `U` and eventually potentials of `πᵢ` over `U`, and
`uᵢ → u` pointwise on `U` with `u : E → ℝ` finite. Then `u` is a potential of `π` over `U`. -/
theorem isPotentialOn_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {U : Set E} (hU : IsOpen U)
    {us : ι → E → ℝ} {u : E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hlim : ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (u x)))
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure) :
    IsPotentialOn U u π.toMeasure := by
  intro z hz hzU x hx
  have hu : ConvexOn ℝ U u := StatFormal.Convex.convexOn_of_tendsto hconv hlim
  have hcu : ContinuousAt u z.1 := (hu.continuousOn hU).continuousAt (hU.mem_nhds hzU)
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hzU)
  have hunif := StatFormal.Convex.tendstoUniformlyOn_of_tendsto hU hconv hlim hrU
    (isCompact_closedBall z.1 r)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set h : E × E → ℝ := fun w => u w.1 + ⟪w.2, x - w.1⟫_ℝ with hh
  have hcont : ContinuousAt h z :=
    (hcu.comp continuousAt_fst).add
      (continuous_snd.inner (continuous_const.sub continuous_fst)).continuousAt
  have hε4 : 0 < ε / 4 := by positivity
  have hN : {w | h z - ε / 4 < h w} ∩ Prod.fst ⁻¹' ball z.1 r ∈ 𝓝 z :=
    inter_mem (hcont.eventually (isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith)))
      (continuous_fst.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr))
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.1 hN
  have hpos : 0 < π.toMeasure V := (Measure.mem_support_iff_forall z).1 hz _ (hVo.mem_nhds hzV)
  obtain ⟨i, hiV, hiu, hipot, hix⟩ :=
    ((OTLimits.eventually_pos_measure_of_tendsto hπ hVo hpos).and
      ((Metric.tendstoUniformlyOn_iff.1 hunif (ε / 4) hε4).and
        (hpot.and ((hlim x hx).eventually (Metric.ball_mem_nhds _ hε4))))).exists
  obtain ⟨w, hwV, hws⟩ := Measure.nonempty_inter_support_of_pos hiV
  have hwN := hVsub hwV
  have hw1 : w.1 ∈ closedBall z.1 r := ball_subset_closedBall hwN.2
  have hineq := hipot w hws (hrU hw1) x hx
  have h1 := hiu w.1 hw1
  rw [Real.dist_eq] at h1 hix
  have hwlt : h z - ε / 4 < h w := hwN.1
  simp only [hh] at hwlt
  have := abs_lt.1 h1
  have := abs_lt.1 hix
  linarith

/-- **Potentials of a common plan have equal gradients almost everywhere.** Let `ρ` be an
additive Haar measure on `E` and `π` a finite measure on `E × E` whose first marginal
`μ = π.fst` satisfies `μ ≪ ρ` and `μ Uᶜ = 0` for the open set `U`. If `u` and `φ` are convex on
`U` and both are potentials of `π` over `U`, then `∇u = ∇φ` at `μ`-a.e. point of `U`. (At
`π`-a.e. `(x, y)`, both are differentiable at `x` and `y` is a subgradient of both, hence equal to
both gradients.) -/
theorem ae_gradient_eq_of_isPotentialOn {ρ : Measure E} [ρ.IsAddHaarMeasure] {U : Set E}
    (hU : IsOpen U) {u φ : E → ℝ} (hu : ConvexOn ℝ U u) (hφ : ConvexOn ℝ U φ)
    {π : Measure (E × E)} (hμ : π.fst ≪ ρ) (hUc : π.fst Uᶜ = 0)
    (hpu : IsPotentialOn U u π) (hpφ : IsPotentialOn U φ π) :
    ∀ᵐ x ∂π.fst, x ∈ U → ∇ u x = ∇ φ x := by
  have hdu : ∀ᵐ x ∂π.fst, x ∈ U → DifferentiableAt ℝ u x :=
    hμ.ae_le (hu.ae_differentiableAt_of_mem (μ := ρ))
  have hdφ : ∀ᵐ x ∂π.fst, x ∈ U → DifferentiableAt ℝ φ x :=
    hμ.ae_le (hφ.ae_differentiableAt_of_mem (μ := ρ))
  have hU' : ∀ᵐ x ∂π.fst, x ∈ U :=
    (measure_eq_zero_iff_ae_notMem.1 hUc).mono fun x hx => not_not.1 hx
  have hfst : ∀ᵐ z ∂π, z.1 ∈ U ∧ DifferentiableAt ℝ u z.1 ∧ DifferentiableAt ℝ φ z.1 := by
    have h := hdu.and (hdφ.and hU')
    rw [Measure.fst] at h
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable h] with z hz
    exact ⟨hz.2.2, hz.1 hz.2.2, hz.2.1 hz.2.2⟩
  have hsupp : ∀ᵐ z ∂π, z ∈ π.support := Measure.support_mem_ae
  have hgood : ∀ᵐ z ∂π, z.1 ∈ U → ∇ u z.1 = ∇ φ z.1 := by
    filter_upwards [hfst, hsupp] with z hz hzs _
    rw [← eq_gradient_of_subgradient hU hu hz.1 hz.2.1 (hpu z hzs hz.1),
      ← eq_gradient_of_subgradient hU hφ hz.1 hz.2.2 (hpφ z hzs hz.1)]
  have hmeas : MeasurableSet {x : E | x ∈ U → ∇ u x = ∇ φ x} := by
    have hgu : Measurable (∇ u) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
    have hgφ : Measurable (∇ φ) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
    have : {x : E | x ∈ U → ∇ u x = ∇ φ x} = Uᶜ ∪ {x | ∇ u x = ∇ φ x} := by
      ext x; simp [imp_iff_not_or]
    rw [this]
    exact hU.measurableSet.compl.union (measurableSet_eq_fun hgu hgφ)
  rw [Measure.fst, ae_map_iff measurable_fst.aemeasurable hmeas]
  exact hgood

/-- **A potential's gradient is the plan's second coordinate** (the Brenier map). Let `ρ` be an
additive Haar measure and `π` a measure on `E × E` with `π.fst ≪ ρ`. If `φ` is convex on the open
set `V` and a potential of `π` over `V`, then `y = ∇φ x` for `π`-a.e. `(x, y)` with `x ∈ V`. -/
theorem ae_snd_eq_gradient_of_isPotentialOn {ρ : Measure E} [ρ.IsAddHaarMeasure] {V : Set E}
    (hV : IsOpen V) {φ : E → ℝ} (hφ : ConvexOn ℝ V φ) {π : Measure (E × E)} (hμ : π.fst ≪ ρ)
    (hpφ : IsPotentialOn V φ π) : ∀ᵐ z ∂π, z.1 ∈ V → z.2 = ∇ φ z.1 := by
  have hdφ : ∀ᵐ x ∂π.fst, x ∈ V → DifferentiableAt ℝ φ x :=
    hμ.ae_le (hφ.ae_differentiableAt_of_mem (μ := ρ))
  rw [Measure.fst] at hdφ
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdφ,
    (Measure.support_mem_ae : π.support ∈ ae π)] with z hz hzs hzV
  exact eq_gradient_of_subgradient hV hφ hzV (hz hzV) (hpφ z hzs hzV)

/-- **Two potentials of a plan differ by a constant** (uniqueness of the Brenier potential, plan
form, general domains). Let `ρ` be an additive Haar measure, `π` a measure on `E × E` with first
marginal `μ = π.fst ≪ ρ`, `V` open with `μ Vᶜ = 0`, and `U ⊆ V` open and convex with
`U ⊆ supp μ`. If `u, φ` are convex on `V` and potentials of `π` over `V`, then `u = φ + C` on `U`.
(Typical choices: `V = U = int (supp μ)` for a convex support and `μ (∂ supp μ) = 0`; or
`V = univ` for globally defined potentials, where `μ Vᶜ = 0` is automatic.) -/
theorem exists_eq_add_const_of_isPotentialOn_of_subset {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {U V : Set E} (hU : IsOpen U) (hUconv : Convex ℝ U) (hV : IsOpen V) (hUV : U ⊆ V)
    {u φ : E → ℝ} (hu : ConvexOn ℝ V u) (hφ : ConvexOn ℝ V φ)
    {π : Measure (E × E)} (hμ : π.fst ≪ ρ) (hVc : π.fst Vᶜ = 0) (hsupp : U ⊆ π.fst.support)
    (hpu : IsPotentialOn V u π) (hpφ : IsPotentialOn V φ π) :
    ∃ C, ∀ x ∈ U, u x = φ x + C :=
  (hu.subset hUV hUconv).exists_eq_add_const_of_ae_gradient_eq hU (hφ.subset hUV hUconv) hμ hsupp
    ((ae_gradient_eq_of_isPotentialOn hV hu hφ hμ hVc hpu hpφ).mono fun _ hx hxU => hx (hUV hxU))

/-- **Two potentials of a plan differ by a constant** (uniqueness of the Brenier potential, plan
form). Let `ρ` be an additive Haar measure, `π` a measure on `E × E` with first marginal
`μ = π.fst ≪ ρ`, `U` open and convex with `μ Uᶜ = 0` and `U ⊆ supp μ` (e.g. `μ` has a density
positive on `U = int (supp μ)` and `supp μ` convex). If `u, φ` are convex on `U` and potentials of
`π` over `U`, then `u = φ + C` on `U`. -/
theorem exists_eq_add_const_of_isPotentialOn {ρ : Measure E} [ρ.IsAddHaarMeasure] {U : Set E}
    (hU : IsOpen U) {u φ : E → ℝ} (hu : ConvexOn ℝ U u) (hφ : ConvexOn ℝ U φ)
    {π : Measure (E × E)} (hμ : π.fst ≪ ρ) (hUc : π.fst Uᶜ = 0) (hsupp : U ⊆ π.fst.support)
    (hpu : IsPotentialOn U u π) (hpφ : IsPotentialOn U φ π) :
    ∃ C, ∀ x ∈ U, u x = φ x + C :=
  exists_eq_add_const_of_isPotentialOn_of_subset hU hu.1 hU subset_rfl hu hφ hμ hUc hsupp hpu hpφ

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- **Pointwise limit points of pointwise eventually bounded functions.** If `uᵢ x` is eventually
bounded for each `x ∈ V`, then along every ultrafilter finer than `l` the `uᵢ` converge pointwise
on `V` to some `g : E → ℝ` (compactness of closed intervals; no diagonal argument is needed). -/
theorem exists_tendsto_ultrafilter {ι : Type*} {l : Filter ι} {V : Set E} {us : ι → E → ℝ}
    (hbdd : ∀ x ∈ V, ∃ M, ∀ᶠ i in l, |us i x| ≤ M) (𝒰 : Ultrafilter ι) (h𝒰 : ↑𝒰 ≤ l) :
    ∃ g : E → ℝ, ∀ y ∈ V, Tendsto (fun i => us i y) (𝒰 : Filter ι) (𝓝 (g y)) := by
  have hex : ∀ y, ∃ c : ℝ, y ∈ V → Tendsto (fun i => us i y) (𝒰 : Filter ι) (𝓝 c) := by
    intro y
    by_cases hy : y ∈ V
    · obtain ⟨M, hM⟩ := hbdd y hy
      have hle : ((𝒰.map fun i => us i y : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓟 (Icc (-M) M) := by
        rw [Ultrafilter.coe_map, le_principal_iff]
        exact h𝒰 (hM.mono fun i hi => abs_le.1 hi)
      obtain ⟨c, -, hc⟩ := isCompact_Icc.ultrafilter_le_nhds _ hle
      exact ⟨c, fun _ => by rwa [Ultrafilter.coe_map] at hc⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose g hg using hex
  exact ⟨g, fun y hy => hg y hy⟩

/-- **Stability of normalised potentials, general domains.** As `tendsto_of_tendsto_plan`, but
the potentials live on an open set `V` (convex on `V`, potentials of the plans over `V`,
pointwise eventually bounded on `V`, `μ Vᶜ = 0`), while identification and convergence happen on
an open convex `U ⊆ V` with `U ⊆ supp μ` and `x₀ ∈ U`. The case `V = univ` covers globally
defined (e.g. Lipschitz) potentials without any condition on `μ (∂U)`. Conclusion:
`uᵢ x → φ x − φ x₀ + a` for every `x ∈ U`. -/
theorem tendsto_of_tendsto_plan_of_subset {ι : Type*} {l : Filter ι} {ρ : Measure E}
    [ρ.IsAddHaarMeasure] {U V : Set E} (hU : IsOpen U) (hUconv : Convex ℝ U) (hV : IsOpen V)
    (hUV : U ⊆ V) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hVc : π.toMeasure.fst Vᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ V (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn V (us i) (πs i).toMeasure)
    (hbdd : ∀ x ∈ V, ∃ M, ∀ᶠ i in l, |us i x| ≤ M)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ V φ) (hpφ : IsPotentialOn V φ π.toMeasure) :
    ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (φ x - φ x₀ + a)) := by
  intro x hx
  rw [tendsto_iff_ultrafilter]
  intro 𝒰 h𝒰
  obtain ⟨g, hlimg⟩ := exists_tendsto_ultrafilter hbdd 𝒰 h𝒰
  have hconv' : ∀ᶠ i in (𝒰 : Filter ι), ConvexOn ℝ V (us i) := h𝒰 hconv
  have hgc : ConvexOn ℝ V g := StatFormal.Convex.convexOn_of_tendsto hconv' hlimg
  have hgpot : IsPotentialOn V g π.toMeasure :=
    isPotentialOn_of_tendsto hV hconv' hlimg (hπ.mono_left h𝒰) (h𝒰 hpot)
  obtain ⟨C, hC⟩ := exists_eq_add_const_of_isPotentialOn_of_subset hU hUconv hV hUV hgc hφ hμ hVc
    hsupp hgpot hpφ
  have hg0 : g x₀ = a := tendsto_nhds_unique (hlimg x₀ (hUV hx₀)) (hnorm.mono_left h𝒰)
  have hCa : C = a - φ x₀ := by have := hC x₀ hx₀; linarith
  have hgx : g x = φ x - φ x₀ + a := by rw [hC x hx, hCa]; ring
  rw [← hgx]
  exact hlimg x (hUV hx)

/-- **Stability of normalised potentials** (Villani, *Optimal Transport*, Thm 5.20, potential
part; otfd-C `prop:conditional-potentials`, identification steps). Let `E` be a
finite-dimensional real inner product space with an additive Haar measure `ρ`, and:

* `U ⊆ E` open and convex, `x₀ ∈ U`;
* `πᵢ → π` weakly along a filter `l` (probability measures on `E × E`), where the first marginal
  `μ = π.fst` of the limit satisfies `μ ≪ ρ`, `μ Uᶜ = 0` and `U ⊆ supp μ`;
* `uᵢ : E → ℝ` eventually convex on `U` and eventually potentials of `πᵢ` over `U`
  (`IsPotentialOn`), pointwise eventually bounded on `U`
  (`∀ x ∈ U, ∃ M, ∀ᶠ i, |uᵢ x| ≤ M`), and normalised by `uᵢ x₀ → a`;
* `φ` convex on `U` and a potential of `π` over `U` (e.g. a Brenier potential of the limit
  problem).

Then `uᵢ x → φ x − φ x₀ + a` for every `x ∈ U`. No optimality, compact support or moment
condition is needed at this level; those enter only through `πᵢ → π`. -/
theorem tendsto_of_tendsto_plan {ι : Type*} {l : Filter ι} {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    (hbdd : ∀ x ∈ U, ∃ M, ∀ᶠ i in l, |us i x| ≤ M)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ U φ) (hpφ : IsPotentialOn U φ π.toMeasure) :
    ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (φ x - φ x₀ + a)) :=
  tendsto_of_tendsto_plan_of_subset hU hφ.1 hU subset_rfl hx₀ hπ hμ hUc hsupp hconv hpot hbdd
    hnorm hφ hpφ

/-- **Locally uniform convergence of normalised potentials.** Under the hypotheses of
`tendsto_of_tendsto_plan`, `uᵢ → φ − φ x₀ + a` locally uniformly on `U`, i.e. uniformly on every
compact subset of `U` (otfd-C `prop:conditional-potentials`: "uniformly on compact subsets of
`int 𝒰_K`"). -/
theorem tendstoLocallyUniformlyOn_of_tendsto_plan {ι : Type*} {l : Filter ι} {ρ : Measure E}
    [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    (hbdd : ∀ x ∈ U, ∃ M, ∀ᶠ i in l, |us i x| ≤ M)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ U φ) (hpφ : IsPotentialOn U φ π.toMeasure) :
    TendstoLocallyUniformlyOn us (fun x => φ x - φ x₀ + a) l U :=
  StatFormal.Convex.tendstoLocallyUniformlyOn_of_tendsto hU hconv
    (tendsto_of_tendsto_plan hU hx₀ hπ hμ hUc hsupp hconv hpot hbdd hnorm hφ hpφ)

/-- **A.e. convergence of the gradients (the transport maps).** Under the hypotheses of
`tendsto_of_tendsto_plan`, along a sequence (`ι` countable) with every `uₙ` convex on `U`,
`∇uₙ y → ∇φ y` for `ρ`-a.e. `y ∈ U`. When `φ` is a Brenier potential of the limit problem,
`∇φ` is the optimal map, so the maps `∇uₙ` converge to it Lebesgue-a.e. on `U`. -/
theorem ae_tendsto_gradient_of_tendsto_plan {ι : Type*} [Countable ι] {l : Filter ι}
    {ρ : Measure E} [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ i, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    (hbdd : ∀ x ∈ U, ∃ M, ∀ᶠ i in l, |us i x| ≤ M)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ U φ) (hpφ : IsPotentialOn U φ π.toMeasure) :
    ∀ᵐ y ∂ρ, y ∈ U → Tendsto (fun i => ∇ (us i) y) l (𝓝 (∇ φ y)) := by
  have hlim := tendsto_of_tendsto_plan hU hx₀ hπ hμ hUc hsupp (Eventually.of_forall hconv) hpot
    hbdd hnorm hφ hpφ
  have hf : ConvexOn ℝ U (fun x => φ x - φ x₀ + a) := by
    have := hφ.add_const (a - φ x₀)
    convert this using 1
    ext x
    simp only [Pi.add_apply]
    ring
  filter_upwards [StatFormal.Convex.ae_tendsto_gradient (μ := ρ) hU hconv hlim
    (fun i => (hconv i).ae_differentiableAt_of_mem) hf.ae_differentiableAt_of_mem] with y hy hyU
  have hgrad : ∇ (fun x => φ x - φ x₀ + a) y = ∇ φ y := by
    simp only [gradient, fderiv_add_const, fderiv_sub_const]
  rw [← hgrad]
  exact hy hyU

end StatFormal.Potentials
