import StatFormal.Lib.OTLimits.PlanStability
import StatFormal.Lib.OTLimits.MapConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# `L²` concentration of plans on a graph

Library component (OT limit theory, part 2b). Untrusted library code; no frozen statement is
touched.

`MapConvergence.lean` turns weak convergence of plans with first marginal `μ` towards a graph
plan `(id × T)#μ` into concentration *in probability* on the graph. Here the conclusion is
upgraded to `L²` under the natural uniform-integrability condition, convergence of the second
moments of the second marginals.

## Main results

* `tendsto_lintegral_enorm_sub_sq_of_tendsto_graphPlan`: let `μ` be a probability on a
  pseudo-metrizable Borel space `X`, `T ∈ L²(μ; E)` (`E` a second-countable real normed space),
  and `πᵢ` plans with first marginal `μ` such that `πᵢ → (id × T)#μ` weakly and
  `∫ ‖y‖² dπᵢ → ∫ ‖T x‖² dμ`. Then `∫ ‖y − T x‖² dπᵢ(x, y) → 0`. This is otfd-A
  `lem:plan-stability-H`(b) / otfd-R `lem:plan-w2`(b), given the weak convergence of part (a).
* `tendsto_lintegral_enorm_sub_sq_of_tendsto_map`: the graph-plan case
  `πᵢ = (id × Tᵢ)#μ`: `∫ ‖Tᵢ − T‖² dμ → 0`.

Proof: approximate `T` in `L²(μ)` by a bounded continuous `g` (Mathlib's density theorem); the
continuous cost `‖y − g x‖²` is dominated by `2‖y‖² + 2‖g x‖²`, whose integrals converge, so its
integrals converge along the plans (`tendsto_lintegral_of_le_of_tendsto`) to
`∫ ‖T − g‖² dμ`; the error `‖g x − T x‖²` integrates against `πᵢ` as against `μ`.

## References

* C. Villani, *Optimal Transport: Old and New*, Corollary 5.23 and Definition 6.8 (`W₂`).
* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows*, Lemma 5.4.1 and Proposition 5.1.10.
-/

open Filter MeasureTheory Set TauCeti
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StatFormal.OTLimits

section Aux

variable {E : Type*} [NormedAddCommGroup E]

/-- `‖u − w‖² ≤ 2‖u − v‖² + 2‖w − v‖²`, in `ℝ≥0∞`. -/
theorem enorm_sub_sq_le (u v w : E) :
    ‖u - w‖ₑ ^ 2 ≤ 2 * ‖u - v‖ₑ ^ 2 + 2 * ‖w - v‖ₑ ^ 2 := by
  have h : ‖u - w‖₊ ≤ ‖u - v‖₊ + ‖w - v‖₊ := by
    simpa using nnnorm_sub_le (u - v) (w - v)
  have h2 : ‖u - w‖₊ ^ 2 ≤ 2 * ‖u - v‖₊ ^ 2 + 2 * ‖w - v‖₊ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) h 2).trans (add_sq_le.trans_eq (mul_add _ _ _))
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

/-- `∫ ‖f‖ₑ² dμ = ‖f‖_{L²(μ)}²`. -/
theorem lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at this
  simpa only [ENNReal.rpow_two] using this.symm

/-- A function of the first coordinate integrates against a plan as against its first
marginal. -/
theorem lintegral_comp_fst_of_fst_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ρ : Measure (X × Y)} {μ : Measure X} (hρ : ρ.fst = μ) {f : X → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ z, f z.1 ∂ρ = ∫⁻ x, f x ∂μ := by
  rw [← hρ] at hf ⊢
  exact (lintegral_map' hf measurable_fst.aemeasurable).symm

end Aux

variable {ι X E : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : ProbabilityMeasure X} {T : X → E}

/-- **`L²` concentration of plans on a graph.** Let `X` be a pseudo-metrizable Borel space, `E` a
second-countable real normed space, `μ` a probability measure on `X` and `T ∈ L²(μ; E)`. Let
probability measures `πᵢ` on `X × E` eventually have first marginal `μ`, converge weakly along a
filter to the graph plan `(id × T)#μ`, and have converging second moments,
`∫ ‖y‖² dπᵢ(x, y) → ∫ ‖T x‖² dμ`. Then `∫ ‖y − T x‖² dπᵢ(x, y) → 0`. -/
theorem tendsto_lintegral_enorm_sub_sq_of_tendsto_graphPlan {l : Filter ι}
    {πs : ι → ProbabilityMeasure (X × E)} (hT : MemLp T 2 (μ : Measure X))
    (hfst : ∀ᶠ i in l, (πs i).toMeasure.fst = μ)
    (h : Tendsto πs l (𝓝 (μ.map fun x ↦ (x, T x))))
    (hmom : Tendsto (fun i ↦ ∫⁻ z, ‖z.2‖ₑ ^ 2 ∂(πs i).toMeasure) l
      (𝓝 (∫⁻ x, ‖T x‖ₑ ^ 2 ∂(μ : Measure X)))) :
    Tendsto (fun i ↦ ∫⁻ z, ‖z.2 - T z.1‖ₑ ^ 2 ∂(πs i).toMeasure) l (𝓝 0) := by
  have hTae : AEMeasurable T μ := hT.aestronglyMeasurable.aemeasurable
  have hTfin : ∫⁻ x, ‖T x‖ₑ ^ 2 ∂(μ : Measure X) ≠ ∞ := by
    rw [lintegral_enorm_sq_eq hT.aestronglyMeasurable]
    exact ENNReal.pow_ne_top hT.eLpNorm_lt_top.ne
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun _ ↦ le_top
  set δ : ℝ≥0∞ := ε / 6 with hδdef
  have hδ : 0 < δ := ENNReal.div_pos hε.ne' (by norm_num)
  have hδtop : δ ≠ ∞ := ENNReal.div_ne_top hεtop (by norm_num)
  -- A bounded continuous approximation of `T` in `L²(μ)`.
  obtain ⟨g, hg, hgL⟩ := hT.exists_boundedContinuous_eLpNorm_sub_le (μ := (μ : Measure X))
    ENNReal.ofNat_ne_top (ε := min δ 1) (ne_of_gt (lt_min hδ one_pos))
  have hJ : ∫⁻ x, ‖T x - g x‖ₑ ^ 2 ∂(μ : Measure X) ≤ δ := by
    have := lintegral_enorm_sq_eq (f := T - (g : X → E))
      (hT.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable)
    simp only [Pi.sub_apply] at this
    rw [this]
    calc eLpNorm (T - (g : X → E)) 2 μ ^ 2 ≤ min δ 1 ^ 2 := pow_le_pow_left₀ (by positivity) hg 2
      _ ≤ min δ 1 := pow_le_of_le_one (by positivity) (min_le_right _ _) two_ne_zero
      _ ≤ δ := min_le_left _ _
  have hgc : Continuous fun x ↦ (g x : E) := g.continuous
  -- The continuous cost `‖y - g x‖²` and its dominating function.
  set c : X × E → ℝ≥0∞ := fun z ↦ ‖z.2 - g z.1‖ₑ ^ 2 with hcdef
  set F : X × E → ℝ≥0∞ := fun z ↦ 2 * ‖z.2‖ₑ ^ 2 + 2 * ‖g z.1‖ₑ ^ 2 with hFdef
  have hc : Continuous c := by fun_prop
  have hF : Continuous F := by
    have h1 : Continuous fun z : X × E ↦ ‖z.2‖ₑ ^ 2 := by fun_prop
    have h2 : Continuous fun z : X × E ↦ ‖g z.1‖ₑ ^ 2 := by fun_prop
    exact ((ENNReal.continuous_const_mul (by norm_num)).comp h1).add
      ((ENNReal.continuous_const_mul (by norm_num)).comp h2)
  have hcF : ∀ z, c z ≤ F z := fun z ↦ by
    simpa [hcdef, hFdef] using enorm_sub_sq_le z.2 0 (g z.1)
  have hgfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(μ : Measure X) ≠ ∞ := by
    rw [lintegral_enorm_sq_eq g.continuous.aestronglyMeasurable]
    exact ENNReal.pow_ne_top hgL.eLpNorm_lt_top.ne
  have hgae : AEMeasurable (fun x ↦ ‖g x‖ₑ ^ 2) (μ : Measure X) := by
    fun_prop
  have hFπ : ∫⁻ z, F z ∂((μ.map fun x ↦ (x, T x) : ProbabilityMeasure (X × E)) :
      Measure (X × E)) = 2 * ∫⁻ x, ‖T x‖ₑ ^ 2 ∂(μ : Measure X) +
        2 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(μ : Measure X) := by
    rw [toMeasure_map_prodMk_self, lintegral_graphPlan hTae hF.measurable.aemeasurable,
      lintegral_add_left' (by fun_prop), lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
  have hFlim : Tendsto (fun i ↦ ∫⁻ z, F z ∂(πs i).toMeasure) l
      (𝓝 (∫⁻ z, F z ∂((μ.map fun x ↦ (x, T x) : ProbabilityMeasure (X × E)) :
        Measure (X × E)))) := by
    rw [hFπ]
    refine Tendsto.congr' (f₁ := fun i ↦ 2 * ∫⁻ z, ‖z.2‖ₑ ^ 2 ∂(πs i).toMeasure +
      2 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(μ : Measure X)) ?_ ?_
    · filter_upwards [hfst] with i hi
      rw [hFdef, lintegral_add_left' (by fun_prop), lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (by norm_num), lintegral_comp_fst_of_fst_eq hi hgae]
    · exact ((ENNReal.Tendsto.const_mul hmom (Or.inr (by norm_num))).add tendsto_const_nhds)
  have hFfin : ∫⁻ z, F z ∂((μ.map fun x ↦ (x, T x) : ProbabilityMeasure (X × E)) :
      Measure (X × E)) ≠ ∞ := by
    rw [hFπ]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) hTfin,
      ENNReal.mul_ne_top (by norm_num) hgfin⟩
  have hI := tendsto_lintegral_of_le_of_tendsto hc (fun z ↦ by simp [hcdef]) hF hcF h hFlim hFfin
  have hIlim : ∫⁻ z, c z ∂((μ.map fun x ↦ (x, T x) : ProbabilityMeasure (X × E)) :
      Measure (X × E)) ≤ δ := by
    rw [toMeasure_map_prodMk_self, lintegral_graphPlan hTae hc.measurable.aemeasurable]
    exact hJ
  have hev : ∀ᶠ i in l, ∫⁻ z, c z ∂(πs i).toMeasure < 2 * δ :=
    hI.eventually (gt_mem_nhds (hIlim.trans_lt (by
      rw [two_mul]; exact ENNReal.lt_add_right hδtop hδ.ne')))
  filter_upwards [hev, hfst] with i hi hfi
  calc ∫⁻ z, ‖z.2 - T z.1‖ₑ ^ 2 ∂(πs i).toMeasure
      ≤ ∫⁻ z, (2 * c z + 2 * ‖T z.1 - g z.1‖ₑ ^ 2) ∂(πs i).toMeasure :=
        lintegral_mono fun z ↦ enorm_sub_sq_le z.2 (g z.1) (T z.1)
    _ = 2 * ∫⁻ z, c z ∂(πs i).toMeasure + 2 * ∫⁻ x, ‖T x - g x‖ₑ ^ 2 ∂(μ : Measure X) := by
        rw [lintegral_add_left' ((hc.measurable.const_mul _).aemeasurable),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
          lintegral_comp_fst_of_fst_eq (f := fun x ↦ ‖T x - g x‖ₑ ^ 2) hfi (by fun_prop)]
    _ ≤ 2 * (2 * δ) + 2 * δ := by gcongr
    _ = 6 * δ := by ring
    _ ≤ ε := ENNReal.mul_div_le

/-- **`L²` convergence of maps from weak convergence of graph plans.** With `μ`, `T ∈ L²(μ; E)` as
above and a.e.-measurable maps `Tᵢ`, if `(id × Tᵢ)#μ → (id × T)#μ` weakly and
`∫ ‖Tᵢ‖² dμ → ∫ ‖T‖² dμ`, then `∫ ‖Tᵢ − T‖² dμ → 0`. -/
theorem tendsto_lintegral_enorm_sub_sq_of_tendsto_map {l : Filter ι} {Ts : ι → X → E}
    (hT : MemLp T 2 (μ : Measure X)) (hTs : ∀ᶠ i in l, AEMeasurable (Ts i) μ)
    (h : Tendsto (fun i ↦ μ.map fun x ↦ (x, Ts i x)) l (𝓝 (μ.map fun x ↦ (x, T x))))
    (hmom : Tendsto (fun i ↦ ∫⁻ x, ‖Ts i x‖ₑ ^ 2 ∂(μ : Measure X)) l
      (𝓝 (∫⁻ x, ‖T x‖ₑ ^ 2 ∂(μ : Measure X)))) :
    Tendsto (fun i ↦ ∫⁻ x, ‖Ts i x - T x‖ₑ ^ 2 ∂(μ : Measure X)) l (𝓝 0) := by
  have hTae : AEMeasurable T μ := hT.aestronglyMeasurable.aemeasurable
  have key := tendsto_lintegral_enorm_sub_sq_of_tendsto_graphPlan hT
    (hTs.mono fun i hi ↦ by rw [toMeasure_map_prodMk_self, fst_graphPlan hi]) h
    (hmom.congr' (hTs.mono fun i hi ↦ by
      dsimp only
      rw [toMeasure_map_prodMk_self, lintegral_graphPlan hi (by fun_prop)]))
  refine key.congr' (hTs.mono fun i hi ↦ ?_)
  have hm : AEMeasurable (fun z : X × E ↦ ‖z.2 - T z.1‖ₑ ^ 2) (graphPlan (Ts i) μ) :=
    (measurable_snd.aemeasurable.sub (aemeasurable_comp_fst_graphPlan hi hTae)).enorm.pow_const 2
  dsimp only
  rw [toMeasure_map_prodMk_self, lintegral_graphPlan hi hm]

end StatFormal.OTLimits
