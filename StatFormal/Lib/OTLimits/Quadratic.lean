import StatFormal.Lib.OTLimits.PlanStability
import StatFormal.Lib.OTLimits.MapConvergence
import StatFormal.Lib.OTLimits.GraphL2
import TauCeti.MeasureTheory.OptimalTransport.Brenier

/-!
# Stability of Brenier maps for the quadratic cost

Library component (OT limit theory, part 3). Untrusted library code; no frozen statement is
touched.

On a finite-dimensional real inner product space `E` (e.g. `EuclideanSpace ℝ (Fin d)`) with the
quadratic cost `quadCost E (x, y) = ‖x − y‖² / 2` (Tau Ceti's Brenier normalisation; optimal plans
and maps are those of `‖x − y‖²`), the general stability theory of `PlanStability.lean`
combines with Tau Ceti's Brenier uniqueness (`TauCeti.IsOptimalCoupling.unique`) and with the
plan/map dictionary (`TauCeti.tendstoInMeasure_of_tendsto_map_prodMk_self`).

"Finite second moment" is written `∫⁻ x, ‖x‖ₑ ^ 2 ∂μ ≠ ∞` (equivalent to `MemLp id 2 μ`).
Absolute continuity is with respect to any additive Haar measure `ρ` (e.g. `volume`).

## Main results

* `tendsto_optimalPlan_quadCost`: if `μₙ → μ`, `νₙ → ν` **weakly**, all with finite second
  moments, `μ ≪ ρ`, `πₙ` is any optimal plan for `(μₙ, νₙ)` and `T` is the Brenier map of
  `(μ, ν)`, then `πₙ → (id × T)#μ` weakly. No convergence of moments is needed.
* `tendstoInMeasure_brenierMap`: with a fixed source `μ ≪ ρ` of finite second moment and
  `νₙ → ν` weakly with finite second moments, the Brenier maps `Tₙ` of `(μ, νₙ)` converge to the
  Brenier map `T` of `(μ, ν)` in `μ`-probability.
* `tendsto_lintegral_brenierMap_sub_sq`: if moreover the second moments of `νₙ` converge
  (`W₂(νₙ, ν) → 0`), then `Tₙ → T` in `L²(μ)`: `∫ ‖Tₙ − T‖² dμ → 0`.
* `tendsto_transportCost_quadCost`: if `μₙ → μ`, `νₙ → ν` weakly and the second moments converge
  (i.e. `W₂`-convergence), then `W₂²(μₙ, νₙ)/2 → W₂²(μ, ν)/2`.

## References

* C. Villani, *Optimal Transport: Old and New*, Theorem 5.20 and Corollary 5.23.
* Y. Brenier, *Polar factorization and monotone rearrangement of vector-valued functions*,
  CPAM 44 (1991); R. J. McCann, Duke Math. J. 80 (1995), for uniqueness.
-/

open Filter MeasureTheory ProbabilityTheory Set TauCeti
open scoped ENNReal Topology

namespace StatFormal.OTLimits

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The quadratic cost `‖x − y‖² / 2`, valued in `ℝ≥0∞` (the cost of Tau Ceti's Brenier
theorem). -/
noncomputable abbrev quadCost (E : Type*) [NormedAddCommGroup E] : E × E → ℝ≥0∞ :=
  fun z ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic cost is continuous (and finite everywhere). -/
theorem continuous_quadCost : Continuous (quadCost E) :=
  ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Split domination `‖x − y‖² / 2 ≤ ‖x‖² + ‖y‖²` (with `‖·‖ₑ`, the `ℝ≥0∞`-valued norm). -/
theorem quadCost_le (z : E × E) : quadCost E z ≤ ‖z.1‖ₑ ^ 2 + ‖z.2‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := norm_sub_le z.1 z.2
  have h0 : 0 ≤ ‖z.1 - z.2‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖z.1‖ - ‖z.2‖), norm_nonneg z.1, norm_nonneg z.2]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The second-moment integrand `x ↦ ‖x‖ₑ²` is continuous. -/
theorem continuous_enorm_sq : Continuous fun x : E ↦ ‖x‖ₑ ^ 2 := by fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Laws with finite second moments have finite quadratic optimal cost. -/
theorem transportCost_quadCost_ne_top (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ ≠ ∞)
    (hν : ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν ≠ ∞) : transportCost (quadCost E) μ ν ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμ, hν⟩)
    (transportCost_le_add quadCost_le continuous_enorm_sq.measurable
      continuous_enorm_sq.measurable μ ν)

variable {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **Stability of optimal quadratic plans towards a Brenier plan** (Villani, Theorem 5.20 +
Brenier uniqueness). On a finite-dimensional real inner product space, let `μₙ → μ` and
`νₙ → ν` weakly, all with finite second moments, with `μ ≪ ρ` for an additive Haar measure `ρ`.
Let `πₙ` be optimal plans for `‖x − y‖²/2` between `μₙ` and `νₙ`, and let `T` be an optimal
(Brenier) transport map from `μ` to `ν` (`IsKantorovichOptimalTransportMap`). Then
`πₙ → (id × T)#μ` weakly. The `μₙ` need not be absolutely continuous. -/
theorem tendsto_optimalPlan_quadCost {μs νs : ℕ → ProbabilityMeasure E}
    {μ ν : ProbabilityMeasure E} {πs : ℕ → ProbabilityMeasure (E × E)} {T : E → E}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hμs2 : ∀ n, ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μs n).toMeasure ≠ ∞)
    (hνs2 : ∀ n, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(νs n).toMeasure ≠ ∞)
    (hμ2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ.toMeasure ≠ ∞)
    (hν2 : ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure ≠ ∞)
    (hac : μ.toMeasure ≪ ρ)
    (hopt : ∀ n, IsOptimalCoupling (quadCost E) (πs n).toMeasure (μs n).toMeasure
      (νs n).toMeasure)
    (hT : IsKantorovichOptimalTransportMap (quadCost E) μ.toMeasure ν.toMeasure T) :
    Tendsto πs atTop (𝓝 (μ.map fun x ↦ (x, T x))) := by
  have hTopt : IsOptimalCoupling (quadCost E) (graphPlan T μ.toMeasure) μ.toMeasure
      ν.toMeasure :=
    (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hT.toHasLaw
      continuous_quadCost.measurable.aemeasurable).1 hT
  refine tendsto_of_forall_isOptimalCoupling_eq continuous_quadCost (fun _ ↦ ENNReal.ofReal_ne_top)
    hμ hν (Eventually.of_forall hopt)
    (Eventually.of_forall fun n ↦ transportCost_quadCost_ne_top _ _ (hμs2 n) (hνs2 n)) ?_
  intro π hπ
  apply Subtype.ext
  change π.toMeasure = ((μ.map fun x ↦ (x, T x) : ProbabilityMeasure (E × E)) : Measure (E × E))
  rw [toMeasure_map_prodMk_self]
  exact hπ.unique hac hTopt (transportCost_quadCost_ne_top _ _ hμ2 hν2)

/-- **Stability of Brenier maps in probability** (fixed source; Villani, Corollary 5.23 for the
quadratic cost). Let `μ ≪ ρ` (additive Haar `ρ`) have finite second moment, and let `νₙ → ν`
weakly, all with finite second moments. If `Tₙ` is an optimal transport map from `μ` to `νₙ` and
`T` one from `μ` to `ν` for `‖x − y‖²/2` (e.g. the Brenier gradients produced by
`TauCeti.exists_isKantorovichOptimalTransportMap_gradient`), then `Tₙ → T` in `μ`-measure. -/
theorem tendstoInMeasure_brenierMap {μ : ProbabilityMeasure E} {νs : ℕ → ProbabilityMeasure E}
    {ν : ProbabilityMeasure E} {Ts : ℕ → E → E} {T : E → E} (hν : Tendsto νs atTop (𝓝 ν))
    (hμ2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ.toMeasure ≠ ∞)
    (hνs2 : ∀ n, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(νs n).toMeasure ≠ ∞)
    (hν2 : ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure ≠ ∞) (hac : μ.toMeasure ≪ ρ)
    (hTs : ∀ n, IsKantorovichOptimalTransportMap (quadCost E) μ.toMeasure (νs n).toMeasure (Ts n))
    (hT : IsKantorovichOptimalTransportMap (quadCost E) μ.toMeasure ν.toMeasure T) :
    TendstoInMeasure μ.toMeasure Ts atTop T := by
  have hopt : ∀ n, IsOptimalCoupling (quadCost E)
      ((μ.map fun x ↦ (x, Ts n x) : ProbabilityMeasure (E × E)) : Measure (E × E))
      μ.toMeasure (νs n).toMeasure := fun n ↦ by
    rw [toMeasure_map_prodMk_self]
    exact (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan (hTs n).toHasLaw
      continuous_quadCost.measurable.aemeasurable).1 (hTs n)
  have hconv := tendsto_optimalPlan_quadCost (μs := fun _ ↦ μ) tendsto_const_nhds hν
    (fun _ ↦ hμ2) hνs2 hμ2 hν2 hac hopt hT
  exact tendstoInMeasure_of_tendsto_map_prodMk_self (fun n ↦ (hTs n).aemeasurable)
    hT.aemeasurable hconv

/-- **Convergence of the quadratic optimal cost under `W₂`-convergence.** If `μₙ → μ`, `νₙ → ν`
weakly and the second moments converge to finite limits, then the optimal costs for
`‖x − y‖²/2` (that is, `W₂²/2`) converge. No absolute continuity is needed. -/
theorem tendsto_transportCost_quadCost {μs νs : ℕ → ProbabilityMeasure E}
    {μ ν : ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hμm : Tendsto (fun n ↦ ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μs n).toMeasure) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ 2 ∂μ.toMeasure)))
    (hνm : Tendsto (fun n ↦ ∫⁻ y, ‖y‖ₑ ^ 2 ∂(νs n).toMeasure) atTop
      (𝓝 (∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure)))
    (hμ2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ.toMeasure ≠ ∞)
    (hν2 : ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure ≠ ∞) :
    Tendsto (fun n ↦ transportCost (quadCost E) (μs n).toMeasure (νs n).toMeasure) atTop
      (𝓝 (transportCost (quadCost E) μ.toMeasure ν.toMeasure)) :=
  tendsto_transportCost_of_le_add continuous_quadCost (fun _ ↦ ENNReal.ofReal_ne_top)
    continuous_enorm_sq continuous_enorm_sq quadCost_le hμ hν hμm hμ2 hνm hν2

/-- **`L²` stability of Brenier maps** (fixed source; Villani, Corollary 5.23 + Vitali; the
finite-dimensional form of otfd-R `lem:plan-w2`(b)). Let `μ ≪ ρ` (additive Haar `ρ`) have finite
second moment, and let `νₙ → ν` weakly with converging finite second moments
(`∫ ‖y‖² dνₙ → ∫ ‖y‖² dν < ∞`, i.e. `W₂(νₙ, ν) → 0`). If `Tₙ` and `T` are optimal transport maps for
`‖x − y‖²/2` from `μ` to `νₙ` and to `ν`, then `∫ ‖Tₙ x − T x‖² dμ → 0`. -/
theorem tendsto_lintegral_brenierMap_sub_sq {μ : ProbabilityMeasure E}
    {νs : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E} {Ts : ℕ → E → E} {T : E → E}
    (hν : Tendsto νs atTop (𝓝 ν)) (hμ2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ.toMeasure ≠ ∞)
    (hνs2 : ∀ n, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(νs n).toMeasure ≠ ∞)
    (hν2 : ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure ≠ ∞)
    (hνm : Tendsto (fun n ↦ ∫⁻ y, ‖y‖ₑ ^ 2 ∂(νs n).toMeasure) atTop
      (𝓝 (∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure)))
    (hac : μ.toMeasure ≪ ρ)
    (hTs : ∀ n, IsKantorovichOptimalTransportMap (quadCost E) μ.toMeasure (νs n).toMeasure (Ts n))
    (hT : IsKantorovichOptimalTransportMap (quadCost E) μ.toMeasure ν.toMeasure T) :
    Tendsto (fun n ↦ ∫⁻ x, ‖Ts n x - T x‖ₑ ^ 2 ∂μ.toMeasure) atTop (𝓝 0) := by
  -- The second moment of a pushforward is the second moment of the target law.
  have hmomT : ∀ {S : E → E} {β : Measure E}, HasLaw S β μ.toMeasure →
      ∫⁻ x, ‖S x‖ₑ ^ 2 ∂μ.toMeasure = ∫⁻ y, ‖y‖ₑ ^ 2 ∂β := by
    intro S β hS
    rw [← hS.map_eq, lintegral_map' (by fun_prop) hS.aemeasurable]
  have hTL : MemLp T 2 μ.toMeasure := by
    have hlt : eLpNorm T 2 μ.toMeasure < ∞ := by
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hT.aemeasurable.aestronglyMeasurable]
      simpa [ENNReal.rpow_two, hmomT hT.toHasLaw] using hν2.lt_top
    exact hlt
  have hplans : ∀ n, IsOptimalCoupling (quadCost E)
      ((μ.map fun x ↦ (x, Ts n x) : ProbabilityMeasure (E × E)) : Measure (E × E))
      μ.toMeasure (νs n).toMeasure := fun n ↦ by
    rw [toMeasure_map_prodMk_self]
    exact (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan (hTs n).toHasLaw
      continuous_quadCost.measurable.aemeasurable).1 (hTs n)
  have hconv := tendsto_optimalPlan_quadCost (ρ := ρ) (μs := fun _ ↦ μ) tendsto_const_nhds hν
    (fun _ ↦ hμ2) hνs2 hμ2 hν2 hac hplans hT
  refine tendsto_lintegral_enorm_sub_sq_of_tendsto_map hTL
    (Eventually.of_forall fun n ↦ (hTs n).aemeasurable) hconv ?_
  rw [hmomT hT.toHasLaw]
  exact hνm.congr fun n ↦ (hmomT (hTs n).toHasLaw).symm

end StatFormal.OTLimits
