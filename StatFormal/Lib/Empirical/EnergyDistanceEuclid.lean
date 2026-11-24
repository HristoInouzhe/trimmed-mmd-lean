import StatFormal.Lib.Empirical.EnergyDistance
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Energy distance in finite-dimensional Euclidean spaces

For probability measures `P, Q` with finite first moments on a finite-dimensional real inner
product space `E` (in particular `EuclideanSpace ℝ (Fin d)`), the energy distance
`ED(P, Q) = 2 E‖X - Y‖ - E‖X - X'‖ - E‖Y - Y'‖` is non-negative and vanishes iff `P = Q`.

## Route (no Fourier integral constant needed)
Instead of the classical identity `‖x‖ = c_d ∫ (1 - cos⟨t, x⟩) / ‖t‖^{d+1} dt`, we use random
one-dimensional projections along a **standard Gaussian direction** `G ~ γ = stdGaussian E`:
`E|⟨x, G⟩| = c ‖x‖` with `c = E|N(0,1)| > 0`, since `⟨x, G⟩ ~ N(0, ‖x‖²)`
(`integral_abs_inner_stdGaussian`). By Fubini,
`ED(P, Q) = c⁻¹ ∫ ED(P_g, Q_g) dγ(g)`, where `P_g` is the law of `⟨X, g⟩`
(`energyDist_eq_integral_proj`). The one-dimensional theory (`EnergyDistance.lean`) gives
`ED(P_g, Q_g) = 2 ∫ (F_g - G_g)² ≥ 0`. If `ED(P, Q) = 0` then `P_g = Q_g` for `γ`-a.e. `g`, so
the characteristic functions of `P` and `Q` agree `γ`-a.e.; they are continuous and `γ` charges
every open set, so they agree everywhere, and `P = Q` by `Measure.ext_of_charFun`.

## Main results
* `energyDist_nonneg` — `0 ≤ ED(P, Q)`.
* `energyDist_eq_zero_iff` — `ED(P, Q) = 0 ↔ P = Q`.
* `energyDist_nonneg_euclidean`, `energyDist_eq_zero_iff_euclidean` — the case
  `E = EuclideanSpace ℝ (Fin d)`.

## References
* G. J. Székely, M. L. Rizzo, *Energy statistics: A class of statistics based on distances*,
  J. Statist. Plann. Inference 143 (2013), Prop. 1 / Thm 1.
* L. Baringhaus, C. Franz, *On a new multivariate two-sample test*, J. Multivariate Anal. 88
  (2004), 190–206 (the projection / Cramér–Wold route).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace StatFormal.Empirical

/-- The standard real Gaussian charges every nonempty open set. -/
instance isOpenPosMeasure_gaussianReal_zero_one : (gaussianReal 0 1).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure

/-- `c = E|Z|` for `Z ~ N(0, 1)` (equal to `√(2/π)`; only positivity is used). -/
noncomputable def gaussAbsMean : ℝ := ∫ s, |s| ∂(gaussianReal 0 1)

lemma integrable_abs_gaussianReal : Integrable (fun s : ℝ ↦ |s|) (gaussianReal 0 1) :=
  (IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs

lemma gaussAbsMean_pos : 0 < gaussAbsMean := by
  rw [gaussAbsMean, integral_pos_iff_support_of_nonneg (fun s ↦ abs_nonneg s)
    integrable_abs_gaussianReal]
  have hsupp : Function.support (fun s : ℝ ↦ |s|) = {0}ᶜ := by ext; simp
  have h0 : gaussianReal 0 1 {0} = 0 :=
    (gaussianReal_absolutelyContinuous 0 one_ne_zero) Real.volume_singleton
  rw [hsupp, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), h0]
  simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian measure on a finite-dimensional inner product space charges every
nonempty open set. -/
instance isOpenPosMeasure_stdGaussian : (stdGaussian E).IsOpenPosMeasure := by
  unfold stdGaussian
  refine Continuous.isOpenPosMeasure_map (by fun_prop) fun y ↦
    ⟨fun i ↦ (stdOrthonormalBasis ℝ E).repr y i, ?_⟩
  exact (stdOrthonormalBasis ℝ E).sum_repr y

/-- **Gaussian projection identity.** For `G ~ stdGaussian E` and any `x : E`,
`E|⟨x, G⟩| = c ‖x‖` with `c = E|N(0,1)|`. Proof: `⟨x, G⟩ ~ N(0, ‖x‖²) = law of ‖x‖ Z`. -/
lemma integral_abs_inner_stdGaussian (x : E) :
    ∫ g, |⟪x, g⟫| ∂(stdGaussian E) = gaussAbsMean * ‖x‖ := by
  have hmap : (stdGaussian E).map (innerSL ℝ x) = gaussianReal 0 (‖x‖ ^ 2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal (innerSL ℝ x), integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm]
  have h2 : gaussianReal 0 (‖x‖ ^ 2).toNNReal = (gaussianReal 0 1).map (‖x‖ * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp
  calc ∫ g, |⟪x, g⟫| ∂(stdGaussian E)
      = ∫ s, |s| ∂((stdGaussian E).map (innerSL ℝ x)) := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        simp
    _ = ∫ s, |‖x‖ * s| ∂(gaussianReal 0 1) := by
        rw [hmap, h2, integral_map (by fun_prop) (by fun_prop)]
    _ = gaussAbsMean * ‖x‖ := by
        simp_rw [abs_mul, abs_norm]
        rw [integral_const_mul, gaussAbsMean]
        ring

/-- Projection `x ↦ ⟨x, g⟩` onto the direction `g`. -/
def proj (g : E) : E → ℝ := fun x ↦ ⟪x, g⟫

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma continuous_proj (g : E) : Continuous (proj g) := by
  unfold proj; fun_prop

omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_proj (g : E) : Measurable (proj g) :=
  (continuous_proj g).measurable

omit [FiniteDimensional ℝ E] in
lemma integrable_id_map_proj {P : Measure E} (hP : Integrable id P) (g : E) :
    Integrable id (P.map (proj g)) := by
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  refine (hP.norm.mul_const ‖g‖).mono' (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
  simpa [proj, Real.norm_eq_abs] using abs_real_inner_le_norm x g

variable {P Q : Measure E} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- **Projection formula for the mean interpoint distance.** For probability measures `P, Q`
with finite first moments, `E‖X - Y‖ = c⁻¹ ∫ E|⟨X, g⟩ - ⟨Y, g⟩| dγ(g)` with
`γ = stdGaussian E`, `c = E|N(0,1)|`, and the integrand is `γ`-integrable. -/
lemma meanDist_eq_integral_proj (hP : Integrable id P) (hQ : Integrable id Q) :
    Integrable (fun g ↦ meanDist (P.map (proj g)) (Q.map (proj g))) (stdGaussian E) ∧
      meanDist P Q =
        gaussAbsMean⁻¹ * ∫ g, meanDist (P.map (proj g)) (Q.map (proj g)) ∂(stdGaussian E) := by
  set f : (E × E) → E → ℝ := fun z g ↦ |⟪z.1 - z.2, g⟫| with hf_def
  have hint : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖) (P.prod Q) :=
    ((hP.comp_fst Q).sub (hQ.comp_snd P)).norm
  have hF : Integrable (Function.uncurry f) ((P.prod Q).prod (stdGaussian E)) := by
    have hb := hint.mul_prod (IsGaussian.integrable_id (μ := stdGaussian E)).norm
    refine hb.mono' (by
      refine Continuous.aestronglyMeasurable ?_
      simp only [hf_def]
      fun_prop) (Eventually.of_forall fun p ↦ ?_)
    simp only [hf_def, Function.uncurry, Real.norm_eq_abs, abs_abs, id]
    exact abs_real_inner_le_norm _ _
  have hinner : ∀ g, ∫ z, f z g ∂(P.prod Q) = meanDist (P.map (proj g)) (Q.map (proj g)) := by
    intro g
    rw [meanDist, Measure.map_prod_map P Q (measurable_proj g) (measurable_proj g),
      integral_map (by fun_prop) (by fun_prop)]
    simp [hf_def, proj, inner_sub_left, Real.norm_eq_abs]
  have hc := gaussAbsMean_pos
  refine ⟨?_, ?_⟩
  · have h := hF.integral_prod_right
    simp only [Function.uncurry_apply_pair, hinner] at h
    exact h
  · have hpt : ∀ z : E × E, ‖z.1 - z.2‖ = gaussAbsMean⁻¹ * ∫ g, f z g ∂(stdGaussian E) := by
      intro z
      rw [hf_def]
      simp only
      rw [integral_abs_inner_stdGaussian]
      field_simp
    simp_rw [← hinner]
    rw [← integral_integral_swap hF, ← integral_const_mul, meanDist]
    exact integral_congr_ae (Eventually.of_forall hpt)

/-- **Projection formula for the energy distance.** For probability measures `P, Q` on `E` with
finite first moments, `ED(P, Q) = c⁻¹ ∫ ED(P_g, Q_g) dγ(g)`, where `P_g = P ∘ ⟨·, g⟩⁻¹`,
`γ = stdGaussian E` and `c = E|N(0,1)|`; the integrand is `γ`-integrable. -/
theorem energyDist_eq_integral_proj (hP : Integrable id P) (hQ : Integrable id Q) :
    Integrable (fun g ↦ energyDist (P.map (proj g)) (Q.map (proj g))) (stdGaussian E) ∧
      energyDist P Q =
        gaussAbsMean⁻¹ * ∫ g, energyDist (P.map (proj g)) (Q.map (proj g)) ∂(stdGaussian E) := by
  obtain ⟨hPQi, hPQ⟩ := meanDist_eq_integral_proj (P := P) (Q := Q) hP hQ
  obtain ⟨hPPi, hPP⟩ := meanDist_eq_integral_proj (P := P) (Q := P) hP hP
  obtain ⟨hQQi, hQQ⟩ := meanDist_eq_integral_proj (P := Q) (Q := Q) hQ hQ
  have h1 : Integrable (fun g ↦ 2 * meanDist (P.map (proj g)) (Q.map (proj g)) -
      meanDist (P.map (proj g)) (P.map (proj g))) (stdGaussian E) :=
    (hPQi.const_mul 2).sub hPPi
  refine ⟨h1.sub hQQi, ?_⟩
  simp only [energyDist]
  rw [integral_sub h1 hQQi, integral_sub (hPQi.const_mul 2) hPPi, integral_const_mul, hPQ, hPP,
    hQQ]
  ring

/-- **Non-negativity of the energy distance** (Székely–Rizzo 2013, Prop. 1). For probability
measures `P, Q` with finite first moments on a finite-dimensional real inner product space,
`ED(P, Q) = 2 E‖X - Y‖ - E‖X - X'‖ - E‖Y - Y'‖ ≥ 0`. -/
theorem energyDist_nonneg (hP : Integrable id P) (hQ : Integrable id Q) :
    0 ≤ energyDist P Q := by
  rw [(energyDist_eq_integral_proj hP hQ).2]
  have hc := gaussAbsMean_pos
  have : 0 ≤ ∫ g, energyDist (P.map (proj g)) (Q.map (proj g)) ∂(stdGaussian E) := by
    refine integral_nonneg fun g ↦ ?_
    exact energyDist_nonneg_real _ _ (integrable_id_map_proj hP g) (integrable_id_map_proj hQ g)
  positivity

omit [FiniteDimensional ℝ E] in
lemma charFun_eq_charFun_map_proj (P : Measure E) (g : E) :
    charFun P g = charFun (P.map (proj g)) 1 := by
  have := charFun_map_eq_charFun_map_inner_one (μ := P) aemeasurable_id g
  change charFun P g = charFun (P.map (fun x ↦ ⟪x, g⟫)) 1
  simpa [Measure.map_id] using this

/-- **The energy distance characterises equality** (Székely–Rizzo 2013, Prop. 1). For
probability measures `P, Q` with finite first moments on a finite-dimensional real inner product
space, `ED(P, Q) = 0 ↔ P = Q`. -/
theorem energyDist_eq_zero_iff (hP : Integrable id P) (hQ : Integrable id Q) :
    energyDist P Q = 0 ↔ P = Q := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ energyDist_self P⟩
  obtain ⟨hint, heq⟩ := energyDist_eq_integral_proj hP hQ
  have hc := gaussAbsMean_pos
  have hnn : ∀ g, 0 ≤ energyDist (P.map (proj g)) (Q.map (proj g)) := fun g ↦ by
    exact energyDist_nonneg_real _ _ (integrable_id_map_proj hP g) (integrable_id_map_proj hQ g)
  have hzero : ∫ g, energyDist (P.map (proj g)) (Q.map (proj g)) ∂(stdGaussian E) = 0 := by
    rw [h0] at heq
    have := mul_eq_zero.1 heq.symm
    rcases this with h | h
    · exact absurd h (inv_ne_zero hc.ne')
    · exact h
  rw [integral_eq_zero_iff_of_nonneg hnn hint] at hzero
  have hae : charFun P =ᵐ[stdGaussian E] charFun Q := by
    filter_upwards [hzero] with g hg
    have hPg : P.map (proj g) = Q.map (proj g) :=
      (energyDist_eq_zero_iff_real _ _ (integrable_id_map_proj hP g)
        (integrable_id_map_proj hQ g)).1 hg
    rw [charFun_eq_charFun_map_proj P g, charFun_eq_charFun_map_proj Q g, hPg]
  have hcf : charFun P = charFun Q :=
    (Continuous.ae_eq_iff_eq (stdGaussian E) continuous_charFun continuous_charFun).1 hae
  exact Measure.ext_of_charFun hcf

/-- **Energy distance on `ℝ^d`: non-negativity.** For probability measures `P, Q` on
`EuclideanSpace ℝ (Fin d)` with finite first moments, `ED(P, Q) ≥ 0`.
Source: Székely–Rizzo (2013), Prop. 1. -/
theorem energyDist_nonneg_euclidean {d : ℕ} {P Q : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable id P) (hQ : Integrable id Q) : 0 ≤ energyDist P Q :=
  energyDist_nonneg hP hQ

/-- **Energy distance on `ℝ^d`: characterisation of equality.** For probability measures `P, Q`
on `EuclideanSpace ℝ (Fin d)` with finite first moments,
`2 E‖X - Y‖ - E‖X - X'‖ - E‖Y - Y'‖ = 0 ↔ P = Q`. Source: Székely–Rizzo (2013), Prop. 1. -/
theorem energyDist_eq_zero_iff_euclidean {d : ℕ} {P Q : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable id P) (hQ : Integrable id Q) : energyDist P Q = 0 ↔ P = Q :=
  energyDist_eq_zero_iff hP hQ

end StatFormal.Empirical
