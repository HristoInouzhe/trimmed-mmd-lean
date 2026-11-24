import StatFormal.Wave31tp.Statements
import StatFormal.Lib.GaussianDensityD
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Convex.PathConnected

/-!
# Finite Gaussian mixtures on `ℝ^d`: density, analyticity, identifiability on open sets

Library component (untrusted). For weights `wᵢ ≥ 0`, means `mᵢ` and covariances `Bᵢ ≻ 0`, the
mixture `Σᵢ wᵢ • N(mᵢ, Bᵢ)` (`Wave31tp.gaussMix`, Mathlib's `multivariateGaussian` laws) has the
explicit density `p = Σᵢ wᵢ ((2π)ᵈ det Bᵢ)^{−1/2} exp(−½ (x − mᵢ)ᵀ Bᵢ⁻¹ (x − mᵢ))`
(`Wave31tp.gaussMixDens`):

* `gaussMix_eq_withDensity`: `Σᵢ wᵢ • N(mᵢ, Bᵢ) = vol.withDensity p`, from the density of each
  component (`GaussianDensityD.multivariateGaussian_eq_withDensity`) and linearity of
  `withDensity` in the density (`withDensity_finset_sum`);
* `analyticOnNhd_gaussMixDens`: `p` is real-analytic on `ℝ^d` (coordinates are continuous linear
  maps, the quadratic form is a finite sum of products, then `exp`);
* `gaussMixDens_pos`: `p > 0` when the weights are positive and sum to one;
* `exists_ne_of_gaussMix_ne`: two distinct mixtures have densities that differ somewhere in every
  nonempty open set (identity theorem for analytic functions on the connected `ℝ^d`; equal
  densities give equal laws).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal Topology

namespace StatFormal.GaussMix

open StatFormal.Wave31tp (gaussMix gaussMixDens)
open StatFormal.Foundations.GaussianDensityD (mvGaussPDF mvGaussPDF_nonneg measurable_mvGaussPDF
  multivariateGaussian_eq_withDensity)

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- `withDensity` of a finite sum of measurable densities is the sum of the `withDensity`s. -/
lemma withDensity_finset_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, Measurable (f i)) :
    μ.withDensity (∑ i ∈ s, f i) = ∑ i ∈ s, μ.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [withDensity_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      withDensity_add_left (hf a (Finset.mem_insert_self _ _)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

variable {d n : ℕ}

/-- The mixture density is the weighted sum of the component densities `mvGaussPDF`. -/
lemma gaussMixDens_eq (w : Fin n → ℝ) (m : Fin n → E d) (B : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (x : E d) : gaussMixDens w m B x = ∑ i, w i * mvGaussPDF (m i) (B i) x := rfl

/-- **The density of a finite Gaussian mixture**: `Σᵢ wᵢ • N(mᵢ, Bᵢ) = vol.withDensity p` for
`wᵢ ≥ 0`, `Bᵢ ≻ 0`. -/
theorem gaussMix_eq_withDensity {w : Fin n → ℝ} (m : Fin n → E d)
    {B : Fin n → Matrix (Fin d) (Fin d) ℝ} (hw : ∀ i, 0 ≤ w i) (hB : ∀ i, (B i).PosDef) :
    gaussMix w m B = volume.withDensity (fun x => ENNReal.ofReal (gaussMixDens w m B x)) := by
  have hpt : (fun x => ENNReal.ofReal (gaussMixDens w m B x)) =
      ∑ i, ENNReal.ofReal (w i) • fun x => ENNReal.ofReal (mvGaussPDF (m i) (B i) x) := by
    ext x
    rw [gaussMixDens_eq,
      ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hw i) (mvGaussPDF_nonneg _ _ _)]
    simp [Finset.sum_apply, ENNReal.ofReal_mul (hw _)]
  rw [hpt, withDensity_finset_sum volume Finset.univ
    (f := fun i => ENNReal.ofReal (w i) • fun x => ENNReal.ofReal (mvGaussPDF (m i) (B i) x))
    fun i _ => (ENNReal.measurable_ofReal.comp (measurable_mvGaussPDF _ _)).const_smul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [withDensity_smul (f := fun x => ENNReal.ofReal (mvGaussPDF (m i) (B i) x)) _
    (ENNReal.measurable_ofReal.comp (measurable_mvGaussPDF _ _)),
    ← multivariateGaussian_eq_withDensity (hB i)]

/-- The coordinates of `ℝ^d` are analytic (continuous linear maps). -/
lemma analyticAt_coord (j : Fin d) (x : E d) : AnalyticAt ℝ (fun y : E d => y j) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) j).analyticAt x

/-- The quadratic form `y ↦ (y − m)ᵀ M (y − m)` is analytic on `ℝ^d`. -/
lemma analyticAt_quadForm (M : Matrix (Fin d) (Fin d) ℝ) (m : E d) (x : E d) :
    AnalyticAt ℝ (fun y : E d => WithLp.ofLp (y - m) ⬝ᵥ M *ᵥ WithLp.ofLp (y - m)) x := by
  have h : (fun y : E d => WithLp.ofLp (y - m) ⬝ᵥ M *ᵥ WithLp.ofLp (y - m)) =
      fun y => ∑ j, (y j - m j) * ∑ k, M j k * (y k - m k) := by
    ext y
    simp [dotProduct, Matrix.mulVec]
  rw [h]
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  refine ((analyticAt_coord j x).sub analyticAt_const).mul ?_
  refine Finset.analyticAt_fun_sum _ fun k _ => ?_
  exact analyticAt_const.mul ((analyticAt_coord k x).sub analyticAt_const)

/-- **The mixture density is real-analytic** on `ℝ^d`. -/
theorem analyticOnNhd_gaussMixDens (w : Fin n → ℝ) (m : Fin n → E d)
    (B : Fin n → Matrix (Fin d) (Fin d) ℝ) : AnalyticOnNhd ℝ (gaussMixDens w m B) univ := by
  intro x _
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  refine analyticAt_const.mul (analyticAt_const.mul ?_)
  exact ((analyticAt_quadForm (B i)⁻¹ (m i) x).fun_neg.div_const (c := 2)).rexp'

/-- **The mixture density is positive** for positive weights summing to one and `Bᵢ ≻ 0`. -/
theorem gaussMixDens_pos {w : Fin n → ℝ} (m : Fin n → E d) {B : Fin n → Matrix (Fin d) (Fin d) ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hB : ∀ i, (B i).PosDef) (x : E d) :
    0 < gaussMixDens w m B x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hsum
  refine Finset.sum_pos (fun i _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hdet : 0 < (2 * Real.pi) ^ d * (B i).det := mul_pos (by positivity) (hB i).det_pos
  exact mul_pos (hw i) (mul_pos (inv_pos.2 (Real.sqrt_pos.2 hdet)) (Real.exp_pos _))

/-- **Distinct mixtures have densities that differ on every nonempty open set**: if the densities
agreed on a nonempty open `U`, the identity theorem on the connected `ℝ^d` would make them equal
everywhere, and then the laws would coincide. -/
theorem exists_ne_of_gaussMix_ne {n' : ℕ} {w : Fin n → ℝ} (m : Fin n → E d)
    {B : Fin n → Matrix (Fin d) (Fin d) ℝ} {w' : Fin n' → ℝ} (m' : Fin n' → E d)
    {B' : Fin n' → Matrix (Fin d) (Fin d) ℝ} (hw : ∀ i, 0 ≤ w i) (hB : ∀ i, (B i).PosDef)
    (hw' : ∀ i, 0 ≤ w' i) (hB' : ∀ i, (B' i).PosDef) (hne : gaussMix w m B ≠ gaussMix w' m' B')
    {U : Set (E d)} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ x ∈ U, gaussMixDens w m B x ≠ gaussMixDens w' m' B' x := by
  by_contra! h
  obtain ⟨x₀, hx₀⟩ := hUne
  have heq : EqOn (gaussMixDens w m B) (gaussMixDens w' m' B') univ :=
    (analyticOnNhd_gaussMixDens w m B).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_gaussMixDens w' m' B') convex_univ.isPreconnected (mem_univ x₀)
      (eventuallyEq_of_mem (hU.mem_nhds hx₀) h)
  apply hne
  rw [gaussMix_eq_withDensity m hw hB, gaussMix_eq_withDensity m' hw' hB']
  congr 1
  funext x
  rw [heq (mem_univ x)]

end StatFormal.GaussMix
