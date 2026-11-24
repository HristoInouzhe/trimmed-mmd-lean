import StatFormal.Lib.GaussianEOT.Optimal

/-!
# The unregularised optimal plan between two Gaussians on `ℝ` is comonotone

Library component (GAUSS-EOT, part 3). Untrusted library code.

Cost `(x − y)²/2`, `μ = N(a, σ²)`, `ν = N(b, τ²)`, `σ, τ > 0`, `ℓ(x) = b + (τ/σ)(x − a)`. The pointwise certificate
`(x−y)²/2 = φ₀(x) + ψ₀(y) + (σ/(2τ))(y − ℓ(x))²` (`φ₀ = potF 0 … (στ)`, `ψ₀ = potG 0 … (στ)`) gives, for every coupling
`P`, `∫ (x−y)²/2 dP = ((a−b)² + (σ−τ)²)/2 + (σ/(2τ)) ∫ (y − ℓ(x))² dP`. Hence:

* `transportCost_gauss`: `transportCost sqCost μ ν = ((a−b)² + (σ−τ)²)/2`;
* `comonotone_optimal`: the Gaussian coupling with cross-covariance `στ` (the law of `(x, ℓ(x))`, `x ∼ μ`) attains it;
* `eq_comonotone_of_optimal`: every optimal coupling is that one.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real TauCeti InformationTheory
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.Foundations.GaussianEOT

variable {μ ν : Measure ℝ} {P : Measure (ℝ × ℝ)}

lemma integrable_fst_of_isCoupling (hP : IsCoupling P μ ν) {f : ℝ → ℝ} (hf : Integrable f μ) :
    Integrable (fun z : ℝ × ℝ => f z.1) P := by
  have h : P.map Prod.fst = μ := hP.fst_eq
  rw [← h] at hf
  exact hf.comp_aemeasurable measurable_fst.aemeasurable

lemma integrable_snd_of_isCoupling (hP : IsCoupling P μ ν) {f : ℝ → ℝ} (hf : Integrable f ν) :
    Integrable (fun z : ℝ × ℝ => f z.2) P := by
  have h : P.map Prod.snd = ν := hP.snd_eq
  rw [← h] at hf
  exact hf.comp_aemeasurable measurable_snd.aemeasurable

lemma integral_fst_of_isCoupling (hP : IsCoupling P μ ν) {f : ℝ → ℝ} (hf : Integrable f μ) :
    ∫ z, f z.1 ∂P = ∫ x, f x ∂μ := by
  have h : P.map Prod.fst = μ := hP.fst_eq
  rw [← h] at hf ⊢
  rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]

lemma integral_snd_of_isCoupling (hP : IsCoupling P μ ν) {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ z, f z.2 ∂P = ∫ y, f y ∂ν := by
  have h : P.map Prod.snd = ν := hP.snd_eq
  rw [← h] at hf ⊢
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]

variable {a σ b τ : ℝ}

/-- The pointwise certificate. -/
lemma sq_certificate (hσ : 0 < σ) (hτ : 0 < τ) (x y : ℝ) :
    (x - y) ^ 2 / 2 = potF 0 a σ b τ (σ * τ) x + potG 0 a σ b τ (σ * τ) y +
      σ / (2 * τ) * (y - (b + τ / σ * (x - a))) ^ 2 := by
  unfold potF potG
  field_simp
  ring

/-- For every coupling of `N(a, σ²)` and `N(b, τ²)`: the quadratic cost splits as the dual value plus a
nonnegative defect. -/
theorem integral_sqCost_eq (hσ : 0 < σ) (hτ : 0 < τ)
    (hP : IsCoupling P (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal)) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2 / 2) P ∧
    Integrable (fun z : ℝ × ℝ => (z.2 - (b + τ / σ * (z.1 - a))) ^ 2) P ∧
      ∫ z, (z.1 - z.2) ^ 2 / 2 ∂P =
        ((a - b) ^ 2 + (σ - τ) ^ 2) / 2 + σ / (2 * τ) * ∫ z, (z.2 - (b + τ / σ * (z.1 - a))) ^ 2 ∂P := by
  have hF := integrable_fst_of_isCoupling hP (integrable_potF 0 a σ b τ (σ * τ) (σ ^ 2).toNNReal)
  have hG := integrable_snd_of_isCoupling hP (integrable_potG 0 a σ b τ (σ * τ) (τ ^ 2).toNNReal)
  have h1 := integrable_fst_of_isCoupling hP (integrable_sq_sub_const a (σ ^ 2).toNNReal a)
  have h2 := integrable_snd_of_isCoupling hP (integrable_sq_sub_const b (τ ^ 2).toNNReal b)
  have hD : Integrable (fun z : ℝ × ℝ => (z.2 - (b + τ / σ * (z.1 - a))) ^ 2) P := by
    have hb : Integrable (fun z : ℝ × ℝ => 2 * (z.2 - b) ^ 2 + 2 * (τ / σ) ^ 2 * (z.1 - a) ^ 2) P :=
      (h2.const_mul 2).add (h1.const_mul _)
    refine hb.mono' (by fun_prop) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (z.2 - b + τ / σ * (z.1 - a))]
  have hsum : Integrable (fun z : ℝ × ℝ => potF 0 a σ b τ (σ * τ) z.1 + potG 0 a σ b τ (σ * τ) z.2 +
      σ / (2 * τ) * (z.2 - (b + τ / σ * (z.1 - a))) ^ 2) P := (hF.add hG).add (hD.const_mul _)
  have he : (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2 / 2) = fun z : ℝ × ℝ => potF 0 a σ b τ (σ * τ) z.1 +
      potG 0 a σ b τ (σ * τ) z.2 + σ / (2 * τ) * (z.2 - (b + τ / σ * (z.1 - a))) ^ 2 := by
    funext z; exact sq_certificate hσ hτ z.1 z.2
  refine ⟨he ▸ hsum, hD, ?_⟩
  rw [he, integral_add (f := fun z : ℝ × ℝ => potF 0 a σ b τ (σ * τ) z.1 + potG 0 a σ b τ (σ * τ) z.2)
    (hF.add hG) (hD.const_mul _), integral_add hF hG, integral_const_mul,
    integral_fst_of_isCoupling hP (integrable_potF 0 a σ b τ (σ * τ) _),
    integral_snd_of_isCoupling hP (integrable_potG 0 a σ b τ (σ * τ) _)]
  have hFe : potF 0 a σ b τ (σ * τ) = fun x => (1 / 2 - σ * τ / (2 * σ ^ 2)) * (x - a) ^ 2 + (a - b) * (x - a) +
      ((a - b) ^ 2 / 2) := by
    funext x; unfold potF; ring
  have hGe : potG 0 a σ b τ (σ * τ) = fun y => (1 / 2 - σ ^ 2 / (2 * (σ * τ)) + 0 / (2 * τ ^ 2)) * (y - b) ^ 2 +
      (-(a - b)) * (y - b) + 0 := by
    funext y; unfold potG; ring
  rw [hFe, hGe, integral_quad, integral_quad, Real.coe_toNNReal _ (sq_nonneg σ),
    Real.coe_toNNReal _ (sq_nonneg τ)]
  field_simp
  ring

/-- The lintegral of the cost as the real integral. -/
lemma lintegral_sqCost_eq (hσ : 0 < σ) (hτ : 0 < τ)
    (hP : IsCoupling P (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal)) :
    ∫⁻ z, sqCost z ∂P = ENNReal.ofReal (((a - b) ^ 2 + (σ - τ) ^ 2) / 2 +
      σ / (2 * τ) * ∫ z, (z.2 - (b + τ / σ * (z.1 - a))) ^ 2 ∂P) := by
  obtain ⟨hi, -, he⟩ := integral_sqCost_eq hσ hτ hP
  rw [← he, ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => by positivity)]
  rfl

/-- The comonotone coupling is the law of `(x, ℓ(x))`, `x ∼ N(a, σ²)`. -/
theorem gaussCoupling_comonotone (hσ : 0 < σ) (_hτ : 0 < τ) :
    gaussCoupling a σ b τ (σ * τ) =
      (gaussianReal a (σ ^ 2).toNNReal).map (fun x => (x, b + τ / σ * (x - a))) := by
  unfold gaussCoupling
  have hs : √(τ ^ 2 - (σ * τ / σ) ^ 2) = 0 := by
    rw [mul_div_cancel_left₀ _ hσ.ne', sub_self, Real.sqrt_zero]
  have he : (fun u : ℝ × ℝ => (a + σ * u.1, b + σ * τ / σ * u.1 + √(τ ^ 2 - (σ * τ / σ) ^ 2) * u.2)) =
      (fun x => (x, b + τ / σ * (x - a))) ∘ (fun u => a + σ * u) ∘ Prod.fst := by
    funext u
    simp only [Function.comp, hs, zero_mul, add_zero]
    congr 1
    field_simp
    ring
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul, gauss_affine_std]

theorem comonotone_defect_zero (hσ : 0 < σ) (hτ : 0 < τ) :
    ∫ z, (z.2 - (b + τ / σ * (z.1 - a))) ^ 2 ∂(gaussCoupling a σ b τ (σ * τ)) = 0 := by
  rw [gaussCoupling_comonotone hσ hτ, integral_map (by fun_prop) (by fun_prop)]
  simp

theorem isCoupling_comonotone (hσ : 0 < σ) (_hτ : 0 < τ) :
    IsCoupling (gaussCoupling a σ b τ (σ * τ)) (gaussianReal a (σ ^ 2).toNNReal)
      (gaussianReal b (τ ^ 2).toNNReal) :=
  isCoupling_gaussCoupling hσ.ne' (by rw [mul_div_cancel_left₀ _ hσ.ne'])

/-- **The quadratic transport cost between Gaussians on `ℝ`.** -/
theorem transportCost_gauss (hσ : 0 < σ) (hτ : 0 < τ) :
    transportCost sqCost (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal) =
      ENNReal.ofReal (((a - b) ^ 2 + (σ - τ) ^ 2) / 2) := by
  refine le_antisymm ?_ (le_transportCost fun P hP => ?_)
  · refine (transportCost_le_lintegral (isCoupling_comonotone hσ hτ) _).trans_eq ?_
    rw [lintegral_sqCost_eq hσ hτ (isCoupling_comonotone hσ hτ), comonotone_defect_zero hσ hτ, mul_zero,
      add_zero]
  · rw [lintegral_sqCost_eq hσ hτ hP]
    refine ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right ?_)
    exact mul_nonneg (by positivity) (integral_nonneg fun z => sq_nonneg _)

theorem comonotone_optimal (hσ : 0 < σ) (hτ : 0 < τ) :
    ∫⁻ z, sqCost z ∂(gaussCoupling a σ b τ (σ * τ)) =
      transportCost sqCost (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal) := by
  rw [transportCost_gauss hσ hτ, lintegral_sqCost_eq hσ hτ (isCoupling_comonotone hσ hτ),
    comonotone_defect_zero hσ hτ, mul_zero, add_zero]

/-- **Uniqueness of the optimal plan** (`π*_0` is comonotone). -/
theorem eq_comonotone_of_optimal (hσ : 0 < σ) (hτ : 0 < τ)
    (hP : IsCoupling P (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal))
    (hopt : ∫⁻ z, sqCost z ∂P =
      transportCost sqCost (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal)) :
    P = gaussCoupling a σ b τ (σ * τ) := by
  obtain ⟨-, hD, -⟩ := integral_sqCost_eq hσ hτ hP
  rw [lintegral_sqCost_eq hσ hτ hP, transportCost_gauss hσ hτ] at hopt
  have hI0 : 0 ≤ ∫ z, (z.2 - (b + τ / σ * (z.1 - a))) ^ 2 ∂P := integral_nonneg fun z => sq_nonneg _
  have hk : 0 < σ / (2 * τ) := by positivity
  have hI : ∫ z, (z.2 - (b + τ / σ * (z.1 - a))) ^ 2 ∂P = 0 := by
    have := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 hopt
    nlinarith
  have hae : ∀ᵐ z ∂P, z.2 = b + τ / σ * (z.1 - a) := by
    have := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hD).1 hI
    filter_upwards [this] with z hz
    simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hz
    linarith
  have hmap : P = P.map (fun z : ℝ × ℝ => (z.1, b + τ / σ * (z.1 - a))) := by
    conv_lhs => rw [← Measure.map_id (μ := P)]
    refine Measure.map_congr ?_
    filter_upwards [hae] with z hz
    simp only [id]
    exact Prod.ext rfl hz
  rw [hmap, gaussCoupling_comonotone hσ hτ]
  have hfst : P.map Prod.fst = gaussianReal a (σ ^ 2).toNNReal := hP.fst_eq
  rw [← hfst, Measure.map_map (by fun_prop) measurable_fst]
  rfl

end StatFormal.Foundations.GaussianEOT
