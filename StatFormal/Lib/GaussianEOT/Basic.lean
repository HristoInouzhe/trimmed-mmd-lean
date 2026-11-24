import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Gaussian couplings on `ℝ × ℝ` and their Schrödinger form

Library component (GAUSS-EOT, part 1). Untrusted library code.

* `gaussCoupling a σ b τ c`: the law of `(a + σU, b + (c/σ)U + √(τ² − (c/σ)²) V)`, `U, V` iid `N(0,1)` (the same
  expression as the frozen Wave 22c `gaussPlan`).
* `lintegral_gaussCoupling`: disintegration, the conditional law of `Y` given `X = a + σu` is
  `N(b + (c/σ)u, τ² − (c/σ)²)`.
* `gaussianReal_eq_withDensity_exp`: a Gaussian whose density is another Gaussian density times `exp ∘ E`.
* `potF`, `potG`: the explicit quadratic Schrödinger potentials, and `pdf_identity`: when `c² + εc = σ²τ²`, `c > 0`,
  the conditional Gaussian density equals `ν`'s density times `exp((φ(x) + ψ(y) − (x−y)²/2)/ε)`.
* `gaussCoupling_eq_withDensity`: then `gaussCoupling = (μ ⊗ ν).withDensity (exp((φ(x) + ψ(y) − (x−y)²/2)/ε))`,
  `μ = N(a, σ²)`, `ν = N(b, τ²)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.Foundations.GaussianEOT

/-- The Gaussian coupling with means `(a, b)`, variances `(σ², τ²)` and cross-covariance `c`. -/
def gaussCoupling (a σ b τ c : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
    fun u => (a + σ * u.1, b + c / σ * u.1 + √(τ ^ 2 - (c / σ) ^ 2) * u.2)

/-- The first Schrödinger potential (against `μ ⊗ ν`). -/
def potF (ε a σ b τ c : ℝ) (x : ℝ) : ℝ :=
  (1 / 2 - c / (2 * σ ^ 2)) * (x - a) ^ 2 + (a - b) * (x - a) + (a - b) ^ 2 / 2 +
    ε / 2 * Real.log (τ ^ 2 / (τ ^ 2 - c ^ 2 / σ ^ 2))

/-- The second Schrödinger potential (against `μ ⊗ ν`). -/
def potG (ε a σ b τ c : ℝ) (y : ℝ) : ℝ :=
  (1 / 2 - σ ^ 2 / (2 * c) + ε / (2 * τ ^ 2)) * (y - b) ^ 2 - (a - b) * (y - b)

/-- The Schrödinger density against `μ ⊗ ν`: `exp((φ(x) + ψ(y) − (x−y)²/2)/ε)`. -/
def schDens (ε a σ b τ c : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp ((potF ε a σ b τ c z.1 + potG ε a σ b τ c z.2 - (z.1 - z.2) ^ 2 / 2) / ε)

lemma measurable_potF (ε a σ b τ c : ℝ) : Measurable (potF ε a σ b τ c) := by
  unfold potF; fun_prop

lemma measurable_potG (ε a σ b τ c : ℝ) : Measurable (potG ε a σ b τ c) := by
  unfold potG; fun_prop

lemma measurable_schDens (ε a σ b τ c : ℝ) : Measurable (schDens ε a σ b τ c) := by
  unfold schDens potF potG; fun_prop

/-! ### Affine images of the standard Gaussian -/

theorem gauss_affine (m : ℝ) (v : ℝ≥0) (α β : ℝ) :
    (gaussianReal m v).map (fun u => α + β * u) =
      gaussianReal (α + β * m) (⟨β ^ 2, sq_nonneg _⟩ * v) := by
  have : (fun u => α + β * u) = (fun u => α + u) ∘ (fun u => β * u) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1; ring

theorem gauss_affine_std (α β : ℝ) :
    (gaussianReal 0 1).map (fun u => α + β * u) = gaussianReal α (β ^ 2).toNNReal := by
  rw [gauss_affine]
  congr 1
  · ring
  · ext
    rw [Real.coe_toNNReal _ (sq_nonneg β)]
    change β ^ 2 * 1 = β ^ 2
    ring

/-- Disintegration of the Gaussian coupling along the first standard coordinate. -/
theorem lintegral_gaussCoupling (a σ b τ c : ℝ) (hs : (c / σ) ^ 2 ≤ τ ^ 2) {f : ℝ × ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(gaussCoupling a σ b τ c) =
      ∫⁻ u, ∫⁻ y, f (a + σ * u, y) ∂(gaussianReal (b + c / σ * u) (τ ^ 2 - (c / σ) ^ 2).toNNReal)
        ∂(gaussianReal 0 1) := by
  unfold gaussCoupling
  rw [lintegral_map hf (by fun_prop)]
  rw [lintegral_prod (fun u : ℝ × ℝ => f (a + σ * u.1, b + c / σ * u.1 + √(τ ^ 2 - (c / σ) ^ 2) * u.2))
    (hf.comp (by fun_prop)).aemeasurable]
  refine lintegral_congr fun u => ?_
  have hm : (gaussianReal 0 1).map (fun w => (b + c / σ * u) + √(τ ^ 2 - (c / σ) ^ 2) * w) =
      gaussianReal (b + c / σ * u) (τ ^ 2 - (c / σ) ^ 2).toNNReal := by
    rw [gauss_affine_std, Real.sq_sqrt (by linarith)]
  rw [← hm, lintegral_map (f := fun y => f (a + σ * u, y)) (hf.comp (by fun_prop)) (by fun_prop)]

/-! ### Densities -/

/-- A Gaussian whose density is the density of another Gaussian times `exp ∘ E`. -/
theorem gaussianReal_eq_withDensity_exp {m b : ℝ} {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0)
    {E : ℝ → ℝ} (hE : Measurable E)
    (h : ∀ y, gaussianPDFReal m w y = gaussianPDFReal b v y * Real.exp (E y)) :
    gaussianReal m w = (gaussianReal b v).withDensity (fun y => ENNReal.ofReal (Real.exp (E y))) := by
  have hm : Measurable (fun y => ENNReal.ofReal (Real.exp (E y))) := by fun_prop
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hw,
    ← withDensity_mul _ (measurable_gaussianPDF _ _) hm]
  congr 1
  funext y
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), h y]

/-- The polynomial part of the exponent identity. -/
theorem key_exponent {a σ b τ c ε x y : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) :
    -(y - (b + c / σ ^ 2 * (x - a))) ^ 2 / (2 * (τ ^ 2 - c ^ 2 / σ ^ 2)) =
      -(y - b) ^ 2 / (2 * τ ^ 2) +
        (((1 / 2 - c / (2 * σ ^ 2)) * (x - a) ^ 2 + (a - b) * (x - a) + (a - b) ^ 2 / 2) +
          ((1 / 2 - σ ^ 2 / (2 * c) + ε / (2 * τ ^ 2)) * (y - b) ^ 2 - (a - b) * (y - b)) -
          (x - y) ^ 2 / 2) / ε := by
  have hr : τ ^ 2 - c ^ 2 / σ ^ 2 = ε * c / σ ^ 2 := by
    field_simp; linarith
  rw [hr]
  field_simp
  ring

/-- The conditional variance is `εc/σ² > 0` on the quadratic `c² + εc = σ²τ²`. -/
theorem condVar_eq {σ τ c ε : ℝ} (hσ : 0 < σ) (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) :
    τ ^ 2 - (c / σ) ^ 2 = ε * c / σ ^ 2 := by
  rw [div_pow]; field_simp; linarith

theorem condVar_pos {σ τ c ε : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) : 0 < τ ^ 2 - (c / σ) ^ 2 := by
  rw [condVar_eq hσ hq]; positivity

/-- The density identity: `N(b + (c/σ²)(x−a), r)(y) = N(b, τ²)(y) · exp((φ(x) + ψ(y) − (x−y)²/2)/ε)`. -/
theorem pdf_identity {a σ b τ c ε : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) (x y : ℝ) :
    gaussianPDFReal (b + c / σ ^ 2 * (x - a)) (τ ^ 2 - (c / σ) ^ 2).toNNReal y =
      gaussianPDFReal b (τ ^ 2).toNNReal y * schDens ε a σ b τ c (x, y) := by
  have hr := condVar_pos hσ hc hε hq
  set r := τ ^ 2 - (c / σ) ^ 2 with hrdef
  have hr' : τ ^ 2 - c ^ 2 / σ ^ 2 = r := by rw [hrdef, div_pow]
  simp only [gaussianPDFReal, schDens, potF, potG, Real.coe_toNNReal _ hr.le,
    Real.coe_toNNReal _ (sq_nonneg τ)]
  rw [hr']
  have hsplit : ((1 / 2 - c / (2 * σ ^ 2)) * (x - a) ^ 2 + (a - b) * (x - a) + (a - b) ^ 2 / 2 +
        ε / 2 * Real.log (τ ^ 2 / r) +
        ((1 / 2 - σ ^ 2 / (2 * c) + ε / (2 * τ ^ 2)) * (y - b) ^ 2 - (a - b) * (y - b)) -
        (x - y) ^ 2 / 2) / ε =
      (((1 / 2 - c / (2 * σ ^ 2)) * (x - a) ^ 2 + (a - b) * (x - a) + (a - b) ^ 2 / 2) +
          ((1 / 2 - σ ^ 2 / (2 * c) + ε / (2 * τ ^ 2)) * (y - b) ^ 2 - (a - b) * (y - b)) -
          (x - y) ^ 2 / 2) / ε + Real.log (τ ^ 2 / r) / 2 := by
    field_simp; ring
  have hk := key_exponent (a := a) (b := b) (x := x) (y := y) hσ hτ hc hε hq
  rw [hr'] at hk
  rw [hsplit, Real.exp_add, hk, Real.exp_add]
  have hl : Real.exp (Real.log (τ ^ 2 / r) / 2) = τ / √r := by
    have hpos : 0 < τ ^ 2 / r := by positivity
    have h1 : Real.exp (Real.log (τ ^ 2 / r) / 2) = √(τ ^ 2 / r) := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, ← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [mul_div_cancel₀ _ (two_ne_zero), Real.exp_log hpos]
    rw [h1, Real.sqrt_div' _ hr.le, Real.sqrt_sq hτ.le]
  rw [hl]
  have h2 : √(2 * π * τ ^ 2) = √(2 * π) * τ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hτ.le]
  have h3 : √(2 * π * r) = √(2 * π) * √r := Real.sqrt_mul (by positivity) _
  rw [h2, h3]
  have hsr : 0 < √r := Real.sqrt_pos.2 hr
  have hpi : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- The conditional law is `ν` reweighted by the Schrödinger density. -/
theorem condGauss_eq_withDensity {a σ b τ c ε : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) (u : ℝ) :
    gaussianReal (b + c / σ * u) (τ ^ 2 - (c / σ) ^ 2).toNNReal =
      (gaussianReal b (τ ^ 2).toNNReal).withDensity
        (fun y => ENNReal.ofReal (schDens ε a σ b τ c (a + σ * u, y))) := by
  have hr := condVar_pos hσ hc hε hq
  have hv : (τ ^ 2).toNNReal ≠ 0 := by simp [hτ.ne']
  have hw : (τ ^ 2 - (c / σ) ^ 2).toNNReal ≠ 0 := by simp; linarith
  have hmean : b + c / σ * u = b + c / σ ^ 2 * ((a + σ * u) - a) := by field_simp; ring
  rw [hmean]
  refine gaussianReal_eq_withDensity_exp hv hw
    (E := fun y => (potF ε a σ b τ c (a + σ * u) + potG ε a σ b τ c y - ((a + σ * u) - y) ^ 2 / 2) / ε)
    (by unfold potF potG; fun_prop) fun y => ?_
  exact pdf_identity hσ hτ hc hε hq _ y

/-- Integrals against the Gaussian coupling as integrals against `μ ⊗ ν` with the Schrödinger density. -/
theorem lintegral_gaussCoupling_eq {a σ b τ c ε : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(gaussCoupling a σ b τ c) =
      ∫⁻ z, f z * ENNReal.ofReal (schDens ε a σ b τ c z)
        ∂((gaussianReal a (σ ^ 2).toNNReal).prod (gaussianReal b (τ ^ 2).toNNReal)) := by
  have hr := condVar_pos hσ hc hε hq
  have hD : Measurable fun z => ENNReal.ofReal (schDens ε a σ b τ c z) :=
    ENNReal.measurable_ofReal.comp (measurable_schDens _ _ _ _ _ _)
  have hfD : Measurable fun z => f z * ENNReal.ofReal (schDens ε a σ b τ c z) := hf.mul hD
  rw [lintegral_gaussCoupling a σ b τ c (by linarith) hf]
  set H : ℝ → ℝ≥0∞ := fun x => ∫⁻ y, f (x, y) * ENNReal.ofReal (schDens ε a σ b τ c (x, y))
    ∂(gaussianReal b (τ ^ 2).toNNReal) with hH
  have hHm : Measurable H := hfD.lintegral_prod_right'
  have hstep : ∀ u, ∫⁻ y, f (a + σ * u, y) ∂(gaussianReal (b + c / σ * u) (τ ^ 2 - (c / σ) ^ 2).toNNReal) =
      H (a + σ * u) := by
    intro u
    have hsl : Measurable fun y : ℝ => (a + σ * u, y) := measurable_const.prodMk measurable_id
    have h1 : Measurable fun y => ENNReal.ofReal (schDens ε a σ b τ c (a + σ * u, y)) := hD.comp hsl
    have h2 : Measurable fun y => f (a + σ * u, y) := hf.comp hsl
    rw [condGauss_eq_withDensity (a := a) hσ hτ hc hε hq u,
      lintegral_withDensity_eq_lintegral_mul _ h1 h2]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
  simp_rw [hstep]
  rw [← lintegral_map (f := H) hHm (by fun_prop), gauss_affine_std, lintegral_prod _ hfD.aemeasurable]

/-- **The Gaussian coupling in Schrödinger form.** If `c > 0` solves `c² + εc = σ²τ²`, the Gaussian coupling of
`μ = N(a, σ²)` and `ν = N(b, τ²)` with cross-covariance `c` has density `exp((φ(x) + ψ(y) − (x−y)²/2)/ε)` against
`μ ⊗ ν`, with the quadratic potentials `potF`, `potG`. -/
theorem gaussCoupling_eq_withDensity {a σ b τ c ε : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) :
    gaussCoupling a σ b τ c =
      ((gaussianReal a (σ ^ 2).toNNReal).prod (gaussianReal b (τ ^ 2).toNNReal)).withDensity
        (fun z => ENNReal.ofReal (schDens ε a σ b τ c z)) := by
  ext S hS
  rw [withDensity_apply _ hS, ← lintegral_indicator_one hS,
    lintegral_gaussCoupling_eq hσ hτ hc hε hq (measurable_one.indicator hS), ← lintegral_indicator hS]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ S <;> simp [hz]

end StatFormal.Foundations.GaussianEOT
