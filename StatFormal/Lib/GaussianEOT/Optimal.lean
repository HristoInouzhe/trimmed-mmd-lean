import StatFormal.Lib.GaussianEOT.Basic
import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

/-!
# The entropic optimal plan between two Gaussians on `ℝ`

Library component (GAUSS-EOT, part 2). Untrusted library code.

Cost `c(x, y) = (x − y)²/2` (`sqCost`, in `ℝ≥0∞`), temperature `ε > 0`, `μ = N(a, σ²)`, `ν = N(b, τ²)`,
`c_ε > 0` the positive root of `c² + εc = σ²τ²`. Entropic optimality is Tau Ceti's: a coupling `π` attaining
`entropicTransportCost sqCost ε μ ν = inf_π ∫ c dπ + ε KL(π ‖ μ ⊗ ν)`.

* `isCoupling_gaussCoupling`: the Gaussian coupling has marginals `μ`, `ν` (whenever `|c| ≤ στ`).
* `gaussCoupling_optimal`: the Gaussian coupling with cross-covariance `c_ε` is optimal (Schrödinger form,
  `Basic.gaussCoupling_eq_withDensity`, and Tau Ceti's sufficiency theorem).
* `entropicTransportCost_gauss`: the value is `½[(a−b)² + σ² + τ² − 2c_ε] + (ε/2) log(σ²τ²/(εc_ε))`.
* `eq_gaussCoupling_of_optimal`: every optimal coupling is the Gaussian coupling (uniqueness of the Schrödinger
  minimiser for the Gibbs reference, Tau Ceti).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real TauCeti InformationTheory
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.Foundations.GaussianEOT

/-- The quadratic cost `c(x, y) = (x − y)²/2`. -/
def sqCost (z : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((z.1 - z.2) ^ 2 / 2)

lemma measurable_sqCost : Measurable sqCost := by unfold sqCost; fun_prop

lemma sqCost_toReal (z : ℝ × ℝ) : (sqCost z).toReal = (z.1 - z.2) ^ 2 / 2 :=
  ENNReal.toReal_ofReal (by positivity)

/-! ### Marginals -/

theorem prod_map_add' (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.prod ν).map (fun u => f u.1 + g u.2) = (μ.map f) ∗ (ν.map g) := by
  change _ = ((μ.map f).prod (ν.map g)).map (fun x => x.1 + x.2)
  rw [Measure.map_prod_map μ ν hf hg, Measure.map_map (by fun_prop) (hf.prodMap hg)]
  rfl

/-- The law of `α + βU + γV`, `U, V` iid `N(0,1)`. -/
theorem gauss_lin2 (α β γ : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun u : ℝ × ℝ => α + β * u.1 + γ * u.2) =
      gaussianReal α ((β ^ 2 + γ ^ 2).toNNReal) := by
  have h := prod_map_add' (gaussianReal 0 1) (gaussianReal 0 1)
    (f := fun u => α + β * u) (g := fun u => 0 + γ * u) (by fun_prop) (by fun_prop)
  have he : (fun u : ℝ × ℝ => α + β * u.1 + γ * u.2) =
      (fun u : ℝ × ℝ => (α + β * u.1) + (0 + γ * u.2)) := by
    ext u; ring
  rw [he, h, gauss_affine, gauss_affine, gaussianReal_conv_gaussianReal]
  congr 1
  · ring
  · ext
    rw [Real.coe_toNNReal _ (by positivity)]
    change β ^ 2 * 1 + γ ^ 2 * 1 = β ^ 2 + γ ^ 2; ring

theorem gaussCoupling_map {F : ℝ × ℝ → ℝ} (hF : Measurable F) (a σ b τ c : ℝ) :
    (gaussCoupling a σ b τ c).map F =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (F ∘ fun u => (a + σ * u.1, b + c / σ * u.1 + √(τ ^ 2 - (c / σ) ^ 2) * u.2)) := by
  unfold gaussCoupling
  rw [Measure.map_map hF (by fun_prop)]

theorem gaussCoupling_fst (a σ b τ c : ℝ) :
    (gaussCoupling a σ b τ c).map Prod.fst = gaussianReal a (σ ^ 2).toNNReal := by
  rw [gaussCoupling_map measurable_fst]
  have he : (Prod.fst ∘ fun u : ℝ × ℝ => (a + σ * u.1, b + c / σ * u.1 + √(τ ^ 2 - (c / σ) ^ 2) * u.2)) =
      (fun u : ℝ × ℝ => a + σ * u.1 + 0 * u.2) := by ext u; simp
  rw [he, gauss_lin2]
  congr 2; ring

theorem gaussCoupling_snd {a σ b τ c : ℝ} (_hσ : σ ≠ 0) (hs : (c / σ) ^ 2 ≤ τ ^ 2) :
    (gaussCoupling a σ b τ c).map Prod.snd = gaussianReal b (τ ^ 2).toNNReal := by
  rw [gaussCoupling_map measurable_snd]
  have he : (Prod.snd ∘ fun u : ℝ × ℝ => (a + σ * u.1, b + c / σ * u.1 + √(τ ^ 2 - (c / σ) ^ 2) * u.2)) =
      (fun u : ℝ × ℝ => b + c / σ * u.1 + √(τ ^ 2 - (c / σ) ^ 2) * u.2) := rfl
  rw [he, gauss_lin2]
  congr 2
  rw [Real.sq_sqrt (by linarith)]; ring

theorem isCoupling_gaussCoupling {a σ b τ c : ℝ} (hσ : σ ≠ 0) (hs : (c / σ) ^ 2 ≤ τ ^ 2) :
    IsCoupling (gaussCoupling a σ b τ c) (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal) :=
  ⟨gaussCoupling_fst a σ b τ c, gaussCoupling_snd hσ hs⟩

/-! ### Integrability and moments under `N(m, v)` -/

lemma integrable_sub_const (m : ℝ) (v : ℝ≥0) (t : ℝ) : Integrable (fun x => x - t) (gaussianReal m v) :=
  ((memLp_id_gaussianReal 1).integrable le_rfl).sub (integrable_const t)

lemma integrable_sq_sub_const (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x => (x - t) ^ 2) (gaussianReal m v) := by
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal m v) := (memLp_id_gaussianReal 2).integrable_sq
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal m v) := (memLp_id_gaussianReal 1).integrable le_rfl
  have : (fun x : ℝ => (x - t) ^ 2) = fun x => x ^ 2 - 2 * t * x + t ^ 2 := by ext x; ring
  rw [this]
  exact (h2.sub (h1.const_mul _)).add (integrable_const _)

lemma integral_sub_mean (m : ℝ) (v : ℝ≥0) : ∫ x, (x - m) ∂(gaussianReal m v) = 0 := by
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal m v) := (memLp_id_gaussianReal 1).integrable le_rfl
  rw [integral_sub h1 (integrable_const m)]
  have h : ∫ x, x ∂(gaussianReal m v) = m := integral_id_gaussianReal
  simp [h]

lemma integral_sq_sub_mean (m : ℝ) (v : ℝ≥0) : ∫ x, (x - m) ^ 2 ∂(gaussianReal m v) = v := by
  have h := variance_eq_integral (X := id) (μ := gaussianReal m v) measurable_id.aemeasurable
  rw [variance_id_gaussianReal] at h
  have h0 : ∫ x, id x ∂(gaussianReal m v) = m := integral_id_gaussianReal
  rw [h0] at h
  simp only [id] at h
  exact h.symm

/-- `∫ (A(x−m)² + B(x−m) + K) dN(m, v) = Av + K`. -/
lemma integral_quad (m : ℝ) (v : ℝ≥0) (A B K : ℝ) :
    ∫ x, (A * (x - m) ^ 2 + B * (x - m) + K) ∂(gaussianReal m v) = A * v + K := by
  have i1 : Integrable (fun x => A * (x - m) ^ 2) (gaussianReal m v) :=
    (integrable_sq_sub_const m v m).const_mul A
  have i2 : Integrable (fun x => B * (x - m)) (gaussianReal m v) := (integrable_sub_const m v m).const_mul B
  rw [integral_add (f := fun x => A * (x - m) ^ 2 + B * (x - m)) (i1.add i2) (integrable_const K),
    integral_add i1 i2, integral_const_mul, integral_const_mul, integral_sq_sub_mean, integral_sub_mean]
  simp

lemma integrable_potF (ε a σ b τ c : ℝ) (v : ℝ≥0) : Integrable (potF ε a σ b τ c) (gaussianReal a v) := by
  unfold potF
  exact ((((integrable_sq_sub_const a v a).const_mul _).add ((integrable_sub_const a v a).const_mul _)).add
    (integrable_const _)).add (integrable_const _)

lemma integrable_potG (ε a σ b τ c : ℝ) (v : ℝ≥0) : Integrable (potG ε a σ b τ c) (gaussianReal b v) := by
  unfold potG
  exact ((integrable_sq_sub_const b v b).const_mul _).sub ((integrable_sub_const b v b).const_mul _)

/-! ### Optimality -/

variable {a σ b τ c ε : ℝ}

/-- The Schrödinger density in Tau Ceti's form, with `(c z).toReal` and the temperature `ε.toNNReal`. -/
theorem gaussCoupling_eq_withDensity' (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) :
    gaussCoupling a σ b τ c =
      ((gaussianReal a (σ ^ 2).toNNReal).prod (gaussianReal b (τ ^ 2).toNNReal)).withDensity
        (fun z => ENNReal.ofReal (Real.exp ((potF ε a σ b τ c z.1 + potG ε a σ b τ c z.2 - (sqCost z).toReal) /
          (ε.toNNReal : ℝ)))) := by
  rw [gaussCoupling_eq_withDensity hσ hτ hc hε hq]
  congr 1
  funext z
  rw [sqCost_toReal, Real.coe_toNNReal _ hε.le]
  rfl

theorem gaussCoupling_optimal (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) :
    ∫⁻ z, sqCost z ∂(gaussCoupling a σ b τ c) +
        ε.toNNReal * klDiv (gaussCoupling a σ b τ c)
          ((gaussianReal a (σ ^ 2).toNNReal).prod (gaussianReal b (τ ^ 2).toNNReal)) =
      entropicTransportCost sqCost ε.toNNReal (gaussianReal a (σ ^ 2).toNNReal)
        (gaussianReal b (τ ^ 2).toNNReal) := by
  have hs : (c / σ) ^ 2 ≤ τ ^ 2 := by linarith [condVar_pos hσ hc hε hq]
  exact (isCoupling_gaussCoupling hσ.ne' hs).lintegral_add_mul_klDiv_eq_entropicTransportCost_of_eq_withDensity
    measurable_sqCost.aemeasurable (ae_of_all _ fun z => ENNReal.ofReal_ne_top)
    (by simp [hε]) (gaussCoupling_eq_withDensity' hσ hτ hc hε hq)
    (integrable_potF _ _ _ _ _ _ _) (integrable_potG _ _ _ _ _ _ _)

/-- The dual value of the explicit potentials. -/
theorem dualValue_gauss (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) :
    kantorovichDualValue (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal)
        (potF ε a σ b τ c) (potG ε a σ b τ c) =
      ((a - b) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * c) / 2 + ε / 2 * Real.log (σ ^ 2 * τ ^ 2 / (ε * c)) := by
  rw [kantorovichDualValue_def]
  have hF : potF ε a σ b τ c = fun x => (1 / 2 - c / (2 * σ ^ 2)) * (x - a) ^ 2 + (a - b) * (x - a) +
      ((a - b) ^ 2 / 2 + ε / 2 * Real.log (τ ^ 2 / (τ ^ 2 - c ^ 2 / σ ^ 2))) := by
    funext x; unfold potF; ring
  have hG : potG ε a σ b τ c = fun y => (1 / 2 - σ ^ 2 / (2 * c) + ε / (2 * τ ^ 2)) * (y - b) ^ 2 +
      (-(a - b)) * (y - b) + 0 := by
    funext y; unfold potG; ring
  rw [hF, hG, integral_quad, integral_quad, Real.coe_toNNReal _ (sq_nonneg σ),
    Real.coe_toNNReal _ (sq_nonneg τ)]
  have hr : τ ^ 2 / (τ ^ 2 - c ^ 2 / σ ^ 2) = σ ^ 2 * τ ^ 2 / (ε * c) := by
    have := condVar_eq hσ hq
    rw [div_pow] at this
    rw [this]; field_simp
  rw [hr]
  have hc' : σ ^ 2 * τ ^ 2 = c * (c + ε) := by linarith
  have h1 : σ ^ 2 / (2 * c) * τ ^ 2 = (c + ε) / 2 := by
    field_simp; linarith
  have h2 : (1 / 2 - σ ^ 2 / (2 * c) + ε / (2 * τ ^ 2)) * τ ^ 2 = τ ^ 2 / 2 - (c + ε) / 2 + ε / 2 := by
    rw [← h1]; field_simp
  rw [h2]
  field_simp
  ring

/-- **The entropic transport cost between Gaussians** (Tau Ceti normalisation `∫ c dπ + ε KL(π ‖ μ ⊗ ν)`). -/
theorem entropicTransportCost_gauss (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) :
    entropicTransportCost sqCost ε.toNNReal (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal) =
      ENNReal.ofReal (((a - b) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * c) / 2 + ε / 2 * Real.log (σ ^ 2 * τ ^ 2 / (ε * c))) := by
  have hs : (c / σ) ^ 2 ≤ τ ^ 2 := by linarith [condVar_pos hσ hc hε hq]
  rw [entropicTransportCost_eq_ofReal_of_eq_withDensity (isCoupling_gaussCoupling hσ.ne' hs)
    measurable_sqCost.aemeasurable (ae_of_all _ fun z => ENNReal.ofReal_ne_top) (by simp [hε])
    (gaussCoupling_eq_withDensity' hσ hτ hc hε hq) (integrable_potF _ _ _ _ _ _ _)
    (integrable_potG _ _ _ _ _ _ _), dualValue_gauss hσ hτ hc hε hq]

/-- **Uniqueness**: every optimal coupling is the Gaussian coupling. -/
theorem eq_gaussCoupling_of_optimal (hσ : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε)
    (hq : c ^ 2 + ε * c = σ ^ 2 * τ ^ 2) {P : Measure (ℝ × ℝ)}
    (hπ : IsCoupling P (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal))
    (hopt : ∫⁻ z, sqCost z ∂P + ε.toNNReal * klDiv P
        ((gaussianReal a (σ ^ 2).toNNReal).prod (gaussianReal b (τ ^ 2).toNNReal)) =
      entropicTransportCost sqCost ε.toNNReal (gaussianReal a (σ ^ 2).toNNReal)
        (gaussianReal b (τ ^ 2).toNNReal)) :
    P = gaussCoupling a σ b τ c := by
  set μ := gaussianReal a (σ ^ 2).toNNReal
  set ν := gaussianReal b (τ ^ 2).toNNReal
  have hs : (c / σ) ^ 2 ≤ τ ^ 2 := by linarith [condVar_pos hσ hc hε hq]
  have hε' : ε.toNNReal ≠ 0 := by simp [hε]
  have hcm : AEMeasurable sqCost (μ.prod ν) := measurable_sqCost.aemeasurable
  have hct : ∀ᵐ z ∂μ.prod ν, sqCost z ≠ ∞ := ae_of_all _ fun z => ENNReal.ofReal_ne_top
  have hexp : Integrable (fun z => Real.exp (-((sqCost z).toReal / ε.toNNReal))) (μ.prod ν) :=
    TauCeti.MeasureTheory.integrable_exp_neg_of_ae_nonneg (hcm.ennreal_toReal.div_const _)
      (ae_of_all _ fun z => by positivity)
  have := isProbabilityMeasure_tilted hexp
  have hG := isCoupling_gaussCoupling (a := a) (b := b) hσ.ne' hs
  have h1 := (lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hπ hcm hct hε').1 hopt
  have h2 := (lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hG hcm hct hε').1
    (gaussCoupling_optimal hσ hτ hc hε hq)
  have hfin : schroedingerValue ((μ.prod ν).tilted fun z => -((sqCost z).toReal / ε.toNNReal)) μ ν ≠ ∞ := by
    intro hS
    have h := entropicTransportCost_eq_mul_schroedingerValue_add hcm hct hε'
    rw [hS, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hε'), top_add, entropicTransportCost_gauss hσ hτ hc hε hq] at h
    exact ENNReal.ofReal_ne_top h
  exact hπ.eq_of_klDiv_eq_schroedingerValue hG h1 h2 hfin

end StatFormal.Foundations.GaussianEOT
