import StatFormal.Lib.Matern.Basic
import StatFormal.Lib.TIKernel.Spectra
import StatFormal.Lib.FourierOps.Dilate

/-!
# Bessel potentials by Gaussian subordination: integrability, Fourier transform, the Matérn family (library, untrusted)

With Mathlib's convention `𝓕 f (ξ) = ∫ 𝐞(−⟪x, ξ⟫) f x dx` on a finite-dimensional real inner-product space `V`,
`d = finrank ℝ V`, and `s > d/2`, the Bessel potential `G_s = Wave31tp.besselPot s` satisfies (Stein, *Singular Integrals*, V.3.1):

* the heat kernel `e^{−‖x‖²/(4t)}` has integral `(4πt)^{d/2}` (`integral_heat`) and transform `(4πt)^{d/2} e^{−4π²t‖ξ‖²}`
  (`fourier_heat`, the Gaussian transform `TIKernel.fourier_gauss` at `σ² = 2t`);
* the subordination integrand is integrable on `V × (0, ∞)` (`integrable_integrand_prod`, Tonelli: its `x`-integral is the Gamma
  integrand `t^{s−1} e^{−t}`), so `G_s` is integrable (`integrable_besselPot`);
* `𝓕 G_s (ξ) = Γ(s)⁻¹ ∫₀^∞ t^{s−1} e^{−t(1 + 4π²‖ξ‖²)} dt = (1 + 4π²‖ξ‖²)^{−s}` (`fourier_besselPot`, Fubini), hence `∫ G_s = 1`
  (`integral_besselPot`).

For `a > 0`, `ℓ > 0` the Matérn profile `k_{a,ℓ}(x) = a G_s(x/ℓ)` (`Wave31tp.maternK`) is continuous, positive and integrable, with
`𝓕 k_{a,ℓ}(ξ) = a ℓ^d (1 + 4π²ℓ²‖ξ‖²)^{−s}` (`fourier_maternK`, via `FourierOps.fourier_dilate`), and its spectral density is
comparable to the Sobolev weight: `a ℓ^d max(1, ℓ²)^{−s} (1 + 4π²‖ξ‖²)^{−s} ≤ specDens k_{a,ℓ} ξ ≤ a ℓ^d max(1, ℓ^{−2})^s
(1 + 4π²‖ξ‖²)^{−s}` (`specDens_maternK_lower`, `specDens_maternK_upper`), from `min(1, ℓ²)(1 + u) ≤ 1 + ℓ²u ≤ max(1, ℓ²)(1 + u)`.
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform
open scoped InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatFormal.Matern

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

section Heat

/-- The heat kernel `e^{−‖x‖²/(4t)}` is the Gaussian profile of variance `σ² = 2t`, `σ = √(2t)`. -/
lemma heat_eq_gauss {t : ℝ} (ht : 0 < t) :
    (fun x : V => Real.exp (-‖x‖ ^ 2 / (4 * t))) = fun x => Real.exp (-‖x‖ ^ 2 / (2 * √(2 * t) ^ 2)) := by
  funext x
  rw [Real.sq_sqrt (by positivity), show 2 * (2 * t) = 4 * t by ring]

/-- The heat kernel is integrable. -/
lemma heat_integrable {t : ℝ} (ht : 0 < t) : Integrable (fun x : V => Real.exp (-‖x‖ ^ 2 / (4 * t))) := by
  rw [heat_eq_gauss ht]
  exact TIKernel.gauss_integrable (Real.sqrt_pos.2 (by positivity))

/-- The integral of the heat kernel: `∫ e^{−‖x‖²/(4t)} dx = (4πt)^{d/2}`. -/
lemma integral_heat {t : ℝ} (ht : 0 < t) :
    ∫ x : V, Real.exp (-‖x‖ ^ 2 / (4 * t)) = (4 * Real.pi * t) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (inv_pos.2 (by positivity : 0 < 4 * t))
  rw [div_inv_eq_mul, show Real.pi * (4 * t) = 4 * Real.pi * t by ring] at h
  rw [← h]
  congr 1
  funext x
  congr 1
  rw [neg_div, neg_mul, div_eq_inv_mul]

/-- **Fourier transform of the heat kernel**: `𝓕[e^{−‖x‖²/(4t)}](ξ) = (4πt)^{d/2} e^{−4π²t‖ξ‖²}`. -/
lemma fourier_heat {t : ℝ} (ht : 0 < t) (ξ : V) :
    𝓕 (fun x : V => ((Real.exp (-‖x‖ ^ 2 / (4 * t)) : ℝ) : ℂ)) ξ =
      (((4 * Real.pi * t) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  have e : (fun x : V => ((Real.exp (-‖x‖ ^ 2 / (4 * t)) : ℝ) : ℂ)) =
      fun x => ((Real.exp (-‖x‖ ^ 2 / (2 * √(2 * t) ^ 2)) : ℝ) : ℂ) := by
    funext x
    rw [Real.sq_sqrt (by positivity), show 2 * (2 * t) = 4 * t by ring]
  rw [e, TIKernel.fourier_gauss (Real.sqrt_pos.2 (by positivity)), Real.sq_sqrt (by positivity),
    show 2 * Real.pi * (2 * t) = 4 * Real.pi * t by ring,
    show -2 * Real.pi ^ 2 * (2 * t) * ‖ξ‖ ^ 2 = -4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 by ring]

end Heat

section Rpow

/-- `x^{−y/2} · x^{y/2} = 1` for `x > 0`. -/
lemma rpow_neg_half_mul_rpow_half {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ (-y / 2) * x ^ (y / 2) = 1 := by
  rw [← Real.rpow_add hx, show -y / 2 + y / 2 = 0 by ring, Real.rpow_zero]

end Rpow

section Subordination

/-- The `x`-integral of the subordination integrand is the Gamma integrand: `∫ integrand s x t dx = t^{s−1} e^{−t}`, `t > 0`. -/
lemma integral_integrand_space (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x : V, integrand s x t = t ^ (s - 1) * Real.exp (-t) := by
  simp only [integrand]
  rw [integral_const_mul, integral_heat (V := V) ht, mul_assoc, rpow_neg_half_mul_rpow_half (by positivity), mul_one]

/-- **Tonelli for the subordination integrand**: for `s > d/2` it is integrable on `V × (0, ∞)`. -/
theorem integrable_integrand_prod {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) :
    Integrable (Function.uncurry (integrand (V := V) s)) ((volume : Measure V).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  rw [integrable_prod_iff' (measurable_integrand s).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    simp only [Function.uncurry_apply_pair]
    unfold integrand
    exact (heat_integrable (V := V) ht).const_mul _
  · have hG : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-t)) (Ioi 0) :=
      IntegrableOn.congr_fun (Real.GammaIntegral_convergent hs0) (fun t _ => mul_comm _ _) measurableSet_Ioi
    refine IntegrableOn.congr_fun hG (fun t ht => ?_) measurableSet_Ioi
    simp only [Function.uncurry_apply_pair]
    rw [← integral_integrand_space (V := V) s ht]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_of_pos (integrand_pos s x ht)]

/-- **Integrability of the Bessel potential** `G_s`, `s > d/2`. -/
theorem integrable_besselPot {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) : Integrable (besselPot (V := V) s) :=
  ((integrable_integrand_prod hs).integral_prod_left).const_mul _

/-- The `x`-Fourier transform of the subordination integrand: `t^{s−1} e^{−t(1 + 4π²‖ξ‖²)}`, `t > 0`. -/
lemma fourier_integrand_space (s : ℝ) {t : ℝ} (ht : 0 < t) (ξ : V) :
    ∫ x : V, (𝐞 (-⟪x, ξ⟫) : ℂ) * (integrand s x t : ℂ) =
      ((t ^ (s - 1) * Real.exp (-((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * t)) : ℝ) : ℂ) := by
  have hpt : ∀ x : V, (𝐞 (-⟪x, ξ⟫) : ℂ) * (integrand s x t : ℂ) =
      ((t ^ (s - 1) * Real.exp (-t) * (4 * Real.pi * t) ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) *
        (𝐞 (-⟪x, ξ⟫) • ((Real.exp (-‖x‖ ^ 2 / (4 * t)) : ℝ) : ℂ)) := by
    intro x
    simp only [integrand, Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  have hF := fourier_heat (V := V) ht ξ
  simp only [Real.fourier_eq] at hF
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, hF, ← Complex.ofReal_mul]
  congr 1
  rw [show -((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * t) = -t + -4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 by ring, Real.exp_add]
  have h1 := rpow_neg_half_mul_rpow_half (by positivity : 0 < 4 * Real.pi * t) (Module.finrank ℝ V : ℝ)
  calc t ^ (s - 1) * Real.exp (-t) * (4 * Real.pi * t) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
        ((4 * Real.pi * t) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2))
      = t ^ (s - 1) * Real.exp (-t) * ((4 * Real.pi * t) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
        (4 * Real.pi * t) ^ ((Module.finrank ℝ V : ℝ) / 2)) * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) := by ring
    _ = _ := by rw [h1]; ring

/-- The character times the integrand is integrable on `V × (0, ∞)` (it has the same norm). -/
lemma integrable_char_integrand_prod {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (ξ : V) :
    Integrable (Function.uncurry fun (x : V) (t : ℝ) => (𝐞 (-⟪x, ξ⟫) : ℂ) * (integrand s x t : ℂ))
      ((volume : Measure V).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  refine (integrable_integrand_prod hs).mono ?_ (Eventually.of_forall fun p => ?_)
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_fst.inner continuous_const).neg)).aestronglyMeasurable
    · exact (Complex.measurable_ofReal.comp (measurable_integrand s)).aestronglyMeasurable
  · simp only [Function.uncurry, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, le_refl]

/-- **The Fourier transform of the Bessel potential**: `𝓕 G_s (ξ) = (1 + 4π²‖ξ‖²)^{−s}` for `s > d/2`. -/
theorem fourier_besselPot {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (ξ : V) :
    𝓕 (fun x : V => (besselPot s x : ℂ)) ξ = (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) : ℝ) : ℂ) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  set r : ℝ := 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 with hr_def
  have hr : 0 < r := by positivity
  have h1 : ∀ x : V, 𝐞 (-⟪x, ξ⟫) • (besselPot s x : ℂ) =
      (((Real.Gamma s)⁻¹ : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ), (𝐞 (-⟪x, ξ⟫) : ℂ) * (integrand s x t : ℂ) := by
    intro x
    have hI : ((∫ t in Ioi (0 : ℝ), integrand s x t : ℝ) : ℂ) = ∫ t in Ioi (0 : ℝ), (integrand s x t : ℂ) :=
      integral_complex_ofReal.symm
    rw [Circle.smul_def, smul_eq_mul, besselPot_eq, Complex.ofReal_mul, hI, integral_const_mul]
    ring
  have h2 : 𝓕 (fun x : V => (besselPot s x : ℂ)) ξ =
      ∫ x : V, (((Real.Gamma s)⁻¹ : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ), (𝐞 (-⟪x, ξ⟫) : ℂ) * (integrand s x t : ℂ) := by
    rw [Real.fourier_eq]
    exact integral_congr_ae (Eventually.of_forall h1)
  rw [h2, integral_const_mul, integral_integral_swap (integrable_char_integrand_prod hs ξ),
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => fourier_integrand_space s ht ξ), integral_complex_ofReal,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 hr, ← Complex.ofReal_mul]
  congr 1
  rw [one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le]
  have hG := (Gamma_pos hs).ne'
  field_simp

/-- **The Bessel potential is a probability density**: `∫ G_s = 1` for `s > d/2` (its transform at `0`). -/
theorem integral_besselPot {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) : ∫ x, besselPot (V := V) s x = 1 := by
  have h := fourier_besselPot hs (0 : V)
  simp only [Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul, norm_zero] at h
  rw [integral_complex_ofReal] at h
  simpa using h

end Subordination

section Family

/-- The Matérn profile is continuous. -/
theorem continuous_maternK {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (a ℓ : ℝ) :
    Continuous (maternK (V := V) s a ℓ) :=
  continuous_const.mul ((continuous_besselPot hs).comp (continuous_const_smul _))

/-- The Matérn profile is positive for `a > 0`. -/
theorem maternK_pos {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) {a : ℝ} (ha : 0 < a) (ℓ : ℝ) (x : V) :
    0 < maternK s a ℓ x :=
  mul_pos ha (besselPot_pos hs _)

/-- The Matérn profile is integrable for `ℓ ≠ 0`. -/
theorem integrable_maternK {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (a : ℝ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    Integrable (maternK (V := V) s a ℓ) :=
  ((integrable_besselPot hs).comp_smul (inv_ne_zero hℓ)).const_mul a

/-- **The Fourier transform of the Matérn profile**: `𝓕 k_{a,ℓ}(ξ) = a ℓ^d (1 + 4π²ℓ²‖ξ‖²)^{−s}` for `ℓ > 0`. -/
theorem fourier_maternK {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (ξ : V) :
    𝓕 (fun x : V => (maternK s a ℓ x : ℂ)) ξ =
      ((a * ℓ ^ Module.finrank ℝ V * (1 + 4 * Real.pi ^ 2 * ℓ ^ 2 * ‖ξ‖ ^ 2) ^ (-s) : ℝ) : ℂ) := by
  have hd : ((ℓ : ℂ) ^ Module.finrank ℝ V) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 hℓ.ne')
  have e : 𝓕 (fun x : V => (maternK s a ℓ x : ℂ)) ξ =
      ((a * ℓ ^ Module.finrank ℝ V : ℝ) : ℂ) * 𝓕 (dilate ℓ fun y : V => (besselPot s y : ℂ)) ξ := by
    rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [maternK, dilate, Circle.smul_def, smul_eq_mul]
    push_cast
    field_simp
  rw [e, FourierOps.fourier_dilate _ hℓ, fourier_besselPot hs, ← Complex.ofReal_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hℓ, mul_pow, ← mul_assoc (4 * Real.pi ^ 2)]

/-- The spectral density of the Matérn profile: `specDens k_{a,ℓ} ξ = a ℓ^d (1 + 4π²ℓ²‖ξ‖²)^{−s}`. -/
theorem specDens_maternK {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (ξ : V) :
    specDens (maternK (V := V) s a ℓ) ξ = a * ℓ ^ Module.finrank ℝ V * (1 + 4 * Real.pi ^ 2 * ℓ ^ 2 * ‖ξ‖ ^ 2) ^ (-s) := by
  simp only [specDens]
  rw [fourier_maternK hs a hℓ ξ, Complex.ofReal_re]

/-- `1 + c u ≤ max(1, c) (1 + u)` for `u ≥ 0`. -/
lemma one_add_mul_le_max {c u : ℝ} (hu : 0 ≤ u) : 1 + c * u ≤ max 1 c * (1 + u) := by
  have h1 := le_max_left 1 c
  have h2 := le_max_right 1 c
  nlinarith [mul_le_mul_of_nonneg_right h2 hu]

/-- `max(1, c⁻¹)⁻¹ (1 + u) ≤ 1 + c u` for `c > 0`, `u ≥ 0` (`max(1, c⁻¹)⁻¹ = min(1, c)`). -/
lemma max_inv_mul_le_one_add_mul {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) : (max 1 c⁻¹)⁻¹ * (1 + u) ≤ 1 + c * u := by
  have hM : 0 < max 1 c⁻¹ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : (max 1 c⁻¹)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_max_left _ _)
  have h2 : (max 1 c⁻¹)⁻¹ ≤ c := inv_le_of_inv_le₀ hc (le_max_right _ _)
  nlinarith [mul_le_mul_of_nonneg_right h2 hu]

/-- **Lower spectral bound of the Matérn profile**: `a ℓ^d max(1, ℓ²)^{−s} (1 + 4π²‖ξ‖²)^{−s} ≤ specDens k_{a,ℓ} ξ`. -/
theorem specDens_maternK_lower {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ)
    (ξ : V) :
    a * ℓ ^ Module.finrank ℝ V * (max 1 (ℓ ^ 2)) ^ (-s) * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤
      specDens (maternK s a ℓ) ξ := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  have hu : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hM : 0 ≤ max 1 (ℓ ^ 2) := le_trans zero_le_one (le_max_left _ _)
  rw [specDens_maternK hs a hℓ, mul_assoc (a * ℓ ^ Module.finrank ℝ V), ← Real.mul_rpow hM (by positivity)]
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.2 hs0.le))
    (by positivity)
  have := one_add_mul_le_max (c := ℓ ^ 2) hu
  calc 1 + 4 * Real.pi ^ 2 * ℓ ^ 2 * ‖ξ‖ ^ 2 = 1 + ℓ ^ 2 * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := by ring
    _ ≤ _ := this

/-- **Upper spectral bound of the Matérn profile**: `specDens k_{a,ℓ} ξ ≤ a ℓ^d max(1, ℓ^{−2})^s (1 + 4π²‖ξ‖²)^{−s}`. -/
theorem specDens_maternK_upper {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ)
    (ξ : V) :
    specDens (maternK s a ℓ) ξ ≤
      a * ℓ ^ Module.finrank ℝ V * (max 1 (ℓ ^ 2)⁻¹) ^ s * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  have hu : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hM : 0 < max 1 (ℓ ^ 2)⁻¹ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hMs : (max 1 (ℓ ^ 2)⁻¹) ^ s = ((max 1 (ℓ ^ 2)⁻¹)⁻¹) ^ (-s) := by
    rw [Real.rpow_neg (inv_nonneg.2 hM.le), Real.inv_rpow hM.le, inv_inv]
  rw [specDens_maternK hs a hℓ, hMs, mul_assoc (a * ℓ ^ Module.finrank ℝ V),
    ← Real.mul_rpow (inv_nonneg.2 hM.le) (by positivity)]
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.2 hs0.le))
    (by positivity)
  have := max_inv_mul_le_one_add_mul (c := ℓ ^ 2) (by positivity) hu
  calc (max 1 (ℓ ^ 2)⁻¹)⁻¹ * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ≤ 1 + ℓ ^ 2 * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := this
    _ = 1 + 4 * Real.pi ^ 2 * ℓ ^ 2 * ‖ξ‖ ^ 2 := by ring

end Family

end StatFormal.Matern
