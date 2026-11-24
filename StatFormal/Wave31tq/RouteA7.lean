import StatFormal.Wave31tq.RouteA2
import StatFormal.Lib.AngularFourier.PosDef

/-!
# Wave 31tq, route A: Q7 `kernel_instances` (untrusted proof file)

Angular rescaling of the certified spectra (`kHat k₀ ξ = specDens k₀ (ξ/2π)`): Matérn from L22 `matern_facts`, Gaussian from L21(a)
`gauss_spec`, the Gaussian spectral moments from L23 `gauss_moments` (substitution `ξ = 2πη`), and the Laplace profile as the Matérn
profile `maternK 1 2 σ` on `ℝ` (L22 `matern_one`). Positive definiteness of each profile from its explicit even, nonnegative,
integrable spectrum (`AngularFourier.isPosDefFun_of_fourier_eq`: L15 `fourier_feature`, Fourier inversion, L14).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter FourierTransform
open scoped ENNReal

namespace StatFormal.Wave31tq.RouteA

open StatFormal.Wave31tp StatFormal.AngularFourier

section Instances

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The Matérn angular spectrum: `k̂₀(ξ) = aℓ^d (1 + ℓ²|ξ|²)^{−s}`. -/
theorem matern_kHat {s a ℓ : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (ha : 0 < a) (hℓ : 0 < ℓ) (ξ : V) :
    kHat (maternK s a ℓ) ξ = a * ℓ ^ Module.finrank ℝ V * (1 + ℓ ^ 2 * ‖ξ‖ ^ 2) ^ (-s) := by
  obtain ⟨-, -, -, -, -, -, -, hm⟩ := matern_facts V s hs
  obtain ⟨-, -, -, hft, -⟩ := hm a ℓ ha hℓ
  rw [kHat_eq, specDens, hft, Complex.ofReal_re]
  have h4 := four_pi_sq_mul_norm_inv_two_pi_smul_sq ξ
  have hb : 1 + 4 * Real.pi ^ 2 * ℓ ^ 2 * ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2 = 1 + ℓ ^ 2 * ‖ξ‖ ^ 2 := by
    linear_combination ℓ ^ 2 * h4
  rw [hb]

/-- The Matérn profiles are positive definite. -/
theorem matern_posDef {s a ℓ : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (ha : 0 < a) (hℓ : 0 < ℓ) :
    IsPosDefFun (fun z : V => (maternK s a ℓ z : ℂ)) := by
  obtain ⟨-, -, -, -, -, -, -, hm⟩ := matern_facts V s hs
  obtain ⟨hcont, -, hint, hft, -⟩ := hm a ℓ ha hℓ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hr : (Module.finrank ℝ V : ℝ) < 2 * s := by linarith
  have hi0 := (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure V)) hr).comp_smul
    (R := 2 * Real.pi * ℓ) (by positivity)
  refine isPosDefFun_of_fourier_eq hcont hint (ψ := fun ξ => a * ℓ ^ Module.finrank ℝ V *
    (1 + 4 * Real.pi ^ 2 * ℓ ^ 2 * ‖ξ‖ ^ 2) ^ (-s)) ?_ (fun ξ => by positivity) ?_ (fun ξ => by simp only [norm_neg]) hft
  · exact measurable_const.mul ((measurable_const.add (measurable_const.mul (measurable_norm.pow_const 2))).pow_const _)
  · refine (hi0.const_mul (a * ℓ ^ Module.finrank ℝ V)).congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [norm_smul, Real.norm_of_nonneg (by positivity), show -(2 * s) / 2 = -s by ring]
    congr 3
    ring

/-- The Gaussian angular spectrum on `V`. -/
theorem gauss_kHat {σ : ℝ} (hσ : 0 < σ) (ξ : V) :
    kHat (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ξ =
      (2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(σ ^ 2 * ‖ξ‖ ^ 2 / 2)) := by
  obtain ⟨-, -, hft⟩ := gauss_spec V σ hσ
  rw [kHat_eq, specDens, hft, Complex.ofReal_re]
  have h4 := four_pi_sq_mul_norm_inv_two_pi_smul_sq ξ
  have hb : -2 * Real.pi ^ 2 * σ ^ 2 * ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2 = -(σ ^ 2 * ‖ξ‖ ^ 2 / 2) := by
    linear_combination (-(σ ^ 2) / 2) * h4
  rw [hb]

/-- The Gaussian profile on `V` is positive definite. -/
theorem gauss_posDef {σ : ℝ} (hσ : 0 < σ) :
    IsPosDefFun (fun z : V => ((Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) := by
  obtain ⟨hcont, hint, hft⟩ := gauss_spec V σ hσ
  have hpi : 0 < Real.pi := Real.pi_pos
  set σ' : ℝ := (2 * Real.pi * σ)⁻¹ with hσ'
  have hσ'0 : 0 < σ' := by positivity
  obtain ⟨-, hint', -⟩ := gauss_spec V σ' hσ'0
  refine isPosDefFun_of_fourier_eq hcont hint (ψ := fun ξ => (2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) *
    Real.exp (-2 * Real.pi ^ 2 * σ ^ 2 * ‖ξ‖ ^ 2)) ?_ (fun ξ => by positivity) ?_ (fun ξ => by simp only [norm_neg]) hft
  · exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (measurable_norm.pow_const 2)))
  · refine (hint'.const_mul ((2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2))).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only
    congr 2
    rw [hσ']
    field_simp

end Instances

/-- The Laplace profile `e^{−|x|/σ}` is the Matérn profile `maternK 1 2 σ` on `ℝ`. -/
theorem laplace_eq_matern {σ : ℝ} (hσ : 0 < σ) : (fun x : ℝ => Real.exp (-|x| / σ)) = maternK (V := ℝ) 1 2 σ := by
  funext x
  have h1 := matern_one (σ⁻¹ • x)
  simp only [maternK]
  rw [h1, smul_eq_mul]
  rw [abs_mul, abs_inv, abs_of_pos hσ, show -(σ⁻¹ * |x|) = -|x| / σ by ring]
  ring

theorem finrank_real_half_lt_one : (Module.finrank ℝ ℝ : ℝ) / 2 < 1 := by
  rw [Module.finrank_self]; norm_num

/-- On `ℝ`, `e^{−x²/(2σ²)}` is the profile `e^{−‖x‖²/(2σ²)}`. -/
theorem gauss_real_eq (σ : ℝ) : (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) = fun x : ℝ => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
  funext x
  rw [Real.norm_eq_abs, sq_abs]

theorem kernel_instances_route : Claims.kernel_instances := by
  refine ⟨fun σ hσ => ?_, fun V _ _ _ _ _ s a ℓ hs ha hℓ => ⟨matern_posDef hs ha hℓ, matern_kHat hs ha hℓ⟩,
    fun V _ _ _ _ _ σ hσ => ⟨gauss_posDef hσ, gauss_kHat hσ⟩, fun σ hσ => ?_⟩
  · -- Laplace
    have hfun := laplace_eq_matern hσ
    obtain ⟨-, -, -, -, -, -, -, hm⟩ := matern_facts ℝ 1 finrank_real_half_lt_one
    obtain ⟨hcont, -, hint, -, -⟩ := hm 2 σ two_pos hσ
    have hK : ∀ ξ : ℝ, kHat (fun x : ℝ => Real.exp (-|x| / σ)) ξ = 2 * σ / (1 + σ ^ 2 * ξ ^ 2) := by
      intro ξ
      rw [hfun, matern_kHat finrank_real_half_lt_one two_pos hσ, Module.finrank_self, pow_one, Real.rpow_neg_one,
        Real.norm_eq_abs, sq_abs, div_eq_mul_inv]
    have hpd : IsPosDefFun (fun z : ℝ => ((Real.exp (-|z| / σ) : ℝ) : ℂ)) := by
      have h := matern_posDef (V := ℝ) finrank_real_half_lt_one two_pos hσ
      rw [← hfun] at h
      exact h
    have hcont' : Continuous (fun x : ℝ => Real.exp (-|x| / σ)) := by rw [hfun]; exact hcont
    have hint' : Integrable (fun x : ℝ => Real.exp (-|x| / σ)) := by rw [hfun]; exact hint
    refine ⟨hcont', hint', hpd, hK, fun ξ => ?_, fun ξ hξ => ?_⟩
    · have hD : 0 < 1 + σ ^ 2 * ξ ^ 2 := by positivity
      have hE : 0 < 1 + ξ ^ 2 := by positivity
      rw [hK, Real.rpow_neg_one]
      set m := min 1 (σ ^ 2)⁻¹ with hm_def
      set M := max 1 (σ ^ 2)⁻¹ with hM_def
      have hm1 : m ≤ 1 := min_le_left _ _
      have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
      have hm2 : m * σ ^ 2 ≤ 1 := by
        calc m * σ ^ 2 ≤ (σ ^ 2)⁻¹ * σ ^ 2 := by gcongr; exact min_le_right _ _
          _ = 1 := inv_mul_cancel₀ (by positivity)
      have hM1 : 1 ≤ M := le_max_left _ _
      have hM2 : 1 ≤ M * σ ^ 2 := by
        calc (1 : ℝ) = (σ ^ 2)⁻¹ * σ ^ 2 := (inv_mul_cancel₀ (by positivity)).symm
          _ ≤ M * σ ^ 2 := by gcongr; exact le_max_right _ _
      have key1 : m * (1 + σ ^ 2 * ξ ^ 2) ≤ 1 + ξ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hm2 (sq_nonneg ξ)]
      have key2 : 1 + ξ ^ 2 ≤ M * (1 + σ ^ 2 * ξ ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hM2 (sq_nonneg ξ)]
      constructor
      · have h : m / (1 + ξ ^ 2) ≤ 1 / (1 + σ ^ 2 * ξ ^ 2) := by
          rw [div_le_div_iff₀ hE hD]; linarith [key1]
        calc 2 * σ * m * (1 + ξ ^ 2)⁻¹ = 2 * σ * (m / (1 + ξ ^ 2)) := by ring
          _ ≤ 2 * σ * (1 / (1 + σ ^ 2 * ξ ^ 2)) := by gcongr
          _ = 2 * σ / (1 + σ ^ 2 * ξ ^ 2) := by ring
      · have h : 1 / (1 + σ ^ 2 * ξ ^ 2) ≤ M / (1 + ξ ^ 2) := by
          rw [div_le_div_iff₀ hD hE]; linarith [key2]
        calc 2 * σ / (1 + σ ^ 2 * ξ ^ 2) = 2 * σ * (1 / (1 + σ ^ 2 * ξ ^ 2)) := by ring
          _ ≤ 2 * σ * (M / (1 + ξ ^ 2)) := by gcongr
          _ = 2 * σ * M * (1 + ξ ^ 2)⁻¹ := by ring
    · have hD : 0 < 1 + σ ^ 2 * ξ ^ 2 := by positivity
      have hξ2 : 0 < ξ ^ 2 := lt_of_le_of_ne (sq_nonneg ξ) (Ne.symm (pow_ne_zero 2 hξ))
      have hr : |ξ| ^ (-2 * (1 : ℝ)) = (ξ ^ 2)⁻¹ := by
        rw [show -2 * (1 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg (abs_nonneg ξ), Real.rpow_two, sq_abs]
      rw [hK, hr, div_le_iff₀ hD]
      have he : 2 / σ * (ξ ^ 2)⁻¹ * (1 + σ ^ 2 * ξ ^ 2) = 2 / σ * (ξ ^ 2)⁻¹ + 2 * σ := by
        field_simp
      have hpos : 0 < 2 / σ * (ξ ^ 2)⁻¹ := by positivity
      rw [he]
      linarith
  · -- Gaussian on ℝ
    have hg := gauss_real_eq σ
    have hpd : IsPosDefFun (fun z : ℝ => ((Real.exp (-z ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) := by
      have h := gauss_posDef (V := ℝ) hσ
      simp only [Real.norm_eq_abs, sq_abs] at h
      exact h
    have hK : ∀ ξ : ℝ, kHat (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ =
        √(2 * Real.pi) * σ * Real.exp (-(σ ^ 2 * ξ ^ 2 / 2)) := by
      intro ξ
      rw [hg, gauss_kHat hσ, Module.finrank_self, Nat.cast_one, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le]
    refine ⟨hpd, hK, fun N => ?_⟩
    obtain ⟨h23i, h23⟩ := gauss_moments σ N hσ
    set F : ℝ → ℝ := fun η => (2 * Real.pi * η) ^ (2 * N) *
      specDens (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) η with hF
    have hFξ : (fun ξ : ℝ => ξ ^ (2 * N) * kHat (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ) =
        fun ξ => F ((2 * Real.pi)⁻¹ • ξ) := by
      funext ξ
      simp only [F, kHat_eq, smul_eq_mul]
      rw [show 2 * Real.pi * ((2 * Real.pi)⁻¹ * ξ) = ξ by field_simp]
    refine ⟨?_, ?_⟩
    · rw [hFξ]
      exact integrable_comp_inv_two_pi_smul h23i
    · rw [hFξ, integral_comp_inv_two_pi_smul, h23, Module.finrank_self, pow_one, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (by positivity), one_mul]

end StatFormal.Wave31tq.RouteA
