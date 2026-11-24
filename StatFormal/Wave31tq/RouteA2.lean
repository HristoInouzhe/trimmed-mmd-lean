import StatFormal.Wave31tq.Statements
import StatFormal.Wave31tp.Proofs
import StatFormal.Wave31tq.RouteSNorm
import StatFormal.Lib.AngularFourier.Basic

/-!
# Wave 31tq, route A: the angular dictionary — Q2 `spectral_angular`, Q3 `native_angular`, Q4 `bochner_angular` (untrusted)

`kHat k₀ ξ = specDens k₀ (ξ/2π)` by definition; every angular statement is the certified 31tp statement after the change of variables
`ξ = 2πη` (`AngularFourier.integral_comp_inv_two_pi_smul`, `integrable_comp_inv_two_pi_smul` for Bochner integrals,
`MollifierNorm.lintegral_comp_inv_smul` for the `[0, ∞]` functionals; `sobolevA = sobolevS` is chunk S's
`RouteS.sobolevA_eq_sobolevS`). Q2 from L13 `bochner_integrable` (inversion `𝓕⁻(𝓕 k₀) = k₀`) and L14 `gram_profile`; Q3 from L18
`native_char`; Q4 from L16 `mmd_fourier`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter FourierTransform
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteA

open StatFormal.Wave31tp StatFormal.AngularFourier

section Dict

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- `k̂₀(ξ) = specDens k₀ (ξ/2π)`. -/
theorem kHat_eq (k₀ : V → ℝ) (ξ : V) : kHat k₀ ξ = specDens k₀ ((2 * Real.pi)⁻¹ • ξ) := rfl

/-- `k̂₀(2πη) = specDens k₀ η`. -/
theorem kHat_two_pi_smul (k₀ : V → ℝ) (η : V) : kHat k₀ ((2 * Real.pi) • η) = specDens k₀ η := by
  rw [kHat_eq, inv_two_pi_smul_two_pi_smul]

/-- The angular native functional equals Mathlib's: `nativeA k₀ f = nativeN k₀ f` (substitution `ξ = 2πη`). -/
theorem nativeA_eq_nativeN (k₀ : V → ℝ) (f : V → ℂ) : nativeA k₀ f = nativeN k₀ f := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set G : V → ℝ≥0∞ := fun η => ‖ft2 f η‖ₑ ^ 2 / ENNReal.ofReal (specDens k₀ η) with hG
  have h1 : ∀ ξ : V, ‖ft2A f ξ‖ₑ ^ 2 / ENNReal.ofReal (kHat k₀ ξ) = G ((2 * Real.pi)⁻¹ • ξ) := fun ξ => rfl
  unfold nativeA nativeN
  simp_rw [h1]
  rw [MollifierNorm.lintegral_comp_inv_smul G hpi, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

end Dict

section Claims

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- `k̂₀` is real and nonnegative, integrable, and `𝓕 k₀ = specDens k₀` (complexified), for a continuous, integrable, positive
definite profile (L13 and the rescaling). -/
theorem kHat_facts {k₀ : V → ℝ} (hc : Continuous k₀) (hi : Integrable k₀) (hpd : IsPosDefFun (fun z => (k₀ z : ℂ))) :
    (∀ ξ, (ftA (fun x => (k₀ x : ℂ)) ξ).im = 0 ∧ 0 ≤ kHat k₀ ξ) ∧ Integrable (kHat k₀) ∧
      (∀ η, 𝓕 (fun x => (k₀ x : ℂ)) η = ((specDens k₀ η : ℝ) : ℂ)) ∧ 𝓕⁻ (𝓕 (fun x => (k₀ x : ℂ))) = fun x => (k₀ x : ℂ) := by
  have hc' : Continuous (fun x => (k₀ x : ℂ)) := Complex.continuous_ofReal.comp hc
  have hi' : Integrable (fun x => (k₀ x : ℂ)) := hi.ofReal
  obtain ⟨-, -, -, hft, hint, -, hinv⟩ := bochner_integrable V _ hc' hi' hpd
  refine ⟨fun ξ => hft _, integrable_comp_inv_two_pi_smul hint.re, fun η => ?_, hinv⟩
  apply Complex.ext
  · rfl
  · rw [(hft η).1, Complex.ofReal_im]

/-- `k̂₀` is integrable for a continuous, integrable, positive definite profile. -/
theorem kHat_integrable {k₀ : V → ℝ} (hc : Continuous k₀) (hi : Integrable k₀) (hpd : IsPosDefFun (fun z => (k₀ z : ℂ))) :
    Integrable (kHat k₀) :=
  (kHat_facts hc hi hpd).2.1

end Claims

theorem spectral_angular_route : Claims.spectral_angular := by
  refine ⟨fun V _ _ _ _ _ k₀ hc hi hpd => ?_, fun V _ _ _ _ _ H _ _ φ k₀ hgram => (gram_profile V H φ k₀ hgram).2.2.2.1⟩
  obtain ⟨h1, h2, hreal, hinv⟩ := kHat_facts hc hi hpd
  refine ⟨h1, h2, fun z => ?_⟩
  have hz := congrFun hinv z
  rw [Real.fourierInv_eq'] at hz
  set F : V → ℂ := fun η => Complex.exp (((2 * Real.pi * ⟪η, z⟫_ℝ : ℝ) : ℂ) * Complex.I) • 𝓕 (fun x => (k₀ x : ℂ)) η with hFdef
  have hF : ∀ ξ, (kHat k₀ ξ : ℂ) * Complex.exp (Complex.I * (⟪ξ, z⟫_ℝ : ℂ)) = F ((2 * Real.pi)⁻¹ • ξ) := by
    intro ξ
    have hin : 2 * Real.pi * ⟪(2 * Real.pi)⁻¹ • ξ, z⟫_ℝ = ⟪ξ, z⟫_ℝ := by
      rw [real_inner_smul_left]
      field_simp
    rw [kHat_eq]
    simp only [F, hreal, smul_eq_mul, hin]
    rw [mul_comm Complex.I, mul_comm]
  simp_rw [hF]
  rw [integral_comp_inv_two_pi_smul, hz, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

theorem native_angular_route : Claims.native_angular := by
  refine ⟨fun V _ _ _ _ _ => ⟨fun k₀ => funext (nativeA_eq_nativeN k₀), fun s => funext (RouteS.sobolevA_eq_sobolevS s),
    fun k₀ ξ => rfl⟩, ?_⟩
  intro V _ _ _ _ _ H _ _ _ φ k₀ hc hi hgram
  have h := native_char V H φ k₀ hc hi hgram
  simp only [nativeA_eq_nativeN]
  exact h

theorem bochner_angular_route : Claims.bochner_angular := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ hc hi hgram μ₁ μ₂ _ _
  obtain ⟨-, -, -, h⟩ := mmd_fourier V H φ k₀ hc hi hgram
  obtain ⟨hint, h1, h2⟩ := h μ₁ μ₂
  set G : V → ℝ := fun η => specDens k₀ η * ‖ftMeas μ₁ η - ftMeas μ₂ η‖ ^ 2 with hG
  have hGξ : (fun ξ => kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2) = fun ξ => G ((2 * Real.pi)⁻¹ • ξ) := rfl
  refine ⟨?_, h2, ?_⟩
  · rw [hGξ]
    exact integrable_comp_inv_two_pi_smul hint
  · change _ = _ * ∫ ξ, G ((2 * Real.pi)⁻¹ • ξ)
    rw [integral_comp_inv_two_pi_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul, h1]

end StatFormal.Wave31tq.RouteA
