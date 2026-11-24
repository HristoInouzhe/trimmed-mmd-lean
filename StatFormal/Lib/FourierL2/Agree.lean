import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The L² Fourier transform agrees with the integral transform on L¹ ∩ L² (library, untrusted)

For `f : V → ℂ` integrable and square integrable on a finite-dimensional real inner-product space `V`, Mathlib's unitary L²
Fourier transform `Lp.fourierTransformₗᵢ` (defined by density of Schwartz functions) equals the integral transform `𝓕 f`
almost everywhere, and likewise for the inverse transforms (Rudin, *Real and Complex Analysis*, Thm 9.13). Route: tempered
distributions (`Lp.fourier_toTemperedDistribution_eq`), the exchange formula against Schwartz test functions, and
`ae_eq_of_integral_contDiff_smul_eq`. Consequence: Plancherel's identity for the integral transform on L¹ ∩ L².
-/

noncomputable section
open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal InnerProductSpace ContDiff

set_option linter.unusedSectionVars false

namespace StatFormal.FourierL2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

lemma innerₗ_flip : (innerₗ V).flip = innerₗ V := by
  ext x y; simp

/-- Exchange formula: `∫ 𝓕u • f = ∫ u • 𝓕f` for a Schwartz `u` and an integrable `f`. -/
lemma integral_fourier_smul_of_schwartz (u : 𝓢(V, ℂ)) {f : V → ℂ} (hf : Integrable f) :
    ∫ x, 𝓕 (u : V → ℂ) x • f x = ∫ ξ, u ξ • 𝓕 f ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar) (μ := volume)
    (ν := volume) (L := innerₗ V) (f := (u : V → ℂ)) (g := f) Real.continuous_fourierChar
    continuous_inner u.integrable hf
  rw [innerₗ_flip] at h
  exact h

/-- Inverse exchange formula: `∫ 𝓕⁻u • f = ∫ u • 𝓕⁻f`. -/
lemma integral_fourierInv_smul_of_schwartz (u : 𝓢(V, ℂ)) {f : V → ℂ} (hf : Integrable f) :
    ∫ x, 𝓕⁻ (u : V → ℂ) x • f x = ∫ ξ, u ξ • 𝓕⁻ f ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar) (μ := volume)
    (ν := volume) (L := -innerₗ V) (f := (u : V → ℂ)) (g := f) Real.continuous_fourierChar
    (by simpa [Pi.neg_def] using (continuous_inner (𝕜 := ℝ) (E := V)).neg) u.integrable hf
  have hflip : (-innerₗ V : V →ₗ[ℝ] V →ₗ[ℝ] ℝ).flip = -innerₗ V := by
    ext x y; simp [real_inner_comm]
  rw [hflip] at h
  exact h

/-- A real smooth compactly supported test function as a complex Schwartz function. -/
def testToSchwartz {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) : 𝓢(V, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (g x : ℂ)) (hgs.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp hg)

@[simp] lemma testToSchwartz_apply {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) (x : V) :
    testToSchwartz hg hgs x = (g x : ℂ) := rfl

lemma real_smul_eq (a : ℝ) (z : ℂ) : a • z = (a : ℂ) • z := by
  simp [Complex.real_smul]

/-- **L² = integral transform on L¹ ∩ L²** (the direct transform). -/
theorem fourier_toLp_ae {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (⇑(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕 f := by
  set F : Lp ℂ 2 (volume : Measure V) := hf2.toLp f
  have hloc1 : LocallyIntegrable (⇑(𝓕 F : Lp ℂ 2 (volume : Measure V))) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf1
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hcont.locallyIntegrable ?_
  intro g hg hgs
  set u := testToSchwartz hg hgs
  have h1 : ∫ x, g x • (⇑(𝓕 F : Lp ℂ 2 (volume : Measure V)) x) =
      Lp.toTemperedDistribution (𝓕 F : Lp ℂ 2 (volume : Measure V)) u := by
    rw [Lp.toTemperedDistribution_apply]
    simp [u, real_smul_eq]
  have h2 : Lp.toTemperedDistribution (𝓕 F : Lp ℂ 2 (volume : Measure V)) u =
      Lp.toTemperedDistribution F (𝓕 u) := by
    rw [← Lp.fourier_toTemperedDistribution_eq]
    rfl
  have h3 : Lp.toTemperedDistribution F (𝓕 u) = ∫ x, 𝓕 (u : V → ℂ) x • f x := by
    rw [Lp.toTemperedDistribution_apply, SchwartzMap.fourier_coe]
    exact integral_congr_ae ((hf2.coeFn_toLp).mono fun x hx => by simp [F, hx])
  rw [h1, h2, h3, integral_fourier_smul_of_schwartz u hf1]
  simp [u, real_smul_eq]

/-- **L² = integral transform on L¹ ∩ L²** (the inverse transform). -/
theorem fourierInv_toLp_ae {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (⇑(𝓕⁻ (hf2.toLp f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  set F : Lp ℂ 2 (volume : Measure V) := hf2.toLp f
  have hloc1 : LocallyIntegrable (⇑(𝓕⁻ F : Lp ℂ 2 (volume : Measure V))) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hcont : Continuous (𝓕⁻ f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by simpa [Pi.neg_def] using (continuous_inner (𝕜 := ℝ) (E := V)).neg) hf1
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hcont.locallyIntegrable ?_
  intro g hg hgs
  set u := testToSchwartz hg hgs
  have h1 : ∫ x, g x • (⇑(𝓕⁻ F : Lp ℂ 2 (volume : Measure V)) x) =
      Lp.toTemperedDistribution (𝓕⁻ F : Lp ℂ 2 (volume : Measure V)) u := by
    rw [Lp.toTemperedDistribution_apply]
    simp [u, real_smul_eq]
  have h2 : Lp.toTemperedDistribution (𝓕⁻ F : Lp ℂ 2 (volume : Measure V)) u =
      Lp.toTemperedDistribution F (𝓕⁻ u) := by
    rw [← Lp.fourierInv_toTemperedDistribution_eq]
    rfl
  have h3 : Lp.toTemperedDistribution F (𝓕⁻ u) = ∫ x, 𝓕⁻ (u : V → ℂ) x • f x := by
    rw [Lp.toTemperedDistribution_apply, SchwartzMap.fourierInv_coe]
    exact integral_congr_ae ((hf2.coeFn_toLp).mono fun x hx => by simp [F, hx])
  rw [h1, h2, h3, integral_fourierInv_smul_of_schwartz u hf1]
  simp [u, real_smul_eq]

/-- Inner products of integral transforms on L¹ ∩ L²: `∫ ⟪𝓕f, 𝓕g⟫ = ∫ ⟪f, g⟫`. -/
theorem integral_inner_fourier {f g : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) (hg1 : Integrable g)
    (hg2 : MemLp g 2) : ∫ ξ, inner ℂ (𝓕 f ξ) (𝓕 g ξ) = ∫ x, inner ℂ (f x) (g x) := by
  have h := Lp.inner_fourier_eq (hf2.toLp f) (hg2.toLp g)
  rw [L2.inner_def, L2.inner_def] at h
  calc ∫ ξ, inner ℂ (𝓕 f ξ) (𝓕 g ξ)
      = ∫ ξ, inner ℂ ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure V)) ξ)
          ((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure V)) ξ) := by
        refine integral_congr_ae ?_
        filter_upwards [fourier_toLp_ae hf1 hf2, fourier_toLp_ae hg1 hg2] with ξ h1 h2
        rw [h1, h2]
    _ = ∫ x, inner ℂ ((hf2.toLp f) x) ((hg2.toLp g) x) := h
    _ = ∫ x, inner ℂ (f x) (g x) := by
        refine integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x h1 h2
        rw [h1, h2]

/-- **Plancherel's identity for the integral transform on L¹ ∩ L²**, with polarization. -/
theorem plancherel_L1L2 {f g : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) (hg1 : Integrable g)
    (hg2 : MemLp g 2) :
    MemLp (𝓕 f) 2 ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∧
      ∫ ξ, 𝓕 f ξ * starRingEnd ℂ (𝓕 g ξ) = ∫ x, f x * starRingEnd ℂ (g x) := by
  refine ⟨(Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure V))).ae_eq (fourier_toLp_ae hf1 hf2), ?_, ?_⟩
  · have h := integral_inner_fourier hf1 hf2 hf1 hf2
    simp_rw [inner_self_eq_norm_sq_to_K] at h
    have h' : ((∫ ξ, ‖𝓕 f ξ‖ ^ 2 : ℝ) : ℂ) = ((∫ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal, ← integral_complex_ofReal]
      simpa using h
    exact_mod_cast h'
  · have h := integral_inner_fourier hg1 hg2 hf1 hf2
    simp_rw [RCLike.inner_apply] at h
    simpa [mul_comm] using h

end StatFormal.FourierL2
