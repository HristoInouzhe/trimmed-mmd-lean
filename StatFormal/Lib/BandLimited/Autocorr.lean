import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion

/-!
# The Fourier transform of a square is the self-convolution of the transform (library, untrusted)

If `F` is continuous with compact support on a finite-dimensional real inner-product space and `f = 𝓕⁻ F` has `f · f`
integrable, then `𝓕 (f · f) = F ⋆ F`: indeed `𝓕⁻ (F ⋆ F)(t) = 𝓕 (F ⋆ F)(−t) = 𝓕 F(−t) 𝓕 F(−t) = f(t) f(t)` (Mathlib's
`Real.fourier_mul_convolution_eq`), and Fourier inversion (`Continuous.fourier_fourierInv_eq`) applies to the continuous
integrable `F ⋆ F`, whose transform `(𝓕 F)²` is integrable. For a real band-limited `f` this is the classical statement that
`(f²)^` is the autocorrelation of `f̂`, supported in `supp F + supp F` (S4 :667-668 of the trimmed-MMD paper).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.BandLimited

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **`𝓕 (f²) = F ⋆ F` for `f = 𝓕⁻ F`**, `F` continuous with compact support and `f²` integrable. -/
theorem fourier_mul_self_fourierInv {F : V → ℂ} (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hint : Integrable (fun t => 𝓕⁻ F t * 𝓕⁻ F t)) :
    𝓕 (fun t => 𝓕⁻ F t * 𝓕⁻ F t) = convolution F F (ContinuousLinearMap.mul ℂ ℂ) volume := by
  have hFi : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  set G := convolution F F (ContinuousLinearMap.mul ℂ ℂ) volume with hG
  have hGF : ∀ ξ, 𝓕 G ξ = 𝓕 F ξ * 𝓕 F ξ := fun ξ => Real.fourier_mul_convolution_eq hFi hFi ξ
  have hinv : 𝓕⁻ G = fun t => 𝓕⁻ F t * 𝓕⁻ F t := by
    funext t
    rw [Real.fourierInv_eq_fourier_neg, hGF, Real.fourierInv_eq_fourier_neg]
  have hGc : Continuous G := hFs.continuous_convolution_left _ hFc hFi.locallyIntegrable
  have hGi : Integrable G := hFi.integrable_convolution _ hFi
  have hGFi : Integrable (𝓕 G) := by
    have : 𝓕 G = fun ξ => 𝓕⁻ F (-ξ) * 𝓕⁻ F (-ξ) := by
      funext ξ; rw [hGF, Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [this]
    exact hint.comp_neg
  rw [← hinv]
  exact Continuous.fourier_fourierInv_eq hGc hGi hGFi

end StatFormal.BandLimited
