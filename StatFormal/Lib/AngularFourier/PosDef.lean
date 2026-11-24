import StatFormal.Wave31tp.Proofs

/-!
# Positive definiteness from an explicit nonnegative integrable spectrum (library, untrusted)

`isPosDefFun_of_fourier_eq`: a continuous integrable real profile `k₀` whose Fourier transform is (the complexification of) a
measurable, nonnegative, integrable, even function `ψ` is positive definite. Route (no Bochner converse is needed): the Fourier
feature map of `ψ` (certified `Wave31tp.fourier_feature`, L15) has Gram function `kSpec ψ (x − y)` with `kSpec ψ = 𝓕⁻ ψ`; by Fourier
inversion (Mathlib's `Continuous.fourierInv_fourier_eq`) `𝓕⁻ ψ = 𝓕⁻ (𝓕 k₀) = k₀`, so `k₀` is a Gram profile and the certified
`Wave31tp.gram_profile` (L14) gives positive definiteness.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory FourierTransform
open scoped InnerProductSpace

namespace StatFormal.AngularFourier

open StatFormal.Wave31tp

/-- A continuous integrable profile with an explicit even, nonnegative, integrable Fourier transform is positive definite. -/
theorem isPosDefFun_of_fourier_eq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k₀ : V → ℝ} (hc : Continuous k₀) (hi : Integrable k₀) {ψ : V → ℝ}
    (hψm : Measurable ψ) (hψ0 : ∀ ξ, 0 ≤ ψ ξ) (hψi : Integrable ψ) (hψe : ∀ ξ, ψ (-ξ) = ψ ξ)
    (hft : ∀ ξ, 𝓕 (fun x => (k₀ x : ℂ)) ξ = (ψ ξ : ℂ)) : IsPosDefFun (fun z => (k₀ z : ℂ)) := by
  obtain ⟨-, -, -, -, hgram, -, -, -, -, hinv, -⟩ := fourier_feature V ψ hψm hψ0 hψi
  have hc' : Continuous (fun x => (k₀ x : ℂ)) := Complex.continuous_ofReal.comp hc
  have hi' : Integrable (fun x => (k₀ x : ℂ)) := hi.ofReal
  have hF : 𝓕 (fun x => (k₀ x : ℂ)) = fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ) := by
    funext ξ
    rw [hft, hψe]
    congr 1
    ring
  have hFi : Integrable (𝓕 (fun x => (k₀ x : ℂ))) := by
    rw [funext hft]
    exact hψi.ofReal
  have hk : ∀ z, kSpec ψ z = k₀ z := by
    intro z
    have h1 := (hinv z).2
    rw [← hF, hc'.fourierInv_fourier_eq hi' hFi] at h1
    have h1' : ((kSpec ψ z : ℝ) : ℂ) = (k₀ z : ℂ) := h1
    exact_mod_cast h1'
  have hg : ∀ x y, ⟪fourierFeature ψ x, fourierFeature ψ y⟫_ℝ = k₀ (x - y) := fun x y => (hgram x y).trans (hk _)
  exact (gram_profile V _ (fourierFeature ψ) k₀ hg).2.2.2.1

end StatFormal.AngularFourier
