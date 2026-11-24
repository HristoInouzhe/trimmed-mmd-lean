import StatFormal.Wave31tp.Statements
import StatFormal.Lib.TIKernel.Native
import StatFormal.Lib.TIKernel.Spectra

/-!
# Wave 31tp, route K: translation-invariant kernels (untrusted proof file)

L13 (`bochner_integrable`) from `Lib/TIKernel/Bochner.lean`; L14 (`gram_profile`) from `Lib/TIKernel/Profile.lean`.
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteK

theorem bochner_integrable_route : Claims.bochner_integrable := by
  intro V _ _ _ _ _ k hc hi hk
  exact TIKernel.bochner_integrable hc hi hk

theorem gram_profile_route : Claims.gram_profile := by
  intro V _ _ _ _ _ H _ _ φ k₀ hφ
  exact ⟨TIKernel.gram_even hφ, TIKernel.gram_abs_le hφ, TIKernel.gram_dist_sq hφ, TIKernel.gram_posdef hφ,
    TIKernel.gram_cont_iff hφ, TIKernel.gram_spec_even hφ, fun hi hc => TIKernel.gram_spec_bochner hφ hi hc⟩

theorem fourier_feature_route : Claims.fourier_feature := by
  intro V _ _ _ _ _ ψ hψm hψ0 hψi
  exact TIKernel.fourier_feature_facts hψm hψ0 hψi

theorem feature_exists_route : Claims.feature_exists := by
  intro V _ _ _ _ _ k₀ hc hi hpd
  exact TIKernel.feature_exists_facts hc hi hpd

theorem ftMeas_facts_route : Claims.ftMeas_facts := by
  intro V _ _ _ _ _ μ ν _ _
  refine ⟨TIKernel.ftMeas_continuous μ, TIKernel.ftMeas_norm_le μ, TIKernel.ftMeas_zero μ, ?_,
    TIKernel.ftMeas_inj⟩
  rintro f hf0 hfi rfl
  exact TIKernel.ftMeas_density hf0 hfi

theorem mmd_fourier_route : Claims.mmd_fourier := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ hc hi hφ
  exact TIKernel.mmd_fourier_facts hφ hc hi

theorem native_incl_route : Claims.native_incl := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ hc hi hφ f
  exact TIKernel.native_incl_facts hφ hc hi f

theorem sobolev_incl_route : Claims.sobolev_incl := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ c s hc hi hφ hc0 hlow f hfc hf2 hS
  exact TIKernel.sobolev_incl_facts hφ hc hi hc0 hlow hfc hf2 hS

theorem gauss_spec_route : Claims.gauss_spec := by
  intro V _ _ _ _ _ σ hσ
  exact ⟨TIKernel.gauss_continuous σ, TIKernel.gauss_integrable hσ, TIKernel.fourier_gauss hσ⟩

theorem laplace_spec_route : Claims.laplace_spec :=
  ⟨by fun_prop, TIKernel.laplace_integrable, TIKernel.fourier_laplace⟩

end StatFormal.Wave31tp.RouteK
