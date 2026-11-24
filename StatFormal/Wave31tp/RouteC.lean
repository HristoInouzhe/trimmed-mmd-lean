import StatFormal.Wave31tp.Statements
import StatFormal.Wave31tg.RouteMatern
import StatFormal.Lib.Matern.Fourier
import StatFormal.Lib.SobolevFin.Smooth

/-!
# Wave 31tp, route C: the composed claim L29 (untrusted proof file)

L29 (`matern_interpolation_free`): the Matérn sentence of Example 5.2 without the bridge of Wave 31tg. A Matérn profile
`a · G_s(·/ℓ)` (`s > d/2`, `a, ℓ > 0`) is continuous and integrable with the spectral lower bound
`a ℓ^d max(1, ℓ²)^{−s} (1 + 4π²‖ξ‖²)^{−s}` (`Lib/Matern/Fourier.lean`); a spectral lower bound gives `ContainsSmoothCompact φ`
(L19 b, `Lib/SobolevFin/Smooth.lean`), which is exactly the hypothesis of the certified `Wave31tg.matern_interpolation`.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tp.RouteC

theorem matern_interpolation_free_route : Claims.matern_interpolation_free := by
  intro d H _ _ _ φ k₀ hφ hk
  have hcs : StatFormal.Wave31tg.ContainsSmoothCompact φ := by
    rcases hk with ⟨s, a, ℓ, hs, ha, hℓ, rfl⟩ | ⟨hc, hi, c, s, hc0, hlow⟩
    · have hs' : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) / 2 < s := by
        rwa [finrank_euclideanSpace_fin]
      exact SobolevFin.containsSmoothCompact_of_spec hφ (Matern.continuous_maternK hs' a ℓ)
        (Matern.integrable_maternK hs' a hℓ.ne') (by positivity) (Matern.specDens_maternK_lower hs' ha hℓ)
    · exact SobolevFin.containsSmoothCompact_of_spec hφ hc hi hc0 hlow
  exact StatFormal.Wave31tg.matern_interpolation d H φ hcs

end StatFormal.Wave31tp.RouteC
