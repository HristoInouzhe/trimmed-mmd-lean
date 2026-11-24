import StatFormal.Wave31tp.Statements
import StatFormal.Lib.Matern.One

/-!
# Wave 31tp, route Mat: Matérn (Bessel-potential) kernels (untrusted proof file)

L22 (`matern_facts`, `matern_one`) from `Lib/Matern/Basic.lean` (integrand, continuity, positivity, bound at `0`),
`Lib/Matern/Fourier.lean` (Tonelli/Fubini: integrability, `𝓕 G_s = (1 + 4π²‖ξ‖²)^{−s}`, `∫ G_s = 1`, the family `a G_s(·/ℓ)` and
its two spectral bounds) and `Lib/Matern/One.lean` (`G₁ = e^{−|x|}/2` on `ℝ` by Fourier inversion).
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteMat

theorem matern_facts_route : Claims.matern_facts := by
  intro V _ _ _ _ _ s hs
  refine ⟨Matern.integrableOn_integrand hs, Matern.continuous_besselPot hs, Matern.besselPot_pos hs,
    Matern.besselPot_le_zero hs, Matern.integrable_besselPot hs, Matern.integral_besselPot hs, Matern.fourier_besselPot hs,
    fun a ℓ ha hℓ => ⟨Matern.continuous_maternK hs a ℓ, Matern.maternK_pos hs ha ℓ, Matern.integrable_maternK hs a hℓ.ne',
      Matern.fourier_maternK hs a hℓ, fun ξ => ⟨Matern.specDens_maternK_lower hs ha hℓ ξ,
      Matern.specDens_maternK_upper hs ha hℓ ξ⟩⟩⟩

theorem matern_one_route : Claims.matern_one :=
  Matern.besselPot_one_real

end StatFormal.Wave31tp.RouteMat
