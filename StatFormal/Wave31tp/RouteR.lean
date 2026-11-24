import StatFormal.Wave31tp.Statements
import StatFormal.Lib.RKHSReg.Gauss
import StatFormal.Lib.RKHSReg.Characteristic

/-!
# Wave 31tp, route R: regularity of RKHS functions and characteristic kernels (untrusted proof file)

L24 (`rkhs_smooth`, `gauss_smooth`) from `Lib/RKHSReg/Smooth.lean` and `Lib/RKHSReg/Gauss.lean`; L25 (`characteristic_spec`) from
`Lib/RKHSReg/Characteristic.lean`; L26 (`rkhs_vanish`) from `Lib/RKHSReg/Smooth.lean`; L30 (`gauss_regular_smooth`) from
`Lib/RKHSReg/Gauss.lean` (`Wave12c.witFn f φ x = ⟪f, φ x⟫` by definition). The common step is `Lib/RKHSReg/Rep.lean`: every
RKHS function of a continuous integrable profile is the real part of the Fourier transform of `specDens k₀ · conj G`.
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteR

theorem rkhs_smooth_route : Claims.rkhs_smooth := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ m hc hi hφ hm g
  exact RKHSReg.rkhs_smooth_facts hφ hc hi hm g

theorem gauss_smooth_route : Claims.gauss_smooth := by
  intro V _ _ _ _ _ H _ _ _ φ σ hσ hφ g
  exact RKHSReg.gauss_smooth_facts hσ hφ g

theorem characteristic_spec_route : Claims.characteristic_spec := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ hc hi hφ hpos
  exact ⟨fun μ ν _ _ h => RKHSReg.mean_embedding_injective hφ hc hi hpos h,
    RKHSReg.characteristic_of_spec hφ hc hi hpos, RKHSReg.strictlyPD_of_spec hφ hc hi hpos⟩

theorem rkhs_vanish_route : Claims.rkhs_vanish := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ hc hi hφ g
  exact RKHSReg.rkhs_vanish_facts hφ hc hi g

theorem gauss_regular_smooth_route : Claims.gauss_regular_smooth := by
  intro d H _ _ _ φ σ hσ hφ f
  exact RKHSReg.gauss_regular_facts hσ hφ f

end StatFormal.Wave31tp.RouteR
