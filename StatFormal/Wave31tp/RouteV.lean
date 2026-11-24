import StatFormal.Wave31tp.Statements
import StatFormal.Lib.SobolevFin.Smooth
import StatFormal.Lib.SobolevFin.BandLimited

/-!
# Wave 31tp, route V: Sobolev finiteness, `ContainsSmoothCompact`, band-limited functions

Untrusted proof file. L9 (`sobolev_smooth_finite`) and L19 (b) (`containsSmoothCompact_of_spec`)
from `Lib/SobolevFin/Smooth.lean`; L20 (`bandlimited`, `bandlimited_gauss`) from
`Lib/SobolevFin/BandLimited.lean`.
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteV

theorem sobolev_smooth_finite_route : Claims.sobolev_smooth_finite := by
  intro V _ _ _ _ _ g s hg hgs
  exact SobolevFin.sobolevS_lt_top_of_contDiff hg hgs s

theorem containsSmoothCompact_of_spec_route : Claims.containsSmoothCompact_of_spec := by
  intro d H _ _ _ φ k₀ c s hc hi hφ hc0 hlow
  exact SobolevFin.containsSmoothCompact_of_spec hφ hc hi hc0 hlow

theorem bandlimited_route : Claims.bandlimited := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ Ω m hc hi hφ _ hm hband f hfc hf2 hsupp
  exact SobolevFin.bandlimited_rep hφ hc hi hm hband hfc hf2 hsupp

theorem bandlimited_gauss_route : Claims.bandlimited_gauss := by
  intro V _ _ _ _ _ H _ _ _ φ σ Ω hσ _ hφ f hfc hf2 hsupp
  exact SobolevFin.bandlimited_gauss_rep hσ hφ hfc hf2 hsupp

end StatFormal.Wave31tp.RouteV
