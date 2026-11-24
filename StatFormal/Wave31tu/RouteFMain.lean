import StatFormal.Wave31tu.RouteFI
import StatFormal.Wave31tu.RouteFII

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: Y15 `lap_fitted` (Proposition S4.27 `prop:lapfitted`, S4 :1293-1344, at `σ = 1` as printed)

`lap_fitted_of`: case (i) is `fitted_i` (with the gap bounds `c_Vε^{1/4}/24 ≤ t̂ − û ≤ V(2ε)/ε`), case (ii) is `fitted_ii`.
Cross-chunk hypotheses (frozen claims of chunks P and D): Y6 `lap_err`, Y7 `lap_const`, Y9 `lap_ratio`, Y10 `lap_clip`,
Y11 `lap_pop`, Y12 `lap_compare`, Y13 `lap_dev`, Y14 `lap_own`.
-/

noncomputable section

namespace StatFormal.Wave31tu.RouteF

/-- **Y15 (a), (b)**, Proposition S4.27. -/
theorem lap_fitted_of (h6 : Claims.lap_err) (h7 : Claims.lap_const) (h9 : Claims.lap_ratio) (h10 : Claims.lap_clip)
    (h11 : Claims.lap_pop) (h12 : Claims.lap_compare) (h13 : Claims.lap_dev) (h14 : Claims.lap_own) :
    Claims.lap_fitted := by
  intro H _ _ _ _ φ P Q _ _ p q x₀ ℓ₀ c₁ c₂ ε₀ c K n m x y hφ hcross hpx0 h54 htv hn hm hxy hc hK hIx hIy
  intro αs κ cv
  exact ⟨fun rs cs pbar hR hpbar ε hfit hεα w v hqp =>
      fitted_i h7 h9 h10 h11 h12 h13 h14 hφ hcross hpx0 h54 htv hn hm hxy hc hK hIx hIy hR hpbar hfit hεα hqp,
    fun ε hfit hεα w v hqp =>
      fitted_ii h6 h7 h10 h11 h12 h13 h14 hφ hcross h54 htv hn hm hxy hc hK hIx hIy hfit hεα hqp⟩

end StatFormal.Wave31tu.RouteF
