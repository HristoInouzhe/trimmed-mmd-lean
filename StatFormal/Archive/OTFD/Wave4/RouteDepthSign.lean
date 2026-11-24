import StatFormal.Archive.OTFD.Wave4.Statements
import TauCeti.Probability.Quantile

/-!
# Route: T `lem:depthsign-rank`

With `ν` the law of `‖U‖` (= the law of `‖U'‖`), Tau Ceti's `quantile_cdf_ae` gives
`ν.quantile (cdf ν r) = r` for `ν`-a.e. `r`, for **every** real law (no continuity). Pulled back
along `‖U‖` and `‖U'‖`, the a.s. identity `c_K(‖U'‖) = c_K(‖U‖)` gives `‖U'‖ = ‖U‖` a.s.; equal
norms and equal signs give `U' = U` (at the origin both vanish, whatever the sign convention).
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace StatFormal.OTFD.Wave4

theorem depthsign_rank : Claims.depthsign_rank := by
  intro E Ω _ _ _ _ _ P _ μ _ U U' sgn hU hU' hUμ hU'μ hsgn hc hs
  set ν := μ.map (fun u => ‖u‖) with hνdef
  have hnorm : Measurable (fun u : E => ‖u‖) := measurable_norm
  have hq := Measure.quantile_cdf_ae ν
  have pull : ∀ W : Ω → E, Measurable W → P.map W = μ →
      ∀ᵐ ω ∂P, ν.quantile (cdf ν ‖W ω‖) = ‖W ω‖ := by
    intro W hW hWμ
    have hmap : P.map (fun ω => ‖W ω‖) = ν := by
      rw [hνdef, ← hWμ, Measure.map_map hnorm hW]; rfl
    have h : ∀ᵐ r ∂(P.map (fun ω => ‖W ω‖)), ν.quantile (cdf ν r) = r := by
      rw [hmap]; exact hq
    exact ae_of_ae_map (hnorm.comp hW).aemeasurable h
  filter_upwards [pull U hU hUμ, pull U' hU' hU'μ, hc, hs] with ω h1 h2 hc hs
  have hn : ‖U' ω‖ = ‖U ω‖ := by rw [← h1, ← h2, hc]
  by_cases h0 : U ω = 0
  · have : U' ω = 0 := norm_eq_zero.mp (hn.trans (by simp [h0]))
    rw [this, h0]
  · have h0' : U' ω ≠ 0 := by
      intro h; apply h0; rw [← norm_eq_zero, ← hn, h, norm_zero]
    rw [hsgn _ h0, hsgn _ h0', hn] at hs
    have hne : ‖U ω‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr h0)
    exact smul_right_injective E hne hs

end StatFormal.OTFD.Wave4
