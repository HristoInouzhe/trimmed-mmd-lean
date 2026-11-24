import StatFormal.Wave31tq.Statements
import StatFormal.Wave31tp.Proofs
import StatFormal.Lib.BandLimited.EvenDensity

/-!
# Wave 31tq, chunk G: eq:newbandlim in the angular convention (Q14) and the tail of an even density (Q15 `bbar_even`)

* `bandlimited_angular_route` (Q14): the certified `Wave31tp.bandlimited_gauss` at the band `Ω/2π` (the angular transform is
  `ft2A f ξ = ft2 f (ξ/2π)`, and the null sets transfer under `ξ ↦ 2πξ`); `e^{2π²σ²(Ω/2π)²} = e^{σ²Ω²/2}`,
  `(2πσ²)^{−1/2} = 1/((2π)^{1/2}σ)`.
* `bbar_even_route` (Q15): `Lib/BandLimited/EvenDensity` (`b̄(0) = 1/2` by evenness, `b̄` antitone, `b̄ → 0`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteG

open StatFormal StatFormal.Wave31tp

/-- Q14 `bandlimited_angular` (eq:newbandlim as printed). -/
theorem bandlimited_angular_route : Claims.bandlimited_angular := by
  intro H _ _ _ φ σ Ω hσ hΩ hφ f hfc hf2 hsupp
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hφ' : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)) := by
    intro x y; rw [hφ, Real.norm_eq_abs, sq_abs]
  have hΩ' : 0 ≤ Ω / (2 * Real.pi) := div_nonneg hΩ hπ.le
  have hsupp' : ∀ᵐ η ∂(volume : Measure ℝ), Ω / (2 * Real.pi) < ‖η‖ → ft2 (fun x => (f x : ℂ)) η = 0 := by
    have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (r := 2 * Real.pi) hπ.ne'
    filter_upwards [hq.ae hsupp] with η hη hlt
    have h1 : Ω < |(2 * Real.pi) • η| := by
      rw [smul_eq_mul, abs_mul, abs_of_pos hπ]
      rw [Real.norm_eq_abs] at hlt
      rwa [div_lt_iff₀' hπ] at hlt
    have := hη h1
    rwa [ft2A, smul_smul, inv_mul_cancel₀ hπ.ne', one_smul] at this
  obtain ⟨g, hg, hgn⟩ := Wave31tp.bandlimited_gauss ℝ H φ σ (Ω / (2 * Real.pi)) hσ hΩ' hφ' f hfc hf2 hsupp'
  refine ⟨g, hg, hgn.trans (le_of_eq ?_)⟩
  have hfin : (Module.finrank ℝ ℝ : ℝ) = 1 := by simp
  rw [hfin]
  congr 1
  have h2 : (2 * Real.pi * σ ^ 2) ^ (-(1 : ℝ) / 2) = 1 / (√(2 * Real.pi) * σ) := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le, one_div]
  rw [h2]
  have h3 : 2 * Real.pi ^ 2 * σ ^ 2 * (Ω / (2 * Real.pi)) ^ 2 = σ ^ 2 * Ω ^ 2 / 2 := by
    field_simp
  rw [h3]
  ring

/-- Q15 `bbar_even`: `b̄ ≤ 1/2` on `[0, ∞)`, `b̄` nonincreasing there, `b̄(∞) = 0`. -/
theorem bbar_even_route : Claims.bbar_even := by
  intro b _ h0 h1 hev
  exact ⟨fun t ht => BandLimited.tail_le_half h0 h1 hev ht, (BandLimited.tail_antitone h0 h1).antitoneOn _,
    BandLimited.tendsto_tail (BandLimited.integrable_of_integral_eq_one h1)⟩

end StatFormal.Wave31tq.RouteG
