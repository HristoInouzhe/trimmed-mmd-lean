import StatFormal.Wave31tu.Statements
import StatFormal.Lib.LaplaceH1.Rep

/-!
# Wave31tu, chunk H: Y3 (a), (c) `laplace_h1`, the `H¹` form of the Laplace RKHS on `ℝ` and `eq:laphone` (S4 :1039-1048)

`laplace_h1_route : Claims.laplace_h1` (no hypotheses). For `g ∈ H` and `f = wit φ g = ⟪g, φ ·⟫`:

* (a) `LaplaceH1.rep_h1`: `f` is locally absolutely continuous with `f, f′ ∈ L²` (`IsH1`) and `∫ (f² + σ² f′²) ≤ 2σ‖g‖²`, with
  equality on the closed span of `φ(ℝ)`; `LaplaceH1.h1_lintegral_eq` turns the `[0, ∞]` functional `h1Laplace σ f` into
  `ofReal ((1/(2σ)) ∫ (f² + σ² f′²))`. The proof goes through the explicit feature `ψ_σ(x) = √(2/σ) e^{(·−x)/σ} 1_{(−∞,x]} ∈ L²(ℝ)`
  (same Gram function, Wave31tp L12 transfer), where `σ f′ = −f + √(2σ) u` a.e. and `∫ f f′ = 0`;
* (c) `rep_abs_le` (`|f| ≤ ‖g‖‖φ x‖ = ‖g‖`), `rep_integral_abs_deriv_le` (Cauchy–Schwarz with `∫ f′² ≤ (2/σ)‖g‖²`),
  `rep_eVariationOn_le` (variation `≤ ∫|f′|` by the fundamental theorem of calculus for absolutely continuous functions),
  `rep_tendsto` (Wave31tp L26), `abs_le_one_of_osc` (`inf f ≤ 0 ≤ sup f` since `f → 0`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteH

open StatFormal.LaplaceH1

/-- `h1Laplace σ f = ofReal ((1/(2σ)) ∫ (f² + σ² f′²))` when `f, f′ ∈ L²`. -/
lemma h1Laplace_eq {σ : ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hd : MemLp (deriv f) 2 volume) :
    h1Laplace σ f = ENNReal.ofReal (1 / (2 * σ) * ∫ x, (f x ^ 2 + σ ^ 2 * deriv f x ^ 2)) :=
  h1_lintegral_eq hf hd

/-- **Y3 (a), (c)** (S4 :1039-1048). -/
theorem laplace_h1_route : Claims.laplace_h1 := by
  intro H _ _ _ σ φ hσ hφ
  have hφ' : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ) := hφ
  refine ⟨fun g => ?_, fun g => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := rep_h1 hσ hφ' g
    have hh := h1Laplace_eq (σ := σ) h2 h3
    refine ⟨⟨h1, h2, h3⟩, ?_, fun hg => ?_⟩
    · change h1Laplace σ (fun x => ⟪g, φ x⟫_ℝ) ≤ _
      rw [hh]
      apply ENNReal.ofReal_le_ofReal
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    · change h1Laplace σ (fun x => ⟪g, φ x⟫_ℝ) = _
      rw [hh, h5 hg]
      congr 1
      field_simp
  · refine ⟨rep_abs_le hφ' g, fun a b hab => rep_integral_abs_deriv_le hσ hφ' g hab,
      fun a b hab => rep_eVariationOn_le hσ hφ' g hab, rep_tendsto hσ hφ' g, fun hosc x => ?_⟩
    have htop : Tendsto (fun x => ⟪g, φ x⟫_ℝ) atTop (𝓝 0) :=
      (rep_tendsto hσ hφ' g).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
    exact abs_le_one_of_osc (rep_abs_le hφ' g) htop hosc x

end StatFormal.Wave31tu.RouteH
