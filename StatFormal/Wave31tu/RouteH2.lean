import StatFormal.Wave31tu.RouteH1
import StatFormal.Lib.LaplaceH1.Char

/-!
# Wave31tu, chunk H: Y3 (b) `laplace_h1_char`, the `H¹` identification of the Laplace RKHS (S4 :1039-1041)

`laplace_h1_char_route : Claims.laplace_h1_char` (no hypotheses). For continuous `f`:

* represented `⇒ IsH1 f`: Y3 (a) (`LaplaceH1.rep_h1`);
* `IsH1 f ⇒` represented, with a least representer `g₀` of `ofReal ‖g₀‖² = h1Laplace σ f`: `LaplaceH1.h1_rep` (the `L²` element
  `u = (σ f′ + f)/√(2σ)` reproduces `f` through the explicit feature `ψ_σ`, by integration by parts against `e^{t/σ}` on
  `(−∞, x]` (an `H¹` function is bounded); the Gram transfer to `φ` does not increase the norm, and every representer has
  `h1Laplace σ f ≤ ‖g‖²` by (a)).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteH

open StatFormal.LaplaceH1

/-- **Y3 (b)** (S4 :1039-1041). -/
theorem laplace_h1_char_route : Claims.laplace_h1_char := by
  intro H _ _ _ σ φ hσ hφ f _
  have hφ' : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ) := hφ
  have hchar : IsH1 f → ∃ g₀ : H, (∀ x, ⟪g₀, φ x⟫_ℝ = f x) ∧ ENNReal.ofReal (‖g₀‖ ^ 2) = h1Laplace σ f ∧
      ∀ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) → ‖g₀‖ ≤ ‖g‖ := by
    rintro ⟨hac, hf, hd⟩
    obtain ⟨g₀, hrep, hnorm, hmin⟩ := h1_rep hσ hφ' hac hf hd
    refine ⟨g₀, hrep, ?_, hmin⟩
    rw [h1Laplace_eq hf hd, ← hnorm]
    congr 1
    field_simp
  refine ⟨⟨fun ⟨g, hg⟩ => ?_, fun h => ?_⟩, hchar⟩
  · obtain rfl : (fun x => ⟪g, φ x⟫_ℝ) = f := funext hg
    obtain ⟨h1, h2, h3, -, -⟩ := rep_h1 hσ hφ' g
    exact ⟨h1, h2, h3⟩
  · obtain ⟨g₀, hrep, -, -⟩ := hchar h
    exact ⟨g₀, hrep⟩

end StatFormal.Wave31tu.RouteH
