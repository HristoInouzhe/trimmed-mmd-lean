import StatFormal.Wave31tu.Statements
import StatFormal.Lib.CrossExamples.Ratio

/-!
# Wave 31tu route S: Y23 `sims_condR` (S6 :157, :167-168; S4 :1029-1030; untrusted proof material)

The two simulated pairs satisfy `eq:condR` at `x₀ = 0` with `r⋆ = 1`: the shift `N(±1,1)` (the two-component Gaussian pair
with `w = 0`, `a = 1`; its ratio is `|tanh x|`) and the mixture `0.8N(0,1) + 0.2N(±1.5,1)` (`w = 0.8`, `a = 1.5`), each with the
explicit constant `c⋆ = gaussPairConst w a` of `Lib/CrossExamples/Ratio` (`gaussPair_ratio_lower`, which holds for every `x`).

* `sims_condR_route : Claims.sims_condR`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set ProbabilityTheory

namespace StatFormal.Wave31tu.RouteS

/-- `eq:condR` at `x₀ = 0`, `r⋆ = 1`, `c⋆ = gaussPairConst w a` for the two-component Gaussian pair. -/
theorem condR_gaussPair {p q : ℝ → ℝ} {w a : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (ha : 0 < a)
    (hp : ∀ x, p x = w * gaussianPDFReal 0 1 x + (1 - w) * gaussianPDFReal a 1 x)
    (hq : ∀ x, q x = w * gaussianPDFReal 0 1 x + (1 - w) * gaussianPDFReal (-a) 1 x) :
    CondR p q 0 1 (CrossExamples.gaussPairConst w a) := by
  refine ⟨one_pos, le_rfl, CrossExamples.gaussPairConst_pos hw0 hw1 ha, Filter.Eventually.of_forall fun x => ?_⟩
  rw [sub_zero]
  exact CrossExamples.gaussPair_ratio_lower hw0 hw1 ha hp hq x

/-- **Y23**: the shift `N(±1,1)` and the mixture `0.8N(0,1) + 0.2N(±1.5,1)` satisfy `eq:condR` (with `r⋆ = 1`). -/
theorem sims_condR_route : Claims.sims_condR := by
  refine ⟨⟨1, _, condR_gaussPair (w := 0) (a := 1) le_rfl one_pos one_pos (fun x => by simp) (fun x => by simp)⟩,
    ⟨1, _, condR_gaussPair (w := 0.8) (a := 1.5) (by norm_num) (by norm_num) (by norm_num) (fun x => by norm_num)
      (fun x => by norm_num)⟩⟩

end StatFormal.Wave31tu.RouteS
