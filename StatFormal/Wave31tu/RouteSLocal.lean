import StatFormal.Wave31tu.RouteTPr

/-!
# Wave 31tu route S: Y20 (d) `lap_local_d` (S4 :1417-1418; untrusted proof material)

"The constants of Proposition 5.5 for `(P_h,Q)` exist": for every `σ > 0` and `h ∈ [0,1]`, the perturbed pair `(P_h, Q)` of
`lem:laplocal` has constants `c₁, c₂, ε₀` of the two-sided bound of Proposition 5.5 at `s = 1`, chosen before the feature space
and map, for every Laplace feature map of bandwidth `σ`.

Route: Y20 (a) (`Claims.lap_local`, a hypothesis: chunk K) gives `IsCross P_h Q p_h q x₀ ℓ₀`, `p_h(x₀) > 0`, the exponential tail
and that `P_h` is a probability measure; then route T's `laplace_twoSided` (31tq Q21 `newsobolev` with Q7 `kernel_instances` at
the Fourier feature map of `e^{−|x|/σ}`, 31tp L15 `feature_exists`/`fourier_feature`, transferred to every feature map with the
same Gram function by 31tp L12 `gram_mmd`), imported with the coordinator's authorization.

* `lap_local_d_of (h20 : Claims.lap_local) : Claims.lap_local_d`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteS

open StatFormal.Wave31tq

/-- **Y20 (d)**: the constants of Proposition 5.5 (at `s = 1`, Laplace kernel of bandwidth `σ`) exist for every perturbed pair
`(P_h, Q)` of `lem:laplocal`, before the feature space and map. -/
theorem lap_local_d_of (h20 : Claims.lap_local) : Claims.lap_local_d := by
  intro σ P Q _ _ p q x₀ ℓ₀ rs cs r C' hσ hcross hpx hexp hcond hr hrs hpc hqc hpos A₁ B₁ πh hh hhI Ph
  obtain ⟨-, hall⟩ := h20 P Q p q x₀ ℓ₀ rs cs r C' 0 hcross hpx hexp hcond hr hrs hpc hqc hpos
  obtain ⟨-, -, hprob, -, -, hcrossh, hpxh, htailh, -, -, -⟩ := hall hh hhI
  have hP' : IsProbabilityMeasure Ph := hprob
  obtain ⟨-, -, c₁, c₂, ε₀, -, -, -, -, hD⟩ :=
    RouteT.laplace_twoSided hσ Ph Q hcrossh hpxh ⟨_, htailh.1, htailh.2⟩
  exact ⟨c₁, c₂, ε₀, fun H _ _ _ _ φ hφ => hD H φ hφ⟩

end StatFormal.Wave31tu.RouteS
