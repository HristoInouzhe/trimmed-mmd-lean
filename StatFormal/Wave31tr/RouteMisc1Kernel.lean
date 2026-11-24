import StatFormal.Wave31tr.Statements
import StatFormal.Lib.KernelFacts.Radial
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Wave 31tr, chunk M1: `kernel_constants` (T35)

The Gaussian and Laplace kernels on `ℝ^d` (`d ≥ 1`) have `κ = 1` and diameter `√2`, by the general `KernelFacts.radial_constants`
with the unit vector `EuclideanSpace.single 0 1`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteMisc1

theorem kernel_constants_route : Claims.kernel_constants := by
  intro d σ g hd hσ hg H _ _ _ φ hk
  have e0 : Fin d := ⟨0, hd⟩
  have he : ‖EuclideanSpace.single e0 (1 : ℝ)‖ = 1 := by simp
  rcases hg with rfl | rfl
  · obtain ⟨h0, hpos, hlim⟩ := KernelFacts.gaussProfile_facts hσ
    exact KernelFacts.radial_constants _ φ hk h0 (fun r _ => hpos r) hlim _ he
  · obtain ⟨h0, hpos, hlim⟩ := KernelFacts.laplaceProfile_facts hσ
    exact KernelFacts.radial_constants _ φ hk h0 (fun r _ => hpos r) hlim _ he

end StatFormal.Wave31tr.RouteMisc1
