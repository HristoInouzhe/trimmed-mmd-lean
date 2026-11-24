import StatFormal.Wave31tp.Statements
import StatFormal.Lib.FourierTaylor.MomentDecay
import StatFormal.Lib.MomentPoly.Basic
import StatFormal.Lib.GaussMoments.Basic

/-!
# Wave 31tp, route E: Taylor bound, moment decay, Gaussian moments, moment polynomials (untrusted)

L4 (`taylor_cexp`) and L5 (`moment_decay`) from `Lib/FourierTaylor/{Taylor,MomentDecay}.lean`;
L23 (`gauss_moments`) from `Lib/GaussMoments/Basic.lean`; L28 (`moment_poly`, `moment_poly_scale`) from
`Lib/MomentPoly/Basic.lean`.
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteE

theorem taylor_cexp_route : Claims.taylor_cexp := fun t N =>
  FourierTaylor.norm_exp_mul_I_sub_sum_le t N

theorem moment_decay_route : Claims.moment_decay := by
  intro ρ₁ ρ₂ _ _ x₀ W N _ _ h₁ h₂ hmom ξ
  exact FourierTaylor.norm_ftMeas_sub_le_of_moments ρ₁ ρ₂ h₁ h₂ hmom ξ

theorem gauss_moments_route : Claims.gauss_moments := by
  intro σ N hσ
  exact ⟨GaussMoments.integrable_gauss_spec_moment hσ N, GaussMoments.integral_gauss_spec_moment hσ N⟩

theorem moment_poly_route : Claims.moment_poly := by
  intro T N hT _ M
  exact MomentPoly.existsUnique_moments hT M

theorem moment_poly_scale_route : Claims.moment_poly_scale := by
  intro T G j hT
  exact ⟨MomentPoly.integral_scale_moment hT G j, MomentPoly.integral_scale_abs hT G⟩

end StatFormal.Wave31tp.RouteE
