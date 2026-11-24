import StatFormal.Lib.Alpha0Witness.Basic
import StatFormal.Lib.Alpha0Witness.KSLocal

/-!
# Wave 31tr, chunk M2: T14 `alpha0_uniform`, T16(a) `ksPlus_locally_constant` (untrusted route)

T14: at `α = 0` the capped simplex is the uniform point (`Alpha0Witness.isCapped_zero_iff`), so the exact minimizers of `eq:qp` are the
uniform pair (`isQPMin_zero_iff`), `D̂` and the witness are the empirical-mean-embedding expressions (`qpVal_unif`, `witness_unif`),
`D̂ = Demp` (`PaperRun.qpVal_eq_Demp`, the certified `Wave8a.georep_qp`) and `∫ φ dP_n` is the sample mean (`integral_empirical`).
T16(a): `Alpha0Witness.ksPlus_eq_of_close` (the up-sets of `f` and `f₀` on the support coincide).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tr.RouteAlpha0

open StatFormal.Wave30tz StatFormal.Alpha0Witness

theorem alpha0_uniform_route : Claims.alpha0_uniform := by
  intro 𝒳 H _ _ _ _ φ n m x y hn hm
  refine ⟨setOf_isCapped_zero hn, isQPMin_zero_iff φ hn hm x y, qpVal_unif φ x y, witness_unif φ x y, fun h0 => ?_,
    fun hφ => ⟨?_, ?_⟩⟩
  · rw [witness_unif, h0, inv_zero, zero_smul]
  · rw [← StatFormal.PaperRun.qpVal_eq_Demp hφ le_rfl one_pos hn hm ((isQPMin_zero_iff φ hn hm x y _ _).2 ⟨rfl, rfl⟩),
      qpVal_unif]
  · rw [integral_empirical hφ, integral_empirical hφ]

theorem ksPlus_locally_constant_route : Claims.ksPlus_locally_constant := by
  intro 𝒳 _ _ P Q _ _ S f₀ g₀ hP hQ _ _ hg₀ hgap f _ hclose
  exact ksPlus_eq_of_close P Q hP hQ hg₀ hgap hclose

end StatFormal.Wave31tr.RouteAlpha0
