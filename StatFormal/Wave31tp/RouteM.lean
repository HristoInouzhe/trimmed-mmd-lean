import StatFormal.Wave31tp.Statements
import StatFormal.Lib.FourierOps.Dilate
import StatFormal.Lib.FourierOps.Laplacian
import StatFormal.Lib.FourierOps.Mollify
import StatFormal.Lib.FourierOps.Translate

/-!
# Wave 31tp, route M: dilations, Laplacians, mollifiers, translations (untrusted proof file)

L6 (`dilate_facts`) from `Lib/FourierOps/Dilate.lean`; L7 (`laplacian_fourier`) from `Lib/FourierOps/Laplacian.lean`;
L8 (`mollify_smooth`, `mollify_cont`) from `Lib/FourierOps/Mollify.lean`; L10 (`translation_plancherel`,
`translation_indicator`) from `Lib/FourierOps/Translate.lean`.
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteM

theorem dilate_facts_route : Claims.dilate_facts := by
  intro V _ _ _ _ _ b w hb hw
  exact ⟨FourierOps.integrable_dilate hb hw, FourierOps.integral_dilate b hw, FourierOps.fourier_dilate b hw,
    FourierOps.norm_fourier_le_integral_norm b⟩

theorem laplacian_fourier_route : Claims.laplacian_fourier := by
  intro V _ _ _ _ _ b m hb hbs
  exact ⟨FourierOps.fourier_laplacian_iterate hb hbs m, fun _ hξ => FourierOps.norm_fourier_le_laplacian hb hbs m hξ⟩

theorem mollify_smooth_route : Claims.mollify_smooth := by
  intro V _ _ _ _ _ E b w hE hEb hb hb0 hb1 hbs hw
  exact FourierOps.mollify_smooth_facts hE hEb hb hb0 hb1 hbs hw

theorem mollify_cont_route : Claims.mollify_cont := by
  intro V _ _ _ _ _ E b hE hfin hbc hbB hbi hb0 hb1
  exact FourierOps.mollify_cont_facts hE hfin hbc hbB hbi hb0 hb1

theorem translation_plancherel_route : Claims.translation_plancherel := by
  intro V _ _ _ _ _ f h hf1 hf2
  exact FourierOps.integral_norm_fourier_sq_mul_phase hf1 hf2 h

theorem translation_indicator_route : Claims.translation_indicator := by
  intro V _ _ _ _ _ E h hE _
  exact ⟨FourierOps.integral_norm_indicator_increment_sq hE h,
    congrArg ENNReal.toReal (FourierOps.volume_symmDiff_add_eq_sub E h)⟩

end StatFormal.Wave31tp.RouteM
