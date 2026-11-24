import StatFormal.Lib.PaperRun.QPMeas

/-!
# Wave 31tr, chunk A1, T3: measurable exact minimizers of `eq:qp` (untrusted route)

Proves `Claims.qp_measurable_argmin` from `StatFormal.Lib.PaperRun.QPMeas`: the measurable selection (`exists_qpSel`, the
measurable argmin on the fixed compact capped set), measurability of `D̂` along a selection (`measurable_qpVal`), `D̂ = Demp`
(`qpVal_eq_Demp`, the certified `Wave8a.georep_qp`) and the identification of the two encodings of `eq:qp`.
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.Wave31tr.RouteRun

open StatFormal.Wave30tz StatFormal.PaperRun

theorem qp_measurable_argmin_route : Claims.qp_measurable_argmin := by
  intro 𝒳 H _ _ _ _ φ α n m hφ hα0 hα1 hn hm
  refine ⟨exists_qpSel hφ hα0 hα1 hn hm, fun σ hσ => ⟨?_, fun p => qpVal_eq_Demp hφ hα0 hα1 hn hm (hσ.2 p)⟩,
    fun x y w v => ⟨isCapped_iff α w, isCapped_iff α v, qp_eq_qpVal_sq φ x y w v, isQPMin_iff φ α x y w v⟩⟩
  exact measurable_qpVal hφ measurable_fst measurable_snd (measurable_fst.comp hσ.1) (measurable_snd.comp hσ.1)

end StatFormal.Wave31tr.RouteRun
