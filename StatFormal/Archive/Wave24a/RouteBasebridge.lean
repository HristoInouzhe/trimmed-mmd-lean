import StatFormal.Archive.Wave24a.Statements
import StatFormal.Archive.OTFD.Wave22b.RouteExp

/-!
# Route — T `eq:basebridge` (untrusted)

Triangle inequality through `Exp_{m̂(t)}(J_t v(t))`: the vertical leg is the Wave 22b `exp_pointwise`
(`‖J_t v‖ = ‖v‖ ≤ b`), the horizontal leg is `∫ spd ≤ C_b ∫ |γ'| = C_b d(m, m̂)`; then take suprema.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatFormal.Wave24a

theorem basebridge : Claims.basebridge := by
  intro T V W M _ _ _ _ _ m mh Ex Exh Dh J Hc spd gspd Cb b v vh hL hJ hends hlen hspd hgeo hv hvh
  refine iSup_le fun t => ?_
  have hJv : ‖J t (v t)‖ ≤ b := by rw [hJ]; exact hv t
  have h1 : edist (Exh t (vh t)) (Exh t (J t (v t))) ≤ StatFormal.OTFD.Wave22b.Lb Dh b * ‖vh t - J t (v t)‖ₑ :=
    StatFormal.OTFD.Wave22b.exp_pointwise hL t (hvh t) hJv
  have h2 : edist (Exh t (J t (v t))) (Ex t (v t)) ≤ (Cb : ℝ≥0∞) * edist (mh t) (m t) := by
    rw [← (hends t (v t)).1, ← (hends t (v t)).2, edist_comm]
    calc edist (Hc t (v t) 0) (Hc t (v t) 1) ≤ ∫⁻ σ in Icc (0 : ℝ) 1, spd t (v t) σ := hlen t (v t)
      _ ≤ ∫⁻ σ in Icc (0 : ℝ) 1, (Cb : ℝ≥0∞) * gspd t σ := lintegral_mono fun σ => hspd t (v t) σ (hv t)
      _ = (Cb : ℝ≥0∞) * ∫⁻ σ in Icc (0 : ℝ) 1, gspd t σ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (Cb : ℝ≥0∞) * edist (mh t) (m t) := by rw [hgeo t, edist_comm]
  calc edist (Exh t (vh t)) (Ex t (v t))
      ≤ edist (Exh t (vh t)) (Exh t (J t (v t))) + edist (Exh t (J t (v t))) (Ex t (v t)) := edist_triangle _ _ _
    _ ≤ StatFormal.OTFD.Wave22b.Lb Dh b * ‖vh t - J t (v t)‖ₑ + (Cb : ℝ≥0∞) * edist (mh t) (m t) :=
        add_le_add h1 h2
    _ ≤ (Cb : ℝ≥0∞) * (⨆ t, edist (mh t) (m t)) + StatFormal.OTFD.Wave22b.Lb Dh b * ⨆ t, ‖vh t - J t (v t)‖ₑ := by
        rw [add_comm]
        gcongr
        · exact le_iSup (fun t => edist (mh t) (m t)) t
        · exact le_iSup (fun t => ‖vh t - J t (v t)‖ₑ) t

example : Claims.basebridge := basebridge

end StatFormal.Wave24a
