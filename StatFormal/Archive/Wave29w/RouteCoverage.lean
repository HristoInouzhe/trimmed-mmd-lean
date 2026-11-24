import StatFormal.Archive.Wave29w.Statements
import StatFormal.Archive.Wave29f.RouteCoverage

/-!
# Route — T `thm:coverage-error`, the "consequently" clause (untrusted)

At each `n` the certified Wave 29f `coverr_rank` (resp. `coverr_model`) gives a measurable event of probability
`≥ p − c·e_n²`, `c = L_b²Λ²/δ²` finite and `e_n² = ∫ ‖Q̂_n − Q‖² dμ → 0`; so `c·e_n² < η` eventually.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave29w

/-- `c · e_n → 0` in `[0, ∞]` for a finite `c`, hence eventually `p − η ≤ p − c · e_n`. -/
lemma eventually_tsub_le {e : ℕ → ℝ≥0∞} (he : Tendsto e atTop (𝓝 0)) (c : ℝ) {η : ℝ≥0∞} (hη : 0 < η)
    (a : ℝ≥0∞) : ∀ᶠ n in atTop, a - η ≤ a - ENNReal.ofReal c * e n := by
  have h : Tendsto (fun n => ENNReal.ofReal c * e n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) he (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  filter_upwards [(tendsto_order.1 h).2 η hη] with n hn
  exact tsub_le_tsub_left hn.le a

theorem coverr_asymp : Claims.coverr_asymp := by
  intro H _ _ _ _ _ Tm V W M C Ω _ _ _ _ _ _ _ P X curve μ Ex D ι Em Lm Dr F Q Qhat tube A b Λ p hP hμ hX hcurve
    hEm hLm hDr hLE hae hrank hQhm hAm hΛ hLB hLb hι hQb hQhb htube hpA hcons δ hδ η hη
  filter_upwards [eventually_tsub_le hcons (((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ) ^ 2 / δ ^ 2) hη
    (ENNReal.ofReal p)] with n hn
  obtain ⟨Ev, hEv, hcov, hPEv⟩ := StatFormal.Wave29f.coverr_rank H Tm V W M C Ω P X curve μ Ex D ι Em Lm Dr F Q
    (Qhat n) (tube n) (A n) b Λ p δ hP hμ hX hcurve hEm hLm hDr hLE hae hrank (hQhm n) (hAm n) hδ hΛ hLB hLb hι hQb
    (hQhb n) (htube n) (hpA n)
  exact ⟨Ev, hEv, hcov, hn.trans hPEv⟩

theorem coverr_asymp_model : Claims.coverr_asymp_model := by
  intro H _ _ _ _ _ _ Tm V W M C Ω _ _ _ _ _ _ _ P X curve μ Ex D ι Em Lm Dr B Bμ Λ hP hμ hX hcurve hEm hLm hDr
    hLE hae hLN hLNμ hB hBμ hΛ hι hLB
  obtain ⟨F, Q, hrank, hF, hQ, hbound⟩ := StatFormal.Wave29f.coverr_model H Tm V W M C Ω P X curve μ Ex D ι Em Lm
    Dr B Bμ Λ hP hμ hX hcurve hEm hLm hDr hLE hae hLN hLNμ hB hBμ hΛ hι hLB
  refine ⟨F, Q, hrank, hF, hQ, fun Qhat tube A b p hQhm hAm hLb hQb hQhb htube hpA hcons δ hδ η hη => ?_⟩
  filter_upwards [eventually_tsub_le hcons (((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ) ^ 2 / δ ^ 2) hη
    (ENNReal.ofReal p)] with n hn
  obtain ⟨Ev, hEv, hcov, hPEv⟩ := hbound (Qhat n) (tube n) (A n) b p δ (hQhm n) (hAm n) hδ hLb hQb (hQhb n)
    (htube n) (hpA n)
  exact ⟨Ev, hEv, hcov, hn.trans hPEv⟩

end StatFormal.Wave29w
