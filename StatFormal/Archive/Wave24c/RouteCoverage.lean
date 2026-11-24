import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.OTFD.Wave22b.RouteExp

/-!
# Route — T `thm:coverage-error` (untrusted)

`lem:exp` (the frozen `LengthBound`, Wave 22b pointwise bound) with `eq:Hembed` gives
`d_M(E_m Q̂(u)(t), E_m Q(u)(t)) ≤ L ‖Q̂(u) − Q(u)‖`, `L = L_b Λ`. On `{U ∈ A} ∩ {‖Q̂(U) − Q(U)‖ ≤ δ/L}` the
reconstructed curves are within `δ` uniformly and `E_m(Q̂(U))(t) ∈ 𝒯(t)`. The complement of the discrepancy event is
contained in `{‖Q̂ − Q‖² ≥ (δ/L)²}`, whose `μ`-mass is at most `(L/δ)² ∫ ‖Q̂ − Q‖² dμ` (Markov). If `L = 0`, the curves
coincide and `{U ∈ A}` works.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave24c

lemma coverage_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] {Tm M Ω : Type*} [PseudoEMetricSpace M] [MeasurableSpace Ω]
    {P : Measure Ω} {U : Ω → H} {μ : Measure H} {E1 E2 : H → Tm → M} {Q Qhat : H → H} {tube : Tm → Set M}
    {A : Set H} {L pbar δ : ℝ} (hU : Measurable U) (hmap : P.map U = μ) (hQ : Measurable Q)
    (hQh : Measurable Qhat) (hA : MeasurableSet A) (hδ : 0 < δ) (hL : 0 < L)
    (hE : ∀ u t, edist (E1 u t) (E2 u t) ≤ ENNReal.ofReal (L * ‖Qhat u - Q u‖))
    (htube : ∀ u ∈ A, ∀ t, E2 u t ∈ tube t) (hpA : ENNReal.ofReal pbar ≤ μ A) :
    ∃ Ev : Set Ω, MeasurableSet Ev ∧ (∀ ω ∈ Ev, ∀ t, ∃ y ∈ tube t, edist (E1 (U ω) t) y ≤ ENNReal.ofReal δ) ∧
      ENNReal.ofReal pbar - ENNReal.ofReal (L ^ 2 / δ ^ 2) * ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ ≤ P Ev := by
  set B : Set H := {u | ‖Qhat u - Q u‖ ≤ δ / L}
  have hBm : MeasurableSet B := measurableSet_le (hQh.sub hQ).norm measurable_const
  refine ⟨U ⁻¹' (A ∩ B), hU (hA.inter hBm), ?_, ?_⟩
  · rintro ω ⟨hωA, hωB⟩ t
    refine ⟨E2 (U ω) t, htube _ hωA t, ?_⟩
    refine (hE _ t).trans (ENNReal.ofReal_le_ofReal ?_)
    calc L * ‖Qhat (U ω) - Q (U ω)‖ ≤ L * (δ / L) := mul_le_mul_of_nonneg_left hωB hL.le
      _ = δ := by field_simp
  · have hPev : P (U ⁻¹' (A ∩ B)) = μ (A ∩ B) := by
      rw [← hmap, Measure.map_apply hU (hA.inter hBm)]
    rw [hPev]
    have hc : Bᶜ ⊆ {u | ENNReal.ofReal ((δ / L) ^ 2) ≤ ‖Qhat u - Q u‖ₑ ^ 2} := by
      intro u hu
      simp only [B, mem_compl_iff, mem_setOf_eq, not_le] at hu ⊢
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (div_pos hδ hL).le hu.le 2)
    have hmarkov : ENNReal.ofReal ((δ / L) ^ 2) * μ {u | ENNReal.ofReal ((δ / L) ^ 2) ≤ ‖Qhat u - Q u‖ₑ ^ 2} ≤
        ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ :=
      mul_meas_ge_le_lintegral₀ ((hQh.sub hQ).enorm.pow_const 2).aemeasurable _
    have hBc : μ Bᶜ ≤ ENNReal.ofReal (L ^ 2 / δ ^ 2) * ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ := by
      have h1 : μ Bᶜ ≤ μ {u | ENNReal.ofReal ((δ / L) ^ 2) ≤ ‖Qhat u - Q u‖ₑ ^ 2} := measure_mono hc
      have hinv : ENNReal.ofReal (L ^ 2 / δ ^ 2) * ENNReal.ofReal ((δ / L) ^ 2) = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        have : L ^ 2 / δ ^ 2 * (δ / L) ^ 2 = 1 := by field_simp
        rw [this, ENNReal.ofReal_one]
      calc μ Bᶜ ≤ μ {u | ENNReal.ofReal ((δ / L) ^ 2) ≤ ‖Qhat u - Q u‖ₑ ^ 2} := h1
        _ = ENNReal.ofReal (L ^ 2 / δ ^ 2) * (ENNReal.ofReal ((δ / L) ^ 2) *
              μ {u | ENNReal.ofReal ((δ / L) ^ 2) ≤ ‖Qhat u - Q u‖ₑ ^ 2}) := by
            rw [← mul_assoc, hinv, one_mul]
        _ ≤ _ := by gcongr
    have hsplit : μ A ≤ μ (A ∩ B) + μ Bᶜ := by
      calc μ A ≤ μ ((A ∩ B) ∪ Bᶜ) := measure_mono (fun u hu => by
            by_cases hb : u ∈ B
            · exact Or.inl ⟨hu, hb⟩
            · exact Or.inr hb)
        _ ≤ μ (A ∩ B) + μ Bᶜ := measure_union_le _ _
    calc ENNReal.ofReal pbar - ENNReal.ofReal (L ^ 2 / δ ^ 2) * ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ
        ≤ μ A - μ Bᶜ := tsub_le_tsub hpA hBc
      _ ≤ μ (A ∩ B) := tsub_le_iff_right.2 hsplit

theorem coverage_error : Claims.coverage_error := by
  intro H _ _ _ _ _ Tm V W M Ω _ _ _ _ _ _ P U μ Ex D ι Q Qhat tube A b Λ pbar δ hP hU hmap hQ hQh hA hδ hΛ hLB
    hLb hι hQb hQhb htube hpA
  have hLr : 0 ≤ (StatFormal.OTFD.Wave22b.Lb D b).toReal := ENNReal.toReal_nonneg
  have hpt : ∀ u t, edist (Ex t (ι (Q u) t)) (Ex t (ι (Qhat u) t)) ≤
      ENNReal.ofReal ((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ * ‖Qhat u - Q u‖) := by
    intro u t
    rw [edist_comm]
    refine (StatFormal.OTFD.Wave22b.exp_pointwise hLB t (hQhb u t) (hQb u t)).trans ?_
    have hsub : ι (Qhat u) t - ι (Q u) t = ι (Qhat u - Q u) t := by rw [map_sub, Pi.sub_apply]
    rw [hsub, ← ofReal_norm]
    have hLe : StatFormal.OTFD.Wave22b.Lb D b = ENNReal.ofReal (StatFormal.OTFD.Wave22b.Lb D b).toReal :=
      (ENNReal.ofReal_toReal hLb).symm
    calc StatFormal.OTFD.Wave22b.Lb D b * ENNReal.ofReal ‖ι (Qhat u - Q u) t‖
        = ENNReal.ofReal ((StatFormal.OTFD.Wave22b.Lb D b).toReal * ‖ι (Qhat u - Q u) t‖) := by
          rw [ENNReal.ofReal_mul hLr, ← hLe]
      _ ≤ _ := by
          rw [mul_assoc]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hι _ _) hLr)
  rcases (mul_nonneg hLr hΛ).lt_or_eq with hL | hL
  · exact coverage_core hU hmap hQ hQh hA hδ hL hpt htube hpA
  · refine ⟨U ⁻¹' A, hU hA, fun ω hω t => ⟨_, htube _ hω t, ?_⟩, ?_⟩
    · refine (hpt _ t).trans ?_
      rw [← hL, zero_mul]
      exact ENNReal.ofReal_le_ofReal hδ.le
    · have hPA : P (U ⁻¹' A) = μ A := by rw [← hmap, Measure.map_apply hU hA]
      rw [hPA]
      exact tsub_le_self.trans hpA

end StatFormal.Wave24c
