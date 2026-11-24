import StatFormal.Wave31tu.RouteP14
import StatFormal.Wave31tu.RouteP10

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y14 `lap_own` (Lemma S4.26 `lem:lapown`, printed form, S4 :1277-1291)

In the setting of Lemma S4.21, for `û ≤ ũ < t̃ ≤ t̂`, `a_o = (ũ − û)/ĝ`, `b_o = (t̂ − t̃)/ĝ`: `a_o + b_o < 1`, the ramp `ψ̃` of `f̂`
between `ũ` and `t̃` is `ϱ ∘ ψ̂` with `ϱ(s) = min{1, max{0, (s − a_o)/(1 − a_o − b_o)}}`, and
`E_Pψ̃ − E_Qψ̃ ≥ E_Pψ̂ − E_Qψ̂ − max(a_o,b_o)err(ψ̂)/(1 − a_o − b_o)` (any laws `P, Q` on `ℝ`); own-term cut points at genuine quantiles
have `û ≤ ũ`, `t̃ ≤ t̂`, `a_o ≤ 1/(m′D̄̂ĝ)` and `b_o ≤ 1/(n′D̄̂ĝ)`.

Route (printed): Lemma S4.21 (`RouteP10.lap_clip_route`: `û ≤ f̂ ≤ t̂`, `ĝ > 0`, and the own-term quantile bounds (k)) and the
general part `own_ramp` (`RouteP14.own_ramp_route`) at `ψ = ψ̂`.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Wave30tz StatFormal.Wave30tq

/-- The ramp between `ũ < t̃` is the clamp of the affine rescaling: `(min(max(s, ũ), t̃) − ũ)/(t̃ − ũ) = min{1, max{0, (s − ũ)/(t̃ − ũ)}}`. -/
theorem clip_div_eq_clamp {s uu tt : ℝ} (h : uu < tt) :
    (min (max s uu) tt - uu) / (tt - uu) = min 1 (max 0 ((s - uu) / (tt - uu))) := by
  have hc : 0 < tt - uu := by linarith
  rcases le_total s uu with h1 | h1
  · rw [max_eq_right h1, min_eq_left h.le, sub_self, zero_div,
      max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le), min_eq_right zero_le_one]
  · rcases le_total s tt with h2 | h2
    · rw [max_eq_left h1, min_eq_left h2, max_eq_right (div_nonneg (by linarith) hc.le),
        min_eq_right ((div_le_one hc).mpr (by linarith))]
    · rw [max_eq_left h1, min_eq_right h2, div_self hc.ne', max_eq_right (div_nonneg (by linarith) hc.le),
        min_eq_left ((one_le_div hc).mpr (by linarith))]

/-- Y14 `lap_own`. -/
theorem lap_own_route : Claims.lap_own := by
  intro H _ _ _ _ σ φ P Q _ _ n m x y α w v tt uu hσ hφ hn hm hxy hα0 hα1 hQP
  intro t u D
  have hc := lap_clip_route H σ φ n m x y α w v hσ hφ hn hm hxy hα0 hα1 hQP
  obtain ⟨hDpos, -, hband, -, htu, -, -, -, -, hramp, -, -, -, -, -, -, -, -, hqOX, hqOY⟩ := hc
  have hband' : ∀ z, u ≤ fitF φ x y w v z ∧ fitF φ x y w v z ≤ t := hband
  have htu' : 0 < t - u := htu
  refine ⟨fun h1 h2 h3 => ?_, fun hX hY => ?_⟩
  · set ao := (uu - u) / (t - u) with hao
    set bo := (t - tt) / (t - u) with hbo
    have hao0 : 0 ≤ ao := div_nonneg (by linarith) htu'.le
    have hbo0 : 0 ≤ bo := div_nonneg (by linarith) htu'.le
    have hc1 : 1 - ao - bo = (tt - uu) / (t - u) := by rw [hao, hbo]; field_simp; ring
    have hab : ao + bo < 1 := by
      have : 0 < (tt - uu) / (t - u) := div_pos (by linarith) htu'
      linarith
    have hψ : ∀ z, ramp (fitF φ x y w v) t u z = (fitF φ x y w v z - u) / (t - u) := fun z => by
      have := congrFun hramp z; exact this
    have hcomp : ramp (fitF φ x y w v) tt uu =
        fun z => min 1 (max 0 ((ramp (fitF φ x y w v) t u z - ao) / (1 - ao - bo))) := by
      funext z
      rw [hψ, hc1]
      have hr : ((fitF φ x y w v z - u) / (t - u) - ao) / ((tt - uu) / (t - u)) =
          (fitF φ x y w v z - uu) / (tt - uu) := by
        rw [hao]; field_simp; ring
      rw [hr]
      exact clip_div_eq_clamp (s := fitF φ x y w v z) h2
    refine ⟨hab, hcomp, ?_⟩
    -- the general part at `ψ = ψ̂`
    have hsm := (laplace_feature_facts hσ hφ).1
    have hFm : Measurable (fitF φ x y w v) :=
      ((continuous_const.inner continuous_id).comp_stronglyMeasurable hsm).measurable
    have hψm : Measurable (ramp (fitF φ x y w v) t u) := by
      unfold ramp clip
      exact ((hFm.max measurable_const).min measurable_const).sub_const _ |>.div_const _
    have hψ01 : ∀ z, 0 ≤ ramp (fitF φ x y w v) t u z ∧ ramp (fitF φ x y w v) t u z ≤ 1 := fun z => by
      rw [hψ]
      exact ⟨div_nonneg (by linarith [(hband' z).1]) htu'.le, (div_le_one htu').mpr (by linarith [(hband' z).2])⟩
    have h := own_ramp_route ℝ P Q (ramp (fitF φ x y w v) t u) ao bo hψm hψ01 hao0 hbo0 hab
    rw [hcomp]
    exact h
  · obtain ⟨hX1, hX2⟩ := hqOX tt hX
    obtain ⟨hY1, hY2⟩ := hqOY uu hY
    have hDD : D = (1 - α) * qpVal φ x y w v := rfl
    refine ⟨hY1, hX2, ?_, ?_⟩
    · rw [← div_div, div_le_div_iff_of_pos_right htu', hDD]; linarith
    · rw [← div_div, div_le_div_iff_of_pos_right htu', hDD]; linarith

end StatFormal.Wave31tu.RouteP
