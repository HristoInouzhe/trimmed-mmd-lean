import StatFormal.Wave31tu.RouteFArith
import StatFormal.Wave31tu.RouteFOwn

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: case (ii) of Proposition S4.27 (`prop:lapfitted`, S4 :1335-1340)

`fitted_ii`: without (5.1), at a level `α = α⋆ − ε` with `ε_fit ≤ ε < α⋆` (case (ii) constants) and an exact minimizer of `eq:qp`:
Lemma S4.25 (a) (frozen Y13 `lap_dev`) for `φ⋆` and `φ̂`, the common part `fitted_common` and the arithmetic `fixed_point_ii`
(`ϖ′N̂^{1/2} ≤ N̂y/4 + ϖ′²/y`, `N̂ ≤ 12c_V^{−1}ε^{−1/4}`, `T̂ ≤ 3ε`, `1 + √12 < 5`) give `|Δ⋆| + Δ̂ ≤ κ₀ε/4`; `T̂ ≥ 0` is `eq:laperr`
(frozen Y6 `lap_err`); own-term cut points lose at most `κ₀ε/4` (`own_excess` with `β = κ₀/24`, `L = 3`).
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteF

open StatFormal StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration
  StatFormal.TrimmedMMD.Unconditional StatFormal.Wave31tq StatFormal.FixedPoint

/-- **Proposition S4.27, case (ii).** -/
theorem fitted_ii (h6 : Claims.lap_err) (h7 : Claims.lap_const) (h10 : Claims.lap_clip) (h11 : Claims.lap_pop)
    (h12 : Claims.lap_compare) (h13 : Claims.lap_dev) (h14 : Claims.lap_own)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ}
    {x₀ ℓ₀ c₁ c₂ ε₀ c K : ℝ} {n m : ℕ} {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hφ : IsLaplaceFeature 1 φ) (hcross : IsCross P Q p q x₀ ℓ₀) (h54 : TwoSided54 φ P Q c₁ c₂ ε₀)
    (htv : Distances.tvDist P Q < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) (hxy : ∀ i j, x i ≠ y j) (hc : Real.log 8 ≤ c)
    (hK : 1 ≤ K) (hIx : IntervalEvent P x c) (hIy : IntervalEvent Q y c)
    {ε : ℝ} (hfit : epsFitII (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) (cV (Distances.tvDist P Q) c₁ ε₀)
      (devA' P Q x₀ K c n m) (devG' K c n m) (devB K c n m) (min n m) ≤ ε)
    (hεα : ε < Distances.tvDist P Q) {w : Fin n → ℝ} {v : Fin m → ℝ} (hqp : IsQPMin φ (Distances.tvDist P Q - ε) x y w v) :
    ∀ t u, GenuineCuts φ x y w v (Distances.tvDist P Q - ε) t u → u < t ∧
      kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * ε / 2 ≤
        (∫ z, ramp (fitF φ x y w v) t u z ∂P) - (∫ z, ramp (fitF φ x y w v) t u z ∂Q) - (Distances.tvDist P Q - ε) := by
  set αs := Distances.tvDist P Q with hαs
  set α := αs - ε with hα
  set κ := kappa0 αs c₁ c₂ ε₀ with hκdef
  set cv := cV αs c₁ ε₀ with hcvdef
  obtain ⟨hcont, hsm, hκ1⟩ := laplace1_facts hφ
  obtain ⟨-, -, hκ0', -, hcv', -, -, -, -⟩ := h7 H φ 1 P Q c₁ c₂ ε₀ hsm hκ1 htv h54
  have hnm : 1 ≤ min n m := le_min hn hm
  have hε : 0 < ε := (epsFitII_pos hκ0' hcv' hnm).trans_le hfit
  have hα0 : 0 < α := by linarith
  have hα1 : α < 1 := by linarith
  obtain ⟨hκ0, hκlt, hcv, hgh, hnormφh, hhalf, hoscφh, hcuts, φs, yy, hosc_s, hNs, -, he, hyD, hi, hii, hiii⟩ :=
    fitted_common h7 h10 h11 h12 hφ h54 htv hn hm hxy hε hεα hqp
  set gh := tHat φ x y w v α - uHat φ x y w v α with hghdef
  set φh := gh⁻¹ • witness φ x y w v with hφhdef
  -- Lemma S4.25 (a) for `φ⋆` and for `φ̂`
  obtain ⟨hΔs, -⟩ := h13 H φ P Q n m x y x₀ c K φs hφ hn hm hc hIx hIy hK hosc_s
  obtain ⟨hΔh, -⟩ := h13 H φ P Q n m x y x₀ c K φh hφ hn hm hc hIx hIy hK hoscφh
  rw [max_eq_left hhalf] at hΔh
  -- `T̂ ≥ 0` by `eq:laperr`
  have hTh0 : 0 ≤ errL P Q (Wave31to.wit φ φh) := by
    obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, -⟩ := hcross
    have hfm : Measurable (Wave31to.wit φ φh) := (continuous_const.inner hcont).measurable
    have hfb : ∃ C, ∀ z, |Wave31to.wit φ φh z| ≤ C := ⟨‖φh‖ * 1, fun z =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hκ1 z) (norm_nonneg _))⟩
    exact (h6 P Q p q _ hpm hqm hp0 hq0 hP hQ hfm hfb hoscφh).2.2.2.2.1
  -- the constants
  have hc0 : 0 ≤ c := le_trans (Real.log_nonneg (by norm_num)) hc
  have hϖ : 0 ≤ devG' K c n m := devG'_nonneg (by linarith)
  have hb : 0 ≤ devB K c n m := devB_nonneg (by linarith) hc0
  -- the fixed point
  obtain ⟨hy1, hNh12, hTh3, hsum⟩ := fixed_point_ii (nm := min n m) hκ0 hκlt hcv hϖ hb hε hfit
    (le_max_of_le_right (by norm_num)) hNs hΔs hiii (norm_nonneg _) hTh0 hi hΔh
  have hκε : 0 < κ * ε := mul_pos hκ0 hε
  have he3 : 3 * κ * ε / 4 ≤ (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂P) -
      (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂Q) - α := by
    have hpos : 0 < κ * ε - |linL (empirical x) (empirical y) (Wave31to.wit φ φs) - linL P Q (Wave31to.wit φ φs)| -
        (linL (empirical x) (empirical y) (Wave31to.wit φ φh) - linL P Q (Wave31to.wit φ φh)) := by linarith
    have := hii hpos
    linarith
  intro t u hcut
  rcases hcuts t u hcut with ⟨rfl, rfl⟩ | ⟨htt, huu⟩
  · exact ⟨by linarith, by linarith⟩
  · -- own-term cut points: `β = κ₀/24`, `L = 3`
    have hT : errL P Q (ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α)) ≤ 3 * ε := by
      rw [errL_eq_sub _ ε]; linarith
    have h5 : (576 / (κ * cv ^ 2 * (min n m : ℕ))) ^ (2 / 3 : ℝ) ≤ ε := (le_max_right _ _).trans hfit
    have hK12 : 1 / gh * (cv * ε ^ (1 / 4 : ℝ)) ≤ 12 := by rw [← hnormφh]; exact hNh12
    have hcapm := cap_le (C := 576) hκ0 hcv hε (by norm_num) hnm (min_le_right n m) h5 hy1 hyD hgh hK12
    have hcapn := cap_le (C := 576) hκ0 hcv hε (by norm_num) hnm (min_le_left n m) h5 hy1 hyD hgh hK12
    exact own_excess h14 hφ hn hm hxy hα0 hα1 hqp htt huu hκ0 hε hgh he3 hT (β := 2 * 12 * κ / 576)
      (by linarith) (by linarith) hcapm hcapn

end StatFormal.Wave31tu.RouteF
