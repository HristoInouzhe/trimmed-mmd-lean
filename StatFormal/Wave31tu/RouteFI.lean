import StatFormal.Wave31tu.RouteFArith
import StatFormal.Wave31tu.RouteFOwn

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: case (i) of Proposition S4.27 (`prop:lapfitted`, S4 :1302-1333) and the gap bounds (S4 :1342-1344)

`fitted_i`: under (5.1) with the `p̄` bound, at a level `α = α⋆ − ε` with `ε_fit ≤ ε < α⋆` and an exact minimizer of `eq:qp`:
Lemma S4.25 (b) (frozen Y13 `lap_dev`) for `φ⋆` and for `φ̂` (deterministic on the interval events, the data-dependent `φ̂`
included), the common part `fitted_common` (Y7, Y10, Y11, Y12) and the arithmetic `fixed_point_i` give `|Δ⋆| + Δ̂ ≤ κ₀ε/4`, so the
plain ramp has excess `≥ 3κ₀ε/4` (Lemma S4.22 (ii)), `N̂ ≤ 24c_V^{−1}ε^{−1/4}` and `T̂ ≤ 5ε`; own-term cut points lose at most
`κ₀ε/4` (`own_excess` with `β = κ₀/40`, `L = 5`, from the fifth term via `FixedPoint.cap_le`). The gap: `ĝ = 1/N̂ ≥ c_Vε^{1/4}/24`,
and Lemma S4.20 (frozen Y9 `lap_ratio`) at the level `α⋆ − 2ε` gives `εĝ ≤ (2ε − T̂)ĝ ≤ V(2ε)` as `e ≥ 0`.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteF

open StatFormal StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration
  StatFormal.TrimmedMMD.Unconditional StatFormal.Wave31tq StatFormal.FixedPoint

/-- **Proposition S4.27, case (i)**, with the gap bounds. -/
theorem fitted_i (h7 : Claims.lap_const) (h9 : Claims.lap_ratio) (h10 : Claims.lap_clip) (h11 : Claims.lap_pop)
    (h12 : Claims.lap_compare) (h13 : Claims.lap_dev) (h14 : Claims.lap_own)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ}
    {x₀ ℓ₀ c₁ c₂ ε₀ c K : ℝ} {n m : ℕ} {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hφ : IsLaplaceFeature 1 φ) (hcross : IsCross P Q p q x₀ ℓ₀) (hpx0 : 0 < p x₀) (h54 : TwoSided54 φ P Q c₁ c₂ ε₀)
    (htv : Distances.tvDist P Q < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) (hxy : ∀ i j, x i ≠ y j) (hc : Real.log 8 ≤ c)
    (hK : 1 ≤ K) (hIx : IntervalEvent P x c) (hIy : IntervalEvent Q y c)
    {rs cs pbar : ℝ} (hR : CondR p q x₀ rs cs) (hpbar : ∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar)
    {ε : ℝ} (hfit : epsFitI (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) (cV (Distances.tvDist P Q) c₁ ε₀)
      (devA P Q x₀ K pbar cs rs c n m) (devG pbar cs rs K c n m) (devB K c n m) (min n m) ≤ ε)
    (hεα : ε < Distances.tvDist P Q) {w : Fin n → ℝ} {v : Fin m → ℝ} (hqp : IsQPMin φ (Distances.tvDist P Q - ε) x y w v) :
    (∀ t u, GenuineCuts φ x y w v (Distances.tvDist P Q - ε) t u → u < t ∧
      kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * ε / 2 ≤
        (∫ z, ramp (fitF φ x y w v) t u z ∂P) - (∫ z, ramp (fitF φ x y w v) t u z ∂Q) - (Distances.tvDist P Q - ε)) ∧
    cV (Distances.tvDist P Q) c₁ ε₀ * ε ^ (1 / 4 : ℝ) / 24 ≤
      tHat φ x y w v (Distances.tvDist P Q - ε) - uHat φ x y w v (Distances.tvDist P Q - ε) ∧
    (2 * ε ≤ Distances.tvDist P Q →
      tHat φ x y w v (Distances.tvDist P Q - ε) - uHat φ x y w v (Distances.tvDist P Q - ε) ≤
        Wave31ti.uPath φ P Q (Distances.tvDist P Q - 2 * ε) / ε) := by
  set αs := Distances.tvDist P Q with hαs
  set α := αs - ε with hα
  set κ := kappa0 αs c₁ c₂ ε₀ with hκdef
  set cv := cV αs c₁ ε₀ with hcvdef
  obtain ⟨-, hsm, hκ1⟩ := laplace1_facts hφ
  obtain ⟨-, -, hκ0', -, hcv', -, -, -, -⟩ := h7 H φ 1 P Q c₁ c₂ ε₀ hsm hκ1 htv h54
  have hnm : 1 ≤ min n m := le_min hn hm
  have hε : 0 < ε := (epsFitI_pos hκ0' hcv' hnm).trans_le hfit
  have hε1 : ε ≤ 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hα1 : α < 1 := by linarith
  obtain ⟨hκ0, hκlt, hcv, hgh, hnormφh, hhalf, hoscφh, hcuts, φs, yy, hosc_s, hNs, hTs, he, hyD, hi, hii, hiii⟩ :=
    fitted_common h7 h10 h11 h12 hφ h54 htv hn hm hxy hε hεα hqp
  set gh := tHat φ x y w v α - uHat φ x y w v α with hghdef
  set φh := gh⁻¹ • witness φ x y w v with hφhdef
  -- Lemma S4.25 (b) for `φ⋆` and for `φ̂`
  obtain ⟨-, hdevs⟩ := h13 H φ P Q n m x y x₀ c K φs hφ hn hm hc hIx hIy hK hosc_s
  obtain ⟨hTs_pos, hΔs⟩ := hdevs p q ℓ₀ rs cs pbar hcross hpx0 hR hpbar
  obtain ⟨-, hdevh⟩ := h13 H φ P Q n m x y x₀ c K φh hφ hn hm hc hIx hIy hK hoscφh
  obtain ⟨hTh_pos, hΔh⟩ := hdevh p q ℓ₀ rs cs pbar hcross hpx0 hR hpbar
  rw [max_eq_left hhalf] at hΔh
  -- the constants
  obtain ⟨hp0, hq0⟩ := And.intro hcross.2.2.1 hcross.2.2.2.1
  have hrs : 0 < rs := hR.1
  have hcs : 0 < cs := hR.2.2.1
  have hc0 : 0 ≤ c := le_trans (Real.log_nonneg (by norm_num)) hc
  have hϖ : 0 ≤ devG pbar cs rs K c n m := devG_nonneg (pbar_nonneg hp0 hq0 hrs.le hpbar) hcs hrs (by linarith)
  have hb : 0 ≤ devB K c n m := devB_nonneg (by linarith) hc0
  -- the fixed point
  obtain ⟨hy1, hNh24, hTh5, hsum⟩ := fixed_point_i (nm := min n m) hκ0 hκlt hcv hϖ hb hε hε1 hfit
    (le_max_of_le_right (by norm_num)) hNs hTs_pos.le hTs hΔs hiii (norm_nonneg _) hTh_pos.le hi hΔh
  have hκε : 0 < κ * ε := mul_pos hκ0 hε
  have he3 : 3 * κ * ε / 4 ≤ (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂P) -
      (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂Q) - α := by
    have hpos : 0 < κ * ε - |linL (empirical x) (empirical y) (Wave31to.wit φ φs) - linL P Q (Wave31to.wit φ φs)| -
        (linL (empirical x) (empirical y) (Wave31to.wit φ φh) - linL P Q (Wave31to.wit φ φh)) := by linarith
    have := hii hpos
    linarith
  -- the gap
  have he4 : 0 < ε ^ (1 / 4 : ℝ) := rpow_quarter_pos hε
  have hgap_lo : cv * ε ^ (1 / 4 : ℝ) / 24 ≤ gh := by
    rw [hnormφh, one_div, inv_mul_eq_div, div_le_iff₀ hgh] at hNh24
    linarith
  refine ⟨?_, hgap_lo, ?_⟩
  · intro t u hcut
    rcases hcuts t u hcut with ⟨rfl, rfl⟩ | ⟨htt, huu⟩
    · exact ⟨by linarith, by linarith⟩
    · -- own-term cut points: `β = κ₀/40`, `L = 5`
      have hT : errL P Q (ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α)) ≤ 5 * ε := by
        rw [errL_eq_sub _ ε]; linarith
      have h5 : (1920 / (κ * cv ^ 2 * (min n m : ℕ))) ^ (2 / 3 : ℝ) ≤ ε := (le_max_right _ _).trans hfit
      have hK24 : 1 / gh * (cv * ε ^ (1 / 4 : ℝ)) ≤ 24 := by rw [← hnormφh]; exact hNh24
      have hcapm := cap_le (C := 1920) hκ0 hcv hε (by norm_num) hnm (min_le_right n m) h5 hy1 hyD hgh hK24
      have hcapn := cap_le (C := 1920) hκ0 hcv hε (by norm_num) hnm (min_le_left n m) h5 hy1 hyD hgh hK24
      exact own_excess h14 hφ hn hm hxy hα0 hα1 hqp htt huu hκ0 hε hgh he3 hT (β := 2 * 24 * κ / 1920)
        (by linarith) (by linarith) hcapm hcapn
  · -- the upper bound on the gap, by Lemma S4.20 at the level `α⋆ − 2ε`
    intro h2ε
    have hφh0 : φh ≠ 0 := by
      intro h0
      have : ‖φh‖ = 0 := by rw [h0, norm_zero]
      rw [hnormφh] at this
      exact (one_div_pos.2 hgh).ne' this
    obtain ⟨-, hrat⟩ := h9 ℝ H φ 1 P Q α φh hsm hκ1 hα0.le hα1 hφh0 hoscφh
    have h2 := hrat htv (2 * ε) ⟨by linarith, h2ε⟩
    rw [hnormφh, div_div_eq_mul_div, div_one] at h2
    rw [le_div_iff₀ hε]
    have hTe : errL P Q (Wave31to.wit φ φh) ≤ ε := by linarith
    calc gh * ε ≤ (2 * ε - errL P Q (Wave31to.wit φ φh)) * gh := by nlinarith
      _ ≤ Wave31ti.uPath φ P Q (αs - 2 * ε) := h2

end StatFormal.Wave31tu.RouteF
