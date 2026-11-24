import StatFormal.Wave31tu.RouteFCommon

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: own-term cut points in Proposition S4.27 (S4 :1330-1333, :1339-1340)

`own_excess`: if the plain ramp has excess at least `3κ₀ε/4`, its error is at most `Lε`, and the own-term fractions satisfy
`1/(m′D̄̂ĝ), 1/(n′D̄̂ĝ) ≤ β` with `4β ≤ 1` and `βL ≤ κ₀/8`, then genuine own-term cut points do not cross and their ramp has excess at
least `κ₀ε/2`: by the frozen claim Y14 `lap_own`, `a_o, b_o ≤ β`, so `a_o + b_o < 1` (`ũ < t̃`) and the loss
`max(a_o,b_o) err(ψ̂)/(1 − a_o − b_o) ≤ κ₀ε/4` (library `FixedPoint.loss_le`). Case (i) uses `β = κ₀/40`, `L = 5`; case (ii)
`β = κ₀/24`, `L = 3`.

`errL_ramp_eq`: the error of the plain ramp is `ε − e` (`= T̂` by Lemma S4.22 (i)).
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteF

open StatFormal StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration
  StatFormal.TrimmedMMD.Unconditional StatFormal.Wave31tq StatFormal.FixedPoint

/-- `err(ψ) = ε − (E_Pψ − E_Qψ − (α⋆ − ε))`. -/
theorem errL_eq_sub {P Q : Measure ℝ} (f : ℝ → ℝ) (ε : ℝ) :
    errL P Q f = ε - ((∫ z, f z ∂P) - (∫ z, f z ∂Q) - (Distances.tvDist P Q - ε)) := by
  simp only [errL, linL]; ring

/-- **Own-term cut points keep most of the excess.** -/
theorem own_excess (h14 : Claims.lap_own)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    {x : Fin n → ℝ} {y : Fin m → ℝ} {w : Fin n → ℝ} {v : Fin m → ℝ} {α tt uu κ ε β L : ℝ}
    (hφ : IsLaplaceFeature 1 φ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hxy : ∀ i j, x i ≠ y j) (hα0 : 0 < α) (hα1 : α < 1)
    (hqp : IsQPMin φ α x y w v)
    (htt : IsEmpQuantile (ownX φ x y w v) (1 - α) tt) (huu : IsEmpQuantile (ownY φ x y w v) α uu)
    (hκ : 0 < κ) (hε : 0 < ε) (hgh : 0 < tHat φ x y w v α - uHat φ x y w v α)
    (he : 3 * κ * ε / 4 ≤ (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂P) -
      (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂Q) - α)
    (hT : errL P Q (ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α)) ≤ L * ε)
    (h4β : 4 * β ≤ 1) (hβL : β * L ≤ κ / 8)
    (hcapm : 1 / (m * ((1 - α) * qpVal φ x y w v) * (tHat φ x y w v α - uHat φ x y w v α)) ≤ β)
    (hcapn : 1 / (n * ((1 - α) * qpVal φ x y w v) * (tHat φ x y w v α - uHat φ x y w v α)) ≤ β) :
    uu < tt ∧ κ * ε / 2 ≤ (∫ z, ramp (fitF φ x y w v) tt uu z ∂P) - (∫ z, ramp (fitF φ x y w v) tt uu z ∂Q) - α := by
  obtain ⟨hA, hB⟩ := h14 H 1 φ P Q n m x y α w v tt uu one_pos hφ hn hm hxy hα0 hα1 hqp
  obtain ⟨hule, htle, hao, hbo⟩ := hB htt huu
  set t := tHat φ x y w v α with ht
  set u := uHat φ x y w v α with hu
  set ao := (uu - u) / (t - u) with hao_def
  set bo := (t - tt) / (t - u) with hbo_def
  have hao0 : 0 ≤ ao := div_nonneg (by linarith) hgh.le
  have hbo0 : 0 ≤ bo := div_nonneg (by linarith) hgh.le
  have haoβ : ao ≤ β := hao.trans hcapm
  have hboβ : bo ≤ β := hbo.trans hcapn
  have hsum : ao + bo < 1 := by linarith
  have hlt : uu < tt := by
    have : (uu - u) + (t - tt) < t - u := by
      have h := hsum
      rw [hao_def, hbo_def, ← add_div, div_lt_one hgh] at h
      exact h
    linarith
  refine ⟨hlt, ?_⟩
  obtain ⟨-, -, hlin⟩ := hA hule hlt htle
  have hloss := loss_le hao0 haoβ hboβ h4β hβL hκ hε hT
  simp only [linL] at hlin
  linarith

end StatFormal.Wave31tu.RouteF
