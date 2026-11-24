import StatFormal.Wave31tq.RouteT20a
import StatFormal.Lib.MomentTrim.Region
import StatFormal.Lib.MomentTrim.SpectralIntegrals
import StatFormal.Wave31ti.Proofs

/-!
# Wave 31tq, route T (Q20): Proposition S4.15 (untrusted)

`Claims.newmoments` from Q1(b) (`Claims.tv_density`) and Q4 (`Claims.bochner_angular`), both hypotheses (chunk A).
The trimmings of the main part come from `MomentTrim.exists_moment_trimming` (RouteT20a for the measures). For (a), (b): with
`w = (8ε/ℓ₀)^{1/2} ≤ w_N` the trimming has `ε(w) ≥ ℓ₀w²/8 = ε`, so, `D̄` being nonincreasing (certified `Wave31ti.pathconvex`),
`D̄_{α⋆−ε} ≤ D̄_{α⋆−ε(w)} ≤ ‖∫ φ dP′ − ∫ φ dQ′‖` (`MomentTrim.uPath_le_of_le`); eq:newbochner (Q4) and eq:newmomentdecay (Q18)
with `W = Tw` bound the norm: in case (a) by `|ν|²(2π)⁻¹C ∫ min{1, (|ξ|W)^{2N}/N!²}|ξ|^{−2s} = |ν|²(2π)⁻¹C W^{2s−1} I_{N,s}` (the
substitution `v = Wξ`, `MomentTrim.integral_minPow_scale`), in case (b) by `|ν|² W^{2N} M_{2N}/N!²` (`k̂₀ ≥ 0`, certified
`Wave31tp.gram_profile`); then `|ν| ≤ 2ℓ₀w²` and `w² = 8ε/ℓ₀`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteT

open StatFormal.MomentTrim

/-- `min(1, a)² = min(1, a²)` for `a ≥ 0`. -/
lemma min_one_sq {a : ℝ} (ha : 0 ≤ a) : (min 1 a) ^ 2 = min 1 (a ^ 2) := by
  rcases le_total a 1 with h | h
  · rw [min_eq_right h, min_eq_right (by nlinarith)]
  · rw [min_eq_left h, min_eq_left (by nlinarith), one_pow]

/-- `((|ξ| W)^N / N!)² = (Wξ)^{2N} / N!²`. -/
lemma sq_moment_term (ξ W : ℝ) (N : ℕ) :
    ((|ξ| * W) ^ N / (N.factorial : ℝ)) ^ 2 = (W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2 := by
  rw [div_pow, ← pow_mul, mul_comm N 2, pow_mul, pow_mul, mul_pow, sq_abs]
  ring

/-- `(1 + ξ²)^{−s} ≤ |ξ|^{−2s}` for `ξ ≠ 0`, `s ≥ 0`. -/
lemma one_add_sq_rpow_le {ξ s : ℝ} (hξ : ξ ≠ 0) (hs : 0 ≤ s) : (1 + ξ ^ 2) ^ (-s) ≤ |ξ| ^ (-2 * s) := by
  have hpos : 0 < ξ ^ 2 := by positivity
  have e : |ξ| ^ (-2 * s) = (ξ ^ 2) ^ (-s) := by
    rw [show -2 * s = 2 * (-s) by ring, Real.rpow_mul (abs_nonneg ξ), Real.rpow_two, sq_abs]
  rw [e]
  exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)

/-- eq:newbochner with a pointwise majorant `B` of `k̂₀ |μ̂₁ − μ̂₂|²`. -/
theorem norm_sq_le_of_majorant (h4 : Claims.bochner_angular) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (φ : ℝ → H) (k₀ : ℝ → ℝ) (hk : Continuous k₀) (hki : Integrable k₀) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y))
    (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (B : ℝ → ℝ) (hBi : Integrable B)
    (hB : ∀ᵐ ξ, kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ B ξ) :
    ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * ∫ ξ, B ξ := by
  obtain ⟨hint, -, heq⟩ := h4 ℝ H φ k₀ hk hki hg μ₁ μ₂
  rw [heq, Module.finrank_self, pow_one]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hint hBi hB) (inv_nonneg.mpr (by positivity))

/-- From `x² ≤ y²`, `x, y ≥ 0`, to `x ≤ y`. -/
lemma le_of_sq_le_sq' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (pow_le_pow_iff_left₀ hx hy two_ne_zero).mp h

/-- **Case (a).** If `k̂₀ ≤ C(1+ξ²)^{−s}` and `|μ̂₁ − μ̂₂| ≤ V min{1, (|ξ|W)^N/N!}`, then
`‖∫ φ dμ₁ − ∫ φ dμ₂‖ ≤ V W^{s−1/2} (C I_{N,s}/2π)^{1/2}`. -/
theorem norm_le_case_a (h4 : Claims.bochner_angular) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (φ : ℝ → H) (k₀ : ℝ → ℝ) (hk : Continuous k₀) (hki : Integrable k₀) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y))
    {C s : ℝ} {N : ℕ} (hC : 0 < C) (hs : 1 / 2 < s) (hsN : s - 1 / 2 < (N : ℝ))
    (hkb : ∀ ξ, kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s))
    (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {V W : ℝ} (hV : 0 ≤ V) (hW : 0 < W)
    (hd : ∀ ξ, ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ≤ V * min 1 ((|ξ| * W) ^ N / (N.factorial : ℝ))) :
    ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ≤
      V * W ^ (s - 1 / 2) * √(C * (∫ v : ℝ, min 1 (v ^ (2 * N) / (N.factorial : ℝ) ^ 2) * |v| ^ (-2 * s)) / (2 * Real.pi)) := by
  set I := ∫ v : ℝ, min 1 (v ^ (2 * N) / (N.factorial : ℝ) ^ 2) * |v| ^ (-2 * s) with hI
  have hfac : (0 : ℝ) < (N.factorial : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos N)) 2
  have hI0 : 0 ≤ I := integral_nonneg fun v => mul_nonneg (le_min zero_le_one (div_nonneg (by rw [pow_mul]; positivity) hfac.le))
    (Real.rpow_nonneg (abs_nonneg _) _)
  set B : ℝ → ℝ := fun ξ => C * V ^ 2 * (min 1 ((W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2) * |ξ| ^ (-2 * s)) with hB
  have hBi : Integrable B := (integrable_minPow_scale N hfac hs hsN hW).const_mul _
  have hBint : ∫ ξ, B ξ = C * V ^ 2 * (W ^ (2 * s - 1) * I) := by
    rw [hB, integral_const_mul, integral_minPow_scale N _ s hW]
  have hpt : ∀ᵐ ξ, kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ B ξ := by
    have hne : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hne] with ξ hξ
    have hm0 : 0 ≤ (|ξ| * W) ^ N / (N.factorial : ℝ) := by positivity
    have hmin0 : 0 ≤ min 1 ((|ξ| * W) ^ N / (N.factorial : ℝ)) := le_min zero_le_one hm0
    have hd2 : ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ V ^ 2 * min 1 ((W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2) := by
      calc ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ (V * min 1 ((|ξ| * W) ^ N / (N.factorial : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hd ξ) 2
        _ = V ^ 2 * min 1 ((W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2) := by
            rw [mul_pow, min_one_sq hm0, sq_moment_term]
    have hk2 : kHat k₀ ξ ≤ C * |ξ| ^ (-2 * s) :=
      (hkb ξ).trans (mul_le_mul_of_nonneg_left (one_add_sq_rpow_le hξ (by linarith)) hC.le)
    calc kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2
        ≤ (C * |ξ| ^ (-2 * s)) * (V ^ 2 * min 1 ((W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2)) :=
          mul_le_mul hk2 hd2 (sq_nonneg _) (mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg _) _))
      _ = B ξ := by simp only [hB]; ring
  have hsq := norm_sq_le_of_majorant h4 φ k₀ hk hki hg μ₁ μ₂ B hBi hpt
  rw [hBint] at hsq
  have hCI : 0 ≤ C * I / (2 * Real.pi) := by positivity
  refine le_of_sq_le_sq' (norm_nonneg _) (by positivity) (hsq.trans (le_of_eq ?_))
  rw [mul_pow, mul_pow, Real.sq_sqrt hCI, ← Real.rpow_natCast (W ^ (s - 1 / 2)), ← Real.rpow_mul hW.le]
  have : (s - 1 / 2) * ((2 : ℕ) : ℝ) = 2 * s - 1 := by push_cast; ring
  rw [this]
  field_simp

/-- **Case (b).** If `∫ ξ^{2N} k̂₀ < ∞` and `|μ̂₁ − μ̂₂| ≤ V min{1, (|ξ|W)^N/N!}`, then
`‖∫ φ dμ₁ − ∫ φ dμ₂‖ ≤ V W^N M_{2N}^{1/2}/N!`. -/
theorem norm_le_case_b (h4 : Claims.bochner_angular) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (φ : ℝ → H) (k₀ : ℝ → ℝ) (hk : Continuous k₀) (hki : Integrable k₀) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y))
    {N : ℕ} (hmi : Integrable (fun ξ : ℝ => ξ ^ (2 * N) * kHat k₀ ξ))
    (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hd : ∀ ξ, ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ≤ V * min 1 ((|ξ| * W) ^ N / (N.factorial : ℝ))) :
    ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ≤
      V * W ^ N * √((2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ξ ^ (2 * N) * kHat k₀ ξ) / (N.factorial : ℝ) := by
  have hk0 : ∀ ξ, 0 ≤ kHat k₀ ξ := fun ξ =>
    ((Wave31tp.gram_profile ℝ H φ k₀ hg).2.2.2.2.2.2 hki hk).1 ((2 * Real.pi)⁻¹ • ξ)
  set M := (2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ξ ^ (2 * N) * kHat k₀ ξ with hM
  have hev : ∀ ξ : ℝ, 0 ≤ ξ ^ (2 * N) := fun ξ => by rw [pow_mul]; positivity
  have hM0 : 0 ≤ M := mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg fun ξ => mul_nonneg (hev ξ) (hk0 ξ))
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  set B : ℝ → ℝ := fun ξ => V ^ 2 * W ^ (2 * N) / (N.factorial : ℝ) ^ 2 * (ξ ^ (2 * N) * kHat k₀ ξ) with hB
  have hBi : Integrable B := hmi.const_mul _
  have hpt : ∀ᵐ ξ, kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ B ξ := by
    refine ae_of_all _ fun ξ => ?_
    have hm0 : 0 ≤ (|ξ| * W) ^ N / (N.factorial : ℝ) := by positivity
    have hd2 : ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ V ^ 2 * ((W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2) := by
      calc ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ (V * ((|ξ| * W) ^ N / (N.factorial : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ((hd ξ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hV)) 2
        _ = V ^ 2 * ((W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2) := by rw [mul_pow, sq_moment_term]
    calc kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2 ≤ kHat k₀ ξ * (V ^ 2 * ((W * ξ) ^ (2 * N) / (N.factorial : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hd2 (hk0 ξ)
      _ = B ξ := by simp only [hB]; rw [mul_pow]; ring
  have hsq := norm_sq_le_of_majorant h4 φ k₀ hk hki hg μ₁ μ₂ B hBi hpt
  have hBint : (2 * Real.pi)⁻¹ * ∫ ξ, B ξ = V ^ 2 * W ^ (2 * N) / (N.factorial : ℝ) ^ 2 * M := by
    rw [hB, integral_const_mul, hM]; ring
  rw [hBint] at hsq
  refine le_of_sq_le_sq' (norm_nonneg _) (by positivity) (hsq.trans (le_of_eq ?_))
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hM0, ← pow_mul, mul_comm N 2]
  ring

end StatFormal.Wave31tq.RouteT
