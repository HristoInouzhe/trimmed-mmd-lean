import StatFormal.Wave31tq.RouteT19
import StatFormal.Lib.MomentTrim.Crossing

/-!
# Wave 31tq, route T (Q21, the small-`s` clause): "For `s < 3/2` and `α⋆ < 1`, Proposition S4.14 with `r = 1` already gives
the upper bound, without `p(x₀) > 0`" (S4 :841-842) (untrusted)

`newsobolev_upper_small_of (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) : Claims.newsobolev_upper_small`.
Under `IsCross`, `e = p − q` vanishes at `x₀` (continuity at `x₀` from differentiability, and the a.e. signs:
`MomentTrim.eq_zero_of_signs`), so `e ≥ (ℓ₀/2)(x − x₀)` on `(x₀, x₀ + δ)` and `−e ≥ (ℓ₀/2)(x₀ − x)` on `(x₀ − δ, x₀)`
(`MomentTrim.exists_linear_lower`); Proposition S4.14 (`newupperone_of`) applies with `r = 1`, `ℓ′ = ℓ₀/2`, `r₀ = δ` and the
constant `C′ = max(C, 1) > 0` (`k̂₀ ≤ C(1+ξ²)^{−s} ≤ C′|ξ|^{−2s}`; the frozen claim has no guard `0 < C`, and `C′` makes none
necessary), with `W_ε = (4ε/ℓ₀)^{1/2}` and `2εW_ε^{s−1/2} = 2(4/ℓ₀)^{(2s−1)/4} ε^{(2s+3)/4}`. Then
`D_{α⋆−ε} ≤ D̄_{α⋆−ε}/(1 − α⋆)` when `α⋆ < 1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteT

open StatFormal.MomentTrim

/-- The algebra of `r = 1`, `ℓ′ = ℓ₀/2`: `2ε((4ε/ℓ₀)^{1/2})^{s−1/2} R = 2(4/ℓ₀)^{(2s−1)/4} R ε^{(2s+3)/4}`. -/
lemma alg_c {ε ℓ₀ s R : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ₀) :
    2 * ε * (((1 + 1) * ε / (ℓ₀ / 2)) ^ (1 / (1 + 1 : ℝ))) ^ (s - 1 / 2) * R =
      2 * (4 / ℓ₀) ^ ((2 * s - 1) / 4) * R * ε ^ ((2 * s + 3) / 4) := by
  have e1 : (1 + 1) * ε / (ℓ₀ / 2) = 4 / ℓ₀ * ε := by field_simp; ring
  rw [e1, ← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) hε.le,
    show 1 / (1 + 1 : ℝ) * (s - 1 / 2) = (2 * s - 1) / 4 by ring,
    show (2 * s + 3) / 4 = 1 + (2 * s - 1) / 4 by ring, Real.rpow_add hε, Real.rpow_one]
  ring

/-- `D_{α⋆−ε} ≤ D̄_{α⋆−ε}/(1 − α⋆)` for `0 ≤ ε` and `α⋆ < 1`. -/
lemma Dpop_le_uPath_div {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) (P Q : Measure 𝒳) {a ε : ℝ} (ha : a < 1) (hε : 0 ≤ ε) :
    StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q (a - ε) ≤ (1 - a)⁻¹ * StatFormal.Wave31ti.uPath φ P Q (a - ε) := by
  have h1a : 0 < 1 - a := by linarith
  have hD := Dpop_nonneg φ P Q (a - ε)
  unfold StatFormal.Wave31ti.uPath
  rw [le_inv_mul_iff₀ h1a]
  nlinarith

/-- Q21 `newsobolev_upper_small` (S4 :841-842), from Q1(b) and Q4 (through Q19). -/
theorem newsobolev_upper_small_of (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) :
    Claims.newsobolev_upper_small := by
  intro H _ _ _ _ φ k₀ C s P Q _ _ p q x₀ ℓ₀ hk hki hg hs hs3 hkb hcross
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, -, hsR, hsL, hd, hℓ⟩ := hcross
  -- `e(x₀) = 0` and the linear lower bounds
  have he0 : (fun x => p x - q x) x₀ = 0 :=
    eq_zero_of_signs (e := fun x => p x - q x) (x₀ := x₀) hd.continuousAt (hsR.mono fun x hx h => sub_nonneg.mpr (hx h))
      (hsL.mono fun x hx h => sub_nonpos.mpr (hx h))
  obtain ⟨δ, hδ, hRlin, hLlin⟩ := exists_linear_lower hd he0 hℓ
  have hR : ∀ᵐ x ∂volume, x ∈ Ioo x₀ (x₀ + δ) → ℓ₀ / 2 * (x - x₀) ^ (1 : ℝ) ≤ p x - q x :=
    ae_of_all _ fun x hx => by rw [Real.rpow_one]; exact hRlin x hx
  have hL : ∀ᵐ x ∂volume, x ∈ Ioo (x₀ - δ) x₀ → ℓ₀ / 2 * (x₀ - x) ^ (1 : ℝ) ≤ q x - p x :=
    ae_of_all _ fun x hx => by
      rw [Real.rpow_one]; have h' : ℓ₀ / 2 * (x₀ - x) ≤ -(p x - q x) := hLlin x hx; linarith
  -- the spectral bound with a positive constant
  set C' := max C 1 with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hkb' : ∀ ξ : ℝ, ξ ≠ 0 → kHat k₀ ξ ≤ C' * |ξ| ^ (-2 * s) := by
    intro ξ hξ
    have h0 : 0 ≤ (1 + ξ ^ 2) ^ (-s) := Real.rpow_nonneg (by positivity) _
    calc kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s) := hkb ξ
      _ ≤ C' * (1 + ξ ^ 2) ^ (-s) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ C' * |ξ| ^ (-2 * s) := mul_le_mul_of_nonneg_left (one_add_sq_rpow_le hξ (by linarith)) hC'0.le
  have hQ19 := newupperone_of h1 h4 H φ k₀ C' s P Q p q x₀ (ℓ₀ / 2) 1 δ hk hki hg hC'0 hs hs3 hkb' hpm hqm hp0 hq0 hP hQ
    (half_pos hℓ) one_pos hδ hR hL
  set ε₀ := ℓ₀ / 2 * δ ^ ((1 : ℝ) + 1) / (1 + 1) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  set R := √(C' / (2 * Real.pi) * (2 / (3 - 2 * s) + 2 / (2 * s - 1))) with hR'
  refine ⟨2 * (4 / ℓ₀) ^ ((2 * s - 1) / 4) * R, ε₀, hε₀0, (hQ19 ε₀ ⟨hε₀0, le_rfl⟩).1, fun ε hε => ?_⟩
  obtain ⟨-, hu, -⟩ := hQ19 ε hε
  have hu' : StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
      2 * (4 / ℓ₀) ^ ((2 * s - 1) / 4) * R * ε ^ ((2 * s + 3) / 4) := by
    refine hu.trans (le_of_eq ?_)
    exact alg_c hε.1 hℓ
  refine ⟨hu', fun htv => ?_⟩
  calc StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε)
      ≤ (1 - StatFormal.Distances.tvDist P Q)⁻¹ * StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) :=
        Dpop_le_uPath_div φ P Q htv hε.1.le
    _ ≤ (1 - StatFormal.Distances.tvDist P Q)⁻¹ * (2 * (4 / ℓ₀) ^ ((2 * s - 1) / 4) * R * ε ^ ((2 * s + 3) / 4)) :=
        mul_le_mul_of_nonneg_left hu' (inv_nonneg.mpr (by linarith))
    _ = 2 * (4 / ℓ₀) ^ ((2 * s - 1) / 4) * R * (1 - StatFormal.Distances.tvDist P Q)⁻¹ * ε ^ ((2 * s + 3) / 4) := by ring

end StatFormal.Wave31tq.RouteT
