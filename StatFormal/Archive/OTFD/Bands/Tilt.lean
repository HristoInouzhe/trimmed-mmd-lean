import StatFormal.Archive.OTFD.Bands.Statements
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Helper lemmas for `lem:ext-solver-error`: exponential tilts move averages by at most `tanh`
-/

noncomputable section
open Finset

namespace StatFormal.OTFD.Bands

lemma tanh_formula (y : ℝ) :
    Real.tanh y = (Real.exp (2 * y) - 1) / (Real.exp (2 * y) + 1) := by
  rw [Real.tanh_eq]
  have h1 : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  have hp := Real.exp_pos y
  rw [h1, h2]
  field_simp

lemma tanh_nonneg' {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.tanh y := by
  rw [tanh_formula]
  have : 1 ≤ Real.exp (2 * y) := Real.one_le_exp (by linarith)
  exact div_nonneg (by linarith) (by positivity)

lemma abs_tanh (y : ℝ) : |Real.tanh y| = Real.tanh |y| := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (tanh_nonneg' h)]
  · have := tanh_nonneg' (by linarith : 0 ≤ -y)
    rw [Real.tanh_neg] at this
    rw [abs_of_neg h, Real.tanh_neg, abs_of_nonpos (by linarith)]

lemma alg_ineq {α R : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (hR : 1 ≤ R) :
    α - α / (α + R * (1 - α)) ≤ (√R - 1) / (√R + 1) := by
  have hs1 : 1 ≤ √R := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hR
  have hR' : R = √R ^ 2 := (Real.sq_sqrt (by linarith)).symm
  set s := √R
  rw [hR']
  have hden : 0 < α + s ^ 2 * (1 - α) := by nlinarith
  rw [sub_le_iff_le_add, div_add_div _ _ (by linarith) hden.ne',
    le_div_iff₀ (mul_pos (by linarith) hden)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (α - (1 - α) * s))]

variable {n : ℕ}

/-- One-sided tilt bound for a function with values in `[0, L]`. -/
lemma tilt_L [Nonempty (Fin n)] (a t ψ : Fin n → ℝ) (t0 R L : ℝ) (ha : ∀ i, 0 < a i)
    (ht0 : 0 < t0) (ht : ∀ i, t0 ≤ t i ∧ t i ≤ t0 * R) (hψ : ∀ i, 0 ≤ ψ i ∧ ψ i ≤ L) :
    (∑ i, a i * ψ i) / (∑ i, a i) - (∑ i, a i * t i * ψ i) / (∑ i, a i * t i) ≤
      (√R - 1) / (√R + 1) * L := by
  obtain ⟨i0⟩ := ‹Nonempty (Fin n)›
  have hR : 1 ≤ R := by
    have h := (ht i0).1.trans (ht i0).2
    by_contra hc
    push Not at hc
    nlinarith
  have hL : 0 ≤ L := (hψ i0).1.trans (hψ i0).2
  have htpos : ∀ i, 0 < t i := fun i => ht0.trans_le (ht i).1
  set P := ∑ i, a i
  set X := ∑ i, a i * ψ i
  set Pt := ∑ i, a i * t i
  set Y := ∑ i, a i * t i * ψ i
  set B := ∑ i, a i * t i * (L - ψ i)
  have hP : 0 < P := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hPt : 0 < Pt := Finset.sum_pos (fun i _ => mul_pos (ha i) (htpos i)) Finset.univ_nonempty
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (hψ i).1
  have hXP : X ≤ L * P := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [ha i, hψ i]
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (ha i).le (htpos i).le) (hψ i).1
  have hY : t0 * X ≤ Y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (ht i).1 (mul_nonneg (ha i).le (hψ i).1)
    nlinarith
  have hB : B ≤ t0 * R * (L * P - X) := by
    have : t0 * R * (L * P - X) = ∑ i, t0 * R * (L * a i - a i * ψ i) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [this]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (ht i).2
      (mul_nonneg (ha i).le (sub_nonneg.mpr (hψ i).2))
    nlinarith
  have hPtYB : L * Pt = Y + B := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rcases hL.lt_or_eq with hLpos | hL0
  · set α := X / (L * P) with hα
    have hLP : 0 < L * P := mul_pos hLpos hP
    have hαP : α * (L * P) = X := div_mul_cancel₀ X hLP.ne'
    have hα0 : 0 ≤ α := div_nonneg hX0 hLP.le
    have hα1 : α ≤ 1 := (div_le_one hLP).mpr hXP
    have halg := alg_ineq hα0 hα1 hR
    have hden : 0 < α + R * (1 - α) := by nlinarith
    have hkey : α / (α + R * (1 - α)) ≤ Y / (L * Pt) := by
      rw [div_le_div_iff₀ hden (mul_pos hLpos hPt), hPtYB]
      have k1 : α * B ≤ α * (t0 * R * (L * P - X)) := mul_le_mul_of_nonneg_left hB hα0
      have k2 : t0 * X * (R * (1 - α)) ≤ Y * (R * (1 - α)) :=
        mul_le_mul_of_nonneg_right hY (by nlinarith)
      have k3 : α * (t0 * R * (L * P - X)) = t0 * X * (R * (1 - α)) := by
        rw [← hαP]; ring
      nlinarith
    have e1 : X / P = L * α := by
      rw [hα]; field_simp
    have e2 : Y / Pt = L * (Y / (L * Pt)) := by
      field_simp
    rw [e1, e2]
    nlinarith
  · subst hL0
    have hψ0 : ∀ i, ψ i = 0 := fun i => le_antisymm (hψ i).2 (hψ i).1
    simp [X, Y, hψ0]

lemma shift_avg (a z : Fin n → ℝ) (c : ℝ) (hP : (∑ i, a i) ≠ 0) :
    (∑ i, a i * (z i - c)) / (∑ i, a i) = (∑ i, a i * z i) / (∑ i, a i) - c := by
  have : ∑ i, a i * (z i - c) = ∑ i, a i * z i - c * ∑ i, a i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  field_simp

lemma shift_avg' (a z : Fin n → ℝ) (c : ℝ) (hP : (∑ i, a i) ≠ 0) :
    (∑ i, a i * (c - z i)) / (∑ i, a i) = c - (∑ i, a i * z i) / (∑ i, a i) := by
  have : ∑ i, a i * (c - z i) = c * ∑ i, a i - ∑ i, a i * z i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  field_simp

/-- Two-sided tilt bound: an exponential tilt with likelihood ratios in `[t0, t0 R]` moves the
average of a function with range in `[lo, hi]` by at most `tanh(log R / 4) (hi − lo)`. -/
lemma tilt_bound [Nonempty (Fin n)] (a t z : Fin n → ℝ) (t0 R lo hi : ℝ) (ha : ∀ i, 0 < a i)
    (ht0 : 0 < t0) (ht : ∀ i, t0 ≤ t i ∧ t i ≤ t0 * R) (hz : ∀ i, lo ≤ z i ∧ z i ≤ hi) :
    |(∑ i, a i * z i) / (∑ i, a i) - (∑ i, a i * t i * z i) / (∑ i, a i * t i)| ≤
      (√R - 1) / (√R + 1) * (hi - lo) := by
  have htpos : ∀ i, 0 < t i := fun i => ht0.trans_le (ht i).1
  have hP : (∑ i, a i) ≠ 0 :=
    (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty).ne'
  have hPt : (∑ i, a i * t i) ≠ 0 :=
    (Finset.sum_pos (fun i _ => mul_pos (ha i) (htpos i)) Finset.univ_nonempty).ne'
  have h1 := tilt_L a t (fun i => z i - lo) t0 R (hi - lo) ha ht0 ht
    (fun i => ⟨by linarith [(hz i).1], by linarith [(hz i).2]⟩)
  have h2 := tilt_L a t (fun i => hi - z i) t0 R (hi - lo) ha ht0 ht
    (fun i => ⟨by linarith [(hz i).2], by linarith [(hz i).1]⟩)
  rw [shift_avg a z lo hP, shift_avg (fun i => a i * t i) z lo hPt] at h1
  rw [shift_avg' a z hi hP, shift_avg' (fun i => a i * t i) z hi hPt] at h2
  rw [abs_le]
  constructor <;> linarith

end StatFormal.OTFD.Bands
