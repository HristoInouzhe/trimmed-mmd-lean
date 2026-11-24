import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The dyadic sum of a mollified Sobolev norm (library, untrusted)

For `s > 1/2`, `m ∈ ℕ` with `4m > 2s − 1`, `0 < w ≤ 1` and `C_b ∈ ℝ`, with `q = 2^{2s−1}`:
`Σ_{j ≥ 0} q^j min{1, C_b² (w 2^j)^{−4m}} ≤ w^{1−2s} [1/(1 − 2^{1−2s}) + C_b²/(1 − 2^{−(4m+1−2s)})]`.

This is the arithmetic of the dyadic shells in the proof of Lemma S4.9 of trimmed-mmd: the sum grows geometrically up to the
frequency `1/w` and decays geometrically beyond it. With `x_j = w 2^j` one has `q^j = w^{1−2s} x_j^{2s−1}`; for the integer
`j₀` with `2^{j₀} ≤ 1/w < 2^{j₀+1}` (`exists_nat_pow_near`), `x_{j₀ − i} ≤ 2^{−i}` gives `x^{2s−1} ≤ (2^{1−2s})^i`, and
`x_{j₀+1+k} ≥ 2^k` gives `x^{2s−1−4m} ≤ (2^{−(4m+1−2s)})^k`; two geometric series finish.
-/

noncomputable section
open Finset

namespace StatFormal.MollifierNorm

/-- The dyadic term rewritten at `x = w 2^j`: `(2^{2s−1})^j = w^{1−2s} (w 2^j)^{2s−1}`. -/
theorem two_rpow_pow_eq {s w : ℝ} (hw0 : 0 < w) (j : ℕ) :
    ((2 : ℝ) ^ (2 * s - 1)) ^ j = w ^ (1 - 2 * s) * (w * 2 ^ j) ^ (2 * s - 1) := by
  rw [Real.rpow_pow_comm zero_le_two, Real.mul_rpow hw0.le (by positivity), ← mul_assoc, ← Real.rpow_add hw0]
  simp

/-- **The dyadic sum**: summability and `Σ_j (2^{2s−1})^j min{1, C_b² ((w 2^j)^{4m})⁻¹} ≤
w^{1−2s}[1/(1 − 2^{1−2s}) + C_b²/(1 − 2^{−(4m+1−2s)})]` for `s > 1/2`, `4m > 2s − 1`, `0 < w ≤ 1`. -/
theorem dyadic_tsum_le {s w Cb : ℝ} {m : ℕ} (hs : 1 / 2 < s) (hm : 2 * s - 1 < 4 * m) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    Summable (fun j : ℕ => ((2 : ℝ) ^ (2 * s - 1)) ^ j * min 1 (Cb ^ 2 * ((w * 2 ^ j) ^ (4 * m))⁻¹)) ∧
    ∑' j : ℕ, ((2 : ℝ) ^ (2 * s - 1)) ^ j * min 1 (Cb ^ 2 * ((w * 2 ^ j) ^ (4 * m))⁻¹) ≤
      w ^ (1 - 2 * s) * (1 / (1 - (2 : ℝ) ^ (1 - 2 * s)) + Cb ^ 2 / (1 - (2 : ℝ) ^ (-(4 * m + 1 - 2 * s)))) := by
  set a : ℕ → ℝ := fun j => ((2 : ℝ) ^ (2 * s - 1)) ^ j * min 1 (Cb ^ 2 * ((w * 2 ^ j) ^ (4 * m))⁻¹) with ha
  set r : ℝ := (2 : ℝ) ^ (1 - 2 * s) with hr
  set y : ℝ := (2 : ℝ) ^ (-(4 * (m : ℝ) + 1 - 2 * s)) with hy
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hW : 0 < w ^ (1 - 2 * s) := Real.rpow_pos_of_pos hw0 _
  have ha0 : ∀ j, 0 ≤ a j := fun j => mul_nonneg (by positivity) (le_min zero_le_one (by positivity))
  obtain ⟨j₀, hj₀, hj₀'⟩ := exists_nat_pow_near (one_le_inv_iff₀.2 ⟨hw0, hw1⟩ : (1 : ℝ) ≤ w⁻¹) one_lt_two
  -- below the frequency `1/w`
  have hlow : ∀ i ∈ range (j₀ + 1), a (j₀ + 1 - 1 - i) ≤ w ^ (1 - 2 * s) * r ^ i := by
    intro i hi
    have hi' : i ≤ j₀ := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hj : j₀ + 1 - 1 - i = j₀ - i := by omega
    rw [hj]
    have hx0 : 0 < w * 2 ^ (j₀ - i) := by positivity
    have key : w * 2 ^ (j₀ - i) * 2 ^ i ≤ 1 := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi']
      calc w * 2 ^ j₀ ≤ w * w⁻¹ := mul_le_mul_of_nonneg_left hj₀ hw0.le
        _ = 1 := mul_inv_cancel₀ hw0.ne'
    have hx : w * 2 ^ (j₀ - i) ≤ ((2 : ℝ) ^ i)⁻¹ := by
      calc w * 2 ^ (j₀ - i) = (w * 2 ^ (j₀ - i) * 2 ^ i) * ((2 : ℝ) ^ i)⁻¹ := by field_simp
        _ ≤ 1 * ((2 : ℝ) ^ i)⁻¹ := by gcongr
        _ = ((2 : ℝ) ^ i)⁻¹ := one_mul _
    have hri : (((2 : ℝ) ^ i)⁻¹) ^ (2 * s - 1) = r ^ i := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), hr, Real.rpow_pow_comm zero_le_two]
      congr 1; ring
    calc a (j₀ - i) ≤ ((2 : ℝ) ^ (2 * s - 1)) ^ (j₀ - i) * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ = w ^ (1 - 2 * s) * (w * 2 ^ (j₀ - i)) ^ (2 * s - 1) := by rw [mul_one, two_rpow_pow_eq hw0]
      _ ≤ w ^ (1 - 2 * s) * r ^ i := by
          rw [← hri]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le hx (by linarith)) hW.le
  -- beyond the frequency `1/w`
  have hw2 : 1 ≤ w * 2 ^ (j₀ + 1) := by
    calc (1 : ℝ) = w * w⁻¹ := (mul_inv_cancel₀ hw0.ne').symm
      _ ≤ w * 2 ^ (j₀ + 1) := mul_le_mul_of_nonneg_left hj₀'.le hw0.le
  have hhigh : ∀ k, a (k + (j₀ + 1)) ≤ w ^ (1 - 2 * s) * Cb ^ 2 * y ^ k := by
    intro k
    have hx0 : 0 < w * 2 ^ (k + (j₀ + 1)) := by positivity
    have hx : (2 : ℝ) ^ k ≤ w * 2 ^ (k + (j₀ + 1)) := by
      calc (2 : ℝ) ^ k = 2 ^ k * 1 := (mul_one _).symm
        _ ≤ 2 ^ k * (w * 2 ^ (j₀ + 1)) := by gcongr
        _ = w * 2 ^ (k + (j₀ + 1)) := by rw [pow_add]; ring
    have hxpow : ((w * 2 ^ (k + (j₀ + 1))) ^ (4 * m))⁻¹ = (w * 2 ^ (k + (j₀ + 1))) ^ (-(4 * (m : ℝ))) := by
      rw [Real.rpow_neg hx0.le, ← Real.rpow_natCast]; push_cast; ring_nf
    have hyk : ((2 : ℝ) ^ k) ^ (2 * s - 1 - 4 * m) = y ^ k := by
      rw [hy, Real.rpow_pow_comm zero_le_two]; congr 1; ring
    calc a (k + (j₀ + 1)) ≤ ((2 : ℝ) ^ (2 * s - 1)) ^ (k + (j₀ + 1)) *
          (Cb ^ 2 * ((w * 2 ^ (k + (j₀ + 1))) ^ (4 * m))⁻¹) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = w ^ (1 - 2 * s) * Cb ^ 2 * ((w * 2 ^ (k + (j₀ + 1))) ^ (2 * s - 1) *
            (w * 2 ^ (k + (j₀ + 1))) ^ (-(4 * (m : ℝ)))) := by
          rw [two_rpow_pow_eq hw0, hxpow]; ring
      _ = w ^ (1 - 2 * s) * Cb ^ 2 * (w * 2 ^ (k + (j₀ + 1))) ^ (2 * s - 1 - 4 * m) := by
          rw [← Real.rpow_add hx0]; ring_nf
      _ ≤ w ^ (1 - 2 * s) * Cb ^ 2 * ((2 : ℝ) ^ k) ^ (2 * s - 1 - 4 * m) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith)) (by positivity)
      _ = w ^ (1 - 2 * s) * Cb ^ 2 * y ^ k := by rw [hyk]
  have hgeo_y : Summable (fun k : ℕ => w ^ (1 - 2 * s) * Cb ^ 2 * y ^ k) :=
    (summable_geometric_of_lt_one hy0.le hy1).mul_left _
  have hsumm_tail : Summable (fun k => a (k + (j₀ + 1))) :=
    Summable.of_nonneg_of_le (fun k => ha0 _) hhigh hgeo_y
  have hsumm : Summable a := (summable_nat_add_iff (j₀ + 1)).1 hsumm_tail
  refine ⟨hsumm, ?_⟩
  rw [← hsumm.sum_add_tsum_nat_add (j₀ + 1)]
  have h1 : ∑ i ∈ range (j₀ + 1), a i ≤ w ^ (1 - 2 * s) * (1 / (1 - r)) := by
    rw [← sum_range_reflect a (j₀ + 1)]
    calc ∑ i ∈ range (j₀ + 1), a (j₀ + 1 - 1 - i) ≤ ∑ i ∈ range (j₀ + 1), w ^ (1 - 2 * s) * r ^ i :=
          sum_le_sum hlow
      _ = w ^ (1 - 2 * s) * ∑ i ∈ range (j₀ + 1), r ^ i := (mul_sum _ _ _).symm
      _ ≤ w ^ (1 - 2 * s) * ∑' i, r ^ i := by
          gcongr
          exact (summable_geometric_of_lt_one hr0.le hr1).sum_le_tsum _ (fun i _ => by positivity)
      _ = w ^ (1 - 2 * s) * (1 / (1 - r)) := by rw [tsum_geometric_of_lt_one hr0.le hr1, one_div]
  have h2 : ∑' k, a (k + (j₀ + 1)) ≤ w ^ (1 - 2 * s) * (Cb ^ 2 / (1 - y)) := by
    calc ∑' k, a (k + (j₀ + 1)) ≤ ∑' k, w ^ (1 - 2 * s) * Cb ^ 2 * y ^ k :=
          hsumm_tail.tsum_le_tsum hhigh hgeo_y
      _ = w ^ (1 - 2 * s) * (Cb ^ 2 / (1 - y)) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hy0.le hy1]; ring
  calc (∑ i ∈ range (j₀ + 1), a i) + ∑' k, a (k + (j₀ + 1))
      ≤ w ^ (1 - 2 * s) * (1 / (1 - r)) + w ^ (1 - 2 * s) * (Cb ^ 2 / (1 - y)) := add_le_add h1 h2
    _ = _ := by ring

end StatFormal.MollifierNorm
