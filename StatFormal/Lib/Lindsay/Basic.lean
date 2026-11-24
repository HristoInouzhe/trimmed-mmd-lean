import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Lindsay's lemma: elementary real analysis on finitely many logarithms

* `log_avg_le`: Jensen for the concave logarithm on a finite average,
  `n⁻¹ Σ log r_i ≤ log(n⁻¹ Σ r_i)`.
* `foc_of_log_le`: the first-order condition. If `b_i > 0`, `a_i > 0` and
  `Σ log((1 − t) b_i + t a_i) ≤ Σ log b_i` for every `t ∈ (0, 1]`, then `Σ a_i / b_i ≤ n`.
-/

noncomputable section
open Filter Topology Set

namespace StatFormal.Foundations.Lindsay

variable {n : ℕ}

/-- Jensen for the logarithm on a finite average, in the elementary form. -/
lemma log_avg_le (hn : 0 < n) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (1 / n : ℝ) * ∑ i, Real.log (r i) ≤ Real.log ((1 / n : ℝ) * ∑ i, r i) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set T := (1 / n : ℝ) * ∑ i, r i with hT
  have hTpos : 0 < T := by
    have : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    positivity
  have hpt : ∀ i, Real.log (r i) ≤ Real.log T + (r i / T - 1) := fun i => by
    have h := Real.log_le_sub_one_of_pos (div_pos (hr i) hTpos)
    rw [Real.log_div (hr i).ne' hTpos.ne'] at h
    linarith
  calc (1 / n : ℝ) * ∑ i, Real.log (r i) ≤ (1 / n : ℝ) * ∑ i, (Real.log T + (r i / T - 1)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpt i) (by positivity)
    _ = Real.log T + (T / T - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← Finset.sum_div, hT]
        field_simp
    _ = Real.log T := by rw [div_self hTpos.ne']; ring

/-- The first-order condition for finitely many logarithms along a segment. -/
lemma foc_of_log_le (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hseg : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∑ i, Real.log ((1 - t) * b i + t * a i) ≤ ∑ i, Real.log (b i)) :
    ∑ i, a i / b i ≤ n := by
  set c : Fin n → ℝ := fun i => a i / b i - 1
  have hc : ∀ i, -1 < c i := fun i => by
    have := div_pos (ha i) (hb i); simp only [c]; linarith
  have hseg' : ∀ t : ℝ, 0 < t → t ≤ 1 → ∑ i, c i / (1 + t * c i) ≤ 0 := by
    intro t ht0 ht1
    have hpos : ∀ i, 0 < 1 + t * c i := fun i => by
      rcases le_total 0 (c i) with h | h
      · nlinarith
      · nlinarith [hc i]
    have hfac : ∀ i, (1 - t) * b i + t * a i = b i * (1 + t * c i) := fun i => by
      simp only [c]; field_simp [(hb i).ne']; ring
    have hle := hseg t ht0 ht1
    simp_rw [hfac, Real.log_mul (hb _).ne' (hpos _).ne', Finset.sum_add_distrib] at hle
    have hlog : ∑ i, Real.log (1 + t * c i) ≤ 0 := by linarith
    have hlow : ∀ i, t * (c i / (1 + t * c i)) ≤ Real.log (1 + t * c i) := fun i => by
      have h := Real.one_sub_inv_le_log_of_pos (hpos i)
      have : 1 - (1 + t * c i)⁻¹ = t * (c i / (1 + t * c i)) := by
        field_simp [(hpos i).ne']; ring
      linarith
    have : t * ∑ i, c i / (1 + t * c i) ≤ 0 := by
      rw [Finset.mul_sum]; exact (Finset.sum_le_sum fun i _ => hlow i).trans hlog
    by_contra h
    push Not at h
    have := mul_pos ht0 h
    linarith
  have hcont : Tendsto (fun t : ℝ => ∑ i, c i / (1 + t * c i)) (𝓝[>] 0) (𝓝 (∑ i, c i)) := by
    have : Tendsto (fun t : ℝ => ∑ i, c i / (1 + t * c i)) (𝓝 0)
        (𝓝 (∑ i, c i / (1 + 0 * c i))) := by
      apply tendsto_finsetSum
      intro i _
      exact tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds))
        (by simp)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ i, c i / (1 + t * c i) ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    exact hseg' t ht.1 ht.2.le
  have hsum : ∑ i, c i ≤ 0 := le_of_tendsto hcont hev
  simp only [c, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hsum
  linarith

end StatFormal.Foundations.Lindsay
