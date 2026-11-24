import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Real powers for polynomial margins (library, untrusted)

* `rpow_le_iff_le_rpow_one_div`: for `e, x ≥ 0`, `γ > 0`: `e^γ ≤ x ↔ e ≤ x^{1/γ}`;
* `sSup_rpow_sublevel`: the generalized inverse of `ε ↦ cε^γ` on `[0, a]`:
  `sup{ε ∈ [0,a] : cε^γ ≤ t} = min{a, (t/c)^{1/γ}}` for `c, γ > 0`, `a, t ≥ 0`;
* `rpow_one_div_div_mul`: `(t/(sc))^{1/γ} = s^{−1/γ}(t/c)^{1/γ}` for `s > 0`, `c > 0`, `t ≥ 0`.
-/

set_option linter.style.longLine false

noncomputable section
open Set

namespace StatFormal.TVFacts

/-- For `e, x ≥ 0` and `γ > 0`: `e^γ ≤ x ↔ e ≤ x^{1/γ}`. -/
theorem rpow_le_iff_le_rpow_one_div {e x γ : ℝ} (he : 0 ≤ e) (hx : 0 ≤ x) (hγ : 0 < γ) :
    e ^ γ ≤ x ↔ e ≤ x ^ (1 / γ) := by
  rw [one_div, Real.le_rpow_inv_iff_of_pos he hx hγ]

/-- **Generalized inverse of a power margin.** For `c > 0`, `γ > 0`, `a ≥ 0` and `t ≥ 0`:
`sup{ε ∈ [0,a] : cε^γ ≤ t} = min{a, (t/c)^{1/γ}}` (the sublevel set is the interval `[0, min{a, (t/c)^{1/γ}}]`). -/
theorem sSup_rpow_sublevel {c γ a t : ℝ} (hc : 0 < c) (hγ : 0 < γ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    sSup {e | e ∈ Icc (0 : ℝ) a ∧ c * e ^ γ ≤ t} = min a ((t / c) ^ (1 / γ)) := by
  have htc : 0 ≤ t / c := div_nonneg ht hc.le
  have hset : {e | e ∈ Icc (0 : ℝ) a ∧ c * e ^ γ ≤ t} = Icc 0 (min a ((t / c) ^ (1 / γ))) := by
    ext e
    simp only [Set.mem_ofPred_eq, mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨he0, hea⟩, hle⟩
      refine ⟨he0, hea, ?_⟩
      rw [← rpow_le_iff_le_rpow_one_div he0 htc hγ, le_div_iff₀ hc]
      linarith [mul_comm c (e ^ γ)]
    · rintro ⟨he0, hea, hle⟩
      refine ⟨⟨he0, hea⟩, ?_⟩
      rw [← rpow_le_iff_le_rpow_one_div he0 htc hγ, le_div_iff₀ hc] at hle
      linarith [mul_comm c (e ^ γ)]
  rw [hset, csSup_Icc (le_min ha (Real.rpow_nonneg htc _))]

/-- `(t/(sc))^{1/γ} = s^{−1/γ}(t/c)^{1/γ}` for `s > 0`, `c > 0`, `t ≥ 0`. -/
theorem rpow_one_div_div_mul {s c t γ : ℝ} (hs : 0 < s) (hc : 0 < c) (ht : 0 ≤ t) :
    (t / (s * c)) ^ (1 / γ) = s ^ (-1 / γ) * (t / c) ^ (1 / γ) := by
  have e1 : t / (s * c) = s⁻¹ * (t / c) := by field_simp
  rw [e1, Real.mul_rpow (inv_nonneg.2 hs.le) (div_nonneg ht hc.le), Real.inv_rpow hs.le, neg_div,
    Real.rpow_neg hs.le]

end StatFormal.TVFacts
