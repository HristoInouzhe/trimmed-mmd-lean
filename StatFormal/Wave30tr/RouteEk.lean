import StatFormal.Wave30tr.Statements
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

/-!
# Route: the constants e_k (untrusted proof material)

`ek_closed`: sign vectors `σ : Fin k → Bool` correspond to subsets (the `true` coordinates), and
`∑ᵢ σᵢ = 2r − k` with `r` the subset size, so `∑_σ |∑ᵢ σᵢ| = ∑_r C(k,r) |2r − k|`
(`Finset.sum_powerset_apply_card`). The telescoping identity
`∑_{r ≤ m} (k+1−2r) C(k+1,r) = (k+1) C(k,m)` (Pascal and `C(k,m+1)(m+1) = C(k,m)(k−m)`),
at `m = k/2` and `m = k+1`, gives `∑_r C(k+1,r)|k+1−2r| = 2(k+1) C(k, k/2)`.

`ek_tendsto`: by `ek_closed`, `e_{2j+1} = e_{2j} = C(2j,j)/4^j` (`j ≥ 1`), and Wallis' product in
factorial form (`Real.Wallis.W_eq_factorial_ratio`) gives `(C(2j,j)/4^j)² (2j+1) = 1/W_j → 2/π`
(`Real.Wallis.tendsto_W_nhds_pi_div_two`); the odd and even subsequences are combined at the end.
-/

noncomputable section
open Finset Filter Real
open scoped Nat Topology

namespace StatFormal.Wave30tr

/-! ### The closed form -/

/-- Telescoping: `∑_{r ≤ m} (k+1−2r) C(k+1,r) = (k+1) C(k,m)`. -/
theorem ek_tele (k m : ℕ) :
    ∑ r ∈ range (m + 1), (((k : ℝ) + 1) - 2 * r) * ((k + 1).choose r : ℝ) =
      ((k : ℝ) + 1) * (k.choose m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ((k + 1).choose (m + 1) : ℝ) = (k.choose m : ℝ) + (k.choose (m + 1) : ℝ) := by
      rw [Nat.choose_succ_succ']; push_cast; ring
    have h2 : ((k : ℝ) - m) * (k.choose m : ℝ) = ((m : ℝ) + 1) * (k.choose (m + 1) : ℝ) := by
      rcases le_or_gt m k with hmk | hmk
      · have h := Nat.choose_succ_right_eq k m
        have h' : ((k.choose (m + 1) * (m + 1) : ℕ) : ℝ) = ((k.choose m * (k - m) : ℕ) : ℝ) := by
          rw [h]
        push_cast [hmk] at h'
        linarith
      · rw [Nat.choose_eq_zero_of_lt hmk, Nat.choose_eq_zero_of_lt (by omega)]
        simp
    push_cast
    linear_combination (((k : ℝ) + 1) - 2 * ((m : ℝ) + 1)) * h1 + 2 * h2

/-- `∑_r C(k+1,r) |k+1−2r| = 2(k+1) C(k, k/2)`. -/
theorem ek_abs_sum (k : ℕ) :
    ∑ r ∈ range (k + 2), |((k : ℝ) + 1) - 2 * r| * ((k + 1).choose r : ℝ) =
      2 * ((k : ℝ) + 1) * (k.choose (k / 2) : ℝ) := by
  have hfull := ek_tele k (k + 1)
  rw [Nat.choose_succ_self, Nat.cast_zero, mul_zero] at hfull
  have hhalf := ek_tele k (k / 2)
  have hle : k / 2 + 1 ≤ k + 2 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hle] at hfull ⊢
  have hA : ∑ r ∈ range (k / 2 + 1), |((k : ℝ) + 1) - 2 * r| * ((k + 1).choose r : ℝ) =
      ∑ r ∈ range (k / 2 + 1), (((k : ℝ) + 1) - 2 * r) * ((k + 1).choose r : ℝ) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    have : (2 * (r : ℝ)) ≤ (k : ℝ) + 1 := by exact_mod_cast (show 2 * r ≤ k + 1 by omega)
    rw [abs_of_nonneg (by linarith)]
  have hB : ∑ r ∈ Ico (k / 2 + 1) (k + 2), |((k : ℝ) + 1) - 2 * r| * ((k + 1).choose r : ℝ) =
      -∑ r ∈ Ico (k / 2 + 1) (k + 2), (((k : ℝ) + 1) - 2 * r) * ((k + 1).choose r : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_Ico] at hr
    have : (k : ℝ) + 1 ≤ 2 * (r : ℝ) := by exact_mod_cast (show k + 1 ≤ 2 * r by omega)
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [hA, hB]
  linarith

/-- Sign vectors are subsets: `σ ↦ {i | σ i}`. -/
def boolFunEquivFinset (k : ℕ) : (Fin k → Bool) ≃ Finset (Fin k) where
  toFun σ := univ.filter fun i => σ i = true
  invFun s i := decide (i ∈ s)
  left_inv σ := by funext i; simp
  right_inv s := by ext i; simp

theorem sum_sign_eq (k : ℕ) (σ : Fin k → Bool) :
    ∑ i, (if σ i then (1 : ℝ) else -1) = 2 * ((boolFunEquivFinset k σ).card : ℝ) - k := by
  have h : ∀ i, (if σ i then (1 : ℝ) else -1) = 2 * (if σ i = true then 1 else 0) - 1 := by
    intro i; cases σ i <;> norm_num
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp [boolFunEquivFinset]

theorem sum_abs_sign_eq (k : ℕ) :
    ∑ σ : Fin k → Bool, |∑ i, (if σ i then (1 : ℝ) else -1)| =
      ∑ r ∈ range (k + 1), (k.choose r : ℝ) * |2 * (r : ℝ) - k| := by
  simp_rw [sum_sign_eq]
  rw [Fintype.sum_equiv (boolFunEquivFinset k) _ (fun s => |2 * ((s.card : ℕ) : ℝ) - k|)
    (fun _ => rfl)]
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun n : ℕ => |2 * (n : ℝ) - k|)]
  simp [nsmul_eq_mul]

theorem ek_closed : Claims.ek_closed := by
  intro K hK
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  unfold ek
  rw [sum_abs_sign_eq]
  have hs : ∑ r ∈ range (k + 1 + 1), ((k + 1).choose r : ℝ) * |2 * (r : ℝ) - ((k + 1 : ℕ) : ℝ)| =
      2 * ((k : ℝ) + 1) * (k.choose (k / 2) : ℝ) := by
    rw [← ek_abs_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    push_cast
    rw [abs_sub_comm]
    ring
  rw [hs, Nat.add_sub_cancel, zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast]
  push_cast
  field_simp

/-! ### The limit -/

theorem ek_odd (j : ℕ) : ek (2 * j + 1) = ((2 * j).choose j : ℝ) / 4 ^ j := by
  rw [ek_closed (2 * j + 1) (by omega), show 2 * j + 1 - 1 = 2 * j by omega,
    show 2 * j / 2 = j by omega, zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast,
    show (4 : ℝ) ^ j = 2 ^ (2 * j) by rw [pow_mul]; norm_num, pow_succ]
  field_simp

theorem ek_even (j : ℕ) (hj : 1 ≤ j) : ek (2 * j) = ((2 * j).choose j : ℝ) / 4 ^ j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hc : (2 * (i + 1)).choose (i + 1) = 2 * (2 * i + 1).choose i := by
    rw [show 2 * (i + 1) = (2 * i + 1) + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
    ring
  rw [ek_closed _ (by omega), hc, show 2 * (i + 1) - 1 = 2 * i + 1 by omega,
    show (2 * i + 1) / 2 = i by omega, zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast,
    show (4 : ℝ) ^ (i + 1) = 2 ^ (2 * i + 1 + 1) by
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, pow_mul]; norm_num,
    show 2 * (i + 1) = 2 * i + 1 + 1 by ring, pow_succ]
  push_cast
  field_simp

/-- `(C(2j,j)/4^j)² (2j+1) = 1/W_j` (Wallis' product in factorial form). -/
theorem cen_sq_mul (j : ℕ) :
    (((2 * j).choose j : ℝ) / 4 ^ j) ^ 2 * (2 * j + 1) = (Real.Wallis.W j)⁻¹ := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
  rw [show 2 * j - j = j by omega] at h
  have h' : ((2 * j).choose j : ℝ) * (j ! : ℝ) * (j ! : ℝ) = ((2 * j)! : ℝ) := by exact_mod_cast h
  have hC : ((2 * j).choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hf : (j ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h4 : (2 : ℝ) ^ (4 * j) = ((4 : ℝ) ^ j) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  rw [← h', h4]
  field_simp

theorem ek_odd_mul (j : ℕ) :
    ek (2 * j + 1) * √((2 * j + 1 : ℕ) : ℝ) = √((Real.Wallis.W j)⁻¹) := by
  rw [← cen_sq_mul, ek_odd, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  push_cast
  ring

theorem ek_even_mul (j : ℕ) (hj : 1 ≤ j) :
    ek (2 * j) * √((2 * j : ℕ) : ℝ) = √(2 * ((j : ℝ) / (2 * j + 1)) / Real.Wallis.W j) := by
  have e : 2 * ((j : ℝ) / (2 * j + 1)) / Real.Wallis.W j =
      (((2 * j).choose j : ℝ) / 4 ^ j) ^ 2 * (2 * j) := by
    rw [div_eq_mul_inv _ (Real.Wallis.W j), ← cen_sq_mul]
    field_simp
  rw [e, ek_even j hj, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  push_cast
  ring

/-- A real sequence whose even and odd subsequences tend to `L` tends to `L`. -/
theorem tendsto_of_even_odd {f : ℕ → ℝ} {L : ℝ} (h0 : Tendsto (fun j => f (2 * j)) atTop (𝓝 L))
    (h1 : Tendsto (fun j => f (2 * j + 1)) atTop (𝓝 L)) : Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at h0 h1 ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := h0 ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  refine ⟨2 * (N0 + N1), fun n hn => ?_⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hN0 j (by omega)
  · exact hN1 j (by omega)

theorem ek_tendsto : Claims.ek_tendsto := by
  have hW := Real.Wallis.tendsto_W_nhds_pi_div_two
  have hpi : π / 2 ≠ 0 := by positivity
  apply tendsto_of_even_odd
  · have h := ((Stirling.tendsto_self_div_two_mul_self_add_one.const_mul 2).div hW hpi).sqrt
    have e : 2 * (1 / 2) / (π / 2) = 2 / π := by field_simp
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (ek_even_mul j hj).symm
  · have h := (hW.inv₀ hpi).sqrt
    rw [inv_div] at h
    exact h.congr fun j => (ek_odd_mul j).symm

end StatFormal.Wave30tr
