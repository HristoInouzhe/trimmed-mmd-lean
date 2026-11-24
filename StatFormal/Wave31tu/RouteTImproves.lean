import StatFormal.Wave31tu.Statements
import StatFormal.Lib.LaplaceRate.Improves

/-!
# Wave 31tu route T: Y19 (c) `laplace_rate_improves` (§5 :240-243; untrusted proof material)

(c1) With `k = 1 + log(1/η)/log 10` and `B = v_min^{−2}{L_δ^{1/2} + (log(2J/η))^{1/2}}`, `L_{n,m} ≤ k·log(n∨m)` for `n∨m ≥ 10`
(`LaplaceRate.log_div_le_mul_log`) and `log(n∨m) ≥ 1`, so both bounds are at most `C(k + B)` times the printed power of `log(n∨m)`
(`log_bound_i`, `log_bound_ii`).
(c2) For `C ≤ 0` both sides are trivially ordered. For `C > 0`, `n∨m ≤ (n∧m)^k` gives `L_{n,m} ≤ (90k + log(1/η))(n∧m)^{1/90}`
(`log_div_le_rpow`), and `n∧m ≥ (C(A + 1 + B)/ε)^{27}` gives both bounds `≤ ε(n∧m)^{−2/5}` (`small_i`, `small_ii`).
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.Wave31tu.RouteT

open StatFormal.LaplaceRate

/-- **Y19 (c)**, §5 :240-243: the bounds of Theorem 5.11 are `(n∧m)^{−1/2}` (resp. `(n∧m)^{−4/9}`) up to a power of `log(n∨m)`, and
`o((n∧m)^{−2/5})` for comparable sizes. -/
theorem laplace_rate_improves_route : Claims.laplace_rate_improves := by
  refine ⟨?_, ?_⟩
  · intro C δ s2 η J hC hδ0 hδ1 hs2 hη0 hη1 hJ
    have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
    have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    set k := 1 + Real.log (1 / η) / Real.log 10 with hkdef
    set B := s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) with hBdef
    have hk : 1 ≤ k := by
      have : 0 ≤ Real.log (1 / η) / Real.log 10 := div_nonneg he hl10.le
      linarith
    have hB : 0 ≤ B := by positivity
    refine ⟨C * (k + B), by positivity, fun n m hnm => ?_⟩
    have hN10 : (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast hnm
    have hMN : ((min n m : ℕ) : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast min_le_max
    have hlM : 1 ≤ Real.log ((max n m : ℕ) : ℝ) := one_le_log_of_ten_le (by linarith)
    have hL : Real.log (((max n m : ℕ) : ℝ) / η) ≤ k * Real.log ((max n m : ℕ) : ℝ) :=
      log_div_le_mul_log (by norm_num) (by linarith) hη0 hη1.le
    have hL0 : 0 ≤ Real.log (((max n m : ℕ) : ℝ) / η) :=
      Real.log_nonneg (by rw [le_div_iff₀ hη0]; nlinarith)
    exact ⟨log_bound_i hC.le hk hB hL0 hL hlM (by linarith), log_bound_ii hC.le hk hB hL0 hL hlM (by linarith)⟩
  · intro k C δ s2 η J hk hδ0 hδ1 hs2 hη0 hη1 hJ ε hε
    have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
    set B := s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) with hBdef
    have hB : 0 ≤ B := by positivity
    by_cases hC : C ≤ 0
    · refine ⟨1, fun n m hnm _ => ?_⟩
      have hN1 : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast hnm
      have hMN : ((min n m : ℕ) : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast min_le_max
      have hL0 : 0 ≤ Real.log (((max n m : ℕ) : ℝ) / η) :=
        Real.log_nonneg (by rw [le_div_iff₀ hη0]; nlinarith)
      have hR : 0 ≤ ε * ((min n m : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) := by positivity
      have h1 : 0 ≤ Real.log (((max n m : ℕ) : ℝ) / η) ^ (3 / 4 : ℝ) / √((min n m : ℕ) : ℝ) + B / √((min n m : ℕ) : ℝ) := by
        positivity
      have h2 : 0 ≤ Real.log (((max n m : ℕ) : ℝ) / η) ^ (2 / 3 : ℝ) * ((min n m : ℕ) : ℝ) ^ (-(4 / 9 : ℝ)) +
          B / √((min n m : ℕ) : ℝ) := by positivity
      exact ⟨by nlinarith, by nlinarith⟩
    · replace hC : 0 < C := not_le.mp hC
      set A := 90 * k + Real.log (1 / η) with hAdef
      have hA : 0 ≤ A := by positivity
      set T := C * (A + 1 + B) / ε with hTdef
      have hT0 : 0 ≤ T := by positivity
      refine ⟨⌈T ^ (27 : ℝ)⌉₊ + 1, fun n m hnm hsize => ?_⟩
      have hN1 : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 _).trans hnm
      have hNT : T ^ (27 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by
        have h1 : T ^ (27 : ℝ) ≤ (⌈T ^ (27 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈T ^ (27 : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast hnm
        rw [Nat.cast_add, Nat.cast_one] at h2
        linarith
      have hT : T ≤ ((min n m : ℕ) : ℝ) ^ (1 / 27 : ℝ) := const_le_rpow_of_le hT0 hNT
      have hMN : ((min n m : ℕ) : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast min_le_max
      have hL0 : 0 ≤ Real.log (((max n m : ℕ) : ℝ) / η) :=
        Real.log_nonneg (by rw [le_div_iff₀ hη0]; nlinarith)
      have hL : Real.log (((max n m : ℕ) : ℝ) / η) ≤ A * ((min n m : ℕ) : ℝ) ^ (1 / 90 : ℝ) :=
        log_div_le_rpow hN1 (hN1.trans hMN) hsize (by linarith) hη0 hη1.le
      exact ⟨small_i hC hε hA hB hN1 hL0 hL hT, small_ii hC hε hA hB hN1 hL0 hL hT⟩

end StatFormal.Wave31tu.RouteT
