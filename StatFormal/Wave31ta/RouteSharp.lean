import StatFormal.Wave31ta.Statements
import StatFormal.Wave30ts.Proofs
import StatFormal.Lib.Bernstein.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Route: the sharper threshold is no larger than the closed form; the coupled counterexample; the sample-size rule

Untrusted proof material for `Claims.pinelis_h_form`, `Claims.sharp_le_plugin`, `Claims.sharp_cpl_counterexample`,
`Claims.samplesize`.

* `τ^{P'} ≤ τ^P`: at `α = 0` the closed form is admissible (McDiarmid's term equals `δ`); at `α > 0` the split `1/2` gives
  `t₁(δ/2) ≤ T₁` (three McDiarmid terms `≤ δ/6`) and `t₂(δ/2) ≤ T₂` (three Chernoff bounds with the two-point MGF, bounded by
  Bernstein's pointwise inequality and evaluated at the sub-gamma choice of `λ`, each `≤ δ/6`).
* The counterexample: below `κ√(βs)` McDiarmid's term is `1` and Pinelis' term is `≥ 2e^{−1}`, so `τ^{cpl}_{P'} ≥ 2`, while the closed
  form is `< 1`.
-/

noncomputable section
open MeasureTheory Real Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31ta.RSharp

open StatFormal.Wave30tp StatFormal.Wave30ts

/-! ### Pinelis' term in the `h`-form -/

theorem pinelis_h (a b2 t : ℝ) (ha : 0 < a) (hb : 0 < b2) :
    psiPin a b2 t =
      2 * Real.exp (-(b2 / a ^ 2) * ((1 + t * a / b2) * Real.log (1 + t * a / b2) - t * a / b2)) := by
  unfold psiPin
  congr 2
  field_simp
  ring

/-! ### The two-point bound and the repair tail -/

/-- `twoPt β y ≤ 1 + y²(β−1)/(2(1 − y/3))` for `β ≥ 1`, `0 ≤ y < 3`. -/
theorem twoPt_le_bern {β y : ℝ} (hβ : 1 ≤ β) (hy0 : 0 ≤ y) (hy3 : y < 3) :
    twoPt β y ≤ 1 + y ^ 2 * (β - 1) / (2 * (1 - y / 3)) := by
  have hβ0 : 0 < β := by linarith
  have h1 := StatFormal.Bernstein.exp_mul_le_bernstein (x := 1 - β) hy0 hy3 (by linarith)
  have h2 := StatFormal.Bernstein.exp_mul_le_bernstein (x := 1) hy0 hy3 le_rfl
  have hb : 0 ≤ β⁻¹ := by positivity
  have hb1 : 0 ≤ 1 - β⁻¹ := by
    have : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
    linarith
  unfold twoPt
  have hc : 0 < 2 * (1 - y / 3) := by linarith
  calc β⁻¹ * exp (y * (1 - β)) + (1 - β⁻¹) * exp y
      ≤ β⁻¹ * (1 + y * (1 - β) + y ^ 2 * (1 - β) ^ 2 / (2 * (1 - y / 3))) +
          (1 - β⁻¹) * (1 + y * 1 + y ^ 2 * 1 ^ 2 / (2 * (1 - y / 3))) := by
        rw [mul_one] at h2
        gcongr
        · rw [mul_one]; exact h2
    _ = 1 + y ^ 2 * (β - 1) / (2 * (1 - y / 3)) := by
        field_simp
        ring

/-- For a list of sample sizes `k ≥ 1` with `1/k ≤ c`, `l ≥ 0`, `lc < 3`:
`∏_{k ∈ K} twoPt(β, l/k)^k ≤ exp(l²(β−1)/(2(1 − lc/3)) · Σ_{k ∈ K} 1/k)`. -/
theorem prodK_le_bern {β l c : ℝ} (hβ : 1 ≤ β) (hl : 0 ≤ l) (hlc : l * c < 3) :
    ∀ K : List ℕ, (∀ k ∈ K, 1 ≤ k ∧ (1 : ℝ) / k ≤ c) →
      (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod ≤
        exp (l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) * (K.map fun k : ℕ => (1 : ℝ) / k).sum) := by
  have hD : 0 < 2 * (1 - l * c / 3) := by linarith
  intro K
  induction K with
  | nil => intro _; simp
  | cons k K ih =>
    intro hK
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    obtain ⟨hk1, hkc⟩ := hK k (List.mem_cons_self ..)
    have ih' := ih fun k' hk' => hK k' (List.mem_cons_of_mem _ hk')
    have hk : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
    set y := l / (k : ℝ) with hy
    have hy0 : 0 ≤ y := div_nonneg hl hk.le
    have hyc : y ≤ l * c := by
      rw [hy, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hkc hl
    have hy3 : y < 3 := lt_of_le_of_lt hyc hlc
    have ht := twoPt_le_bern hβ hy0 hy3
    have hden : 2 * (1 - l * c / 3) ≤ 2 * (1 - y / 3) := by linarith
    have hβ1 : 0 ≤ β - 1 := by linarith
    have ht2 : twoPt β y ≤ exp (y ^ 2 * (β - 1) / (2 * (1 - l * c / 3))) := by
      refine ht.trans ?_
      refine le_trans ?_ (add_one_le_exp _)
      rw [add_comm]
      gcongr
    have hpow : twoPt β y ^ k ≤ exp (l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) * (1 / (k : ℝ))) := by
      calc twoPt β y ^ k ≤ exp (y ^ 2 * (β - 1) / (2 * (1 - l * c / 3))) ^ k :=
            pow_le_pow_left₀ (twoPt_nonneg hβ _) ht2 k
        _ = exp (l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) * (1 / (k : ℝ))) := by
            rw [← exp_nat_mul]
            congr 1
            rw [hy]
            field_simp
    calc twoPt β y ^ k * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod
        ≤ exp (l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) * (1 / (k : ℝ))) *
            exp (l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) * (K.map fun k : ℕ => (1 : ℝ) / k).sum) :=
          mul_le_mul hpow ih' (prodK_nonneg hβ _ _) (exp_pos _).le
      _ = exp (l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) *
            (1 / (k : ℝ) + (K.map fun k : ℕ => (1 : ℝ) / k).sum)) := by
          rw [← exp_add]; ring_nf

/-- The repair tail at the closed-form point: for `β > 1`, `c, s, L > 0`, a list `K` of sizes `k ≥ 1` with `1/k ≤ c` and
`Σ 1/k ≤ s`, and `t ≥ √(2(β−1)sL) + cL/3`: `Ψ_R(t; β, K) ≤ e^{−L}`. -/
theorem psiR_le_exp {β c s L t : ℝ} (hβ : 1 < β) (hc : 0 < c) (hs : 0 < s) (hL : 0 < L) (K : List ℕ)
    (hK : ∀ k ∈ K, 1 ≤ k ∧ (1 : ℝ) / k ≤ c) (hKs : (K.map fun k : ℕ => (1 : ℝ) / k).sum ≤ s)
    (ht : √(2 * ((β - 1) * s) * L) + c * L / 3 ≤ t) : psiR β t K ≤ exp (-L) := by
  set V := (β - 1) * s with hVdef
  have hV0 : 0 < V := mul_pos (by linarith) hs
  set a := √(2 * V * L) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = 2 * V * L := Real.sq_sqrt (by positivity)
  set Dn := V + c / 3 * a with hDn
  have hDn0 : 0 < Dn := by positivity
  set l := a / Dn with hl
  have hl0 : 0 < l := div_pos ha0 hDn0
  have hl3 : l * c < 3 := by
    rw [hl, div_mul_eq_mul_div, div_lt_iff₀ hDn0, hDn]; nlinarith
  have hden : 1 - l * c / 3 = V / Dn := by
    rw [hl, hDn]; field_simp; ring
  set C := l ^ 2 / (2 * (1 - l * c / 3)) with hC
  have hC0 : 0 ≤ C := by rw [hC, hden]; positivity
  have hexp : -l * (a + c * L / 3) + C * V = -L := by
    have hV' : V ≠ 0 := hV0.ne'
    have hD' : Dn ≠ 0 := hDn0.ne'
    rw [hC, hden, hl]
    field_simp
    rw [hDn]
    linear_combination (-3 : ℝ) * ha2
  have hprod := prodK_le_bern (β := β) (c := c) hβ.le hl0.le hl3 K hK
  have hβ1 : 0 ≤ β - 1 := by linarith
  have hsum : l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) * (K.map fun k : ℕ => (1 : ℝ) / k).sum ≤ C * V := by
    have e : l ^ 2 * (β - 1) / (2 * (1 - l * c / 3)) = C * (β - 1) := by rw [hC]; ring
    rw [e, hVdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKs hβ1) hC0
  calc psiR β t K ≤ psiRlam β l t K := psiR_le hβ.le t K hl0
    _ = exp (-(l * t)) * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod := rfl
    _ ≤ exp (-(l * (a + c * L / 3))) * exp (C * V) := by
        refine mul_le_mul (exp_le_exp.2 ?_) (hprod.trans (exp_le_exp.2 hsum)) (prodK_nonneg hβ.le _ _)
          (exp_pos _).le
        have := mul_le_mul_of_nonneg_left ht hl0.le
        linarith
    _ = exp (-L) := by rw [← exp_add, ← hexp]; ring_nf

/-! ### `τ^{P'} ≤ τ^P` -/

theorem log_six_div_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < Real.log (6 / δ) :=
  Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)

theorem exp_neg_log_six {δ : ℝ} (hδ0 : 0 < δ) : exp (-Real.log (6 / δ)) = δ / 6 := by
  rw [exp_neg, exp_log (by positivity)]; field_simp

theorem beta_pos {α : ℝ} (hα1 : α < 1) : 0 < 1 / (1 - α) := by
  have : 0 < 1 - α := by linarith
  positivity

theorem T1_nonneg {D v α δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hα1 : α < 1) : 0 ≤ T1 D v α δ n m := by
  unfold T1
  have := beta_pos hα1
  positivity

theorem T2_nonneg {α δ : ℝ} {n m : ℕ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) : 0 ≤ T2 α δ n m := by
  unfold T2
  have := log_six_div_pos hδ0 hδ1
  have := cNM_pos (m := m) hn
  positivity

/-- `t₁(β, δ/2) ≤ T₁`. -/
theorem rootH_le_T1 {D v ρbar α δ : ℝ} {n m : ℕ} (hD : 0 < D) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    rootH D v ρbar (1 / (1 - α)) (1 / 2 * δ) n m ≤ T1 D v α δ n m := by
  have hβ := beta_pos hα1
  have hL := (log_six_div_pos hδ0 hδ1).le
  have hT : √(1 / (1 - α) * v ^ 2 * sNM n m) + 1 / (1 - α) * D * √(sNM n m * Real.log (6 / δ) / 2) ≤
      T1 D v α δ n m := le_rfl
  have hs := one_div_le_sNM hn hm
  have h1 := psiMcD_le_exp hβ hD (sNM_pos hn hm) le_rfl hL hT
  have h2 := psiMcD_le_exp hβ hD (one_div_pos_nat hn) hs.1 hL hT
  have h3 := psiMcD_le_exp hβ hD (one_div_pos_nat hm) hs.2 hL hT
  rw [exp_neg_log_six hδ0] at h1 h2 h3
  have hmem : T1 D v α δ n m ∈ setH D v ρbar (1 / (1 - α)) (1 / 2 * δ) n m := by
    refine ⟨T1_nonneg hD.le hα1, ?_⟩
    unfold psiH3
    have a1 := psiH_le_McD D v ρbar (1 / (1 - α)) (sNM n m) (cNM n m) (T1 D v α δ n m)
    have a2 := psiH_le_McD D v ρbar (1 / (1 - α)) (1 / (n : ℝ)) (1 / (n : ℝ)) (T1 D v α δ n m)
    have a3 := psiH_le_McD D v ρbar (1 / (1 - α)) (1 / (m : ℝ)) (1 / (m : ℝ)) (T1 D v α δ n m)
    linarith
  exact csInf_le (bddBelow_nonneg_set fun t ht => ht.1) hmem

/-- `t₂(β, δ/2) ≤ T₂` for `α > 0`. -/
theorem rootR_le_T2 {α δ : ℝ} {n m : ℕ} (hα0 : 0 < α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    rootR (1 / (1 - α)) ((1 - 1 / 2) * δ) n m ≤ T2 α δ n m := by
  have hβ : 1 < 1 / (1 - α) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hL := log_six_div_pos hδ0 hδ1
  have hc := cNM_pos (m := m) hn
  have hs := sNM_pos hn hm
  have hT : √(2 * ((1 / (1 - α) - 1) * sNM n m) * Real.log (6 / δ)) + cNM n m * Real.log (6 / δ) / 3 ≤
      T2 α δ n m := by
    unfold T2
    rw [show 2 * ((1 / (1 - α) - 1) * sNM n m) * Real.log (6 / δ) =
      2 * (1 / (1 - α) - 1) * sNM n m * Real.log (6 / δ) by ring]
  have hn' : (1 : ℝ) / n ≤ cNM n m := le_max_left _ _
  have hm' : (1 : ℝ) / m ≤ cNM n m := le_max_right _ _
  have hs' := one_div_le_sNM hn hm
  have r1 := psiR_le_exp hβ hc hs hL [n]
    (fun k hk => by simp only [List.mem_singleton] at hk; subst hk; exact ⟨hn, hn'⟩) (by simpa using hs'.1) hT
  have r2 := psiR_le_exp hβ hc hs hL [m]
    (fun k hk => by simp only [List.mem_singleton] at hk; subst hk; exact ⟨hm, hm'⟩) (by simpa using hs'.2) hT
  have r3 := psiR_le_exp hβ hc hs hL [n, m]
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact ⟨hn, hn'⟩
      · exact ⟨hm, hm'⟩)
    (by simp [sNM]) hT
  rw [exp_neg_log_six hδ0] at r1 r2 r3
  have hmem : T2 α δ n m ∈ setR (1 / (1 - α)) ((1 - 1 / 2) * δ) n m := by
    refine ⟨T2_nonneg hδ0 hδ1 hn, ?_⟩
    unfold psiR3
    linarith
  exact csInf_le (bddBelow_nonneg_set fun t ht => ht.1) hmem

/-- `rem:sharper`, part (1). -/
theorem sharp_le_1 {D v ρbar α δ : ℝ} {n m : ℕ} (hD : 0 < D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    tauPs D v ρbar α δ n m ≤ tauP D v ρbar α δ n m := by
  rcases eq_or_ne α 0 with h0 | h0
  · subst h0
    rw [tauPs_zero_eq]
    have hP : tauP D v ρbar 0 δ n m = v * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2) := by
      simp [tauP]
    rw [hP]
    have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    have hs := sNM_pos hn hm
    refine csInf_le (bddBelow_nonneg_set fun t ht => ht.1) ⟨by positivity, ?_⟩
    refine (psiH_le_McD _ _ _ _ _ _ _).trans ?_
    have ht : √(1 * v ^ 2 * sNM n m) + 1 * D * √(sNM n m * Real.log (1 / δ) / 2) ≤
        v * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2) := by
      rw [one_mul, one_mul, Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
    refine (psiMcD_le_exp one_pos hD hs le_rfl hL ht).trans (le_of_eq ?_)
    rw [exp_neg, exp_log (by positivity)]; field_simp
  · have hα : 0 < α := lt_of_le_of_ne hα0 (Ne.symm h0)
    have hsplit := tauPs_pos_le (D := D) (v := v) (ρbar := ρbar) (δ := δ) (n := n) (m := m) h0
      (Or.inl rfl)
    have hP : tauP D v ρbar α δ n m = T1 D v α δ n m + ρbar * T2 α δ n m := by simp [tauP, h0]
    rw [hP]
    refine hsplit.trans ?_
    unfold tauSplit
    have h1 := rootH_le_T1 (v := v) (ρbar := ρbar) hD hα1 hδ0 hδ1 hn hm
    have h2 := rootR_le_T2 hα hα1 hδ0 hδ1 hn hm
    have := mul_le_mul_of_nonneg_left h2 hρ
    linarith

/-- `rem:sharper`, part (2): the paper's constants, every `D ≥ 0`. -/
theorem sharp_le_2 {κ D α δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    tauPs D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m ≤ tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m := by
  rcases hD.eq_or_lt with h | h
  · subst h
    have hv : √(min (κ ^ 2) ((0 : ℝ) ^ 2 / 2)) = 0 := by
      rw [show ((0 : ℝ)) ^ 2 / 2 = 0 by norm_num, min_eq_right (sq_nonneg κ), Real.sqrt_zero]
    rw [hv]
    have hP : tauP 0 0 0 α δ n m = 0 := by
      unfold tauP T1 T2; split_ifs <;> simp
    rw [hP]
    rcases eq_or_ne α 0 with h0 | h0
    · subst h0
      rw [tauPs_zero_eq, set0_empty le_rfl hδ1 hn hm (Or.inl rfl), Real.sInf_empty]
    · refine (tauPs_pos_le h0 (Or.inl rfl)).trans (le_of_eq ?_)
      unfold tauSplit
      rw [rootH_eq, setH_empty le_rfl (beta_pos hα1).le (by nlinarith) hn hm (Or.inl rfl), Real.sInf_empty]
      ring
  · exact sharp_le_1 h (Real.sqrt_nonneg _) h.le hα0 hα1 hδ0 hδ1 hn hm

/-- `rem:sharper`, part (3): the coupled supremum at `D_φ = √2κ`. -/
theorem sharp_le_3 {κ α δ : ℝ} {n m : ℕ} (hκ : 0 < κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    tauCpl (√2 * κ) κ α δ n m ≤ tauP (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) α δ n m := by
  have hD : 0 < √2 * κ := by positivity
  have hv : √(min (κ ^ 2) ((√2 * κ) ^ 2 / 2)) = κ := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), show 2 * κ ^ 2 / 2 = κ ^ 2 by ring, min_self,
      Real.sqrt_sq hκ.le]
  rw [hv]
  have hPnn : 0 ≤ tauP (√2 * κ) κ (√2 * κ) α δ n m :=
    (plugin_monotone _ _ _ δ n m hD.le hκ.le hD.le hδ0 hδ1 hn hm).2 α ⟨hα0, hα1⟩
  refine tauCpl_le hPnn fun u hu => ?_
  obtain ⟨hu0, hu1⟩ := hu
  have hv0 : 0 < √(κ ^ 2 - u) := Real.sqrt_pos.2 (by linarith)
  have hvκ : √(κ ^ 2 - u) ≤ κ :=
    (Real.sqrt_le_sqrt (by linarith : κ ^ 2 - u ≤ κ ^ 2)).trans_eq (Real.sqrt_sq hκ.le)
  have hρ0 : 0 < √(κ ^ 2 + u) := Real.sqrt_pos.2 (by positivity)
  have hρκ : √(κ ^ 2 + u) ≤ √2 * κ := by
    rw [show √2 * κ = √(2 * κ ^ 2) by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hκ.le]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  exact (tauPs_mono_const hD.le hv0 hvκ hρ0 hρκ hα0 hα1 hδ0 hδ1 hn hm).trans
    (sharp_le_1 hD hκ.le hD.le hα0 hα1 hδ0 hδ1 hn hm)

/-! ### The coupled counterexample -/

/-- Two unit vectors at distance `1/10` with a nonnegative inner product. -/
def phiCex : Bool → EuclideanSpace ℝ (Fin 2) :=
  fun b => if b then !₂[1, 0] else !₂[199 / 200, √399 / 200]

theorem sq_sqrt399 : (√399 / 200 : ℝ) ^ 2 = 399 / 40000 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem norm_phiCex (b : Bool) : ‖phiCex b‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  cases b
  · simp only [phiCex, Fin.sum_univ_two]
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp
    rw [abs_of_nonneg (Real.sqrt_nonneg _), sq_sqrt399]; norm_num
  · simp [phiCex, Fin.sum_univ_two]

theorem inner_phiCex_tf : ⟪phiCex true, phiCex false⟫_ℝ = 199 / 200 := by
  simp [phiCex, PiLp.inner_apply]

theorem dist_phiCex : ‖phiCex true - phiCex false‖ = 1 / 10 := by
  rw [EuclideanSpace.norm_eq]
  simp [phiCex, Fin.sum_univ_two]
  rw [show (1 - 199 / 200 : ℝ) ^ 2 + (√399 / 200) ^ 2 = (10⁻¹) ^ 2 by rw [sq_sqrt399]; norm_num,
    Real.sqrt_sq (by norm_num)]

theorem phiCex_props :
    (∀ x y, 0 ≤ ⟪phiCex x, phiCex y⟫_ℝ) ∧ (∀ x, ⟪phiCex x, phiCex x⟫_ℝ = 1) ∧
      (∀ x x', ‖phiCex x - phiCex x'‖ ≤ 1 / 10) ∧ ‖phiCex true - phiCex false‖ = 1 / 10 := by
  have hself : ∀ x, ⟪phiCex x, phiCex x⟫_ℝ = 1 := fun x => by
    rw [real_inner_self_eq_norm_sq, norm_phiCex]; norm_num
  refine ⟨fun x y => ?_, hself, fun x x' => ?_, dist_phiCex⟩
  · cases x <;> cases y
    · rw [hself]; norm_num
    · rw [real_inner_comm, inner_phiCex_tf]; norm_num
    · rw [inner_phiCex_tf]; norm_num
    · rw [hself]; norm_num
  · cases x <;> cases x'
    · simp
    · rw [norm_sub_rev, dist_phiCex]
    · rw [dist_phiCex]
    · simp

theorem log_twelve_lt : Real.log 12 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have : (2.7 : ℝ) ^ 3 < exp 1 ^ 3 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  nlinarith

theorem log_twelve_pos : 0 < Real.log 12 := Real.log_pos (by norm_num)

/-- `τ^P(1/2, 1/2) < 2` at `κ = 1`, `D = 1/10`, `n = m = 1`. -/
theorem tauP_cex_lt :
    tauP (1 / 10) (√(min (1 ^ 2) ((1 / 10) ^ 2 / 2))) (1 / 10) (1 / 2) (1 / 2) 1 1 < 2 := by
  have hP : tauP (1 / 10) (√(min (1 ^ 2) ((1 / 10) ^ 2 / 2))) (1 / 10) (1 / 2) (1 / 2) 1 1 =
      T1 (1 / 10) (√(min (1 ^ 2) ((1 / 10) ^ 2 / 2))) (1 / 2) (1 / 2) 1 1 + 1 / 10 * T2 (1 / 2) (1 / 2) 1 1 := by
    simp [tauP]
  rw [hP]
  have hv2 : √(min ((1 : ℝ) ^ 2) ((1 / 10) ^ 2 / 2)) ^ 2 = 1 / 200 := by
    rw [Real.sq_sqrt (by positivity)]; norm_num
  have hs : sNM 1 1 = 2 := by norm_num [sNM]
  have hc : cNM 1 1 = 1 := by norm_num [cNM]
  have hb : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
  have h6 : (6 : ℝ) / (1 / 2) = 12 := by norm_num
  have hL := log_twelve_lt
  have hL0 := log_twelve_pos
  unfold T1 T2
  rw [hs, hc, hb, h6, hv2]
  have e1 : √(2 * (1 / 200) * 2 : ℝ) ≤ 1 / 7 :=
    (Real.sqrt_le_sqrt (by norm_num : (2 * (1 / 200) * 2 : ℝ) ≤ (1 / 7) ^ 2)).trans_eq (Real.sqrt_sq (by norm_num))
  have e2 : √(2 * Real.log 12 / 2) ≤ 2 :=
    (Real.sqrt_le_sqrt (by linarith : 2 * Real.log 12 / 2 ≤ 2 ^ 2)).trans_eq (Real.sqrt_sq (by norm_num))
  have e3 : √(2 * (2 - 1) * 2 * Real.log 12) ≤ 4 :=
    (Real.sqrt_le_sqrt (by nlinarith : 2 * (2 - 1) * 2 * Real.log 12 ≤ 4 ^ 2)).trans_eq (Real.sqrt_sq (by norm_num))
  generalize √(2 * (1 / 200) * 2 : ℝ) = A at e1 ⊢
  generalize √(2 * Real.log 12 / 2) = B at e2 ⊢
  generalize √(2 * (2 - 1) * 2 * Real.log 12) = C at e3 ⊢
  linarith

/-- Below `κ√(βs) = 2` the Hilbert sum at `v = ρ̄ = 1`, `β = 2`, `s = 2`, `c = 1` is `≥ 2/3`. -/
theorem psiH3_cex_ge {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) : 2 / 3 ≤ psiH3 (1 / 10) 1 1 2 t 1 1 := by
  have hs : sNM 1 1 = 2 := by norm_num [sNM]
  have hc : cNM 1 1 = 1 := by norm_num [cNM]
  have h2 := psiH_nonneg (1 / 10) 1 1 2 (1 / ((1 : ℕ) : ℝ)) (1 / ((1 : ℕ) : ℝ)) t
  unfold psiH3
  rw [hs, hc]
  suffices h : 2 / 3 ≤ psiH (1 / 10) 1 1 2 2 1 t by linarith
  unfold psiH
  refine le_min ?_ ?_
  · unfold psiMcD
    have : max (t - √(2 * 1 ^ 2 * 2)) 0 = 0 := by
      rw [show (2 * 1 ^ 2 * 2 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      exact max_eq_right (by linarith)
    rw [this]; norm_num
  · unfold psiPin
    have hx : Real.log (1 + t * (2 * 1 * 1) / (2 * 1 ^ 2 * 2)) ≤ t * (2 * 1 * 1) / (2 * 1 ^ 2 * 2) := by
      have := Real.log_le_sub_one_of_pos (x := 1 + t * (2 * 1 * 1) / (2 * 1 ^ 2 * 2)) (by positivity)
      linarith
    have hcoef : 0 ≤ t / (2 * 1 * 1) + 2 * 1 ^ 2 * 2 / (2 * 1 * 1) ^ 2 := by positivity
    have hexp : -1 ≤ t / (2 * 1 * 1) - (t / (2 * 1 * 1) + 2 * 1 ^ 2 * 2 / (2 * 1 * 1) ^ 2) *
        Real.log (1 + t * (2 * 1 * 1) / (2 * 1 ^ 2 * 2)) := by
      have := mul_le_mul_of_nonneg_left hx hcoef
      nlinarith
    have he : exp (-1 : ℝ) ≤ exp (t / (2 * 1 * 1) - (t / (2 * 1 * 1) + 2 * 1 ^ 2 * 2 / (2 * 1 * 1) ^ 2) *
        Real.log (1 + t * (2 * 1 * 1) / (2 * 1 ^ 2 * 2))) := exp_le_exp.2 hexp
    have h3 : exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hinv : (1 : ℝ) / 3 < exp (-1) := by
      rw [exp_neg, one_div]; exact inv_strictAnti₀ (exp_pos _) h3
    linarith

/-- `t₁ ≥ 2` at the counterexample's constants, for every split `f`. -/
theorem rootH_cex_ge {f : ℝ} (hf : IsSplit f) : 2 ≤ rootH (1 / 10) 1 1 2 (f * (1 / 2)) 1 1 := by
  obtain ⟨hf0, hf1⟩ := hf.bounds
  have hf9 : f ≤ 9 / 10 := by rcases hf with h | h | h | h | h <;> subst h <;> norm_num
  rw [rootH_eq]
  refine le_csInf (setH_nonempty zero_le_one zero_le_one (by norm_num) (by positivity) le_rfl le_rfl
    (Or.inl (by norm_num))) fun t ht => ?_
  by_contra hlt
  push Not at hlt
  have := psiH3_cex_ge ht.1 hlt
  have := ht.2
  nlinarith

/-- `τ^{cpl}_{P'}(1/2, 1/2) ≥ 2` at `κ = 1`, `D = 1/10`, `n = m = 1`. -/
theorem tauCpl_cex_ge : 2 ≤ tauCpl (1 / 10) 1 (1 / 2) (1 / 2) 1 1 := by
  have hu : (0 : ℝ) ∈ Ico (0 : ℝ) (1 ^ 2) := ⟨le_rfl, by norm_num⟩
  have h := le_tauCpl (D := 1 / 10) (κ := 1) (α := 1 / 2) (δ := 1 / 2) (n := 1) (m := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl hu
  refine le_trans ?_ h
  rw [show √((1 : ℝ) ^ 2 - 0) = 1 by norm_num, show √((1 : ℝ) ^ 2 + 0) = 1 by norm_num]
  refine le_tauPs_pos (by norm_num) fun f hf => ?_
  unfold tauSplit
  rw [show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num]
  have h1 := rootH_cex_ge hf
  have h2 := rootR_nonneg 2 ((1 - f) * (1 / 2)) 1 1
  linarith

/-! ### The sample-size rule -/

theorem tauP_gauss_zero {κ δ : ℝ} {n : ℕ} (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) :
    tauP (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) 0 δ n n =
      κ * (1 + √(Real.log (1 / δ))) * √(2 / n) := by
  have hv : √(min (κ ^ 2) ((√2 * κ) ^ 2 / 2)) = κ := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), show 2 * κ ^ 2 / 2 = κ ^ 2 by ring, min_self,
      Real.sqrt_sq hκ.le]
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hs : sNM n n = 2 / n := by unfold sNM; ring
  simp only [tauP, ite_true, hv, hs]
  have e : √2 * √(2 / n * Real.log (1 / δ) / 2) = √(2 / n) * √(Real.log (1 / δ)) := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  calc κ * √(2 / n) + √2 * κ * √(2 / n * Real.log (1 / δ) / 2)
      = κ * √(2 / n) + κ * (√2 * √(2 / n * Real.log (1 / δ) / 2)) := by ring
    _ = κ * (1 + √(Real.log (1 / δ))) * √(2 / n) := by rw [e]; ring

end StatFormal.Wave31ta.RSharp

namespace StatFormal.Wave31ta

open StatFormal.Wave30tp StatFormal.Wave30ts

theorem pinelis_h_form : Claims.pinelis_h_form := fun a b2 t ha hb => RSharp.pinelis_h a b2 t ha hb

theorem sharp_le_plugin : Claims.sharp_le_plugin :=
  ⟨fun _ _ _ _ _ _ _ hD hv hρ hα0 hα1 hδ0 hδ1 hn hm => RSharp.sharp_le_1 hD hv hρ hα0 hα1 hδ0 hδ1 hn hm,
    fun _ _ _ _ _ _ hD hα0 hα1 hδ0 hδ1 hn hm => RSharp.sharp_le_2 hD hα0 hα1 hδ0 hδ1 hn hm,
    fun _ _ _ _ _ hκ hα0 hα1 hδ0 hδ1 hn hm => RSharp.sharp_le_3 hκ hα0 hα1 hδ0 hδ1 hn hm⟩

theorem sharp_cpl_counterexample : Claims.sharp_cpl_counterexample :=
  ⟨⟨RSharp.phiCex, RSharp.phiCex_props⟩, RSharp.tauP_cex_lt.trans_le RSharp.tauCpl_cex_ge⟩

theorem samplesize : Claims.samplesize := by
  intro κ δ Dh n hκ hδ0 hδ1 hn
  have hP := RSharp.tauP_gauss_zero hκ hδ0 hδ1 hn
  have hF : StatFormal.Wave30tu.Full.tauFull κ (√2 * κ) 0 δ n n ≤
      tauP (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) 0 δ n n :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hV : tauV2Cpl κ (√2 * κ) 0 δ n n ≤
      tauP (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) 0 δ n n :=
    (min_le_right _ _).trans (min_le_left _ _)
  rw [hP] at hF hV
  refine ⟨hP, hF, hV, fun hDh hlt => ?_⟩
  set C0 := κ * (1 + √(Real.log (1 / δ))) with hC0
  have hC0n : 0 ≤ C0 := by positivity
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have key : C0 * √(2 / n) < Dh := by
    rw [show C0 * √(2 / n) = √(C0 ^ 2 * (2 / n)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC0n]]
    rw [Real.sqrt_lt' hDh]
    rw [div_pow] at hlt
    have h1 : 2 * C0 ^ 2 < n * Dh ^ 2 := by
      have hd : (0 : ℝ) < Dh ^ 2 := by positivity
      have := (div_lt_iff₀ hd).1 (by rw [mul_div_assoc]; exact hlt)
      linarith
    rw [show C0 ^ 2 * (2 / n) = 2 * C0 ^ 2 / n by ring, div_lt_iff₀ hn0]
    linarith
  exact ⟨hF.trans_lt key, hV.trans_lt key⟩

end StatFormal.Wave31ta

