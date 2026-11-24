import StatFormal.Wave30tp.RouteMcDiarmid2
import StatFormal.Lib.Bernstein.Bernstein

/-!
# Route (library-grade): one-sided Bernstein (sub-gamma) for two independent samples

Untrusted proof material.

* `integral_exp_le_subgamma`: for a bounded centred `W ≤ c` (`c > 0`) and `0 ≤ λ`, `λc < 3`:
  `E e^{λW} ≤ exp(λ² E W² / (2(1 − λc/3)))` (only the upper bound `W ≤ c` is used; the library pointwise inequality
  `StatFormal.Bernstein.exp_mul_le_bernstein`, rescaled).
* `bernstein_two_sample`: under `P^{⊗n} ⊗ Q^{⊗m}`, for `S = Σ_i W₁(X_i) + Σ_j W₂(Y_j)` with centred bounded `W₁ ≤ c`,
  `W₂ ≤ c` and `n E W₁² + m E W₂² ≤ V`, `V > 0`, `L ≥ 0`: `P(S ≥ √(2VL) + cL/3) ≤ e^{−L}` (Bernstein in sub-gamma form,
  Boucheron–Lugosi–Massart §2.4, for non-identically distributed summands).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real

namespace StatFormal.Wave30tp

variable {β : Type*} [MeasurableSpace β]

theorem integral_exp_le_subgamma (ν : Measure β) [IsProbabilityMeasure ν] {W : β → ℝ} (hW : Measurable W)
    {K : ℝ} (hWK : ∀ x, |W x| ≤ K) (hW0 : ∫ x, W x ∂ν = 0) {c : ℝ} (hc : 0 < c) (hWc : ∀ x, W x ≤ c)
    {l : ℝ} (hl0 : 0 ≤ l) (hl3 : l * c < 3) :
    ∫ x, exp (l * W x) ∂ν ≤ exp (l ^ 2 / (2 * (1 - l * c / 3)) * ∫ x, W x ^ 2 ∂ν) := by
  set C := l ^ 2 / (2 * (1 - l * c / 3)) with hC
  have hD : 0 < 1 - l * c / 3 := by linarith
  have hi : Integrable W ν :=
    Integrable.of_bound hW.aestronglyMeasurable K (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hWK x)
  have hi2 : Integrable (fun x => W x ^ 2) ν :=
    Integrable.of_bound (hW.pow_const 2).aestronglyMeasurable (K ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hWK x) 2)
  have hie : Integrable (fun x => exp (l * W x)) ν :=
    Integrable.of_bound (measurable_exp.comp (hW.const_mul l)).aestronglyMeasurable (exp (l * K))
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hWK x)) hl0))
  have hpt : ∀ x, exp (l * W x) ≤ 1 + l * W x + C * W x ^ 2 := fun x => by
    have h := StatFormal.Bernstein.exp_mul_le_bernstein (l := l * c) (x := W x / c)
      (mul_nonneg hl0 hc.le) hl3 (by rw [div_le_one hc]; exact hWc x)
    have e1 : l * c * (W x / c) = l * W x := by field_simp
    have e2 : (l * c) ^ 2 * (W x / c) ^ 2 / (2 * (1 - l * c / 3)) = C * W x ^ 2 := by
      rw [hC, div_pow, mul_pow]
      field_simp
    rw [e1, e2] at h
    exact h
  calc ∫ x, exp (l * W x) ∂ν ≤ ∫ x, (1 + l * W x + C * W x ^ 2) ∂ν :=
        integral_mono hie (((integrable_const 1).add (hi.const_mul l)).add (hi2.const_mul C)) hpt
    _ = 1 + C * ∫ x, W x ^ 2 ∂ν := by
        have j1 : Integrable (fun x => 1 + l * W x) ν := (integrable_const 1).add (hi.const_mul l)
        rw [integral_add j1 (hi2.const_mul C), integral_add (integrable_const 1) (hi.const_mul l),
          integral_const_mul, integral_const_mul, hW0]
        simp
    _ ≤ exp (C * ∫ x, W x ^ 2 ∂ν) := by linarith [add_one_le_exp (C * ∫ x, W x ^ 2 ∂ν)]

/-- **One-sided Bernstein for two independent samples** (sub-gamma form). -/
theorem bernstein_two_sample (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    {W1 W2 : β → ℝ} (hW1 : Measurable W1) (hW2 : Measurable W2) {K : ℝ} (hK1 : ∀ x, |W1 x| ≤ K)
    (hK2 : ∀ x, |W2 x| ≤ K) (h01 : ∫ x, W1 x ∂P = 0) (h02 : ∫ x, W2 x ∂Q = 0) {c : ℝ} (hc : 0 < c)
    (hc1 : ∀ x, W1 x ≤ c) (hc2 : ∀ x, W2 x ≤ c) {V : ℝ} (hV0 : 0 < V)
    (hV : n * ∫ x, W1 x ^ 2 ∂P + m * ∫ x, W2 x ^ 2 ∂Q ≤ V) {L : ℝ} (hL : 0 ≤ L) :
    (sampleLaw P Q n m).real {z | √(2 * V * L) + c * L / 3 ≤ ∑ i, W1 (z.1 i) + ∑ j, W2 (z.2 j)} ≤
      exp (-L) := by
  set μ := sampleLaw P Q n m
  set S : (Fin n → β) × (Fin m → β) → ℝ := fun z => ∑ i, W1 (z.1 i) + ∑ j, W2 (z.2 j) with hS
  have hSm : Measurable S :=
    (Finset.measurable_sum _ fun i _ => hW1.comp ((measurable_pi_apply i).comp measurable_fst)).add
      (Finset.measurable_sum _ fun j _ => hW2.comp ((measurable_pi_apply j).comp measurable_snd))
  have hK0 : 0 ≤ K := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (abs_nonneg _).trans (hK1 x)
  have hSb : ∀ z, |S z| ≤ (n + m) * K := fun z => by
    simp only [hS]
    refine (abs_add_le _ _).trans ?_
    have h1 : |∑ i, W1 (z.1 i)| ≤ n * K := (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ i, |W1 (z.1 i)| ≤ ∑ _i : Fin n, K := Finset.sum_le_sum fun i _ => hK1 _
        _ = n * K := by simp)
    have h2 : |∑ j, W2 (z.2 j)| ≤ m * K := (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ j, |W2 (z.2 j)| ≤ ∑ _j : Fin m, K := Finset.sum_le_sum fun j _ => hK2 _
        _ = m * K := by simp)
    linarith
  have hint : ∀ t : ℝ, Integrable (fun z => exp (t * S z)) μ := fun t =>
    Integrable.of_bound (measurable_exp.comp (hSm.const_mul t)).aestronglyMeasurable
      (exp (|t| * ((n + m) * K))) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        refine exp_le_exp.2 ((le_abs_self _).trans ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hSb z) (abs_nonneg _))
  -- the MGF factorises
  have hmgf : ∀ t : ℝ, mgf S μ t = (∫ x, exp (t * W1 x) ∂P) ^ n * (∫ y, exp (t * W2 y) ∂Q) ^ m := by
    intro t
    rw [mgf]
    have : ∀ z : (Fin n → β) × (Fin m → β), exp (t * S z) =
        exp (t * ∑ i, W1 (z.1 i)) * exp (t * ∑ j, W2 (z.2 j)) := fun z => by
      rw [← exp_add, ← mul_add]
    simp_rw [this]
    rw [show μ = (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) from rfl,
      integral_prod_mul (fun x : Fin n → β => exp (t * ∑ i, W1 (x i)))
      (fun y : Fin m → β => exp (t * ∑ j, W2 (y j))),
      StatFormal.Bernstein.integral_exp_mul_sum_eq, StatFormal.Bernstein.integral_exp_mul_sum_eq]
  set a := √(2 * V * L) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * V * L := Real.sq_sqrt (by positivity)
  set Dn := V + c / 3 * a with hDn
  have hDn0 : 0 < Dn := by positivity
  set l := a / Dn with hl
  have hl0 : 0 ≤ l := div_nonneg ha0 hDn0.le
  have hl3 : l * c < 3 := by
    rw [hl, div_mul_eq_mul_div, div_lt_iff₀ hDn0, hDn]; nlinarith
  have hden : 1 - l * c / 3 = V / Dn := by
    rw [hl, hDn]; field_simp; ring
  set C := l ^ 2 / (2 * (1 - l * c / 3)) with hC
  have hC0 : 0 ≤ C := by rw [hC, hden]; positivity
  have hbound : mgf S μ l ≤ exp (C * V) := by
    rw [hmgf]
    have e1 := integral_exp_le_subgamma P hW1 hK1 h01 hc hc1 hl0 hl3
    have e2 := integral_exp_le_subgamma Q hW2 hK2 h02 hc hc2 hl0 hl3
    have p1 : 0 ≤ ∫ x, exp (l * W1 x) ∂P := integral_nonneg fun _ => (exp_pos _).le
    have p2 : 0 ≤ ∫ y, exp (l * W2 y) ∂Q := integral_nonneg fun _ => (exp_pos _).le
    calc (∫ x, exp (l * W1 x) ∂P) ^ n * (∫ y, exp (l * W2 y) ∂Q) ^ m
        ≤ exp (C * ∫ x, W1 x ^ 2 ∂P) ^ n * exp (C * ∫ y, W2 y ^ 2 ∂Q) ^ m := by gcongr
      _ = exp (C * (n * ∫ x, W1 x ^ 2 ∂P + m * ∫ y, W2 y ^ 2 ∂Q)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      _ ≤ exp (C * V) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hV hC0)
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := S) (a + c * L / 3) hl0 (hint l)
  have hexp : -l * (a + c * L / 3) + C * V = -L := by
    have hV' : V ≠ 0 := hV0.ne'
    have hD' : Dn ≠ 0 := hDn0.ne'
    rw [hC, hden, hl]
    field_simp
    rw [hDn]
    linear_combination (-3 : ℝ) * ha2
  calc μ.real {z | a + c * L / 3 ≤ S z} ≤ exp (-l * (a + c * L / 3)) * mgf S μ l := hchern
    _ ≤ exp (-l * (a + c * L / 3)) * exp (C * V) := by gcongr
    _ = exp (-L) := by rw [← exp_add, hexp]

end StatFormal.Wave30tp
