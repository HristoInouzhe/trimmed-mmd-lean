import StatFormal.Wave30ts.RouteRoots

/-!
# Route: Pinelis (claims), and the three tail bounds on two samples

Untrusted proof material.

* `pinelis_mgf`, `pinelis`: the frozen Pinelis claims, from `StatFormal.Lib.Concentration.Pinelis`.
* `twoDev_pinelis`: Pinelis' tail for the two-sample deviation `n⁻¹Σψ₁(X_i) − m⁻¹Σψ₂(Y_j)` under `P^{⊗n} ⊗ Q^{⊗m}` (one
  `P ⊗ Q` draw per index of `Fin n ⊕ Fin m`, wave 30tp's `splitMap`); junk parameters (`a = 0` or `b² = 0`) give a bound `≥ 1`.
* `twoDev_mcd`: wave 30tp's McDiarmid tail `twoDev_tail` rewritten as the McDiarmid term of `Ψ_H`.
* `chernoff_two_sample`: `P(S ≥ t) ≤ e^{−λt} (E e^{λW₁})ⁿ (E e^{λW₂})^m` for `S = ΣW₁(X_i) + ΣW₂(Y_j)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set

namespace StatFormal.Wave30ts

open StatFormal.Wave30tp

theorem pinelis_mgf : Claims.pinelis_mgf := by
  intro ι H _ _ _ _ Ω _ μ _ η l r hη hexp h0 hl hr
  exact ⟨StatFormal.Pinelis.pinelis_mgf_tail μ η hη hl hexp h0 hr,
    StatFormal.Pinelis.two_exp_mul_prod_le _ fun i =>
      StatFormal.Pinelis.integral_exp_sub_nonneg (μ i) (fun ω => ‖η i ω‖) l⟩

theorem pinelis : Claims.pinelis := by
  intro ι H _ _ _ _ Ω _ μ _ η a b2 r hη h0 ha hb ha0 hb0 hr
  exact StatFormal.Pinelis.pinelis_tail μ η hη h0 ha hb ha0 hb0 hr

section TwoSample

variable {β : Type*} [MeasurableSpace β]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Pinelis for two samples.** -/
theorem twoDev_pinelis (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {ψ1 ψ2 : β → H}
    (h1 : StronglyMeasurable ψ1) (h2 : StronglyMeasurable ψ2) (h01 : ∫ x, ψ1 x ∂P = 0) (h02 : ∫ x, ψ2 x ∂Q = 0)
    {K1 K2 : ℝ} (hK1 : ∀ x, ‖ψ1 x‖ ≤ K1) (hK2 : ∀ x, ‖ψ2 x‖ ≤ K2) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {a b2 r : ℝ} (ha1 : K1 / n ≤ a) (ha2 : K2 / m ≤ a) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b2)
    (hb : (∫ x, ‖ψ1 x‖ ^ 2 ∂P) / n + (∫ x, ‖ψ2 x‖ ^ 2 ∂Q) / m ≤ b2) (hr : 0 ≤ r) :
    sampleLaw P Q n m {z | r ≤ ‖twoDev ψ1 ψ2 z‖} ≤ ENNReal.ofReal (psiPin a b2 r) := by
  by_cases hj : a = 0 ∨ b2 = 0
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (one_le_psiPin_of_junk ha0 hr hj))
  push_neg at hj
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  set ν : Measure (β × β) := P.prod Q
  set η : Fin n ⊕ Fin m → β × β → H :=
    Sum.elim (fun _ pq => (n : ℝ)⁻¹ • ψ1 pq.1) (fun _ pq => -((m : ℝ)⁻¹ • ψ2 pq.2)) with hη
  have hsum : ∀ ω : Fin n ⊕ Fin m → β × β, ∑ k, η k (ω k) = twoDev ψ1 ψ2 (splitMap n m ω) := by
    intro ω
    simp only [hη, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, twoDev, splitMap, Finset.smul_sum,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  have hset : MeasurableSet {z : (Fin n → β) × (Fin m → β) | r ≤ ‖twoDev ψ1 ψ2 z‖} :=
    measurableSet_le measurable_const (stronglyMeasurable_twoDev h1 h2 n m).norm.measurable
  rw [← map_splitMap P Q n m, Measure.map_apply (measurable_splitMap n m) hset]
  have hpre : splitMap n m ⁻¹' {z | r ≤ ‖twoDev ψ1 ψ2 z‖} = {ω | r ≤ ‖∑ k, η k (ω k)‖} := by
    ext ω; simp only [mem_preimage, mem_setOf_eq, hsum]
  rw [hpre]
  have hsm : ∀ k, StronglyMeasurable (η k) := by
    intro k; cases k with
    | inl i => exact (h1.comp_measurable measurable_fst).const_smul _
    | inr j => exact ((h2.comp_measurable measurable_snd).const_smul _).neg
  have hmean : ∀ k, ∫ ω, η k ω ∂ν = 0 := by
    intro k; cases k with
    | inl i =>
      simp only [hη, Sum.elim_inl]
      rw [integral_smul, integral_fun_fst (fun x => ψ1 x), h01]; simp
    | inr j =>
      simp only [hη, Sum.elim_inr]
      rw [integral_neg, integral_smul, integral_fun_snd (fun x => ψ2 x), h02]; simp
  have hbd : ∀ k, ∀ᵐ ω ∂ν, ‖η k ω‖ ≤ a := by
    intro k; refine ae_of_all _ fun ω => ?_
    cases k with
    | inl i =>
      simp only [hη, Sum.elim_inl, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
      refine le_trans ?_ ha1
      rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left (hK1 _) (by positivity)
    | inr j =>
      simp only [hη, Sum.elim_inr, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
      refine le_trans ?_ ha2
      rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left (hK2 _) (by positivity)
  have e1 : ∀ i : Fin n, ∫ ω, ‖η (Sum.inl i) ω‖ ^ 2 ∂ν = ((n : ℝ)⁻¹) ^ 2 * ∫ x, ‖ψ1 x‖ ^ 2 ∂P := by
    intro i
    simp only [hη, Sum.elim_inl, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, mul_pow]
    rw [integral_const_mul, integral_fun_fst (fun x => ‖ψ1 x‖ ^ 2)]
    simp
  have e2 : ∀ j : Fin m, ∫ ω, ‖η (Sum.inr j) ω‖ ^ 2 ∂ν = ((m : ℝ)⁻¹) ^ 2 * ∫ x, ‖ψ2 x‖ ^ 2 ∂Q := by
    intro j
    simp only [hη, Sum.elim_inr, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, mul_pow]
    rw [integral_const_mul, integral_fun_snd (fun x => ‖ψ2 x‖ ^ 2)]
    simp
  have hvar : ∑ k, ∫ ω, ‖η k ω‖ ^ 2 ∂ν ≤ b2 := by
    refine le_trans (le_of_eq ?_) hb
    rw [Fintype.sum_sum_type]
    simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  exact StatFormal.Pinelis.pinelis_tail (fun _ => ν) η hsm hmean hbd hvar
    (lt_of_le_of_ne ha0 (Ne.symm hj.1)) (lt_of_le_of_ne hb0 (Ne.symm hj.2)) hr

/-- **McDiarmid for two samples**, as the McDiarmid term of `Ψ_H`. -/
theorem twoDev_mcd (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ψ1 ψ2 : β → H} (h1 : StronglyMeasurable ψ1) (h2 : StronglyMeasurable ψ2) {K : ℝ}
    (hK1 : ∀ x, ‖ψ1 x‖ ≤ K) (hK2 : ∀ x, ‖ψ2 x‖ ≤ K) (h01 : ∫ x, ψ1 x ∂P = 0) (h02 : ∫ x, ψ2 x ∂Q = 0)
    {σ1 σ2 : ℝ} (hσ1 : ∫ y, ‖ψ1 y‖ ^ 2 ∂P ≤ σ1) (hσ2 : ∫ y, ‖ψ2 y‖ ^ 2 ∂Q ≤ σ2)
    {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hd1 : ∀ x x', ‖ψ1 x - ψ1 x'‖ ≤ c1)
    (hd2 : ∀ x x', ‖ψ2 x - ψ2 x'‖ ≤ c2) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {D v bt s' t : ℝ}
    (hσ : σ1 / n + σ2 / m = bt * v ^ 2 * s') (hc : c1 ^ 2 / n + c2 ^ 2 / m = bt ^ 2 * D ^ 2 * s') :
    sampleLaw P Q n m {z | t < ‖twoDev ψ1 ψ2 z‖} ≤ ENNReal.ofReal (psiMcD D v bt s' t) := by
  have hd0 : 0 ≤ bt ^ 2 * D ^ 2 * s' := by
    rw [← hc]
    have : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
    have : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
    positivity
  by_cases htriv : bt ^ 2 * D ^ 2 * s' = 0 ∨ t ≤ √(bt * v ^ 2 * s')
  · have h1' : psiMcD D v bt s' t = 1 := by
      unfold psiMcD
      rcases htriv with h | h
      · rw [h, div_zero, exp_zero]
      · rw [max_eq_right (by linarith)]; simp
    rw [h1']; simpa using prob_le_one
  push_neg at htriv
  have hdpos : 0 < bt ^ 2 * D ^ 2 * s' := lt_of_le_of_ne hd0 (Ne.symm htriv.1)
  have hL0 : 0 ≤ 2 * (t - √(bt * v ^ 2 * s')) ^ 2 / (bt ^ 2 * D ^ 2 * s') := by positivity
  have htail := twoDev_tail P Q h1 h2 hK1 hK2 h01 h02 hσ1 hσ2 hc1 hc2 hd1 hd2 hn hm hL0
  have hthr : √(σ1 / n + σ2 / m) + √((c1 ^ 2 / n + c2 ^ 2 / m) *
      (2 * (t - √(bt * v ^ 2 * s')) ^ 2 / (bt ^ 2 * D ^ 2 * s')) / 2) = t := by
    rw [hσ, hc]
    have : bt ^ 2 * D ^ 2 * s' * (2 * (t - √(bt * v ^ 2 * s')) ^ 2 / (bt ^ 2 * D ^ 2 * s')) / 2 =
        (t - √(bt * v ^ 2 * s')) ^ 2 := by
      generalize bt ^ 2 * D ^ 2 * s' = d at hdpos ⊢
      field_simp
    rw [this, Real.sqrt_sq (by linarith)]
    ring
  rw [hthr] at htail
  refine htail.trans (le_of_eq ?_)
  congr 1
  unfold psiMcD
  rw [max_eq_left (by linarith)]
  congr 1
  ring

theorem psiH_of_two (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    {F : (Fin n → β) × (Fin m → β) → ℝ} {t A B : ℝ}
    (hA : sampleLaw P Q n m {z | t < F z} ≤ ENNReal.ofReal A)
    (hB : sampleLaw P Q n m {z | t ≤ F z} ≤ ENNReal.ofReal B) :
    sampleLaw P Q n m {z : (Fin n → β) × (Fin m → β) | t < F z} ≤ ENNReal.ofReal (min A B) := by
  rcases le_total A B with h | h
  · rw [min_eq_left h]; exact hA
  · rw [min_eq_right h]
    exact (measure_mono fun z (hz : t < F z) => (show t ≤ F z from hz.le)).trans hB

/-- The MGF of `S = ΣW₁(X_i) + ΣW₂(Y_j)` factorises; Chernoff. -/
theorem chernoff_two_sample (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    {W1 W2 : β → ℝ} (hW1 : Measurable W1) (hW2 : Measurable W2) {K : ℝ} (hK1 : ∀ x, |W1 x| ≤ K)
    (hK2 : ∀ x, |W2 x| ≤ K) {l t : ℝ} (hl : 0 ≤ l) :
    sampleLaw P Q n m {z | t ≤ ∑ i, W1 (z.1 i) + ∑ j, W2 (z.2 j)} ≤
      ENNReal.ofReal (exp (-(l * t)) * ((∫ x, exp (l * W1 x) ∂P) ^ n * (∫ y, exp (l * W2 y) ∂Q) ^ m)) := by
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
      calc ∑ j, |W2 (z.2 j)| ≤ ∑ _j : Fin m, K := Finset.sum_le_sum fun i _ => hK2 _
        _ = m * K := by simp)
    linarith
  have hint : Integrable (fun z => exp (l * S z)) μ :=
    Integrable.of_bound (measurable_exp.comp (hSm.const_mul l)).aestronglyMeasurable
      (exp (|l| * ((n + m) * K))) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        refine exp_le_exp.2 ((le_abs_self _).trans ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hSb z) (abs_nonneg _))
  have hmgf : mgf S μ l = (∫ x, exp (l * W1 x) ∂P) ^ n * (∫ y, exp (l * W2 y) ∂Q) ^ m := by
    rw [mgf]
    have : ∀ z : (Fin n → β) × (Fin m → β), exp (l * S z) =
        exp (l * ∑ i, W1 (z.1 i)) * exp (l * ∑ j, W2 (z.2 j)) := fun z => by
      rw [← exp_add, ← mul_add]
    simp_rw [this]
    rw [show μ = (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) from rfl,
      integral_prod_mul (fun x : Fin n → β => exp (l * ∑ i, W1 (x i)))
      (fun y : Fin m → β => exp (l * ∑ j, W2 (y j))),
      StatFormal.Bernstein.integral_exp_mul_sum_eq, StatFormal.Bernstein.integral_exp_mul_sum_eq]
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := S) t hl hint
  rw [hmgf] at hchern
  calc μ {z | t ≤ S z} = ENNReal.ofReal (μ.real {z | t ≤ S z}) := (ofReal_measureReal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [neg_mul] at hchern; exact hchern)

end TwoSample

end StatFormal.Wave30ts
