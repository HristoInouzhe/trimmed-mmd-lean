import StatFormal.Lib.Concentration.HilbertMean

/-!
# Markov bounds for the deviation of empirical mean embeddings (library)

Library component (untrusted).

* `prod_measure_le_add`: under a product of probability measures, `P(t ≤ A(ω₁) + B(ω₂)) ≤ P(t/2 ≤ A) + P(t/2 ≤ B)` (no measurability
  needed);
* `measurable_norm_meanDev`: `x ↦ ‖n⁻¹Σφ(x_i) − ∫φ dP‖` is measurable for strongly measurable `φ`;
* `measure_meanDev_ge_le`: **Markov with `E‖meanDev‖ ≤ κ/√k`** (`Concentration.integral_norm_meanDev_le`), for the sample mean of a
  measure-preserving reindexing `f` of the sample (e.g. the fitting sample of a batch):
  `P^{⊗p}(s ≤ ‖meanDev(f x)‖) ≤ κ/(s√k)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Alpha0Witness

open StatFormal.Concentration

/-- Under `μ ⊗ ν` (probability measures), `{t ≤ A(ω₁) + B(ω₂)}` has measure at most `μ(t/2 ≤ A) + ν(t/2 ≤ B)`. -/
theorem prod_measure_le_add {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : α → ℝ) (B : β → ℝ) (t : ℝ) :
    μ.prod ν {ω | t ≤ A ω.1 + B ω.2} ≤ μ {x | t / 2 ≤ A x} + ν {y | t / 2 ≤ B y} := by
  have hsub : {ω : α × β | t ≤ A ω.1 + B ω.2} ⊆ {x | t / 2 ≤ A x} ×ˢ univ ∪ univ ×ˢ {y | t / 2 ≤ B y} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases h : t / 2 ≤ A ω.1
    · exact Or.inl ⟨h, mem_univ _⟩
    · exact Or.inr ⟨mem_univ _, by simp only [Set.mem_ofPred_eq]; linarith⟩
  calc μ.prod ν {ω | t ≤ A ω.1 + B ω.2}
      ≤ μ.prod ν ({x | t / 2 ≤ A x} ×ˢ univ ∪ univ ×ˢ {y | t / 2 ≤ B y}) := measure_mono hsub
    _ ≤ μ.prod ν ({x | t / 2 ≤ A x} ×ˢ univ) + μ.prod ν (univ ×ˢ {y | t / 2 ≤ B y}) := measure_union_le _ _
    _ = μ {x | t / 2 ≤ A x} + ν {y | t / 2 ≤ B y} := by
        rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `x ↦ ‖meanDev P φ k x‖` is measurable. -/
theorem measurable_norm_meanDev (P : Measure X) {φ : X → H} (hφ : StronglyMeasurable φ) (k : ℕ) :
    Measurable fun x : Fin k → X => ‖meanDev P φ k x‖ := by
  refine (StronglyMeasurable.norm ?_).measurable
  refine StronglyMeasurable.sub ?_ stronglyMeasurable_const
  refine StronglyMeasurable.const_smul ?_ _
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hφ.comp_measurable (measurable_pi_apply i)

/-- **Markov bound for the mean deviation of a reindexed sample**: if `f : X^p → X^k` is measurable and carries `P^{⊗p}` to `P^{⊗k}`
(`k ≥ 1`), then `P^{⊗p}(s ≤ ‖k⁻¹Σφ(f(x)_i) − ∫φ dP‖) ≤ κ/(s√k)` for `s > 0` and `‖φ‖ ≤ κ`. -/
theorem measure_meanDev_ge_le (P : Measure X) [IsProbabilityMeasure P] {φ : X → H} {κ : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {p k : ℕ} (hk : k ≠ 0) {f : (Fin p → X) → (Fin k → X)} (hf : Measurable f)
    (hmap : (Measure.pi fun _ : Fin p => P).map f = Measure.pi fun _ : Fin k => P) {s : ℝ} (hs : 0 < s) :
    (Measure.pi fun _ : Fin p => P) {x | s ≤ ‖meanDev P φ k (f x)‖} ≤ ENNReal.ofReal (κ / (s * √k)) := by
  set S : Set (Fin k → X) := {x | s ≤ ‖meanDev P φ k x‖} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const (measurable_norm_meanDev P hφ k)
  have hpre : {x | s ≤ ‖meanDev P φ k (f x)‖} = f ⁻¹' S := rfl
  rw [hpre, ← Measure.map_apply hf hSm, hmap]
  set Pk := Measure.pi fun _ : Fin k => P
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x)
  have hint : Integrable (fun x : Fin k → X => ‖meanDev P φ k x‖) Pk := by
    refine Integrable.of_bound (measurable_norm_meanDev P hφ k).aestronglyMeasurable (2 * κ) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_norm]
    refine (norm_sub_le _ _).trans ?_
    have hn : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
    have h1 : ‖(k : ℝ)⁻¹ • ∑ i, φ (x i)‖ ≤ κ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
      calc (k : ℝ)⁻¹ * ‖∑ i, φ (x i)‖ ≤ (k : ℝ)⁻¹ * ∑ i : Fin k, κ :=
            mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hκ (x i))) (by positivity)
        _ = κ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have h2 := norm_integral_le_of_bound (P := P) hκ
    linarith
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hint s
  have hE := integral_norm_meanDev_le (P := P) hk hφ hκ
  have hreal : Pk.real S ≤ κ / (s * √k) := by
    have hk' : (0 : ℝ) < √k := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk))
    rw [le_div_iff₀ (mul_pos hs hk')]
    have : s * Pk.real S ≤ κ / √k := hM.trans hE
    rw [le_div_iff₀ hk'] at this
    linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

end StatFormal.Alpha0Witness
