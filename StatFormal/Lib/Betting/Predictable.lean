import StatFormal.Lib.Betting.Wealth

/-!
# Testing by betting with predictable outcomes: the wealth is a nonnegative supermartingale

Library component (untrusted library code: no `Statements.lean` is involved).

## Setting

As in `Lib/Betting/Wealth.lean`, but the outcome `Y_k` need not be independent of the past `𝒢_k`: it is enough that
its conditional mean given `𝒢_k` is `≤ 0`, in the weak form `E[V Y_k] ≤ 0` for every bounded nonnegative
`𝒢_k`-measurable `V`. The bettor also starts with a `𝒢_0`-measurable capital `W_0 ∈ [0,1]` (`W_0 = 1_s` for an event
`s ∈ 𝒢_0` gives Ville's inequality conditionally on `s`).

## Main results

* `betting_supermartingale_pred`: `(W_0 · ∏_{k<t}(1 + Λ_k Y_k))_t` is a supermartingale for `𝒢`;
* `betting_ville_pred`: `a · μ{∃ t ≤ N, W_0 ∏_{k<t}(1 + Λ_k Y_k) ≥ a} ≤ E W_0` for `a > 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatFormal.Betting

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The wealth of a predictable betting strategy on outcomes with nonpositive conditional mean is a
supermartingale** (initial capital `W_0`, `𝒢_0`-measurable with values in `[0,1]`). -/
theorem betting_supermartingale_pred [IsFiniteMeasure μ] {N : ℕ} (𝒢 : Filtration ℕ m0)
    (W0 : Ω → ℝ) (Λ Y : Fin N → Ω → ℝ) (hW0 : Measurable[𝒢 0] W0) (hW0b : ∀ ω, 0 ≤ W0 ω ∧ W0 ω ≤ 1)
    (hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k)) (hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k))
    {L B : ℝ} (hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ L) (hYb : ∀ k ω, |Y k ω| ≤ B)
    (hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω)
    (hmean : ∀ k : Fin N, ∀ V : Ω → ℝ, Measurable[𝒢 k] V → (∀ ω, 0 ≤ V ω) → (∃ C, ∀ ω, V ω ≤ C) →
      ∫ ω, V ω * Y k ω ∂μ ≤ 0) :
    Supermartingale (fun t ω => W0 ω * wealthP Λ Y t ω) 𝒢 μ := by
  set M : ℕ → ℝ := fun t => ∏ _k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + L * B) with hM
  have hWt : ∀ t, Measurable[𝒢 t] (fun ω => W0 ω * wealthP Λ Y t ω) := fun t =>
    (hW0.mono (𝒢.mono (Nat.zero_le t)) le_rfl).mul (measurable_wealthP 𝒢 hY hΛ t)
  have hWt0 : ∀ t, Measurable (fun ω => W0 ω * wealthP Λ Y t ω) := fun t => (hWt t).mono (𝒢.le t) le_rfl
  have hWnn : ∀ t ω, 0 ≤ W0 ω * wealthP Λ Y t ω := fun t ω =>
    mul_nonneg (hW0b ω).1 (wealthP_nonneg hfac t ω)
  have hWle : ∀ t ω, W0 ω * wealthP Λ Y t ω ≤ M t := fun t ω => by
    have h1 := wealthP_le hΛb hYb hfac t ω
    have h2 : W0 ω * wealthP Λ Y t ω ≤ 1 * wealthP Λ Y t ω :=
      mul_le_mul_of_nonneg_right (hW0b ω).2 (wealthP_nonneg hfac t ω)
    linarith
  have hint : ∀ t, Integrable (fun ω => W0 ω * wealthP Λ Y t ω) μ := fun t =>
    Integrable.of_mem_Icc 0 (M t) (hWt0 t).aemeasurable (ae_of_all _ fun ω => ⟨hWnn t ω, hWle t ω⟩)
  have hYm : ∀ k, Measurable (Y k) := fun k => (hY k).mono (𝒢.le _) le_rfl
  have hΛm : ∀ k, Measurable (Λ k) := fun k => (hΛ k).mono (𝒢.le _) le_rfl
  refine supermartingale_of_setIntegral_succ_le
    (fun t => (hWt t).stronglyMeasurable) hint fun t s hs => ?_
  rcases lt_or_ge t N with ht | ht
  · set k : Fin N := ⟨t, ht⟩ with hk
    have hs0 : MeasurableSet s := 𝒢.le t s hs
    have hsplit : ∀ ω, W0 ω * wealthP Λ Y (t + 1) ω =
        W0 ω * wealthP Λ Y t ω + (W0 ω * wealthP Λ Y t ω * Λ k ω) * Y k ω := fun ω => by
      rw [wealthP_succ Λ Y t ht ω]; ring
    simp_rw [hsplit]
    have hb0 : ∀ ω, 0 ≤ W0 ω * wealthP Λ Y t ω * Λ k ω := fun ω => mul_nonneg (hWnn t ω) (hΛb k ω).1
    have hb1 : ∀ ω, W0 ω * wealthP Λ Y t ω * Λ k ω ≤ M t * L := fun ω =>
      mul_le_mul (hWle t ω) (hΛb k ω).2 (hΛb k ω).1 ((hWnn t ω).trans (hWle t ω))
    have hprodint : Integrable (fun ω => W0 ω * wealthP Λ Y t ω * Λ k ω * Y k ω) μ := by
      refine Integrable.of_mem_Icc (-(M t * L * B)) (M t * L * B)
        (((hWt0 t).mul (hΛm k)).mul (hYm k)).aemeasurable (ae_of_all _ fun ω => ?_)
      have h2 : |W0 ω * wealthP Λ Y t ω * Λ k ω * Y k ω| ≤ M t * L * B := by
        rw [abs_mul, abs_of_nonneg (hb0 ω)]
        exact mul_le_mul (hb1 ω) (hYb k ω) (abs_nonneg _) ((hb0 ω).trans (hb1 ω))
      exact ⟨by linarith [neg_abs_le (W0 ω * wealthP Λ Y t ω * Λ k ω * Y k ω)], (le_abs_self _).trans h2⟩
    rw [integral_add (hint t).integrableOn hprodint.integrableOn]
    set V : Ω → ℝ := s.indicator fun ω => W0 ω * wealthP Λ Y t ω * Λ k ω with hV
    have hVm : Measurable[𝒢 t] V :=
      Measurable.indicator ((hWt t).mul ((hΛ k).mono le_rfl le_rfl)) hs
    have hVnn : ∀ ω, 0 ≤ V ω := fun ω => by
      simp only [hV]
      by_cases h : ω ∈ s
      · simp only [h, Set.indicator_of_mem]; exact hb0 ω
      · simp [h]
    have hVb : ∃ C, ∀ ω, V ω ≤ C := ⟨M t * L, fun ω => by
      simp only [hV]
      by_cases h : ω ∈ s
      · simp only [h, Set.indicator_of_mem]; exact hb1 ω
      · simp only [h, not_false_eq_true, Set.indicator_of_notMem]
        exact (hb0 ω).trans (hb1 ω)⟩
    have hVY : ∫ ω in s, W0 ω * wealthP Λ Y t ω * Λ k ω * Y k ω ∂μ = ∫ ω, V ω * Y k ω ∂μ := by
      rw [← integral_indicator hs0]
      congr 1
      funext ω
      simp only [hV]
      by_cases h : ω ∈ s <;> simp [h]
    have hneg : ∫ ω in s, W0 ω * wealthP Λ Y t ω * Λ k ω * Y k ω ∂μ ≤ 0 := by
      rw [hVY]; exact hmean k V hVm hVnn hVb
    linarith
  · simp_rw [wealthP_succ_of_le Λ Y ht]
    exact le_rfl

/-- **Ville's inequality for predictable betting with initial capital `W_0`**:
`a · μ{∃ t ≤ N, W_0 ∏_{k<t}(1 + Λ_k Y_k) ≥ a} ≤ E W_0`. -/
theorem betting_ville_pred [IsFiniteMeasure μ] {N : ℕ} (𝒢 : Filtration ℕ m0)
    (W0 : Ω → ℝ) (Λ Y : Fin N → Ω → ℝ) (hW0 : Measurable[𝒢 0] W0) (hW0b : ∀ ω, 0 ≤ W0 ω ∧ W0 ω ≤ 1)
    (hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k)) (hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k))
    {L B : ℝ} (hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ L) (hYb : ∀ k ω, |Y k ω| ≤ B)
    (hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω)
    (hmean : ∀ k : Fin N, ∀ V : Ω → ℝ, Measurable[𝒢 k] V → (∀ ω, 0 ≤ V ω) → (∃ C, ∀ ω, V ω ≤ C) →
      ∫ ω, V ω * Y k ω ∂μ ≤ 0) {a : ℝ} (ha : 0 < a) :
    a * μ.real {ω | ∃ t ≤ N, a ≤ W0 ω * wealthP Λ Y t ω} ≤ ∫ ω, W0 ω ∂μ := by
  have hK := betting_supermartingale_pred 𝒢 W0 Λ Y hW0 hW0b hY hΛ hΛb hYb hfac hmean
  have h := ville_finite hK (fun t ω => mul_nonneg (hW0b ω).1 (wealthP_nonneg hfac t ω)) N ha
  simp_rw [wealthP_zero, mul_one] at h
  exact h

end StatFormal.Betting
