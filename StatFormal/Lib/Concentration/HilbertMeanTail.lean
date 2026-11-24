import StatFormal.Lib.Concentration.HilbertMean
import TauCeti.Probability.McDiarmid

/-!
# Hilbert-space sample means: high-probability bound (McDiarmid)

Library component (concentration, part 2). Untrusted library code. Setting and `meanDev` as in
`StatFormal/Foundations/Concentration/HilbertMean.lean`; probabilities are `Measure.real` of the
product measure `Measure.pi (fun _ : Fin n => P)`.

## Main results

* `abs_norm_meanDev_update_sub_le`: `x ↦ ‖meanDev x‖` has bounded differences `2κ/n`;
* `hasSubgaussianMGF_norm_meanDev`: the centred norm is sub-Gaussian with proxy `κ²/n`
  (Tau Ceti's McDiarmid `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin`);
* `one_sub_le_measureReal_norm_meanDev_le`: for `n ≠ 0`, `0 < δ ≤ 1`, with probability
  `≥ 1 − δ`, `‖meanDev‖ ≤ κ/√n + κ √(2 log(1/δ)/n)`;
* `one_sub_le_measureReal_norm_meanDev_le_paper`: the paper's constants, for `n ≥ 1`,
  `0 < δ < 1`: with probability `≥ 1 − δ`, `‖meanDev‖ ≤ 4κ/√n + κ √(2 log(2/δ)/n)`;
* `abs_inner_meanDev_le` / `inner_meanDev_eq_norm`: dual-norm form — for `‖g‖ ≤ 1`,
  `|(1/n)∑⟪g,φ(xᵢ)⟫ − ∫⟪g,φ⟫ dP| ≤ ‖meanDev x‖`, with equality attained at
  `g = meanDev x / ‖meanDev x‖`; i.e. `sup_{‖g‖≤1} |(Pₙ − P)⟪g, φ ·⟫| = ‖meanDev x‖`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace StatFormal.Concentration

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
variable {P : Measure X} [IsProbabilityMeasure P] {φ : X → H} {κ : ℝ}

theorem stronglyMeasurable_meanDev (hφ : StronglyMeasurable φ) (n : ℕ) :
    StronglyMeasurable (meanDev P φ n) := by
  refine StronglyMeasurable.sub ?_ stronglyMeasurable_const
  refine StronglyMeasurable.const_smul ?_ _
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hφ.comp_measurable (measurable_pi_apply i)

theorem measurable_norm_meanDev (hφ : StronglyMeasurable φ) (n : ℕ) :
    Measurable fun x => ‖meanDev P φ n x‖ :=
  (stronglyMeasurable_meanDev hφ n).norm.measurable

/-- **Bounded differences**: changing one coordinate moves `‖meanDev‖` by at most `2κ/n`. -/
theorem abs_norm_meanDev_update_sub_le (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ} (x : Fin n → X)
    (i : Fin n) (b : X) :
    |‖meanDev P φ n (Function.update x i b)‖ - ‖meanDev P φ n x‖| ≤ 2 * κ / n := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have hdiff : meanDev P φ n (Function.update x i b) - meanDev P φ n x =
      (n : ℝ)⁻¹ • (φ b - φ (x i)) := by
    simp only [meanDev]
    rw [sub_sub_sub_cancel_right, ← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Function.update_of_ne hj]
    · simp
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  gcongr
  exact (norm_sub_le _ _).trans (by linarith [hκ b, hκ (x i)])

/-- **McDiarmid** for the Hilbert-space sample mean: the centred norm is sub-Gaussian with
variance proxy `κ²/n` (as an `ℝ≥0` expression; see `coe_proxy`). -/
theorem hasSubgaussianMGF_norm_meanDev (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (n : ℕ) :
    HasSubgaussianMGF
      (fun x => ‖meanDev P φ n x‖ - ∫ y, ‖meanDev P φ n y‖ ∂(Measure.pi fun _ : Fin n => P))
      ((n : ℝ≥0) * ((2 * κ / n).toNNReal / 2) ^ 2) (Measure.pi fun _ : Fin n => P) :=
  TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin P (fun x => ‖meanDev P φ n x‖)
    (measurable_norm_meanDev hφ n) (2 * κ / n)
    (fun x i b => abs_norm_meanDev_update_sub_le hκ x i b)

theorem coe_proxy {n : ℕ} (hn : n ≠ 0) (hκ0 : 0 ≤ κ) :
    (((n : ℝ≥0) * ((2 * κ / n).toNNReal / 2) ^ 2 : ℝ≥0) : ℝ) = κ ^ 2 / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  push_cast [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 2 * κ / n)]
  field_simp

/-- **High-probability bound**: for `n ≠ 0` and `0 < δ ≤ 1`, with probability at least `1 − δ`,
`‖(1/n) ∑ φ(Xᵢ) − Eφ‖ ≤ κ/√n + κ √(2 log(1/δ)/n)`. -/
theorem one_sub_le_measureReal_norm_meanDev_le {n : ℕ} (hn : n ≠ 0) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => P).real
      {x | ‖meanDev P φ n x‖ ≤ κ / √n + κ * √(2 * log (1 / δ) / n)} := by
  set Pn := Measure.pi fun _ : Fin n => P
  set F : (Fin n → X) → ℝ := fun x => ‖meanDev P φ n x‖ with hF
  set ε := κ * √(2 * log (1 / δ) / n) with hε
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hL : 0 ≤ log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hε0 : 0 ≤ ε := by positivity
  set B := {x | κ / √n + ε < F x} with hB
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (measurable_norm_meanDev hφ n)
  have hcompl : {x | ‖meanDev P φ n x‖ ≤ κ / √n + ε} = Bᶜ := by
    ext x; simp [hB, hF, not_lt]
  rw [hcompl, probReal_compl_eq_one_sub hBm]
  suffices Pn.real B ≤ δ by linarith
  rcases hκ0.eq_or_lt with hκe | hκpos
  · -- `κ = 0`: `φ = 0`, so `meanDev = 0` and `B = ∅`.
    subst hκe
    have hφ0 : φ = 0 := funext fun x => norm_le_zero_iff.1 (hκ x)
    have : B = ∅ := by
      ext x; simp [hB, hF, meanDev, hφ0, hε]
    rw [this, measureReal_empty]; exact hδ0.le
  · have hE := integral_norm_meanDev_le (P := P) hn hφ hκ
    have hsub : B ⊆ {x | ε ≤ F x - ∫ y, F y ∂Pn} := by
      intro x hx
      simp only [hB, Set.mem_ofPred_eq] at hx ⊢
      change κ / √n + ε < F x at hx
      have : ∫ y, F y ∂Pn ≤ κ / √n := hE
      linarith
    have htail := (hasSubgaussianMGF_norm_meanDev (P := P) hφ hκ n).measure_ge_le hε0
    rw [coe_proxy hn hκ0] at htail
    have hexp : -ε ^ 2 / (2 * (κ ^ 2 / n)) = -log (1 / δ) := by
      rw [hε, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    rw [hexp, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv] at htail
    exact (measureReal_mono hsub).trans htail

/-- **The paper's constants** (`trimmed-mmd` `thm:concentration`, ball part): for `n ≥ 1` and
`0 < δ < 1`, with probability at least `1 − δ`,
`‖(1/n) ∑ φ(Xᵢ) − Eφ‖ ≤ 4κ/√n + κ √(2 log(2/δ)/n)`. -/
theorem one_sub_le_measureReal_norm_meanDev_le_paper {n : ℕ} (hn : 1 ≤ n)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => P).real
      {x | ‖meanDev P φ n x‖ ≤ 4 * κ / √n + κ * √(2 * log (2 / δ) / n)} := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x)
  refine (one_sub_le_measureReal_norm_meanDev_le hn0 hφ hκ hδ0 hδ1.le).trans
    (measureReal_mono ?_)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have h1 : κ / √n ≤ 4 * κ / √n := by
    gcongr; linarith
  have h2 : κ * √(2 * log (1 / δ) / n) ≤ κ * √(2 * log (2 / δ) / n) := by
    gcongr
    norm_num
  linarith

/-! ### Dual-norm form -/

/-- `⟪g, meanDev x⟫ = (Pₙ − P)⟪g, φ ·⟫` (for bounded strongly measurable `φ`). -/
theorem inner_meanDev (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ} (g : H)
    (x : Fin n → X) :
    inner ℝ g (meanDev P φ n x) =
      (n : ℝ)⁻¹ * ∑ i, inner ℝ g (φ (x i)) - ∫ y, inner ℝ g (φ y) ∂P := by
  rw [meanDev, inner_sub_right, real_inner_smul_right, inner_sum,
    integral_inner (integrable_of_bound hφ hκ) g]

/-- Over the unit ball, `|(Pₙ − P)⟪g, φ ·⟫| ≤ ‖meanDev x‖`. -/
theorem abs_inner_meanDev_le (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ}
    {g : H} (hg : ‖g‖ ≤ 1) (x : Fin n → X) :
    |(n : ℝ)⁻¹ * ∑ i, inner ℝ g (φ (x i)) - ∫ y, inner ℝ g (φ y) ∂P| ≤
      ‖meanDev P φ n x‖ := by
  rw [← inner_meanDev hφ hκ g x]
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖g‖ * ‖meanDev P φ n x‖ ≤ 1 * ‖meanDev P φ n x‖ := by gcongr
    _ = _ := one_mul _

/-- The supremum over the unit ball is attained: some `‖g‖ ≤ 1` has
`(Pₙ − P)⟪g, φ ·⟫ = ‖meanDev x‖`. -/
theorem exists_inner_meanDev_eq_norm (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    {n : ℕ} (x : Fin n → X) :
    ∃ g : H, ‖g‖ ≤ 1 ∧
      (n : ℝ)⁻¹ * ∑ i, inner ℝ g (φ (x i)) - ∫ y, inner ℝ g (φ y) ∂P = ‖meanDev P φ n x‖ := by
  set v := meanDev P φ n x
  by_cases hv : v = 0
  · exact ⟨0, by simp, by rw [← inner_meanDev hφ hκ 0 x]; simp [v, hv]⟩
  · refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
    · rw [← inner_meanDev hφ hκ _ x, real_inner_smul_left, real_inner_self_eq_norm_sq]
      have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
      field_simp

end StatFormal.Concentration
