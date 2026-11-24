import StatFormal.Archive.Wave9b.Statements

/-!
# A calculus for the frozen `BigOP` (measurable-event `O_P`) (untrusted library)

* `prob_compl_le`, `prob_ge_of_compl_le`: `P A ≥ 1 − a ↔ P Aᶜ ≤ a` for measurable `A`.
* `bigOP_of_le_on`: if `X_n, Y_n = O_P(r_n)` with `r_n ≥ 0`, `r_n → 0`, and `T_n ≤ C (X_n + Y_n)` wherever
  `X_n ≤ δ` (a fixed `δ > 0`), then `T_n = O_P(r_n)`. This discards the events of vanishing probability on which
  `X_n` is not small (e.g. an estimated covariance far from the population one).
* Corollaries: `bigOP_zero`, `bigOP_mono`, `bigOP_add`, `bigOP_const_mul`, `bigOP_mul`, `bigOP_finset_sum`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace StatFormal.MatrixSqrtPerturb

open StatFormal.Wave9b (BigOP)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma prob_compl_le [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) {a : ℝ} (ha : 0 ≤ a)
    (h : ENNReal.ofReal (1 - a) ≤ P A) : P Aᶜ ≤ ENNReal.ofReal a := by
  rw [prob_compl_eq_one_sub hA]
  rcases le_total a 1 with h1 | h1
  · rw [ENNReal.ofReal_sub _ ha, ENNReal.ofReal_one] at h
    calc 1 - P A ≤ 1 - (1 - ENNReal.ofReal a) := tsub_le_tsub_left h _
      _ = ENNReal.ofReal a := ENNReal.sub_sub_cancel ENNReal.one_ne_top
          (by simpa using ENNReal.ofReal_le_ofReal h1)
  · calc 1 - P A ≤ 1 := tsub_le_self
      _ ≤ ENNReal.ofReal a := by simpa using ENNReal.ofReal_le_ofReal h1

lemma prob_ge_of_compl_le [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) {a : ℝ} (ha : 0 ≤ a)
    (h : P Aᶜ ≤ ENNReal.ofReal a) : ENNReal.ofReal (1 - a) ≤ P A := by
  rw [prob_compl_eq_one_sub hA] at h
  rcases le_total a 1 with h1 | h1
  · rw [ENNReal.ofReal_sub _ ha, ENNReal.ofReal_one]
    have hPA : P A ≤ 1 := prob_le_one
    calc 1 - ENNReal.ofReal a ≤ 1 - (1 - P A) := tsub_le_tsub_left h _
      _ = P A := ENNReal.sub_sub_cancel ENNReal.one_ne_top hPA
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact bot_le

/-- Two events of probability `≥ 1 − η/2` meet in an event of probability `≥ 1 − η`. -/
lemma prob_inter_ge [IsProbabilityMeasure P] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {η : ℝ} (hη : 0 ≤ η) (hPA : ENNReal.ofReal (1 - η / 2) ≤ P A) (hPB : ENNReal.ofReal (1 - η / 2) ≤ P B) :
    ENNReal.ofReal (1 - η) ≤ P (A ∩ B) := by
  have h2 : 0 ≤ η / 2 := by linarith
  refine prob_ge_of_compl_le (hA.inter hB) hη ?_
  calc P (A ∩ B)ᶜ ≤ P Aᶜ + P Bᶜ := by rw [Set.compl_inter]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add (prob_compl_le hA h2 hPA) (prob_compl_le hB h2 hPB)
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add h2 h2]; congr 1; ring

/-- **The main combinator.** -/
theorem bigOP_of_le_on [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n)
    (hr0 : Tendsto r atTop (𝓝 0)) {X Y T : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) (hY : BigOP P r Y) {δ C : ℝ}
    (hδ : 0 < δ) (N0 : ℕ)
    (h : ∀ n ≥ N0, ∀ ω, X n ω ≤ ENNReal.ofReal δ → T n ω ≤ ENNReal.ofReal C * (X n ω + Y n ω)) :
    BigOP P r T := by
  intro η hη
  obtain ⟨M1, N1, h1⟩ := hX (η / 2) (by positivity)
  obtain ⟨M2, N2, h2⟩ := hY (η / 2) (by positivity)
  set M1' := max M1 0
  set M2' := max M2 0
  have hev : ∀ᶠ n in atTop, M1' * r n < δ := by
    have := hr0.const_mul M1'
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  obtain ⟨N3, hN3⟩ := eventually_atTop.mp hev
  refine ⟨max C 0 * (M1' + M2'), max (max (max N1 N2) N3) N0, fun n hn' => ?_⟩
  have hn : max (max N1 N2) N3 ≤ n := le_trans (le_max_left _ _) hn'
  have hn0 : N0 ≤ n := le_trans (le_max_right _ _) hn'
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨A1, hA1m, hA1P, hA1⟩ := h1 n hn1
  obtain ⟨A2, hA2m, hA2P, hA2⟩ := h2 n hn2
  refine ⟨A1 ∩ A2, hA1m.inter hA2m, prob_inter_ge hA1m hA2m hη.le hA1P hA2P, fun ω hω => ?_⟩
  have hX1 : X n ω ≤ ENNReal.ofReal (M1' * r n) :=
    (hA1 ω hω.1).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (hr n)))
  have hY1 : Y n ω ≤ ENNReal.ofReal (M2' * r n) :=
    (hA2 ω hω.2).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (hr n)))
  have hsmall : X n ω ≤ ENNReal.ofReal δ := hX1.trans (ENNReal.ofReal_le_ofReal (hN3 n hn3).le)
  have hM1 : 0 ≤ M1' * r n := mul_nonneg (le_max_right _ _) (hr n)
  have hM2 : 0 ≤ M2' * r n := mul_nonneg (le_max_right _ _) (hr n)
  calc T n ω ≤ ENNReal.ofReal C * (X n ω + Y n ω) := h n hn0 ω hsmall
    _ ≤ ENNReal.ofReal (max C 0) * (ENNReal.ofReal (M1' * r n) + ENNReal.ofReal (M2' * r n)) := by
        gcongr; exact le_max_left _ _
    _ = ENNReal.ofReal (max C 0 * (M1' + M2') * r n) := by
        rw [← ENNReal.ofReal_add hM1 hM2, ← ENNReal.ofReal_mul (le_max_right _ _)]
        congr 1; ring

lemma bigOP_zero [IsProbabilityMeasure P] (r : ℕ → ℝ) : BigOP P r (fun _ _ => 0) := by
  intro η _
  refine ⟨0, 0, fun n _ => ⟨Set.univ, MeasurableSet.univ, ?_, fun _ _ => zero_le⟩⟩
  rw [measure_univ]
  exact ENNReal.ofReal_le_one.mpr (by linarith)

lemma bigOP_mono [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hr0 : Tendsto r atTop (𝓝 0))
    {X T : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) (h : ∀ n ω, T n ω ≤ X n ω) : BigOP P r T :=
  bigOP_of_le_on hr hr0 hX (bigOP_zero r) (δ := 1) (C := 1) one_pos 0 fun n _ ω _ => by
    simpa using h n ω

/-- Monotonicity from some index on. -/
lemma bigOP_mono_of_ge [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hr0 : Tendsto r atTop (𝓝 0))
    {X T : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) (N0 : ℕ) (h : ∀ n ≥ N0, ∀ ω, T n ω ≤ X n ω) : BigOP P r T :=
  bigOP_of_le_on hr hr0 hX (bigOP_zero r) (δ := 1) (C := 1) one_pos N0 fun n hn ω _ => by
    simpa using h n hn ω

lemma bigOP_add [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hr0 : Tendsto r atTop (𝓝 0))
    {X Y : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) (hY : BigOP P r Y) : BigOP P r (fun n ω => X n ω + Y n ω) :=
  bigOP_of_le_on hr hr0 hX hY (δ := 1) (C := 1) one_pos 0 fun n _ ω _ => by simp

lemma bigOP_const_mul [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hr0 : Tendsto r atTop (𝓝 0))
    {X : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) (c : ℝ) : BigOP P r (fun n ω => ENNReal.ofReal c * X n ω) :=
  bigOP_of_le_on hr hr0 hX (bigOP_zero r) (δ := 1) (C := c) one_pos 0 fun n _ ω _ => by simp

/-- A product of two `O_P(r_n)` terms is `O_P(r_n)` (it is even `O_P(r_n²)`). -/
lemma bigOP_mul [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hr0 : Tendsto r atTop (𝓝 0))
    {X Y : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) (hY : BigOP P r Y) : BigOP P r (fun n ω => X n ω * Y n ω) :=
  bigOP_of_le_on hr hr0 hX hY (δ := 1) (C := 1) one_pos 0 fun n _ ω hx => by
    rw [ENNReal.ofReal_one] at hx ⊢
    calc X n ω * Y n ω ≤ 1 * Y n ω := by gcongr
      _ ≤ 1 * (X n ω + Y n ω) := by gcongr; exact le_add_self

lemma bigOP_finset_sum [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n)
    (hr0 : Tendsto r atTop (𝓝 0)) {ι : Type*} (s : Finset ι) {X : ι → ℕ → Ω → ℝ≥0∞}
    (hX : ∀ i ∈ s, BigOP P r (X i)) : BigOP P r (fun n ω => ∑ i ∈ s, X i n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bigOP_zero (P := P) r
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact bigOP_add hr hr0 (hX a (Finset.mem_insert_self a s))
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

/-- The rate `n^{-1/2}` is nonnegative and tends to `0`. -/
lemma rate_nonneg (n : ℕ) : 0 ≤ 1 / Real.sqrt n := by positivity

lemma rate_tendsto : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have := h.inv_tendsto_atTop
  simpa [one_div, Function.comp_def, Pi.inv_def] using this

lemma rate_le_one {n : ℕ} (hn : 1 ≤ n) : 1 / Real.sqrt n ≤ 1 := by
  have : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  rw [div_le_one (by linarith)]; exact this

end StatFormal.MatrixSqrtPerturb
