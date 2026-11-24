import StatFormal.Lib.Bernstein.SampleVariance

/-!
# The empirical Bernstein inequality (Maurer–Pontil 2009, Thm 4)

Library component F.B (part 6). Untrusted library code: no `Statements.lean` is involved.

Setting of `Bernstein.lean`: `Z_i = g(ω i)` i.i.d. under `ν^n`; `sampleMean`, `sampleVar`
(`V_n = (1/(n(n−1))) Σ_{i<j} (Z_i − Z_j)²`), `popMean`.

## Main results

* `empirical_bernstein`: for `g ∈ [0,1]`, `n ≥ 2`, `0 < δ ≤ 1`,
  `P(√(2 V_n log(2/δ)/n) + 7 log(2/δ)/(3(n−1)) < E Z − Z̄) ≤ δ` — exactly Maurer–Pontil's Thm 4
  (Bernstein at `δ/2` + sample-standard-deviation bound at `δ/2`);
* `empirical_bernstein_ge`: the same as `P(E Z − Z̄ ≤ bound) ≥ 1 − δ`;
* `empirical_bernstein_Icc`: **rescaled form** used by JASA `prop:allpairs`: for `g ∈ [a, a+b]`,
  `b ≥ 0`, `P(√(2 V_n log(2/δ)/n) + 7 b log(2/δ)/(3(n−1)) < E Z − Z̄) ≤ δ`;
* `empirical_bernstein_Icc_of_le`: the same with `V_n` replaced by any pointwise upper bound
  (the observable envelope `V_v ≥ V_n` of `prop:allpairs`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set

namespace StatFormal.Bernstein

variable {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]

theorem measurable_sampleMean {n : ℕ} {g : β → ℝ} (hg : Measurable g) :
    Measurable (sampleMean (n := n) g) :=
  (Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)).div_const _

/-- **Empirical Bernstein inequality** (Maurer–Pontil 2009, Thm 4): for i.i.d. `Z_i ∈ [0,1]`,
`n ≥ 2` and `0 < δ ≤ 1`, with probability at least `1 − δ`,
`E Z − Z̄ ≤ √(2 V_n log(2/δ)/n) + 7 log(2/δ)/(3(n−1))`. -/
theorem empirical_bernstein {g : β → ℝ} (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(2 * sampleVar g ω * log (2 / δ) / n) + 7 * log (2 / δ) / (3 * (n - 1)) <
        popMean ν g - sampleMean g ω} ≤ δ := by
  set P := Measure.pi fun _ : Fin n => ν with hP
  set L := log (2 / δ) with hL
  have hL' : log (1 / (δ / 2)) = L := by rw [hL]; congr 1; field_simp
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ21 : δ / 2 ≤ 1 := by linarith
  have hL0 : 0 ≤ L := log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hA := bernstein ν hg hg01 (by omega : 0 < n) hδ2 hδ21
  have hB := sqrt_popVar_le ν hg hg01 hn hδ2 hδ21
  rw [hL'] at hA hB
  set A := {ω : Fin n → β | √(2 * popVar ν g * L / n) + L / (3 * n) ≤
    popMean ν g - sampleMean g ω} with hAdef
  set B := {ω : Fin n → β | √(sampleVar g ω) + √(2 * L / (n - 1)) ≤ √(popVar ν g)} with hBdef
  have hsub : {ω | √(2 * sampleVar g ω * L / n) + 7 * L / (3 * (n - 1)) <
      popMean ν g - sampleMean g ω} ⊆ A ∪ B := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or, hAdef, hBdef, mem_ofPred_eq, not_le] at hnot hω
    obtain ⟨h1, h2⟩ := hnot
    set V := sampleVar g ω
    have hV0 : 0 ≤ V := sampleVar_nonneg (by omega) g ω
    set σ := √(popVar ν g)
    set a := √(2 * L / n) with ha
    set c := √(2 * L / (n - 1)) with hc
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hac : a ≤ c := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) hn1
      (by linarith))
    have hc2 : c ^ 2 = 2 * L / (n - 1) := Real.sq_sqrt (by positivity)
    have hs1 : √(2 * popVar ν g * L / n) = σ * a := by
      rw [show 2 * popVar ν g * L / n = popVar ν g * (2 * L / n) by ring,
        Real.sqrt_mul (popVar_nonneg ν g)]
    have hs2 : √(2 * V * L / n) = √V * a := by
      rw [show 2 * V * L / n = V * (2 * L / n) by ring, Real.sqrt_mul hV0]
    rw [hs1] at h1
    rw [hs2] at hω
    have h3 : σ * a ≤ (√V + c) * a := mul_le_mul_of_nonneg_right h2.le ha0
    have h4 : c * a ≤ c ^ 2 := by nlinarith [Real.sqrt_nonneg (2 * L / (n - 1))]
    have h5 : L / (3 * n) ≤ L / (3 * (n - 1)) :=
      div_le_div_of_nonneg_left hL0 (by positivity) (by linarith)
    have h6 : 7 * L / (3 * (n - 1)) = 2 * L / (n - 1) + L / (3 * (n - 1)) := by
      field_simp; ring
    rw [h6, ← hc2] at hω
    nlinarith
  calc P.real _ ≤ P.real (A ∪ B) := measureReal_mono hsub
    _ ≤ P.real A + P.real B := measureReal_union_le A B
    _ ≤ δ / 2 + δ / 2 := add_le_add hA hB
    _ = δ := by ring

/-- **Empirical Bernstein inequality**, high-probability form:
`P(E Z − Z̄ ≤ √(2 V_n log(2/δ)/n) + 7 log(2/δ)/(3(n−1))) ≥ 1 − δ`. -/
theorem empirical_bernstein_ge {g : β → ℝ} (hg : Measurable g)
    (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => ν).real
      {ω | popMean ν g - sampleMean g ω ≤
        √(2 * sampleVar g ω * log (2 / δ) / n) + 7 * log (2 / δ) / (3 * (n - 1))} := by
  have hmeas : MeasurableSet {ω : Fin n → β |
      √(2 * sampleVar g ω * log (2 / δ) / n) + 7 * log (2 / δ) / (3 * (n - 1)) <
        popMean ν g - sampleMean g ω} :=
    measurableSet_lt (((((measurable_sampleVar hg).const_mul 2).mul_const _).div_const _).sqrt.add
      measurable_const) (measurable_const.sub (measurable_sampleMean hg))
  have hc : {ω : Fin n → β | popMean ν g - sampleMean g ω ≤
      √(2 * sampleVar g ω * log (2 / δ) / n) + 7 * log (2 / δ) / (3 * (n - 1))} =
      {ω | √(2 * sampleVar g ω * log (2 / δ) / n) + 7 * log (2 / δ) / (3 * (n - 1)) <
        popMean ν g - sampleMean g ω}ᶜ := by
    ext ω; simp [not_lt]
  rw [hc, measureReal_compl hmeas, probReal_univ]
  linarith [empirical_bernstein ν hg hg01 hn hδ0 hδ1]

/-! ### Rescaling to an interval of length `b` -/

omit [IsProbabilityMeasure ν] in
private theorem popMean_affine (hν : IsProbabilityMeasure ν) {g : β → ℝ} (hg : Measurable g)
    {a b : ℝ} (hgab : ∀ x, g x ∈ Icc a (a + b)) :
    popMean ν (fun x => (g x - a) / b) = (popMean ν g - a) / b := by
  have hgi : Integrable g ν :=
    Integrable.of_mem_Icc a (a + b) hg.aemeasurable (ae_of_all _ hgab)
  unfold popMean
  rw [integral_div, integral_sub hgi (integrable_const a), integral_const]
  simp

omit [MeasurableSpace β] in
private theorem sampleMean_affine {n : ℕ} (g : β → ℝ) (a b : ℝ) (ω : Fin n → β) (hn : 0 < n) :
    sampleMean (fun x => (g x - a) / b) ω = (sampleMean g ω - a) / b := by
  unfold sampleMean
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [MeasurableSpace β] in
private theorem sampleVar_affine {n : ℕ} (g : β → ℝ) (a b : ℝ) (ω : Fin n → β) :
    sampleVar (fun x => (g x - a) / b) ω = sampleVar g ω / b ^ 2 := by
  unfold sampleVar
  have h : ∀ i j : Fin n, (if i < j then ((g (ω i) - a) / b - (g (ω j) - a) / b) ^ 2 else 0) =
      (if i < j then (g (ω i) - g (ω j)) ^ 2 else 0) * (b ^ 2)⁻¹ := fun i j => by
    split_ifs
    · rw [div_sub_div_same, sub_sub_sub_cancel_right, div_pow, div_eq_mul_inv]
    · simp
  simp_rw [h, ← Finset.sum_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Rescaled empirical Bernstein inequality** (the form of JASA `prop:allpairs`): for i.i.d.
`Z_i ∈ [a, a + b]`, `b ≥ 0`, `n ≥ 2`, `0 < δ ≤ 1`, with probability at least `1 − δ`,
`E Z − Z̄ ≤ √(2 V_n log(2/δ)/n) + 7 b log(2/δ)/(3(n−1))`. -/
theorem empirical_bernstein_Icc {g : β → ℝ} (hg : Measurable g) {a b : ℝ} (hb : 0 ≤ b)
    (hgab : ∀ x, g x ∈ Icc a (a + b)) {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(2 * sampleVar g ω * log (2 / δ) / n) + 7 * b * log (2 / δ) / (3 * (n - 1)) <
        popMean ν g - sampleMean g ω} ≤ δ := by
  set L := log (2 / δ) with hL
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  rcases hb.eq_or_lt with h0 | hbpos
  · -- `b = 0`: `g` is constant and the event is empty
    have hga : ∀ x, g x = a := fun x => by
      have := hgab x; rw [← h0, add_zero] at this; exact le_antisymm this.2 this.1
    have hempty : {ω : Fin n → β | √(2 * sampleVar g ω * L / n) + 7 * b * L / (3 * (n - 1)) <
        popMean ν g - sampleMean g ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      have hm : popMean ν g = a := by simp [popMean, hga]
      have hs : sampleMean g ω = a := by
        unfold sampleMean
        simp only [hga, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      rw [hm, hs, sub_self, ← h0]
      simp only [mul_zero, zero_mul, zero_div, add_zero]
      exact Real.sqrt_nonneg _
    rw [hempty]
    simp [hδ0.le]
  -- `b > 0`: apply the `[0,1]` result to `(g − a)/b`
  set g' : β → ℝ := fun x => (g x - a) / b with hg'
  have hg'm : Measurable g' := (hg.sub measurable_const).div_const b
  have hg'01 : ∀ x, g' x ∈ Icc (0 : ℝ) 1 := fun x => by
    have := hgab x
    simp only [hg', mem_Icc]
    constructor
    · exact div_nonneg (by linarith [this.1]) hbpos.le
    · rw [div_le_one hbpos]; linarith [this.2]
  have h := empirical_bernstein ν hg'm hg'01 hn hδ0 hδ1
  refine (measureReal_mono fun ω hω => ?_).trans h
  simp only [mem_ofPred_eq] at hω ⊢
  rw [hg', popMean_affine ν inferInstance hg hgab, sampleMean_affine g a b ω (by omega),
    sampleVar_affine g a b ω]
  have hV0 := sampleVar_nonneg (by omega) g ω
  have hsq : √(2 * (sampleVar g ω / b ^ 2) * L / n) = √(2 * sampleVar g ω * L / n) / b := by
    rw [show 2 * (sampleVar g ω / b ^ 2) * L / n = (2 * sampleVar g ω * L / n) / b ^ 2 by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hbpos.le]
  rw [hsq, show (popMean ν g - a) / b - (sampleMean g ω - a) / b =
    (popMean ν g - sampleMean g ω) / b by ring]
  rw [lt_div_iff₀ hbpos]
  calc (√(2 * sampleVar g ω * L / n) / b + 7 * L / (3 * (n - 1))) * b
      = √(2 * sampleVar g ω * L / n) + 7 * b * L / (3 * (n - 1)) := by
        field_simp
    _ < popMean ν g - sampleMean g ω := hω

/-- Rescaled empirical Bernstein inequality with any pointwise upper bound `Vup ≥ V_n` in place of
the sample variance (the bound is nondecreasing in the variance term). -/
theorem empirical_bernstein_Icc_of_le {g : β → ℝ} (hg : Measurable g) {a b : ℝ} (hb : 0 ≤ b)
    (hgab : ∀ x, g x ∈ Icc a (a + b)) {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (Vup : (Fin n → β) → ℝ) (hV : ∀ ω, sampleVar g ω ≤ Vup ω) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(2 * Vup ω * log (2 / δ) / n) + 7 * b * log (2 / δ) / (3 * (n - 1)) <
        popMean ν g - sampleMean g ω} ≤ δ := by
  refine (measureReal_mono fun ω hω => ?_).trans
    (empirical_bernstein_Icc ν hg hb hgab hn hδ0 hδ1)
  simp only [mem_ofPred_eq] at hω ⊢
  have hL : 0 ≤ log (2 / δ) := log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine lt_of_le_of_lt (add_le_add (Real.sqrt_le_sqrt ?_) le_rfl) hω
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hV ω) (by norm_num)) hL) hnR.le

end StatFormal.Bernstein
