import StatFormal.Lib.IntervalDev.SetBernstein
import StatFormal.Lib.Bernstein.Empirical
import StatFormal.Lib.NormalScores.Atomless

set_option linter.style.longLine false

/-!
# Relative deviations of empirical frequencies of intervals (atomless laws on the line)

Let `P` be an atomless probability on `ℝ` with distribution function `F`, `n ≥ 1` and `L ≥ 0`. With probability at
least `1 − 2(n+1)²e^{−L}` under `P^{⊗n}`, **every** interval (order-connected set) `I ⊆ ℝ` satisfies
`|P̃(I) − P(I)| ≤ √(2P(I)L/n) + (2L+4)/n`, with `P̃(I) = (1/n)#{i : ω_i ∈ I}` (`sampleMean (I.indicator 1) ω`).
This is the ratio bound of trimmed-mmd S4, Lemma S4.23 (`lem:lapintervals`, `x = L`, `c_x = 2x + 4`).

## Route (printed: probability integral transform, a grid, Bernstein, a union bound, a sandwich)

* `F_*P` is uniform on `[0,1]` (Tau Ceti's `Measure.cdf_map_eq_volume_restrict`), so the grid sets
  `F⁻¹[k/n, l/n]` (`gridC`) and `F⁻¹(k/n, l/n)` (`gridO`) have probability `(l − k)/n` (`measureReal_cdf_Icc`,
  `le_measureReal_cdf_Ioo`);
* Bernstein's inequality (`prob_upper_dev_le` on the closed grid sets, `prob_lower_dev_le` on the open ones) and a
  union bound over the `2(n+1)²` one-sided events;
* the deterministic sandwich (`abs_sampleMean_sub_le_of_grid`): for an interval `I` with `lo = inf F(I)`,
  `hi = sup F(I)`, `F⁻¹(lo, hi) ⊆ I ⊆ F⁻¹[lo, hi]`, so `P(I) = hi − lo`, and the grid sets
  `F⁻¹(⌈n lo⌉/n, ⌊n hi⌋/n) ⊆ I ⊆ F⁻¹[⌊n lo⌋/n, ⌈n hi⌉/n]` differ from `P(I)` by at most `2/n`; the cost
  `(2√L + 2)/n` is absorbed by `2√L + 2L/3 + 2 ≤ 2L + 4` (here even `L/3` in place of `2L/3`).
  No almost-sure event is needed: the sandwich is deterministic.

## Main results

* `abs_sampleMean_sub_le_of_grid` (deterministic), `exists_interval_event` (the event and its probability).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real

namespace StatFormal.IntervalDev

open StatFormal.Bernstein

/-- The closed grid set `F⁻¹[k/n, l/n]`. -/
def gridC (P : Measure ℝ) (n k l : ℕ) : Set ℝ := {y | (k : ℝ) / n ≤ cdf P y ∧ cdf P y ≤ (l : ℝ) / n}

/-- The open grid set `F⁻¹(k/n, l/n)`. -/
def gridO (P : Measure ℝ) (n k l : ℕ) : Set ℝ := {y | (k : ℝ) / n < cdf P y ∧ cdf P y < (l : ℝ) / n}

theorem measurableSet_gridC (P : Measure ℝ) (n k l : ℕ) : MeasurableSet (gridC P n k l) :=
  (NormalScores.measurable_cdf' P) measurableSet_Icc

theorem measurableSet_gridO (P : Measure ℝ) (n k l : ℕ) : MeasurableSet (gridO P n k l) :=
  (NormalScores.measurable_cdf' P) measurableSet_Ioo

/-- The empirical frequency is monotone in the set. -/
theorem sampleMean_indicator_mono {β : Type*} {n : ℕ} {A B : Set β} (hAB : A ⊆ B) (ω : Fin n → β) :
    sampleMean (A.indicator (1 : β → ℝ)) ω ≤ sampleMean (B.indicator 1) ω := by
  unfold sampleMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact Finset.sum_le_sum fun i _ => indicator_le_indicator_of_subset hAB (fun _ => zero_le_one) _

section PIT

variable (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P]

/-- The probability integral transform: `P(F⁻¹ J) = |J ∩ [0,1]|`. -/
theorem measure_cdf_preimage {J : Set ℝ} (hJ : MeasurableSet J) :
    P (cdf P ⁻¹' J) = volume (J ∩ Icc 0 1) := by
  rw [← Measure.map_apply (NormalScores.measurable_cdf' P) hJ, Measure.cdf_map_eq_volume_restrict,
    Measure.restrict_apply hJ]

theorem measureReal_cdf_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    P.real {y | a ≤ cdf P y ∧ cdf P y ≤ b} = b - a := by
  have : {y | a ≤ cdf P y ∧ cdf P y ≤ b} = cdf P ⁻¹' Icc a b := rfl
  rw [this, measureReal_def, measure_cdf_preimage P measurableSet_Icc,
    inter_eq_left.2 (Icc_subset_Icc ha hb), Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

theorem le_measureReal_cdf_Ioo {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    b - a ≤ P.real {y | a < cdf P y ∧ cdf P y < b} := by
  have : {y | a < cdf P y ∧ cdf P y < b} = cdf P ⁻¹' Ioo a b := rfl
  rw [this, measureReal_def, measure_cdf_preimage P measurableSet_Ioo,
    inter_eq_left.2 (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hb)), Real.volume_Ioo,
    ENNReal.toReal_ofReal']
  exact le_max_left _ _

/-- **Deterministic sandwich.** If the one-sided Bernstein bounds hold on every closed grid set (upper) and every open
grid set (lower), then every interval `I` has `|P̃(I) − P(I)| ≤ √(2P(I)L/n) + (2L+4)/n`. -/
theorem abs_sampleMean_sub_le_of_grid {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) (ω : Fin n → ℝ)
    (hc : ∀ k ≤ n, ∀ l ≤ n, sampleMean ((gridC P n k l).indicator 1) ω - P.real (gridC P n k l) <
      √(2 * P.real (gridC P n k l) * L / n) + L / (3 * n))
    (ho : ∀ k ≤ n, ∀ l ≤ n, P.real (gridO P n k l) - sampleMean ((gridO P n k l).indicator 1) ω <
      √(2 * P.real (gridO P n k l) * L / n) + L / (3 * n))
    (I : Set ℝ) (hI : I.OrdConnected) :
    |sampleMean (I.indicator 1) ω - P.real I| ≤ √(2 * P.real I * L / n) + (2 * L + 4) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp only [indicator_empty, sampleMean, Finset.sum_const_zero, zero_div,
      measureReal_empty, sub_zero, abs_zero]
    positivity
  set S := (fun y => cdf P y) '' I with hS
  have hSne : S.Nonempty := hne.image _
  have hS01 : ∀ v ∈ S, 0 ≤ v ∧ v ≤ 1 := by
    rintro _ ⟨y, _, rfl⟩; exact ⟨cdf_nonneg P y, cdf_le_one P y⟩
  have hSb : BddBelow S := ⟨0, fun v hv => (hS01 v hv).1⟩
  have hSa : BddAbove S := ⟨1, fun v hv => (hS01 v hv).2⟩
  set lo := sInf S with hlo
  set hi := sSup S with hhi
  have hlo0 : 0 ≤ lo := le_csInf hSne fun v hv => (hS01 v hv).1
  have hhi1 : hi ≤ 1 := csSup_le hSne fun v hv => (hS01 v hv).2
  have hlohi : lo ≤ hi := csInf_le_csSup hSne hSb hSa
  have hsub1 : I ⊆ {y | lo ≤ cdf P y ∧ cdf P y ≤ hi} := fun y hy =>
    ⟨csInf_le hSb ⟨y, hy, rfl⟩, le_csSup hSa ⟨y, hy, rfl⟩⟩
  have hsub2 : {y | lo < cdf P y ∧ cdf P y < hi} ⊆ I := by
    rintro y ⟨h1, h2⟩
    obtain ⟨_, ⟨y1, hy1, rfl⟩, hv1⟩ := exists_lt_of_csInf_lt hSne h1
    obtain ⟨_, ⟨y2, hy2, rfl⟩, hv2⟩ := exists_lt_of_lt_csSup hSne h2
    have h1' : y1 ≤ y := le_of_lt (lt_of_not_ge fun h => (not_le.2 hv1) (monotone_cdf P h))
    have h2' : y ≤ y2 := le_of_lt (lt_of_not_ge fun h => (not_le.2 hv2) (monotone_cdf P h))
    exact hI.out hy1 hy2 ⟨h1', h2'⟩
  have hPI1 : P.real I ≤ hi - lo :=
    (measureReal_mono hsub1).trans (measureReal_cdf_Icc P hlo0 hlohi hhi1).le
  have hPI2 : hi - lo ≤ P.real I := (le_measureReal_cdf_Ioo P hlo0 hhi1).trans (measureReal_mono hsub2)
  have hnlo : 0 ≤ (n : ℝ) * lo := mul_nonneg hn'.le hlo0
  have hnhi : 0 ≤ (n : ℝ) * hi := mul_nonneg hn'.le (hlo0.trans hlohi)
  have hnlo1 : (n : ℝ) * lo ≤ n := by nlinarith
  have hnhi1 : (n : ℝ) * hi ≤ n := by nlinarith
  have hP0 : 0 ≤ P.real I := measureReal_nonneg
  have hsq : 0 ≤ √(2 * P.real I * L / n) := Real.sqrt_nonneg _
  -- the upper half
  have hupper : sampleMean (I.indicator 1) ω - P.real I ≤ √(2 * P.real I * L / n) + (2 * L + 4) / n := by
    set kc := ⌊(n : ℝ) * lo⌋₊ with hkc
    set lc := ⌈(n : ℝ) * hi⌉₊ with hlc
    have hkcn : kc ≤ n := Nat.floor_le_of_le hnlo1
    have hlcn : lc ≤ n := Nat.ceil_le.2 hnhi1
    have hk1 : (kc : ℝ) ≤ n * lo := Nat.floor_le hnlo
    have hk2 : n * lo < kc + 1 := Nat.lt_floor_add_one _
    have hl1 : n * hi ≤ (lc : ℝ) := Nat.le_ceil _
    have hl2 : (lc : ℝ) < n * hi + 1 := Nat.ceil_lt_add_one hnhi
    have hlcn' : (lc : ℝ) ≤ n := by exact_mod_cast hlcn
    have ha0 : 0 ≤ (kc : ℝ) / n := by positivity
    have halo : (kc : ℝ) / n ≤ lo := by rw [div_le_iff₀ hn']; linarith
    have hhib : hi ≤ (lc : ℝ) / n := by rw [le_div_iff₀ hn']; linarith
    have hb1 : (lc : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact hlcn'
    have hIc : I ⊆ gridC P n kc lc := fun y hy => by
      have := hsub1 hy
      exact ⟨halo.trans this.1, this.2.trans hhib⟩
    have hpc : P.real (gridC P n kc lc) = (lc : ℝ) / n - (kc : ℝ) / n :=
      measureReal_cdf_Icc P ha0 (halo.trans (hlohi.trans hhib)) hb1
    have hpc2 : P.real (gridC P n kc lc) ≤ P.real I + 2 / n := by
      rw [hpc, div_sub_div_same, div_le_iff₀ hn']
      have : P.real I + 2 / n = (P.real I * n + 2) / n := by field_simp
      rw [add_mul, div_mul_cancel₀ _ hn'.ne']
      nlinarith
    have h1 := sampleMean_indicator_mono hIc ω
    have h2 := hc kc hkcn lc hlcn
    have hpc0 : 0 ≤ P.real (gridC P n kc lc) := measureReal_nonneg
    have h3 : √(2 * P.real (gridC P n kc lc) * L / n) ≤ √(2 * P.real I * L / n) + 2 * √L / n := by
      calc √(2 * P.real (gridC P n kc lc) * L / n) ≤ √(2 * P.real I * L / n + 4 * L / n ^ 2) := by
            apply Real.sqrt_le_sqrt
            have : 2 * P.real (gridC P n kc lc) * L / n ≤ 2 * (P.real I + 2 / n) * L / n := by
              apply div_le_div_of_nonneg_right _ hn'.le
              exact mul_le_mul_of_nonneg_right (by linarith) hL
            have e : 2 * (P.real I + 2 / n) * L / n = 2 * P.real I * L / n + 4 * L / n ^ 2 := by
              field_simp; ring
            linarith
        _ ≤ √(2 * P.real I * L / n) + √(4 * L / n ^ 2) := by
            rw [Real.sqrt_le_left (by positivity)]
            have ha := Real.sq_sqrt (show 0 ≤ 2 * P.real I * L / n by positivity)
            have hb := Real.sq_sqrt (show 0 ≤ 4 * L / n ^ 2 by positivity)
            nlinarith [Real.sqrt_nonneg (2 * P.real I * L / n), Real.sqrt_nonneg (4 * L / n ^ 2)]
        _ = √(2 * P.real I * L / n) + 2 * √L / n := by
            congr 1
            rw [show 4 * L / n ^ 2 = (2 / n) ^ 2 * L by field_simp; ring, Real.sqrt_mul (by positivity),
              Real.sqrt_sq (by positivity)]
            ring
    have h4 : 2 / n + 2 * √L / n + L / (3 * n) ≤ (2 * L + 4) / n := by
      have e : 2 / n + 2 * √L / n + L / (3 * n) = (2 + 2 * √L + L / 3) / n := by
        field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ hn'.le
      nlinarith [Real.sq_sqrt hL, Real.sqrt_nonneg L, sq_nonneg (√L - 1)]
    linarith
  -- the lower half
  have hlower : P.real I - sampleMean (I.indicator 1) ω ≤ √(2 * P.real I * L / n) + (2 * L + 4) / n := by
    set ko := ⌈(n : ℝ) * lo⌉₊ with hko
    set lo' := ⌊(n : ℝ) * hi⌋₊ with hlo'
    have hkon : ko ≤ n := Nat.ceil_le.2 hnlo1
    have hlon : lo' ≤ n := Nat.floor_le_of_le hnhi1
    have hk1 : n * lo ≤ (ko : ℝ) := Nat.le_ceil _
    have hk2 : (ko : ℝ) < n * lo + 1 := Nat.ceil_lt_add_one hnlo
    have hl1 : (lo' : ℝ) ≤ n * hi := Nat.floor_le hnhi
    have hl2 : n * hi < lo' + 1 := Nat.lt_floor_add_one _
    have ha0 : 0 ≤ (ko : ℝ) / n := by positivity
    have hb1 : (lo' : ℝ) / n ≤ 1 := by
      rw [div_le_one hn']; exact_mod_cast hlon
    have halo : lo ≤ (ko : ℝ) / n := by rw [le_div_iff₀ hn']; linarith
    have hhib : (lo' : ℝ) / n ≤ hi := by rw [div_le_iff₀ hn']; linarith
    have hIo : gridO P n ko lo' ⊆ I := fun y hy => hsub2 ⟨halo.trans_lt hy.1, hy.2.trans_le hhib⟩
    have hpo1 : (lo' : ℝ) / n - (ko : ℝ) / n ≤ P.real (gridO P n ko lo') :=
      le_measureReal_cdf_Ioo P ha0 hb1
    have hpo2 : P.real I - 2 / n ≤ P.real (gridO P n ko lo') := by
      refine le_trans ?_ hpo1
      rw [div_sub_div_same, le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
      nlinarith
    have hpo3 : P.real (gridO P n ko lo') ≤ P.real I := measureReal_mono hIo
    have h1 := sampleMean_indicator_mono hIo ω
    have h2 := ho ko hkon lo' hlon
    have h3 : √(2 * P.real (gridO P n ko lo') * L / n) ≤ √(2 * P.real I * L / n) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_right _ hn'.le
      exact mul_le_mul_of_nonneg_right (by linarith) hL
    have h4 : 2 / n + L / (3 * n) ≤ (2 * L + 4) / n := by
      have e : 2 / n + L / (3 * n) = (2 + L / 3) / n := by field_simp
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) hn'.le
    linarith
  rw [abs_le]
  constructor <;> linarith

end PIT

/-- **Relative deviations for all intervals** (Lemma S4.23 of trimmed-mmd S4, general form): for an atomless
probability `P` on `ℝ`, `n ≥ 1` and `L ≥ 0`, there is a measurable event `E` with `P^{⊗n}(Eᶜ) ≤ 2(n+1)²e^{−L}` on which
every interval `I` has `|P̃(I) − P(I)| ≤ √(2P(I)L/n) + (2L+4)/n`. -/
theorem exists_interval_event (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P] {n : ℕ} (hn : 0 < n)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ E : Set (Fin n → ℝ), MeasurableSet E ∧
      (Measure.pi fun _ : Fin n => P).real Eᶜ ≤ 2 * ((n : ℝ) + 1) ^ 2 * exp (-L) ∧
      ∀ ω ∈ E, ∀ I : Set ℝ, I.OrdConnected →
        |sampleMean (I.indicator 1) ω - P.real I| ≤ √(2 * P.real I * L / n) + (2 * L + 4) / n := by
  set Bc : ℕ × ℕ → Set (Fin n → ℝ) := fun kl =>
    {ω | √(2 * P.real (gridC P n kl.1 kl.2) * L / n) + L / (3 * n) ≤
      sampleMean ((gridC P n kl.1 kl.2).indicator 1) ω - P.real (gridC P n kl.1 kl.2)} with hBc
  set Bo : ℕ × ℕ → Set (Fin n → ℝ) := fun kl =>
    {ω | √(2 * P.real (gridO P n kl.1 kl.2) * L / n) + L / (3 * n) ≤
      P.real (gridO P n kl.1 kl.2) - sampleMean ((gridO P n kl.1 kl.2).indicator 1) ω} with hBo
  set T := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hT
  have hmeasC : ∀ kl, MeasurableSet (Bc kl) := fun kl =>
    measurableSet_le measurable_const
      ((measurable_sampleMean (measurable_const.indicator (measurableSet_gridC P n _ _))).sub measurable_const)
  have hmeasO : ∀ kl, MeasurableSet (Bo kl) := fun kl =>
    measurableSet_le measurable_const
      (measurable_const.sub (measurable_sampleMean (measurable_const.indicator (measurableSet_gridO P n _ _))))
  refine ⟨(⋃ kl ∈ T, (Bc kl ∪ Bo kl))ᶜ, ?_, ?_, ?_⟩
  · exact (Finset.measurableSet_biUnion T fun kl _ => (hmeasC kl).union (hmeasO kl)).compl
  · rw [compl_compl]
    calc (Measure.pi fun _ : Fin n => P).real (⋃ kl ∈ T, (Bc kl ∪ Bo kl))
        ≤ ∑ kl ∈ T, (Measure.pi fun _ : Fin n => P).real (Bc kl ∪ Bo kl) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _kl ∈ T, (exp (-L) + exp (-L)) := by
          refine Finset.sum_le_sum fun kl _ => (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
          · exact prob_upper_dev_le P (measurableSet_gridC P n _ _) hn hL
          · exact prob_lower_dev_le P (measurableSet_gridO P n _ _) hn hL
      _ = 2 * ((n : ℝ) + 1) ^ 2 * exp (-L) := by
          rw [Finset.sum_const, hT, Finset.card_product, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  · intro ω hω I hI
    simp only [mem_compl_iff, mem_iUnion, not_exists, mem_union, not_or] at hω
    refine abs_sampleMean_sub_le_of_grid P hn hL ω (fun k hk l hl => ?_) (fun k hk l hl => ?_) I hI
    · have hkl : (k, l) ∈ T := Finset.mem_product.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hk), Finset.mem_range.2 (Nat.lt_succ_of_le hl)⟩
      have := (hω (k, l) hkl).1
      simp only [hBc, mem_ofPred_eq, not_le] at this
      exact this
    · have hkl : (k, l) ∈ T := Finset.mem_product.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hk), Finset.mem_range.2 (Nat.lt_succ_of_le hl)⟩
      have := (hω (k, l) hkl).2
      simp only [hBo, mem_ofPred_eq, not_le] at this
      exact this

end StatFormal.IntervalDev
