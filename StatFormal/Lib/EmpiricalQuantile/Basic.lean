import StatFormal.Lib.PaperRun.OrdStat
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs
import StatFormal.Wave30tq.Statements

/-!
# Quantiles of an empirical law and order statistics (library)

Library component (untrusted). For a sample `x : Fin n → 𝒳` (`n ≥ 1`) with empirical law `P̃ = n⁻¹Σᵢδ_{xᵢ}`
(`TrimmedMMD.Concentration.empirical`) and a measurable `f : 𝒳 → ℝ`:

* `empirical_real_lt`, `empirical_real_le`: `P̃{f < q} = #{i : f(xᵢ) < q}/n` and `P̃{f ≤ q} = #{i : f(xᵢ) ≤ q}/n`;
* `isQuantileAt_empirical_iff`: `q` is a `p`-quantile of `f` under `P̃` (`Wave30tq.IsQuantileAt`) iff it is an empirical `p`-quantile
  of the values `f(xᵢ)` (`Wave30tz.IsEmpQuantile`);
* `isLeast_empQuantile_ceil` (`p ∈ (0,1]`): the smallest empirical `p`-quantile is the order statistic of rank `⌈np⌉`;
  `isGreatest_empQuantile_floor` (`p ∈ [0,1)`): the largest is the order statistic of rank `⌊np⌋ + 1`;
  `isLeast_quantileAt_empirical`, `isGreatest_quantileAt_empirical`: the same for `IsQuantileAt` under `P̃`;
* `rank_ceil_pos`, `rank_ceil_le_floor_succ`, `rank_floor_succ_le`: `1 ≤ ⌈np⌉ ≤ ⌊np⌋ + 1 ≤ n` for `p ∈ (0,1)`;
* `empQuantile_bracket`: every empirical `p`-quantile lies between the order statistics of ranks `⌈np⌉` and `⌊np⌋ + 1`
  (`p ∈ (0,1)`).

The order-statistic counting facts are those of `StatFormal.Wave30tz.RouteOrder` and `StatFormal.PaperRun` (`OrdStat.lean`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Finset

namespace StatFormal.EmpiricalQuantile

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration

section Ranks

/-- `⌈np⌉ ≥ 1` for `n ≥ 1`, `p > 0`. -/
theorem rank_ceil_pos {n : ℕ} {p : ℝ} (hn : 1 ≤ n) (hp0 : 0 < p) : 1 ≤ ⌈(n : ℝ) * p⌉₊ :=
  Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (mul_pos (by exact_mod_cast hn) hp0)).ne'

/-- `⌈np⌉ ≤ ⌊np⌋ + 1`. -/
theorem rank_ceil_le_floor_succ (n : ℕ) (p : ℝ) : ⌈(n : ℝ) * p⌉₊ ≤ ⌊(n : ℝ) * p⌋₊ + 1 :=
  Nat.ceil_le_floor_add_one _

/-- `⌊np⌋ + 1 ≤ n` for `p < 1`, `n ≥ 1`. -/
theorem rank_floor_succ_le {n : ℕ} {p : ℝ} (hn : 1 ≤ n) (hp0 : 0 ≤ p) (hp1 : p < 1) : ⌊(n : ℝ) * p⌋₊ + 1 ≤ n := by
  have hlt : (n : ℝ) * p < n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  have := (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) hp0)).mpr hlt
  omega

end Ranks

section Quantiles

variable {n : ℕ}

/-- **The smallest empirical quantile.** For `p ∈ (0,1]` and `n ≥ 1`, the order statistic of rank `⌈np⌉` is the least
empirical `p`-quantile. -/
theorem isLeast_empQuantile_ceil (h : Fin n → ℝ) {p : ℝ} (hn : 1 ≤ n) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsLeast {q | IsEmpQuantile h p q} (ordStat h ⌈(n : ℝ) * p⌉₊) := by
  refine ⟨?_, fun q hq => StatFormal.PaperRun.ordStat_ceil_le_of_isEmpQuantile h hp0 hp1 hn hq⟩
  have h1 := StatFormal.PaperRun.isEmpQuantile_ordStat_ceil h hn hp0.le hp1
  rwa [max_eq_right (rank_ceil_pos hn hp0)] at h1

/-- **The largest empirical quantile.** For `p ∈ [0,1)` and `n ≥ 1`, the order statistic of rank `⌊np⌋ + 1` is the
greatest empirical `p`-quantile. -/
theorem isGreatest_empQuantile_floor (h : Fin n → ℝ) {p : ℝ} (hn : 1 ≤ n) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IsGreatest {q | IsEmpQuantile h p q} (ordStat h (⌊(n : ℝ) * p⌋₊ + 1)) := by
  have hr := rank_floor_succ_le hn hp0 hp1
  refine ⟨?_, fun q hq => StatFormal.PaperRun.le_ordStat_floor_of_isEmpQuantile h hp0 hr hq⟩
  have h1 := StatFormal.PaperRun.isEmpQuantile_ordStat_floor h hn hp0 hp1.le
  rwa [min_eq_right hr] at h1

/-- **Genuine quantiles are bracketed.** For `p ∈ (0,1)`, every empirical `p`-quantile lies between the order statistics
of ranks `⌈np⌉` and `⌊np⌋ + 1`. -/
theorem empQuantile_bracket (h : Fin n → ℝ) {p q : ℝ} (hn : 1 ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hq : IsEmpQuantile h p q) : ordStat h ⌈(n : ℝ) * p⌉₊ ≤ q ∧ q ≤ ordStat h (⌊(n : ℝ) * p⌋₊ + 1) :=
  ⟨(isLeast_empQuantile_ceil h hn hp0 hp1.le).2 hq, (isGreatest_empQuantile_floor h hn hp0.le hp1).2 hq⟩

end Quantiles

section Empirical

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n : ℕ}

omit [MeasurableSpace 𝒳] in
/-- `n⁻¹ Σ_i 1_S(x_i)` written as a count. -/
theorem sum_indicator_eq_card (x : Fin n → 𝒳) (S : Set 𝒳) [DecidablePred fun i => x i ∈ S] :
    ∑ i, S.indicator (1 : 𝒳 → ℝ) (x i) = ((univ.filter fun i => x i ∈ S).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : x i ∈ S <;> simp [hi]

/-- `P̃(S) = #{i : x_i ∈ S}/n` for a measurable `S`. -/
theorem empirical_real_eq (hn : n ≠ 0) (x : Fin n → 𝒳) {S : Set 𝒳} (hS : MeasurableSet S)
    [DecidablePred fun i => x i ∈ S] :
    (empirical x).real S = ((univ.filter fun i => x i ∈ S).card : ℝ) / n := by
  have := isProbabilityMeasure_empirical hn x
  have h1 : ∫ z, S.indicator (1 : 𝒳 → ℝ) z ∂(empirical x) = (empirical x).real S := integral_indicator_one hS
  have h2 := integral_empirical x (h := S.indicator (1 : 𝒳 → ℝ)) (stronglyMeasurable_one.indicator hS) (C := 1)
    (fun z => by by_cases hz : z ∈ S <;> simp [hz])
  rw [← h1, h2, sum_indicator_eq_card, div_eq_inv_mul]

/-- `P̃{f < q} = #{i : f(x_i) < q}/n`. -/
theorem empirical_real_lt (hn : n ≠ 0) (x : Fin n → 𝒳) {f : 𝒳 → ℝ} (hf : Measurable f) (q : ℝ) :
    (empirical x).real {z | f z < q} = ((univ.filter fun i => f (x i) < q).card : ℝ) / n := by
  classical
  rw [empirical_real_eq hn x (measurableSet_lt hf measurable_const)]
  congr 3

/-- `P̃{f ≤ q} = #{i : f(x_i) ≤ q}/n`. -/
theorem empirical_real_le (hn : n ≠ 0) (x : Fin n → 𝒳) {f : 𝒳 → ℝ} (hf : Measurable f) (q : ℝ) :
    (empirical x).real {z | f z ≤ q} = ((univ.filter fun i => f (x i) ≤ q).card : ℝ) / n := by
  classical
  rw [empirical_real_eq hn x (measurableSet_le hf measurable_const)]
  congr 3

/-- **Quantiles under an empirical law.** `q` is a `p`-quantile of `f` under `P̃` iff it is an empirical `p`-quantile of the
values `f(x_i)`. -/
theorem isQuantileAt_empirical_iff (hn : 1 ≤ n) (x : Fin n → 𝒳) {f : 𝒳 → ℝ} (hf : Measurable f) (p q : ℝ) :
    IsQuantileAt (empirical x) f p q ↔ IsEmpQuantile (fun i => f (x i)) p q := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold IsQuantileAt IsEmpQuantile
  rw [empirical_real_lt hn0 x hf, empirical_real_le hn0 x hf, div_le_iff₀ hnpos, le_div_iff₀ hnpos]
  constructor
  · rintro ⟨h1, h2⟩; constructor
    · convert h1 using 1; ring
    · convert h2 using 1; ring
  · rintro ⟨h1, h2⟩; constructor
    · convert h1 using 1; ring
    · convert h2 using 1; ring

/-- The set of `p`-quantiles of `f` under `P̃` is the set of empirical `p`-quantiles of the values. -/
theorem setOf_quantileAt_empirical (hn : 1 ≤ n) (x : Fin n → 𝒳) {f : 𝒳 → ℝ} (hf : Measurable f) (p : ℝ) :
    {q | IsQuantileAt (empirical x) f p q} = {q | IsEmpQuantile (fun i => f (x i)) p q} := by
  ext q; exact isQuantileAt_empirical_iff hn x hf p q

/-- The least `p`-quantile of `f` under `P̃` (`p ∈ (0,1]`) is the order statistic of rank `⌈np⌉` of the values. -/
theorem isLeast_quantileAt_empirical (hn : 1 ≤ n) (x : Fin n → 𝒳) {f : 𝒳 → ℝ} (hf : Measurable f) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsLeast {q | IsQuantileAt (empirical x) f p q} (ordStat (fun i => f (x i)) ⌈(n : ℝ) * p⌉₊) := by
  rw [setOf_quantileAt_empirical hn x hf p]
  exact isLeast_empQuantile_ceil _ hn hp0 hp1

/-- The greatest `p`-quantile of `f` under `P̃` (`p ∈ [0,1)`) is the order statistic of rank `⌊np⌋ + 1` of the values. -/
theorem isGreatest_quantileAt_empirical (hn : 1 ≤ n) (x : Fin n → 𝒳) {f : 𝒳 → ℝ} (hf : Measurable f) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IsGreatest {q | IsQuantileAt (empirical x) f p q} (ordStat (fun i => f (x i)) (⌊(n : ℝ) * p⌋₊ + 1)) := by
  rw [setOf_quantileAt_empirical hn x hf p]
  exact isGreatest_empQuantile_floor _ hn hp0 hp1

end Empirical

end StatFormal.EmpiricalQuantile
