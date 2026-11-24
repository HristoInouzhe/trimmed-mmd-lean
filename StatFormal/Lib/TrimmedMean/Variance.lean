import StatFormal.Lib.TrimmedMean.Asymp

/-!
# The plug-in variance of an extreme trimmed mean is consistent (library)

`varLo n α v = P_n g_{ĉ}² − (P_n g_{ĉ})²` with `g_c(y) = (c − y)_+` and `ĉ = quantLo n α v` the empirical
`β`-quantile (the influence-function plug-in for the lower trimmed mean). Under `UQ`,
`tip0_varLo`: `varLo n α (h(X_0), …, h(X_{n−1})) → Var_P((q − h)_+)` in probability.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Foundations.TrimmedMean

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.CLT

variable {n : ℕ}

/-- Plug-in variance `P_n g_{ĉ}² − (P_n g_{ĉ})²`, `g_c(y) = (c − y)_+`, `ĉ` the empirical `β`-quantile. -/
def varLo (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ :=
  (∑ i, max (quantLo n α v - v i) 0 ^ 2) / n - ((∑ i, max (quantLo n α v - v i) 0) / n) ^ 2

lemma measurable_varLo (α : ℝ) : Measurable fun v : Fin n → ℝ => varLo n α v := by
  have hq : Measurable fun v : Fin n → ℝ => quantLo n α v := measurable_ordStat _
  unfold varLo
  refine Measurable.sub ((Finset.measurable_sum _ fun i _ => ((hq.sub (measurable_pi_apply i)).max
    measurable_const).pow_const 2).div_const _) (((Finset.measurable_sum _ fun i _ =>
    (hq.sub (measurable_pi_apply i)).max measurable_const).div_const _).pow_const 2)

lemma abs_avg_sub_le {a b : Fin n → ℝ} {e : ℝ} (hn : 0 < n) (h : ∀ i, |a i - b i| ≤ e) :
    |(∑ i, a i) / n - (∑ i, b i) / n| ≤ e := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hn', div_le_iff₀ hn']
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |a i - b i| ≤ ∑ _i : Fin n, e := sum_le_sum fun i _ => h i
    _ = e * n := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma avg_bounds {a : Fin n → ℝ} {K : ℝ} (hn : 0 < n) (h0 : ∀ i, 0 ≤ a i) (hK : ∀ i, a i ≤ K) :
    0 ≤ (∑ i, a i) / n ∧ (∑ i, a i) / n ≤ K := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨div_nonneg (sum_nonneg fun i _ => h0 i) hn'.le, ?_⟩
  rw [div_le_iff₀ hn']
  calc ∑ i, a i ≤ ∑ _i : Fin n, K := sum_le_sum fun i _ => hK i
    _ = K * n := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma abs_sq_sub_sq_le {x y K : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) : |x ^ 2 - y ^ 2| ≤ 2 * K * |x - y| := by
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)

/-- Deterministic Lipschitz bound for the plug-in variance. -/
lemma varLo_sub_le {v : Fin n → ℝ} {c q Bb m1 m2 : ℝ} (hn : 0 < n) (hv : ∀ i, |v i| ≤ Bb) (hc : |c| ≤ Bb)
    (hm1 : |m1| ≤ |q| + 2 * Bb) :
    |((∑ i, max (c - v i) 0 ^ 2) / n - ((∑ i, max (c - v i) 0) / n) ^ 2) - (m2 - m1 ^ 2)| ≤
      4 * (|q| + 2 * Bb) * |c - q| + |(∑ i, max (q - v i) 0 ^ 2) / n - m2| +
        2 * (|q| + 2 * Bb) * |(∑ i, max (q - v i) 0) / n - m1| := by
  set K := |q| + 2 * Bb
  have hB0 : 0 ≤ Bb := (abs_nonneg _).trans hc
  have ha0 : ∀ i, 0 ≤ max (c - v i) 0 := fun i => le_max_right _ _
  have hb0 : ∀ i, 0 ≤ max (q - v i) 0 := fun i => le_max_right _ _
  have haK : ∀ i, max (c - v i) 0 ≤ K := fun i => max_le (by
    have := le_abs_self c; have := neg_abs_le (v i); have := hv i; have := abs_nonneg q; linarith) (by positivity)
  have hbK : ∀ i, max (q - v i) 0 ≤ K := fun i => max_le (by
    have := le_abs_self q; have := neg_abs_le (v i); have := hv i; linarith) (by positivity)
  have hab : ∀ i, |max (c - v i) 0 - max (q - v i) 0| ≤ |c - q| := fun i =>
    (abs_max_sub_max_le_abs _ _ _).trans (by rw [show c - v i - (q - v i) = c - q by ring])
  set A1 := (∑ i, max (c - v i) 0) / n
  set B1 := (∑ i, max (q - v i) 0) / n
  set A2 := (∑ i, max (c - v i) 0 ^ 2) / n
  set B2 := (∑ i, max (q - v i) 0 ^ 2) / n
  have h1 : |A1 - B1| ≤ |c - q| := abs_avg_sub_le hn hab
  have h2 : |A2 - B2| ≤ 2 * K * |c - q| := abs_avg_sub_le hn fun i =>
    (abs_sq_sub_sq_le (by rw [abs_of_nonneg (ha0 i)]; exact haK i) (by rw [abs_of_nonneg (hb0 i)]; exact hbK i)).trans
      (mul_le_mul_of_nonneg_left (hab i) (by positivity))
  obtain ⟨hA10, hA1K⟩ := avg_bounds hn ha0 haK
  obtain ⟨hB10, hB1K⟩ := avg_bounds hn hb0 hbK
  have h3 : |A1 ^ 2 - B1 ^ 2| ≤ 2 * K * |c - q| :=
    (abs_sq_sub_sq_le (by rw [abs_of_nonneg hA10]; exact hA1K) (by rw [abs_of_nonneg hB10]; exact hB1K)).trans
      (mul_le_mul_of_nonneg_left h1 (by positivity))
  have h4 : |B1 ^ 2 - m1 ^ 2| ≤ 2 * K * |B1 - m1| :=
    abs_sq_sub_sq_le (by rw [abs_of_nonneg hB10]; exact hB1K) hm1
  have e : (A2 - A1 ^ 2) - (m2 - m1 ^ 2) = (A2 - B2) + (B2 - m2) - (A1 ^ 2 - B1 ^ 2) - (B1 ^ 2 - m1 ^ 2) := by ring
  rw [e]
  have t1 := abs_sub (A2 - B2 + (B2 - m2) - (A1 ^ 2 - B1 ^ 2)) (B1 ^ 2 - m1 ^ 2)
  have t2 := abs_sub (A2 - B2 + (B2 - m2)) (A1 ^ 2 - B1 ^ 2)
  have t3 := abs_add_le (A2 - B2) (B2 - m2)
  linarith

lemma _root_.StatFormal.Foundations.CLT.TIP0.abs' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : ℕ → Ω → ℝ} (hA : TIP0 μ A) :
    TIP0 μ (fun n ω => |A n ω|) := fun ε hε => by simpa only [abs_abs] using hA ε hε

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Measure 𝒳} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳}

theorem tip0_varLo (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    {α q : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hq : UQ P h (1 - α) q) :
    TIP0 μ (fun n ω => varLo n α (smp X h n ω) - Var[fun x => max (q - h x) 0; P]) := by
  set g : 𝒳 → ℝ := fun x => max (q - h x) 0
  have hgm : Measurable g := (hm.const_sub q).max measurable_const
  have hB0 : ∀ x, |h x| ≤ |B| := fun x => (hB x).trans (le_abs_self B)
  set K := |q| + 2 * |B|
  have hgK : ∀ x, |g x| ≤ K := fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := le_abs_self q; have := neg_abs_le (h x); have := hB0 x; have := abs_nonneg B; linarith
  have hg2K : ∀ x, |g x ^ 2| ≤ K ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgK x) 2
  have hmem : MemLp g 2 P := MemLp.of_bound hgm.aestronglyMeasurable K (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hgK x)
  have hvar : Var[g; P] = ∫ x, g x ^ 2 ∂P - (∫ x, g x ∂P) ^ 2 := by
    rw [variance_eq_sub hmem]; rfl
  have hm1 : |∫ x, g x ∂P| ≤ K := abs_integral_le_of_abs_le hgK
  have hW : TIP0 μ (fun n ω => 4 * K * |quantLo n α (smp X h n ω) - q| +
      |(∑ i ∈ range n, g (X i ω) ^ 2) / n - ∫ x, g x ^ 2 ∂P| +
      2 * K * |(∑ i ∈ range n, g (X i ω)) / n - ∫ x, g x ∂P|) :=
    (((tip0_quantLo hS hm hα0 hα1 hq).abs'.const_mul _).add
      (tip0_avg hS (hgm.pow_const 2) hg2K).abs').add ((tip0_avg hS hgm hgK).abs'.const_mul _)
  refine TIP0.of_dominated hW (Bad := fun _ => ∅) (by simp) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω _
  have hc : |quantLo n α (smp X h n ω)| ≤ |B| := by
    obtain ⟨-, -, j, hj⟩ := quantLo_spec hn hα0 hα1 (smp X h n ω)
    rw [hj]; exact hB0 _
  have key := varLo_sub_le (v := smp X h n ω) (m2 := ∫ x, g x ^ 2 ∂P) hn (fun i => hB0 (X i ω)) hc hm1
  rw [hvar]
  simp only [varLo]
  rw [sum_smp X h n ω (fun y => max (q - y) 0 ^ 2), sum_smp X h n ω (fun y => max (q - y) 0)] at key
  refine key.trans (le_abs_self _)

end StatFormal.Foundations.TrimmedMean
