import StatFormal.Lib.TrimmedMean.Normal

/-!
# The split statistic at `α = 0`: plain sample means (library)

At `α = 0` the capped simplex `capped n 0` is the single point `(1/n, …, 1/n)`, so both extreme trimmed means are
sample means, and the plug-in variance `varLo n 0` (centred at the `n`-th order statistic, the maximum) is the
(`1/n`) sample variance. No quantile condition is needed:

* `trimLo_zero`, `trimUp_zero`, `varLo_zero`, `varLo_zero_centred`: the deterministic identities;
* `clt_zero`: `√n (T̂_n − (P h − Q h)) ⇝ N(0, Var_P h + Var_Q h/κ)` (two-sample CLT, `clt_two_sample`);
* `tip0_varLo_zero`, `tip0_seHat_zero`: plug-in consistency (Chebyshev);
* `coverage_zero`: `P(T̂_n − z ŝe_n ≤ P h − Q h) → Φ(z)` when `σ₀² > 0`;
* `coverage_zero_degenerate`: when `σ₀² = 0`, eventually `T̂_n − z ŝe_n = P h − Q h` almost surely.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Foundations.TrimmedMean

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.CLT

/-! ### Deterministic identities -/

section Det

variable {n : ℕ}

lemma capped_zero_eq (hn : 0 < n) : capped n 0 = {fun _ => 1 / (n : ℝ)} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcap : cap n 0 = 1 / (n : ℝ) := by simp [cap]
  ext w
  simp only [capped, hcap, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hb, hs⟩
    have hsum : ∑ i, (1 / (n : ℝ) - w i) = 0 := by
      rw [sum_sub_distrib, hs, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp; ring
    have h0 := (sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hb i).2).1 hsum
    funext i
    linarith [h0 i (mem_univ i)]
  · rintro rfl
    refine ⟨fun i => ⟨by positivity, le_rfl⟩, ?_⟩
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

lemma sum_uniform_mul (v : Fin n → ℝ) : ∑ i, (fun _ => 1 / (n : ℝ)) i * v i = (∑ i, v i) / n := by
  simp only [one_div]
  rw [← mul_sum, inv_mul_eq_div]

lemma trimLo_zero (hn : 0 < n) (v : Fin n → ℝ) :
    sInf ((fun w => ∑ i, w i * v i) '' capped n 0) = (∑ i, v i) / n := by
  rw [capped_zero_eq hn, Set.image_singleton, csInf_singleton, sum_uniform_mul]

lemma trimUp_zero (hn : 0 < n) (v : Fin n → ℝ) :
    sSup ((fun w => ∑ i, w i * v i) '' capped n 0) = (∑ i, v i) / n := by
  rw [capped_zero_eq hn, Set.image_singleton, csSup_singleton, sum_uniform_mul]

lemma le_ordStat_top (v : Fin n → ℝ) (j : Fin n) : v j ≤ ordStat n v := by
  haveI : Nonempty {S : Finset (Fin n) // S.card = n} := ⟨⟨univ, by simp⟩⟩
  refine le_ciInf fun S => ?_
  have hS : S.1 = univ := eq_univ_of_card S.1 (by simp [S.2])
  have hj : j ∈ S.1 := by rw [hS]; exact mem_univ j
  exact le_ciSup (f := fun i : S.1 => v i) (Set.finite_range _).bddAbove ⟨j, hj⟩

lemma le_quantLo_zero (v : Fin n → ℝ) (j : Fin n) : v j ≤ quantLo n 0 v := by
  have : ⌈(n : ℝ) * (1 - 0)⌉₊ = n := by simp
  unfold quantLo
  rw [this]
  exact le_ordStat_top v j

/-- The shift-invariance of the plug-in variance. -/
lemma shift_var (hn : 0 < n) (v : Fin n → ℝ) (c : ℝ) :
    (∑ i, (c - v i) ^ 2) / n - ((∑ i, (c - v i)) / n) ^ 2 = (∑ i, v i ^ 2) / n - ((∑ i, v i) / n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e1 : ∑ i, (c - v i) ^ 2 = n * c ^ 2 + (-2 * c) * ∑ i, v i + ∑ i, v i ^ 2 := by
    have : ∀ i, (c - v i) ^ 2 = c ^ 2 + (-2 * c) * v i + v i ^ 2 := fun i => by ring
    simp only [this, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e2 : ∑ i, (c - v i) = n * c - ∑ i, v i := by
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [e1, e2]
  field_simp
  ring

lemma centred_var (hn : 0 < n) (v : Fin n → ℝ) :
    (∑ i, (v i - (∑ j, v j) / n) ^ 2) / n = (∑ i, v i ^ 2) / n - ((∑ i, v i) / n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set S := ∑ j, v j
  have e : ∑ i, (v i - S / n) ^ 2 = ∑ i, v i ^ 2 + (-2 * (S / n)) * S + n * (S / n) ^ 2 := by
    have : ∀ i, (v i - S / n) ^ 2 = v i ^ 2 + (-2 * (S / n)) * v i + (S / n) ^ 2 := fun i => by ring
    simp only [this, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, S]
  rw [e]
  field_simp
  ring

/-- `varLo n 0 v = n⁻¹ Σ v_i² − (n⁻¹ Σ v_i)²`. -/
lemma varLo_zero (hn : 0 < n) (v : Fin n → ℝ) :
    varLo n 0 v = (∑ i, v i ^ 2) / n - ((∑ i, v i) / n) ^ 2 := by
  have hmax : ∀ i, max (quantLo n 0 v - v i) 0 = quantLo n 0 v - v i := fun i =>
    max_eq_left (sub_nonneg.2 (le_quantLo_zero v i))
  unfold varLo
  simp only [hmax]
  exact shift_var hn v _

/-- `varLo n 0 v` is the (`1/n`) sample variance. -/
lemma varLo_zero_centred (hn : 0 < n) (v : Fin n → ℝ) :
    varLo n 0 v = (∑ i, (v i - (∑ j, v j) / n) ^ 2) / n := by
  rw [varLo_zero hn, centred_var hn]

end Det

/-! ### Probabilistic statements -/

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X Y : ℕ → Ω → 𝒳}

lemma statT_zero {h : 𝒳 → ℝ} {m : ℕ → ℕ} {n : ℕ} (hn : 0 < n) (hmn : 0 < m n) (ω : Ω) :
    statT X Y h m 0 n ω = (∑ i ∈ range n, h (X i ω)) / n - (∑ j ∈ range (m n), h (Y j ω)) / (m n) := by
  unfold statT
  rw [trimLo_zero hn, trimUp_zero hmn]
  simp only [smp]
  rw [Fin.sum_univ_eq_sum_range (fun i => h (X i ω)) n, Fin.sum_univ_eq_sum_range (fun i => h (Y i ω)) (m n)]

/-- Asymptotic normality at `α = 0`: the two-sample CLT for the sample means. -/
theorem clt_zero (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (statT X Y h m 0 n ω - (∫ x, h x ∂P - ∫ x, h x ∂Q)))
      atTop id (fun _ => μ) (gaussianReal 0 (Var[h; P] + Var[h; Q] / κ).toNNReal) := by
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
  obtain ⟨hUm, hUi, hUid, hU2, hU0, hUv⟩ := clt_terms hX hm hB 1
  obtain ⟨hWm, hWi, hWid, hW2, hW0, hWv⟩ := clt_terms hY hm hB (-1)
  set U : ℕ → Ω → ℝ := fun i ω => 1 * (h (X i ω) - ∫ x, h x ∂P)
  set W : ℕ → Ω → ℝ := fun i ω => -1 * (h (Y i ω) - ∫ x, h x ∂Q)
  have hUW : IndepFun (fun ω i => U i ω) (fun ω i => W i ω) μ := by
    have hf : Measurable fun (x : ℕ → 𝒳) (i : ℕ) => 1 * (h (x i) - ∫ x, h x ∂P) :=
      measurable_pi_iff.2 fun i => ((hm.comp (measurable_pi_apply i)).sub_const _).const_mul _
    have hf' : Measurable fun (x : ℕ → 𝒳) (i : ℕ) => -1 * (h (x i) - ∫ x, h x ∂Q) :=
      measurable_pi_iff.2 fun i => ((hm.comp (measurable_pi_apply i)).sub_const _).const_mul _
    exact hXY.comp hf hf'
  have hvar : Var[U 0; μ] + Var[W 0; μ] / κ = Var[h; P] + Var[h; Q] / κ := by
    rw [hUv, hWv]; ring
  have hG : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (Var[U 0; μ] + Var[W 0; μ] / κ).toNNReal)
      (gaussianReal 0 (Var[h; P] + Var[h; Q] / κ).toNNReal) := by
    rw [hvar]; exact ⟨aemeasurable_id, Measure.map_id⟩
  have hlin := clt_two_sample (fun i => hUm i) (fun i => hWm i) hUi hWi hUW hUid hWid hU2 hW2 hU0 hW0 hκ hmr hG
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hlin ?_ fun n =>
    (((measurable_statT hX hY hm le_rfl zero_lt_one m n).sub_const _).const_mul _).aemeasurable
  rw [tip0_iff]
  refine tip0_zero.congr ?_
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn ω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn' : (0 : ℝ) < m n := by exact_mod_cast hmn
  have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
  have hs0 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn').ne'
  simp only [Pi.sub_apply, statT_zero hn hmn, U, W]
  simp only [one_mul, neg_one_mul, sum_neg_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  set Sx := ∑ i ∈ range n, h (X i ω)
  set Sy := ∑ j ∈ range (m n), h (Y j ω)
  set r := √(n : ℝ)
  rw [← hs]
  field_simp
  ring

/-- Plug-in variance consistency at `α = 0`. -/
theorem tip0_varLo_zero (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) :
    TIP0 μ (fun n ω => varLo n 0 (smp X h n ω) - Var[h; P]) := by
  have hB0 : ∀ x, |h x| ≤ |B| := fun x => (hB x).trans (le_abs_self B)
  have hB2 : ∀ x, |h x ^ 2| ≤ |B| ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB0 x) 2
  have h1 := tip0_avg hS hm hB0
  have h2 := tip0_avg hS (hm.pow_const 2) hB2
  set a := ∫ x, h x ∂P
  have hbip : BIP μ (fun n ω => (∑ i ∈ range n, h (X i ω)) / n + a) := by
    refine (BIP.add (BIP.of_tip0 h1) (bip_det (P := μ) (tendsto_const_nhds (x := 2 * a)))).congr
      (Eventually.of_forall fun n ω => ?_)
    ring
  have hprod := h1.mul_bip hbip
  have hmem : MemLp h 2 P :=
    MemLp.of_bound hm.aestronglyMeasurable |B| (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB0 x)
  have hvar : Var[h; P] = ∫ x, h x ^ 2 ∂P - a ^ 2 := by
    rw [variance_eq_sub hmem]; rfl
  refine (h2.sub hprod).congr ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω
  rw [varLo_zero hn, hvar]
  simp only [smp]
  rw [Fin.sum_univ_eq_sum_range (fun i => h (X i ω) ^ 2) n, Fin.sum_univ_eq_sum_range (fun i => h (X i ω)) n]
  ring

/-- Plug-in standard error consistency at `α = 0`: `√n ŝe_n → σ₀` in probability. -/
theorem tip0_seHat_zero (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hσ : 0 < Var[h; P] + Var[h; Q] / κ) :
    TIP0 μ (fun n ω => √(n : ℝ) * seHat n (m n) 0 (smp X h n ω) (smp Y h (m n) ω) -
      √(Var[h; P] + Var[h; Q] / κ)) := by
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
  set S := Var[h; P] + Var[h; Q] / κ
  have h1 := tip0_varLo_zero hX hm hB
  have h2 := tip0_varLo_zero (h := fun x => -h x) hY hm.neg (B := B) (fun x => by rw [abs_neg]; exact hB x)
  have hneg : Var[fun x => -h x; Q] = Var[h; Q] := variance_fun_neg
  rw [hneg] at h2
  have h2m : TIP0 μ (fun n ω => varLo (m n) 0 (smp Y (fun x => -h x) (m n) ω) - Var[h; Q]) :=
    fun ε hε => (h2 ε hε).comp hmtop
  have hinv : Tendsto (fun n : ℕ => (n : ℝ) / m n) atTop (𝓝 κ⁻¹) := by
    have := hmr.inv₀ hκ.ne'
    refine this.congr fun n => ?_
    rw [inv_div]
  set A : ℕ → Ω → ℝ := fun n ω => varLo n 0 (smp X h n ω) + (n : ℝ) / m n * varLo (m n) 0 (smp Y (fun x => -h x) (m n) ω)
  have hA : TIP0 μ (fun n ω => A n ω - S) := by
    have hdet : Tendsto (fun n : ℕ => ((n : ℝ) / m n - κ⁻¹) * Var[h; Q]) atTop (𝓝 0) := by
      simpa using (hinv.sub_const κ⁻¹).mul_const (Var[h; Q])
    have := (h1.add (h2m.bip_mul (bip_det hinv))).add (tip0_det (P := μ) hdet)
    refine this.congr (Eventually.of_forall fun n ω => ?_)
    simp only [A, S]
    ring
  have hsq : TIP0 μ (fun n ω => √(A n ω) - √S) := by
    refine TIP0.of_dominated ((hA.abs').const_mul (√S)⁻¹) (Bad := fun _ => ∅) (by simp)
      (Eventually.of_forall fun n ω _ => ?_)
    refine (abs_sqrt_sub_sqrt_le hσ).trans ?_
    rw [abs_mul, abs_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hσ)), div_eq_inv_mul]
  refine hsq.congr ?_
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn ω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn' : (0 : ℝ) < m n := by exact_mod_cast hmn
  have e1 : √(n : ℝ) * seHat n (m n) 0 (smp X h n ω) (smp Y h (m n) ω) = √(A n ω) := by
    simp only [seHat, A, sub_zero, div_one]
    rw [← Real.sqrt_mul hn'.le]
    congr 1
    have : (fun j => -smp Y h (m n) ω j) = smp Y (fun x => -h x) (m n) ω := rfl
    rw [this]
    field_simp
  rw [e1]

/-- Coverage of the plug-in lower limit at `α = 0` (`σ₀² > 0`). -/
theorem coverage_zero (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ))
    (hσ : 0 < Var[h; P] + Var[h; Q] / κ) (z : ℝ) :
    Tendsto (fun n => μ.real {ω | statT X Y h m 0 n ω - z * seHat n (m n) 0 (smp X h n ω) (smp Y h (m n) ω) ≤
      ∫ x, h x ∂P - ∫ x, h x ∂Q}) atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic z))) := by
  set s2 := Var[h; P] + Var[h; Q] / κ
  have clt := clt_zero hX hY hXY hm hB hκ hmr
  have hσ' : 0 < √s2 := Real.sqrt_pos.2 hσ
  have hv : (√s2 ^ 2).toNNReal = s2.toNNReal := by rw [Real.sq_sqrt hσ.le]
  rw [← hv] at clt
  have hcons := tip0_seHat_zero hX hY hm hB hκ hmr hσ
  have key := coverage_lim hσ' clt hcons (fun n => (measurable_seHat hX hY hm 0 m n).const_mul _) z
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  set T := statT X Y h m 0 n ω
  set se := seHat n (m n) 0 (smp X h n ω) (smp Y h (m n) ω)
  rw [show √(n : ℝ) * (T - (∫ x, h x ∂P - ∫ x, h x ∂Q)) - z * (√(n : ℝ) * se) =
      √(n : ℝ) * ((T - z * se) - (∫ x, h x ∂P - ∫ x, h x ∂Q)) by ring]
  constructor
  · intro hle
    by_contra hc
    push_neg at hc
    have := mul_pos hs (sub_pos.2 hc)
    linarith
  · intro hle
    exact mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith)

/-- The degenerate case `σ₀² = 0`: eventually the lower limit equals `P h − Q h` almost surely. -/
theorem coverage_zero_degenerate (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hσ : Var[h; P] + Var[h; Q] / κ = 0) (z : ℝ) :
    ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, statT X Y h m 0 n ω - z * seHat n (m n) 0 (smp X h n ω) (smp Y h (m n) ω) =
      ∫ x, h x ∂P - ∫ x, h x ∂Q := by
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
  have hvP : Var[h; P] = 0 := by
    have := variance_nonneg h P; have := div_nonneg (variance_nonneg h Q) hκ.le; linarith
  have hvQ : Var[h; Q] = 0 := by
    have h1 := variance_nonneg h P; have h2 := div_nonneg (variance_nonneg h Q) hκ.le
    have : Var[h; Q] / κ = 0 := by linarith
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hκ.ne'
  have hB0 : ∀ x, |h x| ≤ |B| := fun x => (hB x).trans (le_abs_self B)
  have hmem : ∀ R : Measure 𝒳, [IsProbabilityMeasure R] → MemLp h 2 R := fun R _ =>
    MemLp.of_bound hm.aestronglyMeasurable |B| (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB0 x)
  have haeP := ae_eq_integral_of_variance_eq_zero (hmem P) hvP
  have haeQ := ae_eq_integral_of_variance_eq_zero (hmem Q) hvQ
  set a := ∫ x, h x ∂P
  set b := ∫ x, h x ∂Q
  have hXa : ∀ᵐ ω ∂μ, ∀ i, h (X i ω) = a := by
    rw [ae_all_iff]; intro i
    have := haeP; rw [← hX.law i] at this
    exact ae_of_ae_map (hX.meas i).aemeasurable this
  have hYb : ∀ᵐ ω ∂μ, ∀ j, h (Y j ω) = b := by
    rw [ae_all_iff]; intro j
    have := haeQ; rw [← hY.law j] at this
    exact ae_of_ae_map (hY.meas j).aemeasurable this
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn
  filter_upwards [hXa, hYb] with ω hω1 hω2
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmn' : (m n : ℝ) ≠ 0 := by exact_mod_cast hmn.ne'
  have hsx : smp X h n ω = fun _ => a := funext fun i => hω1 i
  have hsy : smp Y h (m n) ω = fun _ => b := funext fun j => hω2 j
  have hvx : varLo n 0 (fun _ : Fin n => a) = 0 := by
    rw [varLo_zero hn]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  have hvy : varLo (m n) 0 (fun _ : Fin (m n) => -b) = 0 := by
    rw [varLo_zero hmn]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  have hse : seHat n (m n) 0 (smp X h n ω) (smp Y h (m n) ω) = 0 := by
    rw [hsx, hsy]
    simp only [seHat]
    rw [hvx, show (fun j : Fin (m n) => -(fun _ : Fin (m n) => b) j) = fun _ => -b from rfl, hvy]
    simp
  rw [hse, statT_zero hn hmn]
  simp only [hω1, hω2, sum_const, card_range, nsmul_eq_mul, mul_zero, sub_zero]
  field_simp

end StatFormal.Foundations.TrimmedMean
