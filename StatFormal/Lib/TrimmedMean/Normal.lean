import StatFormal.Lib.TrimmedMean.Variance
import StatFormal.Lib.CLT.TwoSample
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The two-sample split statistic: asymptotic normality, plug-in standard error, coverage (library)

`X` i.i.d. `P`, `Y` i.i.d. `Q`, independent, sizes `n`, `m(n)` with `m(n)/n → κ > 0`; `h : 𝒳 → ℝ` bounded
measurable; `β = 1 − α`, `q` the unique `β`-quantile of `h` under `P`, `q'` the unique `α`-quantile under `Q`.

* `clt_split`: `√n (T̂_n − T₀) ⇝ N(0, σ²)` with `T̂_n = min_{capped n} Σ w_i h(X_i) − max_{capped m} Σ w_j h(Y_j)`,
  `T₀ = L(P) − U(Q)` and `σ² = (Var_P (q − h)_+ + Var_Q (h − q')_+ / κ)/β²`;
* `tip0_seHat`: the plug-in `√n ŝe_n → σ` in probability;
* `coverage_lim`: Slutsky + portmanteau: `P(A_n − z S_n ≤ 0) → Φ(z)` when `A_n ⇝ N(0,σ²)`, `S_n → σ > 0`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Foundations.TrimmedMean

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.CLT

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X Y : ℕ → Ω → 𝒳}

/-- Population lower trimmed mean `q − β⁻¹ P (q − h)_+`. -/
def popLo (P : Measure 𝒳) (h : 𝒳 → ℝ) (α q : ℝ) : ℝ := q - (1 - α)⁻¹ * ∫ x, max (q - h x) 0 ∂P

/-- Population upper trimmed mean `q' + β⁻¹ Q (h − q')_+`. -/
def popUp (Q : Measure 𝒳) (h : 𝒳 → ℝ) (α q' : ℝ) : ℝ := q' + (1 - α)⁻¹ * ∫ x, max (h x - q') 0 ∂Q

/-- The asymptotic variance. -/
def sigma2 (P Q : Measure 𝒳) (h : 𝒳 → ℝ) (α q q' κ : ℝ) : ℝ :=
  (Var[fun x => max (q - h x) 0; P] + Var[fun x => max (h x - q') 0; Q] / κ) / (1 - α) ^ 2

/-- The split statistic. -/
def statT (X Y : ℕ → Ω → 𝒳) (h : 𝒳 → ℝ) (m : ℕ → ℕ) (α : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sInf ((fun w => ∑ i, w i * smp X h n ω i) '' capped n α) -
    sSup ((fun w => ∑ j, w j * smp Y h (m n) ω j) '' capped (m n) α)

/-- The plug-in standard error. -/
def seHat (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ :=
  √(varLo n α vx / n + varLo m α (fun j => -vy j) / m) / (1 - α)

lemma integral_comp_law (hS : IIDSample μ P X) (i : ℕ) {F : 𝒳 → ℝ} (hF : Measurable F) :
    ∫ ω, F (X i ω) ∂μ = ∫ x, F x ∂P := by
  rw [← hS.law i, integral_map (hS.meas i).aemeasurable hF.aestronglyMeasurable]

lemma measurable_statT (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (m : ℕ → ℕ) (n : ℕ) : Measurable (statT X Y h m α n) :=
  ((measurable_trimLo hα0 hα1).comp (measurable_smp hX hm n)).sub
    ((measurable_trimUp hα0 hα1).comp (measurable_smp hY hm (m n)))

lemma measurable_seHat (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) (α : ℝ)
    (m : ℕ → ℕ) (n : ℕ) : Measurable fun ω => seHat n (m n) α (smp X h n ω) (smp Y h (m n) ω) := by
  unfold seHat
  refine (Measurable.sqrt (((measurable_varLo α).comp (measurable_smp hX hm n)).div_const _ |>.add
    (((measurable_varLo α).comp ((measurable_smp hY hm (m n)).neg)).div_const _))).div_const _

/-! ### Influence terms -/

lemma clt_terms (hS : IIDSample μ P X) {g : 𝒳 → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) (b : ℝ) :
    let U : ℕ → Ω → ℝ := fun i ω => b * (g (X i ω) - ∫ x, g x ∂P)
    (∀ i, Measurable (U i)) ∧ iIndepFun U μ ∧ (∀ i, IdentDistrib (U i) (U 0) μ μ) ∧ MemLp (U 0) 2 μ ∧
      μ[U 0] = 0 ∧ Var[U 0; μ] = b ^ 2 * Var[g; P] := by
  intro U
  set F : 𝒳 → ℝ := fun z => b * (g z - ∫ x, g x ∂P)
  have hF : Measurable F := (hg.sub_const _).const_mul b
  have hUF : ∀ i, U i = F ∘ X i := fun i => rfl
  have hFb : ∀ z, |F z| ≤ |b| * (C + C) := fun z => by
    simp only [F, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hC z) (abs_integral_le_of_abs_le hC)))
      (abs_nonneg _)
  refine ⟨fun i => hF.comp (hS.meas i), hS.indep.comp (fun _ => F) (fun _ => hF), fun i => ?_, ?_, ?_, ?_⟩
  · have hid : IdentDistrib (X i) (X 0) μ μ :=
      ⟨(hS.meas i).aemeasurable, (hS.meas 0).aemeasurable, by rw [hS.law i, hS.law 0]⟩
    exact hid.comp hF
  · exact MemLp.of_bound (hF.comp (hS.meas 0)).aestronglyMeasurable _ (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hFb _)
  · show ∫ ω, F (X 0 ω) ∂μ = 0
    rw [integral_comp_law hS 0 hF]
    simp only [F]
    rw [integral_const_mul, integral_sub (integrable_of_abs_le hg hC) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self, mul_zero]
  · rw [hUF 0, ← variance_map hF.aemeasurable (hS.meas 0).aemeasurable, hS.law 0]
    simp only [F]
    rw [variance_const_mul, variance_sub_const hg.aestronglyMeasurable]

/-! ### Asymptotic normality -/

lemma alg_two {s r m b A A' SX SY : ℝ} (hr : r ≠ 0) (hm : r * r = m) :
    s * A + s * A' - (b * (s⁻¹ * SX) + b * (s / m * SY)) * (-1) =
      (s * A + b * (s⁻¹ * SX)) + (r * A' + b * (r⁻¹ * SY)) * (s / r) := by
  subst hm
  field_simp
  ring

theorem clt_split (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (statT X Y h m α n ω - (popLo P h α q - popUp Q h α q')))
      atTop id (fun _ => μ) (gaussianReal 0 (sigma2 P Q h α q q' κ).toNNReal) := by
  have hβ : 0 < 1 - α := by linarith
  set β := 1 - α with hβdef
  have hQ' : UQ Q (fun x => -h x) (1 - α) (-q') := by
    have := hQ.neg hm; simpa only [sub_sub_cancel] using this
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
  -- influence functions
  set g : 𝒳 → ℝ := fun x => max (q - h x) 0
  set g' : 𝒳 → ℝ := fun x => max (-q' - -h x) 0
  have hg' : g' = fun x => max (h x - q') 0 := funext fun x => by simp only [g']; ring_nf
  have hgm : Measurable g := (hm.const_sub q).max measurable_const
  have hgm' : Measurable g' := (hm.neg.const_sub (-q')).max measurable_const
  have hB0 : ∀ x, |h x| ≤ |B| := fun x => (hB x).trans (le_abs_self B)
  have hgb : ∀ x, |g x| ≤ |q| + |B| := fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := le_abs_self q; have := neg_abs_le (h x); have := hB0 x; linarith
  have hgb' : ∀ x, |g' x| ≤ |q'| + |B| := fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := neg_abs_le q'; have := le_abs_self (h x); have := hB0 x; linarith
  obtain ⟨hUm, hUi, hUid, hU2, hU0, hUv⟩ := clt_terms hX hgm hgb (-β⁻¹)
  obtain ⟨hWm, hWi, hWid, hW2, hW0, hWv⟩ := clt_terms hY hgm' hgb' (-β⁻¹)
  set U : ℕ → Ω → ℝ := fun i ω => -β⁻¹ * (g (X i ω) - ∫ x, g x ∂P)
  set W : ℕ → Ω → ℝ := fun i ω => -β⁻¹ * (g' (Y i ω) - ∫ x, g' x ∂Q)
  have hUW : IndepFun (fun ω i => U i ω) (fun ω i => W i ω) μ := by
    have hf : Measurable fun (x : ℕ → 𝒳) (i : ℕ) => -β⁻¹ * (g (x i) - ∫ x, g x ∂P) :=
      measurable_pi_iff.2 fun i => ((hgm.comp (measurable_pi_apply i)).sub_const _).const_mul _
    have hf' : Measurable fun (x : ℕ → 𝒳) (i : ℕ) => -β⁻¹ * (g' (x i) - ∫ x, g' x ∂Q) :=
      measurable_pi_iff.2 fun i => ((hgm'.comp (measurable_pi_apply i)).sub_const _).const_mul _
    exact hXY.comp hf hf'
  have hvar : (Var[U 0; μ] + Var[W 0; μ] / κ) = sigma2 P Q h α q q' κ := by
    rw [hUv, hWv, sigma2, hg', ← hβdef]
    field_simp
    ring
  have hG : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (Var[U 0; μ] + Var[W 0; μ] / κ).toNNReal)
      (gaussianReal 0 (sigma2 P Q h α q q' κ).toNNReal) := by
    rw [hvar]; exact ⟨aemeasurable_id, Measure.map_id⟩
  have hlin := clt_two_sample (fun i => hUm i) (fun i => hWm i) hUi hWi hUW hUid hWid hU2 hW2 hU0 hW0 hκ hmr hG
  -- the remainders
  have hR := tip0_trimLo hX hm hα0 hα1 hP
  have hR' := tip0_trimLo hY hm.neg hα0 hα1 hQ'
  have hR'm : TIP0 μ (fun n ω => alRem Y Q (fun x => -h x) α (-q') (m n) ω) := fun ε hε => (hR' ε hε).comp hmtop
  have hrat : BIP μ (fun n (_ : Ω) => √(n : ℝ) / √(m n : ℝ)) := bip_det (tendsto_sqrt_ratio hκ hmr)
  have hE : TIP0 μ (fun n ω => alRem X P h α q n ω + alRem Y Q (fun x => -h x) α (-q') (m n) ω *
      (√(n : ℝ) / √(m n : ℝ))) := hR.add (hR'm.mul_bip hrat)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hlin ?_ fun n =>
    (((measurable_statT hX hY hm hα0 hα1 m n).sub_const _).const_mul _).aemeasurable
  rw [tip0_iff]
  refine hE.congr ?_
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn ω
  have hmn' : (0 : ℝ) < m n := by exact_mod_cast hmn
  have hr : √(m n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hmn').ne'
  have hup := trimUp_eq hmn hα0 hα1 (smp Y h (m n) ω)
  have hPU : popUp Q h α q' = -(-q' - (1 - α)⁻¹ * ∫ x, max (-q' - -h x) 0 ∂Q) := by
    rw [popUp, ← hg']; ring
  simp only [Pi.sub_apply, statT, hup, alRem, popLo, hPU]
  have hsX : ∑ i ∈ range n, U i ω = -β⁻¹ * ∑ i ∈ range n, (max (q - h (X i ω)) 0 - ∫ x, max (q - h x) 0 ∂P) := by
    rw [mul_sum]
  have hsY : ∑ i ∈ range (m n), W i ω =
      -β⁻¹ * ∑ i ∈ range (m n), (max (-q' - -h (Y i ω)) 0 - ∫ x, max (-q' - -h x) 0 ∂Q) := by
    rw [mul_sum]
  rw [hsX, hsY]
  have e1 : (fun w : Fin (m n) → ℝ => ∑ i, w i * (fun i => -smp Y h (m n) ω i) i) =
      fun w => ∑ i, w i * smp Y (fun x => -h x) (m n) ω i := rfl
  rw [e1]
  rw [← alg_two hr (Real.mul_self_sqrt hmn'.le)]
  ring

/-! ### Plug-in standard error -/

lemma abs_sqrt_sub_sqrt_le {a S : ℝ} (hS : 0 < S) : |√a - √S| ≤ |a - S| / √S := by
  have hs : 0 < √S := Real.sqrt_pos.2 hS
  rw [le_div_iff₀ hs]
  rcases le_or_gt a 0 with ha | ha
  · rw [Real.sqrt_eq_zero'.2 ha, zero_sub, abs_neg, abs_of_pos hs, abs_of_nonpos (by linarith)]
    have : √S * √S = S := Real.mul_self_sqrt hS.le
    nlinarith
  · have hsa : 0 < √a := Real.sqrt_pos.2 ha
    have e : |a - S| = |√a - √S| * (√a + √S) := by
      rw [← abs_of_pos (by positivity : 0 < √a + √S), ← abs_mul]
      congr 1
      have h1 : √a * √a = a := Real.mul_self_sqrt ha.le
      have h2 : √S * √S = S := Real.mul_self_sqrt hS.le
      nlinarith
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

theorem tip0_seHat (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q')
    (hσ : 0 < sigma2 P Q h α q q' κ) :
    TIP0 μ (fun n ω => √(n : ℝ) * seHat n (m n) α (smp X h n ω) (smp Y h (m n) ω) -
      √(sigma2 P Q h α q q' κ)) := by
  have hβ : 0 < 1 - α := by linarith
  have hQ' : UQ Q (fun x => -h x) (1 - α) (-q') := by
    have := hQ.neg hm; simpa only [sub_sub_cancel] using this
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
  set Vg := Var[fun x => max (q - h x) 0; P]
  set Vg' := Var[fun x => max (-q' - -h x) 0; Q]
  have hg' : (fun x => max (-q' - -h x) 0) = fun x => max (h x - q') 0 := funext fun x => by ring_nf
  set S := Vg + Vg' / κ
  have hSσ : sigma2 P Q h α q q' κ = S / (1 - α) ^ 2 := by
    simp only [sigma2, S, Vg, Vg', hg']
  have hS : 0 < S := by
    rw [hSσ] at hσ
    exact (div_pos_iff_of_pos_right (by positivity)).1 hσ
  have h1 := tip0_varLo hX hm hB hα0 hα1 hP
  have h2 := tip0_varLo (h := fun x => -h x) hY hm.neg (B := B) (fun x => by rw [abs_neg]; exact hB x) hα0 hα1 hQ'
  have h2m : TIP0 μ (fun n ω => varLo (m n) α (smp Y (fun x => -h x) (m n) ω) - Vg') :=
    fun ε hε => (h2 ε hε).comp hmtop
  have hinv : Tendsto (fun n : ℕ => (n : ℝ) / m n) atTop (𝓝 κ⁻¹) := by
    have := hmr.inv₀ hκ.ne'
    refine this.congr fun n => ?_
    rw [inv_div]
  set A : ℕ → Ω → ℝ := fun n ω => varLo n α (smp X h n ω) + (n : ℝ) / m n * varLo (m n) α (smp Y (fun x => -h x) (m n) ω)
  have hA : TIP0 μ (fun n ω => A n ω - S) := by
    have hdet : Tendsto (fun n : ℕ => ((n : ℝ) / m n - κ⁻¹) * Vg') atTop (𝓝 0) := by
      simpa using (hinv.sub_const κ⁻¹).mul_const Vg'
    have := (h1.add (h2m.bip_mul (bip_det hinv))).add (tip0_det (P := μ) hdet)
    refine this.congr (Eventually.of_forall fun n ω => ?_)
    simp only [A, S]
    ring
  have hsq : TIP0 μ (fun n ω => √(A n ω) - √S) := by
    refine TIP0.of_dominated ((hA.abs').const_mul (√S)⁻¹) (Bad := fun _ => ∅) (by simp)
      (Eventually.of_forall fun n ω _ => ?_)
    refine (abs_sqrt_sub_sqrt_le hS).trans ?_
    rw [abs_mul, abs_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hS)), div_eq_inv_mul]
  refine (hsq.const_mul (1 - α)⁻¹).congr ?_
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn ω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn' : (0 : ℝ) < m n := by exact_mod_cast hmn
  have e1 : √(n : ℝ) * seHat n (m n) α (smp X h n ω) (smp Y h (m n) ω) = √(A n ω) / (1 - α) := by
    simp only [seHat, A]
    rw [← mul_div_assoc, ← Real.sqrt_mul hn'.le]
    congr 2
    have : (fun j => -smp Y h (m n) ω j) = smp Y (fun x => -h x) (m n) ω := rfl
    rw [this]
    field_simp
  have e2 : √(sigma2 P Q h α q q' κ) = √S / (1 - α) := by
    rw [hSσ, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hβ.le]
  rw [e1, e2]
  ring

/-! ### Coverage via Slutsky and the portmanteau theorem -/

theorem coverage_lim {A S : ℕ → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hA : TendstoInDistribution A atTop id (fun _ => μ) (gaussianReal 0 (σ ^ 2).toNNReal))
    (hS : TIP0 μ (fun n ω => S n ω - σ)) (hSm : ∀ n, Measurable (S n)) (z : ℝ) :
    Tendsto (fun n => μ.real {ω | A n ω - z * S n ω ≤ 0}) atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic z))) := by
  have hS' : TendstoInMeasure μ S atTop (fun _ => σ) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    simpa only [Real.norm_eq_abs] using hS ε hε
  have hD := hA.continuous_comp_prodMk_of_tendstoInMeasure_const (g := fun p : ℝ × ℝ => p.1 - z * p.2)
    (by fun_prop) hS' (fun n => (hSm n).aemeasurable)
  set ν := gaussianReal 0 (σ ^ 2).toNNReal
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have : NullSingletonClass ν := nullSingletonClass_gaussianReal hv
  have hLm : Measurable fun x : ℝ => id x - z * σ := measurable_id.sub_const _
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hD.tendsto (E := Set.Iic (0 : ℝ)) (by
    rw [frontier_Iic]
    change ((ν.map (fun x => id x - z * σ)) {0}).toNNReal = 0
    rw [Measure.map_apply hLm (measurableSet_singleton _)]
    have : (fun x : ℝ => id x - z * σ) ⁻¹' {0} = {z * σ} := by
      ext x; simp [sub_eq_zero]
    rw [this, measure_singleton]; rfl)
  have key' := NNReal.tendsto_coe.2 key
  have hlim : ((((ν.map (fun x => id x - z * σ)) (Set.Iic 0)).toNNReal : ℝ≥0) : ℝ) =
      (gaussianReal 0 1).real (Set.Iic z) := by
    rw [ENNReal.coe_toNNReal_eq_toReal]
    change (ν.map (fun x => id x - z * σ)).real (Set.Iic 0) = _
    rw [map_measureReal_apply hLm measurableSet_Iic]
    have hν : ν = (gaussianReal 0 1).map (σ * ·) := by
      rw [gaussianReal_map_const_mul, mul_zero]
      change gaussianReal 0 (σ ^ 2).toNNReal = _
      congr 1
      ext
      simp [Real.coe_toNNReal _ (sq_nonneg σ)]
    rw [hν, map_measureReal_apply (measurable_const_mul σ) (measurableSet_Iic.preimage hLm)]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, id]
    constructor
    · intro hx; nlinarith
    · intro hx; nlinarith
  have key'' : Tendsto (fun n => (((μ.map fun ω => A n ω - z * S n ω) (Set.Iic 0)).toNNReal : ℝ)) atTop
      (𝓝 ((((ν.map (fun x => id x - z * σ)) (Set.Iic 0)).toNNReal : ℝ≥0) : ℝ)) := key'
  rw [hlim] at key''
  refine key''.congr fun n => ?_
  rw [ENNReal.coe_toNNReal_eq_toReal]
  show (μ.map fun ω => A n ω - z * S n ω).real (Set.Iic 0) = _
  rw [map_measureReal_apply_of_aemeasurable (hD.forall_aemeasurable n) measurableSet_Iic]
  rfl

end StatFormal.Foundations.TrimmedMean
