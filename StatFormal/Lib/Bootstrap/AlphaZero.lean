import StatFormal.Lib.Bootstrap.Percentile
import StatFormal.Lib.TrimmedMean.AlphaZero

/-!
# The bootstrap of the split statistic at `α = 0`: the classical bootstrap of a difference of means (library)

At `α = 0` both extreme trimmed means are sample means (`Foundations/TrimmedMean/AlphaZero`), so the resampled
statistic is `T̂* = v̄_x* − v̄_y*` and no quantile condition is needed:

* `bootD_zero`: the duality remainder of `Foundations/Bootstrap/TrimVar` vanishes identically at `α = 0`;
* `bVar_tLo_zero`, `bootVar2_zero`: the exact bootstrap variance `Var*(T̂*) = s²_X/n + s²_Y/m` (the `1/n` sample
  variances), i.e. the ideal bootstrap variance equals the plug-in variance;
* `tip0_bootVar2_zero`: `n Var*(T̂*) → σ₀² = Var_P h + Var_Q h/κ` in probability (also when `σ₀² = 0`);
* `tip0_bootCdf_zero`: the bootstrap CLT in probability (`σ₀² > 0`), from the deterministic uniform bootstrap CLT
  `boot_root_unif` at `α = 0` (remainders identically zero) and the plug-in consistency `tip0_varLo_zero`;
* `perc_coverage_zero`, `perc_le_degenerate`: coverage of the percentile lower limit (`σ₀² > 0`, through
  `perc_coverage_of`), and in the degenerate case `σ₀² = 0` almost surely eventually every replicate equals
  `P h − Q h`, so the percentile limit is `≤ P h − Q h`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Foundations.Bootstrap

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT

/-! ### Deterministic identities -/

section Det

variable {n : ℕ}

lemma tLo_zero (hn : 0 < n) (v : Fin n → ℝ) : tLo n 0 v = (∑ i, v i) / n := trimLo_zero hn v

lemma tUp_zero' (hn : 0 < n) (v : Fin n → ℝ) : tUp n 0 v = (∑ i, v i) / n := trimUp_zero hn v

/-- At `α = 0` the duality remainder is identically zero. -/
lemma bootD_zero (hn : 0 < n) (v : Fin n → ℝ) (I : Fin n → Fin n) : bootD v 0 I = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmax : ∀ i, max (quantLo n 0 v - v (I i)) 0 = quantLo n 0 v - v (I i) := fun i =>
    max_eq_left (sub_nonneg.2 (le_quantLo_zero v (I i)))
  unfold bootD emean
  simp only [tLo_zero hn, sub_zero, one_mul, Function.comp]
  simp only [hmax, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The bootstrap variance of a resampled mean: `Var*(v̄*) = varLo n 0 v / n` (the `1/n` sample variance over `n`). -/
lemma bVar_tLo_zero (hn : 0 < n) (v : Fin n → ℝ) :
    bVar (fun I : Fin n → Fin n => tLo n 0 (v ∘ I)) = varLo n 0 v / n := by
  have : Nonempty (Fin n → Fin n) := ⟨fun i => i⟩
  have e : (fun I : Fin n → Fin n => tLo n 0 (v ∘ I)) = fun I => (∑ i, v (I i)) / n := funext fun I => by
    rw [tLo_zero hn]; rfl
  have hmean : bAvg (fun I : Fin n → Fin n => (∑ i, v (I i)) / n) = (∑ j, v j) / n := by
    have h := bAvg_resample_mean hn v
    rw [bAvg_sub, bAvg_const] at h
    linarith
  rw [e]
  unfold bVar
  rw [hmean, bAvg_resample_sq hn v, varLo_zero hn]

/-- **The bootstrap variance at `α = 0`**: `Var*(T̂*) = varLo n 0 v_x / n + varLo m 0 (−v_y) / m`. -/
lemma bootVar2_zero {m : ℕ} (hn : 0 < n) (hm : 0 < m) (vx : Fin n → ℝ) (vy : Fin m → ℝ) :
    bootVar2 n m 0 vx vy = varLo n 0 vx / n + varLo m 0 (fun j => -vy j) / m := by
  have h := bootVar2_eq hn hm le_rfl zero_lt_one vx vy
  simp only [sub_zero, one_pow, one_mul] at h
  rw [h, bVar_tLo_zero hn, bVar_tLo_zero hm]

end Det

/-! ### Probabilistic statements -/

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X Y : ℕ → Ω → 𝒳}

/-- **Bootstrap variance consistency at `α = 0`** (no quantile condition, `σ₀² = 0` allowed):
`n Var*(T̂*) → Var_P h + Var_Q h/κ` in probability. -/
theorem tip0_bootVar2_zero (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) :
    TIP0 μ (fun n ω => (n : ℝ) * bootVar2 n (m n) 0 (smp X h n ω) (smp Y h (m n) ω) -
      (Var[h; P] + Var[h; Q] / κ)) := by
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
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
  have hdet : Tendsto (fun n : ℕ => ((n : ℝ) / m n - κ⁻¹) * Var[h; Q]) atTop (𝓝 0) := by
    simpa using (hinv.sub_const κ⁻¹).mul_const (Var[h; Q])
  have hA := (h1.add (h2m.bip_mul (bip_det hinv))).add (tip0_det (P := μ) hdet)
  refine hA.congr ?_
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn ω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn' : (0 : ℝ) < m n := by exact_mod_cast hmn
  rw [bootVar2_zero hn hmn]
  have e : (fun j => -smp Y h (m n) ω j) = smp Y (fun x => -h x) (m n) ω := rfl
  rw [e]
  field_simp
  ring

/-- **Bootstrap standard error consistency at `α = 0`**: `√n · √Var*(T̂*) → σ₀` in probability, `σ₀² > 0`. -/
theorem tip0_bootSE_zero (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ))
    (hσ : 0 < Var[h; P] + Var[h; Q] / κ) :
    TIP0 μ (fun n ω => √(n : ℝ) * √(bootVar2 n (m n) 0 (smp X h n ω) (smp Y h (m n) ω)) -
      √(Var[h; P] + Var[h; Q] / κ)) := by
  have hA := tip0_bootVar2_zero hX hY hm hB hκ hmr
  refine TIP0.of_dominated ((hA.abs').const_mul (√(Var[h; P] + Var[h; Q] / κ))⁻¹) (Bad := fun _ => ∅) (by simp)
    (Eventually.of_forall fun n ω _ => ?_)
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
  refine (abs_sqrt_sub_sqrt_le hσ).trans ?_
  rw [abs_mul, abs_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hσ)), div_eq_inv_mul]

/-- **Bootstrap CLT in probability at `α = 0`**: for every `t`, the bootstrap cdf of the root `√n (T̂* − T̂)` at
`t` converges in probability to `Φ_{σ₀}(t)`, `σ₀² = Var_P h + Var_Q h/κ > 0`. -/
theorem tip0_bootCdf_zero (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ))
    (hσ : 0 < Var[h; P] + Var[h; Q] / κ) (t : ℝ) :
    TIP0 μ (fun n ω => bAvg (fun p => if bootRoot n (m n) 0 (smp X h n ω) (smp Y h (m n) ω) p ≤ t then (1 : ℝ) else 0) -
      (gaussianReal 0 (Var[h; P] + Var[h; Q] / κ).toNNReal).real (Set.Iic t)) := by
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
  have hneg : Var[fun x => -h x; Q] = Var[h; Q] := variance_fun_neg
  have hσ' : 0 < (Var[h; P] + Var[h; Q] / κ) / (1 - 0) ^ 2 := by simpa using hσ
  have hS : (Var[h; P] + Var[h; Q] / κ) / (1 - 0 : ℝ) ^ 2 = Var[h; P] + Var[h; Q] / κ := by simp
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := boot_root_unif (B := B) hκ hmr le_rfl zero_lt_one hσ' t hε
  rw [hS] at hN
  have e1 := tip0_varLo_zero hX hm hB δ hδ
  have e2' := tip0_varLo_zero (h := fun x => -h x) hY hm.neg (B := B) (fun x => by rw [abs_neg]; exact hB x) δ hδ
  rw [hneg] at e2'
  have e2 := e2'.comp hmtop
  have hsum := e1.add e2
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hn0 hmn
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Function.comp] at hω ⊢
  by_contra hc
  push_neg at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hD1 : (n : ℝ) * bAvg (fun I : Fin n → Fin n => bootD (smp X h n ω) 0 I ^ 2) < δ := by
    simp only [bootD_zero hn0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    have : Nonempty (Fin n → Fin n) := ⟨fun i => i⟩
    rw [bAvg_const, mul_zero]; exact hδ
  have hD2 : (m n : ℝ) * bAvg (fun J : Fin (m n) → Fin (m n) => bootD (fun j => -smp Y h (m n) ω j) 0 J ^ 2) < δ := by
    simp only [bootD_zero hmn, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    have : Nonempty (Fin (m n) → Fin (m n)) := ⟨fun i => i⟩
    rw [bAvg_const, mul_zero]; exact hδ
  have := hN n hn (smp X h n ω) (smp Y h (m n) ω) (fun i => hB _) (fun j => hB _) hc1 hc2 hD1 hD2
  linarith

/-- **Coverage of the percentile lower limit at `α = 0`** (`σ₀² > 0`): `liminf P(percLo ≤ P h − Q h) ≥ 1 − δ`. -/
theorem perc_coverage_zero (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ))
    (hσ : 0 < Var[h; P] + Var[h; Q] / κ) {δ z : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hz : (gaussianReal 0 1).real (Set.Ioi z) = δ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
      percLo n (m n) 0 δ (smp X h n ω) (smp Y h (m n) ω) ≤ ∫ x, h x ∂P - ∫ x, h x ∂Q} :=
  perc_coverage_of (tendsto_atTop_of_ratio hκ hmr) hσ (clt_zero hX hY hXY hm hB hκ hmr)
    (fun t => tip0_bootCdf_zero hX hY hm hB hκ hmr hσ t) hδ0 hδ1 hz

/-- **The degenerate case `σ₀² = 0`**: almost surely, eventually, the percentile lower limit is `≤ P h − Q h`
(every replicate equals `P h − Q h`). -/
theorem perc_le_degenerate (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, |h x| ≤ B) {κ : ℝ} {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hσ : Var[h; P] + Var[h; Q] / κ = 0) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, percLo n (m n) 0 δ (smp X h n ω) (smp Y h (m n) ω) ≤ ∫ x, h x ∂P - ∫ x, h x ∂Q := by
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
  have hrep : ∀ p : (Fin n → Fin n) × (Fin (m n) → Fin (m n)),
      tLo n 0 (smp X h n ω ∘ p.1) - tUp (m n) 0 (smp Y h (m n) ω ∘ p.2) = a - b := fun p => by
    rw [tLo_zero hn, tUp_zero' hmn]
    simp only [Function.comp, smp, hω1, hω2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have : Nonempty ((Fin n → Fin n) × (Fin (m n) → Fin (m n))) := ⟨(fun i => i, fun j => j)⟩
  set N := Fintype.card ((Fin n → Fin n) × (Fin (m n) → Fin (m n))) with hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have hk1 : 1 ≤ ⌈δ * (N : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.2 fun h0 => by
    rw [Nat.ceil_eq_zero] at h0; nlinarith
  have hkN : ⌈δ * (N : ℝ)⌉₊ ≤ N := Nat.ceil_le.2 (by nlinarith)
  unfold percLo
  rw [fOrd_le_iff hk1 hkN]
  have hf : (univ.filter fun p : (Fin n → Fin n) × (Fin (m n) → Fin (m n)) =>
      tLo n 0 (smp X h n ω ∘ p.1) - tUp (m n) 0 (smp Y h (m n) ω ∘ p.2) ≤ a - b) = univ :=
    Finset.filter_true_of_mem fun p _ => le_of_eq (hrep p)
  rw [hf, card_univ]
  exact hkN

end StatFormal.Foundations.Bootstrap
