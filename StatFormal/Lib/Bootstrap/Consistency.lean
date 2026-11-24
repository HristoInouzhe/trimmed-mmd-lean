import StatFormal.Lib.Bootstrap.TrimVar
import StatFormal.Lib.TrimmedMean.Normal

/-!
# Consistency of the bootstrap variance of the split statistic (library)

`X` i.i.d. `P`, `Y` i.i.d. `Q`, independent, `h` bounded measurable, `q` the unique `β`-quantile under `P`, `q'` the
unique `α`-quantile under `Q`, `m(n)/n → κ > 0`.

* `tip0_bootLo`: `√(n Var*(β L*)) − √varLo → 0` in probability (the deterministic `boot_trim_bound` with
  `d = ε/4`, `γ` from quantile uniqueness at `q ± d/2`, consistency of `ĉ` and of `F_n(q ± d/2)`, and
  `n e^{−2nγ²} → 0`);
* `tip0_bootLo_var`: `n Var*(β L*) → Var_P (q − h)_+` in probability;
* `bootVar2`: the bootstrap variance of `T̂* = L(v_x ∘ I) − U(v_y ∘ J)` under independent resampling of both samples;
  `bootVar2_eq`: `β² Var*(T̂*) = Var*(β L_X*) + Var*(β L_{−Y}*)`;
* `tip0_bootVar2`: `n Var*(T̂*) → σ²` in probability; `tip0_bootSE`: `√n · √Var*(T̂*) → σ` when `σ² > 0`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Foundations.Bootstrap

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT

lemma ecdf_mono {n : ℕ} (v : Fin n → ℝ) {x y : ℝ} (h : x ≤ y) : ecdf v x ≤ ecdf v y := by
  unfold ecdf
  refine div_le_div_of_nonneg_right (sum_le_sum fun i _ => ?_) (Nat.cast_nonneg n)
  by_cases h1 : v i ≤ x
  · rw [if_pos h1, if_pos (h1.trans h)]
  · rw [if_neg h1]; split_ifs <;> norm_num

lemma ecdfLt_mono {n : ℕ} (v : Fin n → ℝ) {x y : ℝ} (h : x ≤ y) : ecdfLt v x ≤ ecdfLt v y := by
  unfold ecdfLt
  refine div_le_div_of_nonneg_right (sum_le_sum fun i _ => ?_) (Nat.cast_nonneg n)
  by_cases h1 : v i < x
  · rw [if_pos h1, if_pos (h1.trans_le h)]
  · rw [if_neg h1]; split_ifs <;> norm_num

lemma tendsto_nat_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(c * n))) atTop (𝓝 0) := by
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have h2 := h1.const_mul c⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp, pow_one]
  field_simp

lemma varLo_nonneg {n : ℕ} (hn : 0 < n) (α : ℝ) (v : Fin n → ℝ) : 0 ≤ varLo n α v := by
  rw [← bVar_bootA v hn]
  exact mul_nonneg (Nat.cast_nonneg n) (bVar_nonneg _)

lemma varLo_le {n : ℕ} (hn : 0 < n) {α B : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {v : Fin n → ℝ}
    (hv : ∀ i, |v i| ≤ B) : varLo n α v ≤ (2 * B) ^ 2 := by
  have hc := abs_quantLo_le hn hα0 hα1 hv
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv ⟨0, hn⟩)
  unfold varLo
  have h1 : (∑ i, max (quantLo n α v - v i) 0 ^ 2) / n ≤ (2 * B) ^ 2 := by
    refine (avg_bounds hn (fun i => sq_nonneg _) fun i => ?_).2
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ (by positivity)) 2
    have := neg_abs_le (v i); have := hv i; have := le_abs_self (quantLo n α v); linarith
  nlinarith [sq_nonneg ((∑ i, max (quantLo n α v - v i) 0) / n)]

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X Y : ℕ → Ω → 𝒳}

/-- **Bootstrap consistency, one side**: `√(n Var*(β L*)) − √varLo → 0` in probability. -/
theorem tip0_bootLo (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    {α q : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hq : UQ P h (1 - α) q) :
    TIP0 μ (fun n ω => √((n : ℝ) * bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (smp X h n ω ∘ I))) -
      √(varLo n α (smp X h n ω))) := by
  have hq' := hq
  obtain ⟨-, -, hl, hr⟩ := hq
  intro ε hε
  set d : ℝ := ε / 4 with hd_def
  have hd : 0 < d := by positivity
  set γ : ℝ := min (P.real {z | h z ≤ q + d / 2} - (1 - α)) ((1 - α) - P.real {z | h z < q - d / 2}) / 2
    with hγ_def
  have hr' := hr (d / 2) (by positivity)
  have hl' := hl (d / 2) (by positivity)
  have hmin1 := min_le_left (P.real {z | h z ≤ q + d / 2} - (1 - α)) ((1 - α) - P.real {z | h z < q - d / 2})
  have hmin2 := min_le_right (P.real {z | h z ≤ q + d / 2} - (1 - α)) ((1 - α) - P.real {z | h z < q - d / 2})
  have hmin0 : 0 < min (P.real {z | h z ≤ q + d / 2} - (1 - α)) ((1 - α) - P.real {z | h z < q - d / 2}) :=
    lt_min (by linarith) (by linarith)
  have hγ : 0 < γ := by rw [hγ_def]; positivity
  have hγ1 : 1 - α + γ < P.real {z | h z ≤ q + d / 2} := by rw [hγ_def]; linarith
  have hγ2 : P.real {z | h z < q - d / 2} < 1 - α - γ := by rw [hγ_def]; linarith
  have h1 := tip0_quantLo hS hm hα0 hα1 hq' (d / 2) (by positivity)
  have h2 := tail_ecdf hS hm hγ1
  have h3 := tail_ecdfLt hS hm hγ2
  have hdet := tendsto_nat_mul_exp_neg (c := 2 * γ ^ 2) (by positivity)
  have hdet' : ∀ᶠ n : ℕ in atTop, 32 * B ^ 2 * ((n : ℝ) * Real.exp (-(2 * γ ^ 2 * n))) < ε ^ 2 / 4 := by
    have := hdet.const_mul (32 * B ^ 2)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  have hsum := (h1.add h2).add h3
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0, hdet'] with n hn hdn
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _))
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_contra hc
  push_neg at hc
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
  have hv : ∀ i, |smp X h n ω i| ≤ B := fun i => hB _
  have hc1' := abs_lt.1 hc1
  have hF : 1 - α + γ ≤ ecdf (smp X h n ω) (quantLo n α (smp X h n ω) + d) :=
    hc2.trans (ecdf_mono _ (by linarith [hc1'.1]))
  have hG : ecdfLt (smp X h n ω) (quantLo n α (smp X h n ω) - d) ≤ 1 - α - γ :=
    (ecdfLt_mono _ (by linarith [hc1'.2])).trans hc3.le
  have key := boot_trim_bound (smp X h n ω) hn hα0 hα1 hv hd.le hγ.le hF hG
  have hlt : √(4 * d ^ 2 + 32 * B ^ 2 * n * Real.exp (-2 * n * γ ^ 2)) < ε := by
    rw [Real.sqrt_lt' hε]
    have e : -2 * (n : ℝ) * γ ^ 2 = -(2 * γ ^ 2 * n) := by ring
    rw [e, hd_def]
    nlinarith
  linarith

/-- `n Var*(β L*) → Var_P (q − h)_+` in probability. -/
theorem tip0_bootLo_var (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    {α q : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hq : UQ P h (1 - α) q) :
    TIP0 μ (fun n ω => (n : ℝ) * bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (smp X h n ω ∘ I)) -
      Var[fun x => max (q - h x) 0; P]) := by
  have hs := tip0_bootLo hS hm hB hα0 hα1 hq
  have hv := tip0_varLo hS hm hB hα0 hα1 hq
  have hB0 : ∀ x, |h x| ≤ |B| := fun x => (hB x).trans (le_abs_self B)
  set s : ℕ → Ω → ℝ := fun n ω => √((n : ℝ) * bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (smp X h n ω ∘ I))) -
      √(varLo n α (smp X h n ω))
  have hW : TIP0 μ (fun n ω => |s n ω| * (4 * |B| + |s n ω|)) := by
    have a := hs.abs'.mul_bip ((bip_det (P := μ) (a := fun _ => 4 * |B|) tendsto_const_nhds).add (BIP.of_tip0 hs.abs'))
    exact a
  have hdiff : TIP0 μ (fun n ω => (n : ℝ) * bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (smp X h n ω ∘ I)) -
      varLo n α (smp X h n ω)) := by
    refine TIP0.of_dominated hW (Bad := fun _ => ∅) (by simp) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn ω _
    set a := (n : ℝ) * bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (smp X h n ω ∘ I))
    set b := varLo n α (smp X h n ω)
    have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg n) (bVar_nonneg _)
    have hb : 0 ≤ b := varLo_nonneg hn α _
    have hb4 : b ≤ (2 * |B|) ^ 2 := varLo_le hn hα0 hα1 fun i => hB0 _
    have hsb : √b ≤ 2 * |B| := Real.sqrt_le_iff.2 ⟨by positivity, hb4⟩
    have e : a - b = (√a - √b) * (√a + √b) := by
      have := Real.sq_sqrt ha; have := Real.sq_sqrt hb; nlinarith
    have hsn : s n ω = √a - √b := rfl
    rw [e, abs_mul, abs_mul, abs_abs, hsn]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (by positivity : 0 ≤ √a + √b)]
    have : √a ≤ √b + |√a - √b| := by have := le_abs_self (√a - √b); linarith
    rw [abs_of_nonneg (by positivity : 0 ≤ 4 * |B| + |√a - √b|)]
    linarith
  exact (hdiff.add hv).congr (Eventually.of_forall fun n ω => by ring)

/-- The bootstrap variance of `T̂* = L(v_x ∘ I) − U(v_y ∘ J)` under independent uniform resampling of both
samples. -/
def bootVar2 (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ :=
  bVar (fun p : (Fin n → Fin n) × (Fin m → Fin m) =>
    tLo n α (vx ∘ p.1) - sSup ((fun w => ∑ j, w j * (vy ∘ p.2) j) '' capped m α))

lemma bootVar2_eq {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (vx : Fin n → ℝ)
    (vy : Fin m → ℝ) :
    (1 - α) ^ 2 * bootVar2 n m α vx vy = bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (vx ∘ I)) +
      bVar (fun J : Fin m → Fin m => (1 - α) * tLo m α ((fun j => -vy j) ∘ J)) := by
  have : Nonempty (Fin n → Fin n) := ⟨fun i => i⟩
  have : Nonempty (Fin m → Fin m) := ⟨fun i => i⟩
  have e : (fun p : (Fin n → Fin n) × (Fin m → Fin m) =>
      tLo n α (vx ∘ p.1) - sSup ((fun w => ∑ j, w j * (vy ∘ p.2) j) '' capped m α)) =
      fun p => tLo n α (vx ∘ p.1) + tLo m α ((fun j => -vy j) ∘ p.2) := funext fun p => by
    rw [trimUp_eq hm hα0 hα1 (vy ∘ p.2), sub_neg_eq_add]
    rfl
  have hp := bVar_prod_add (fun I : Fin n → Fin n => tLo n α (vx ∘ I))
    (fun J : Fin m → Fin m => tLo m α ((fun j => -vy j) ∘ J))
  unfold bootVar2
  rw [e, hp, mul_add, ← bVar_const_mul, ← bVar_const_mul]

/-- **Bootstrap variance consistency**: `n Var*(T̂*) → σ²` in probability. -/
theorem tip0_bootVar2 (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q') :
    TIP0 μ (fun n ω => (n : ℝ) * bootVar2 n (m n) α (smp X h n ω) (smp Y h (m n) ω) - sigma2 P Q h α q q' κ) := by
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
  have h1 := tip0_bootLo_var hX hm hB hα0 hα1 hP
  have h2 := tip0_bootLo_var (h := fun x => -h x) hY hm.neg (B := B) (fun x => by rw [abs_neg]; exact hB x)
    hα0 hα1 hQ'
  have h2m : TIP0 μ (fun n ω => (m n : ℝ) * bVar (fun J : Fin (m n) → Fin (m n) =>
      (1 - α) * tLo (m n) α (smp Y (fun x => -h x) (m n) ω ∘ J)) - Vg') :=
    fun ε hε => (h2 ε hε).comp hmtop
  have hinv : Tendsto (fun n : ℕ => (n : ℝ) / m n) atTop (𝓝 κ⁻¹) := by
    have := hmr.inv₀ hκ.ne'
    refine this.congr fun n => ?_
    rw [inv_div]
  have hdet : Tendsto (fun n : ℕ => ((n : ℝ) / m n - κ⁻¹) * Vg') atTop (𝓝 0) := by
    simpa using (hinv.sub_const κ⁻¹).mul_const Vg'
  have hA := ((h1.add (h2m.bip_mul (bip_det hinv))).add (tip0_det (P := μ) hdet)).const_mul ((1 - α) ^ 2)⁻¹
  refine hA.congr ?_
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn ω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn' : (0 : ℝ) < m n := by exact_mod_cast hmn
  have hb := bootVar2_eq hn hmn hα0 hα1 (smp X h n ω) (smp Y h (m n) ω)
  have e : (fun j => -smp Y h (m n) ω j) = smp Y (fun x => -h x) (m n) ω := rfl
  rw [e] at hb
  have hb' : bootVar2 n (m n) α (smp X h n ω) (smp Y h (m n) ω) =
      (bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (smp X h n ω ∘ I)) +
        bVar (fun J : Fin (m n) → Fin (m n) => (1 - α) * tLo (m n) α (smp Y (fun x => -h x) (m n) ω ∘ J))) /
          (1 - α) ^ 2 := by
    rw [← hb]; field_simp
  rw [hb', hSσ]
  simp only [S]
  field_simp
  ring

/-- **Bootstrap standard error consistency**: `√n · √Var*(T̂*) → σ` in probability, `σ² > 0`. -/
theorem tip0_bootSE (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q')
    (hσ : 0 < sigma2 P Q h α q q' κ) :
    TIP0 μ (fun n ω => √(n : ℝ) * √(bootVar2 n (m n) α (smp X h n ω) (smp Y h (m n) ω)) -
      √(sigma2 P Q h α q q' κ)) := by
  have hA := tip0_bootVar2 hX hY hm hB hα0 hα1 hκ hmr hP hQ
  refine TIP0.of_dominated ((hA.abs').const_mul (√(sigma2 P Q h α q q' κ))⁻¹) (Bad := fun _ => ∅) (by simp)
    (Eventually.of_forall fun n ω _ => ?_)
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
  refine (abs_sqrt_sub_sqrt_le hσ).trans ?_
  rw [abs_mul, abs_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hσ)), div_eq_inv_mul]

end StatFormal.Foundations.Bootstrap
