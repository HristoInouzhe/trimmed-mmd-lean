import StatFormal.Lib.Bootstrap.Clt

/-!
# The bootstrap CLT for the split statistic, in probability (library)

* `boot_root_unif`: the sequential bootstrap CLT `boot_root_seq` in uniform (`ε`–`δ`) form, by contradiction over
  arbitrary data sequences;
* `tip0_bootD`: `n E*[D*²] → 0` in probability (the remainder of the duality decomposition);
* `tip0_bootCdf`: for every `t`, the bootstrap cdf of the root `√n (T̂* − T̂)` at `t` converges in probability to
  `Φ_σ(t)` — the conditional law of the root converges weakly to `N(0, σ²)` in probability.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatFormal.Foundations.Bootstrap

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT

/-- **Uniform bootstrap CLT** (deterministic). -/
theorem boot_root_unif {m : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ))
    {α B VX VY : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hσ : 0 < (VX + VY / κ) / (1 - α) ^ 2) (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ (vx : Fin n → ℝ) (vy : Fin (m n) → ℝ), (∀ i, |vx i| ≤ B) → (∀ j, |vy j| ≤ B) →
      |varLo n α vx - VX| < δ → |varLo (m n) α (fun j => -vy j) - VY| < δ →
      (n : ℝ) * bAvg (fun I => bootD vx α I ^ 2) < δ →
      (m n : ℝ) * bAvg (fun J => bootD (fun j => -vy j) α J ^ 2) < δ →
      |bAvg (fun p => if bootRoot n (m n) α vx vy p ≤ t then (1 : ℝ) else 0) -
        (gaussianReal 0 ((VX + VY / κ) / (1 - α) ^ 2).toNNReal).real (Set.Iic t)| < ε := by
  by_contra hcon
  push_neg at hcon
  choose nk hnk vx vy hbx hby h1 h2 h3 h4 h5 using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity) k
  have hn : Tendsto nk atTop atTop := tendsto_atTop_mono hnk tendsto_id
  have hmr' : Tendsto (fun k => (m (nk k) : ℝ) / nk k) atTop (𝓝 κ) := hmr.comp hn
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have conv : ∀ {a : ℕ → ℝ} {L : ℝ}, (∀ k, |a k - L| < 1 / ((k : ℝ) + 1)) → Tendsto a atTop (𝓝 L) :=
    fun {a L} ha => by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact (ha k).le) h0
  have conv0 : ∀ {a : ℕ → ℝ}, (∀ k, 0 ≤ a k) → (∀ k, a k < 1 / ((k : ℝ) + 1)) → Tendsto a atTop (𝓝 0) :=
    fun {a} ha0 ha => squeeze_zero ha0 (fun k => (ha k).le) h0
  have hseq := boot_root_seq hn hκ hmr' hα0 hα1 hbx hby (conv h1) (conv h2)
    (conv0 (fun k => mul_nonneg (Nat.cast_nonneg _) (bAvg_nonneg fun _ => sq_nonneg _)) h3)
    (conv0 (fun k => mul_nonneg (Nat.cast_nonneg _) (bAvg_nonneg fun _ => sq_nonneg _)) h4) hσ t
  have := (tendsto_iff_norm_sub_tendsto_zero.1 hseq).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := this.exists
  rw [Real.norm_eq_abs] at hk
  exact absurd (h5 k) (not_le.2 hk)

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X Y : ℕ → Ω → 𝒳}

/-- `n E*[D*²] → 0` in probability. -/
theorem tip0_bootD (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    {α q : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hq : UQ P h (1 - α) q) :
    TIP0 μ (fun n ω => (n : ℝ) * bAvg (fun I : Fin n → Fin n => bootD (smp X h n ω) α I ^ 2)) := by
  have hq' := hq
  obtain ⟨-, -, hl, hr⟩ := hq
  intro ε hε
  set d : ℝ := √ε / 4 with hd_def
  have hd : 0 < d := by have := Real.sqrt_pos.2 hε; positivity
  have hd2 : 4 * d ^ 2 = ε / 4 := by
    rw [hd_def, div_pow, Real.sq_sqrt hε.le]; ring
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
  have hdet' : ∀ᶠ n : ℕ in atTop, 32 * B ^ 2 * ((n : ℝ) * Real.exp (-(2 * γ ^ 2 * n))) < ε / 4 := by
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
  have key := bAvg_bootD_sq_le (smp X h n ω) hn hα0 hα1 hv hd.le hγ.le hF hG
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) * bAvg (fun I : Fin n → Fin n => bootD (smp X h n ω) α I ^ 2) :=
    mul_nonneg hn'.le (bAvg_nonneg fun _ => sq_nonneg _)
  rw [abs_of_nonneg hnn] at hω
  have : (n : ℝ) * bAvg (fun I : Fin n → Fin n => bootD (smp X h n ω) α I ^ 2) < ε := by
    calc (n : ℝ) * bAvg (fun I : Fin n → Fin n => bootD (smp X h n ω) α I ^ 2)
        ≤ n * (4 * d ^ 2 / n + 32 * B ^ 2 * Real.exp (-2 * n * γ ^ 2)) := mul_le_mul_of_nonneg_left key hn'.le
      _ = 4 * d ^ 2 + 32 * B ^ 2 * ((n : ℝ) * Real.exp (-(2 * γ ^ 2 * n))) := by
          rw [show -2 * (n : ℝ) * γ ^ 2 = -(2 * γ ^ 2 * n) by ring]; field_simp
      _ < ε := by rw [hd2]; linarith
  linarith

/-- **Bootstrap CLT in probability**: the bootstrap cdf of `√n (T̂* − T̂)` at `t` converges in probability to
`Φ_σ(t)`. -/
theorem tip0_bootCdf (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q')
    (hσ : 0 < sigma2 P Q h α q q' κ) (t : ℝ) :
    TIP0 μ (fun n ω => bAvg (fun p => if bootRoot n (m n) α (smp X h n ω) (smp Y h (m n) ω) p ≤ t then (1 : ℝ) else 0) -
      (gaussianReal 0 (sigma2 P Q h α q q' κ).toNNReal).real (Set.Iic t)) := by
  have hQ' : UQ Q (fun x => -h x) (1 - α) (-q') := by
    have := hQ.neg hm; simpa only [sub_sub_cancel] using this
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hmr
  set VX := Var[fun x => max (q - h x) 0; P]
  set VY := Var[fun x => max (-q' - -h x) 0; Q]
  have hg' : (fun x => max (-q' - -h x) 0) = fun x => max (h x - q') 0 := funext fun x => by ring_nf
  have hSσ : sigma2 P Q h α q q' κ = (VX + VY / κ) / (1 - α) ^ 2 := by
    simp only [sigma2, VX, VY, hg']
  rw [hSσ] at hσ ⊢
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := boot_root_unif (B := B) hκ hmr hα0 hα1 hσ t hε
  have e1 := tip0_varLo hX hm hB hα0 hα1 hP δ hδ
  have e2 := (tip0_varLo (h := fun x => -h x) hY hm.neg (B := B) (fun x => by rw [abs_neg]; exact hB x) hα0 hα1 hQ'
    δ hδ).comp hmtop
  have e3 := tip0_bootD hX hm hB hα0 hα1 hP δ hδ
  have e4 := (tip0_bootD (h := fun x => -h x) hY hm.neg (B := B) (fun x => by rw [abs_neg]; exact hB x) hα0 hα1 hQ'
    δ hδ).comp hmtop
  have hsum := ((e1.add e2).add e3).add e4
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add_left
    ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)) _))
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Function.comp] at hω ⊢
  by_contra hc
  push_neg at hc
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hc
  have hnn3 : 0 ≤ (n : ℝ) * bAvg (fun I : Fin n → Fin n => bootD (smp X h n ω) α I ^ 2) :=
    mul_nonneg (Nat.cast_nonneg _) (bAvg_nonneg fun _ => sq_nonneg _)
  have hnn4 : 0 ≤ (m n : ℝ) * bAvg (fun J : Fin (m n) → Fin (m n) => bootD (smp Y (fun x => -h x) (m n) ω) α J ^ 2) :=
    mul_nonneg (Nat.cast_nonneg _) (bAvg_nonneg fun _ => sq_nonneg _)
  rw [abs_of_nonneg hnn3] at hc3
  rw [abs_of_nonneg hnn4] at hc4
  have := hN n hn (smp X h n ω) (smp Y h (m n) ω) (fun i => hB _) (fun j => hB _) hc1 hc2 hc3 hc4
  linarith

end StatFormal.Foundations.Bootstrap
