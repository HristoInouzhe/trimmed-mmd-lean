import StatFormal.Archive.Wave30d.Statements
import StatFormal.Lib.Bootstrap.AlphaZero
import StatFormal.Archive.Wave29l.RouteBootPerc
import StatFormal.Archive.Wave29w.RouteSplitZero

/-!
# Route (wave 30d) — trimmed MMD `thm:split` at `α = 0`: the nonparametric bootstrap (untrusted)

* `split_zero_boot_exact`: `Foundations/Bootstrap/AlphaZero.bootVar2_zero` (at `α = 0` the replicate is a
  difference of resampled means, `Var*(v̄*) = s²/n` by `bAvg_resample_sq`) and the frozen `splitBootVar = bootVar2`
  (Wave 29l route `splitBootVar_eq`).
* `split_zero_boot_se`: `tip0_bootVar2_zero`, `tip0_bootSE_zero` (the plug-in consistency `tip0_varLo_zero` of
  `Foundations/TrimmedMean/AlphaZero`; no quantile condition).
* `split_zero_boot_clt`: `tip0_bootCdf_zero` (the deterministic uniform bootstrap CLT `boot_root_unif` at `α = 0`,
  whose duality remainders vanish identically, `bootD_zero`).
* `split_zero_level_bootstrap`: the certified frozen `Wave29w.split_zero_level` (plug-in SE) transported along the
  exact identity `ŝe* = ŝe` (`n, m(n) ≥ 1`, eventually), then the certified frozen `Wave22c.split_level`.
* `split_zero_boot_percentile`: `σ₀² > 0` — `perc_coverage_zero` (`perc_coverage_of` with the frozen-route CLT
  `clt_zero` and `tip0_bootCdf_zero`); `σ₀² = 0` — `perc_le_degenerate`; then `Wave22c.split_level`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave30d

open StatFormal.Foundations.Bootstrap StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT
open StatFormal.Wave29i (splitSE splitStat splitSEn)
open StatFormal.Wave29l (splitBootVar splitBootSE splitBootSEn splitBootCdfn splitBootPercn)
open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

lemma splitBootVar_zero {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (vx : Fin n → ℝ) (vy : Fin m → ℝ) :
    splitBootVar n m 0 vx vy = varLo n 0 vx / n + varLo m 0 (fun j => -vy j) / m := by
  rw [StatFormal.Wave29l.splitBootVar_eq, bootVar2_zero hn hm]

lemma splitBootSE_zero {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (vx : Fin n → ℝ) (vy : Fin m → ℝ) :
    splitBootSE n m 0 vx vy = splitSE n m 0 vx vy := by
  unfold splitBootSE
  rw [splitBootVar_zero hn hm]
  change _ = √(varLo n 0 vx / n + varLo m 0 (fun j => -vy j) / m) / (1 - 0)
  rw [sub_zero, div_one]

/-- At `α = 0` the ideal bootstrap of the split statistic is the classical bootstrap of a difference of means (route
lemma, not a target; moved out of the draft statements by the critic, 2026-10-20: not printed — `thm:split` asserts
only consistency): for `n, m ≥ 1` the frozen bootstrap variance `splitBootVar` is `s²_X/n + s²_Y/m` (`1/n` sample
variances), so the frozen bootstrap standard error equals the frozen plug-in standard error `splitSE` at `α = 0`. -/
theorem split_zero_boot_exact (n m : ℕ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (hn : 0 < n) (hm : 0 < m) :
    splitBootVar n m 0 vx vy = (∑ i, (vx i - (∑ j, vx j) / n) ^ 2) / n / n +
      (∑ j, (vy j - (∑ k, vy k) / m) ^ 2) / m / m ∧
    splitBootSE n m 0 vx vy = splitSE n m 0 vx vy := by
  refine ⟨?_, splitBootSE_zero hn hm vx vy⟩
  rw [splitBootVar_zero hn hm, varLo_zero_centred hn, varLo_zero_centred hm]
  have e : ∀ j, (-vy j - (∑ k, -vy k) / m) ^ 2 = (vy j - (∑ k, vy k) / m) ^ 2 := fun j => by
    rw [Finset.sum_neg_distrib]; ring
  simp only [e]

section Common

variable {Ω 𝒳 H : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma splitBootSEn_eq (φ : 𝒳 → H) (f : H) (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ) (n : ℕ) (ω : Ω) :
    splitBootSEn φ f X Y m 0 n ω =
      √(bootVar2 n (m n) 0 (smp X (fun x => ⟪f, φ x⟫) n ω) (smp Y (fun x => ⟪f, φ x⟫) (m n) ω)) := by
  unfold splitBootSEn splitBootSE
  rw [StatFormal.Wave29l.splitBootVar_eq]
  rfl

lemma measurable_splitBootSEn_zero {X Y : ℕ → Ω → 𝒳} (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    {φ : 𝒳 → H} {f : H} (hm : Measurable fun x => ⟪f, φ x⟫) (m : ℕ → ℕ) (n : ℕ) :
    Measurable (splitBootSEn φ f X Y m 0 n) := by
  have : splitBootSEn φ f X Y m 0 n = fun ω =>
      √(bootVar2 n (m n) 0 (smp X (fun x => ⟪f, φ x⟫) n ω) (smp Y (fun x => ⟪f, φ x⟫) (m n) ω)) :=
    funext fun ω => splitBootSEn_eq φ f X Y m n ω
  rw [this]
  exact (StatFormal.Wave29l.measurable_bootVar2 hXm hYm hm le_rfl zero_lt_one m n).sqrt

/-- Eventually (`n ≥ 1`, `m(n) ≥ 1`) the bootstrap standard error is the plug-in standard error. -/
lemma eventually_boot_eq_plugin {φ : 𝒳 → H} {f : H} {X Y : ℕ → Ω → 𝒳} {m : ℕ → ℕ}
    (hmtop : Tendsto m atTop atTop) :
    ∀ᶠ n in atTop, ∀ ω, splitBootSEn φ f X Y m 0 n ω = splitSEn φ f X Y m 0 n ω := by
  filter_upwards [eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hn hmn ω
  unfold splitBootSEn splitSEn
  exact splitBootSE_zero hn hmn _ _

end Common

theorem split_zero_boot_se : Claims.split_zero_boot_se := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ f Ω _ μ _ X Y m hφ hκ hXm hYm hXi hYi hXl hYl hκ0 hmr
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  refine ⟨?_, fun hσ => ?_⟩
  · refine StatFormal.Wave29l.tendstoInMeasure_of_tip0 ((tip0_bootVar2_zero hX hY hm hB hκ0 hmr).congr
      (Eventually.of_forall fun n ω => ?_))
    rw [splitBootSEn_eq, Real.sq_sqrt (show 0 ≤ bootVar2 n (m n) 0 _ _ from bVar_nonneg _)]
  · have h := tip0_bootSE_zero hX hY hm hB hκ0 hmr hσ
    set S := Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ
    have hs : 0 < √S := Real.sqrt_pos.2 hσ
    refine StatFormal.Wave29l.tendstoInMeasure_of_tip0 ((h.const_mul (√S)⁻¹).congr ?_)
    filter_upwards [eventually_gt_atTop 0] with n hn ω
    have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [splitBootSEn_eq]
    field_simp

theorem split_zero_boot_clt : Claims.split_zero_boot_clt := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ f Ω _ μ _ X Y m hφ hκ hXm hYm hXi hYi hXl hYl hκ0 hmr hσ t
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  refine StatFormal.Wave29l.tendstoInMeasure_of_tip0 ((tip0_bootCdf_zero hX hY hm hB hκ0 hmr hσ t).congr
    (Eventually.of_forall fun n ω => ?_))
  unfold splitBootCdfn
  rw [StatFormal.Wave29l.splitBootCdf_eq]
  rfl

theorem split_zero_level_bootstrap : Claims.split_zero_level_bootstrap := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ δ z f Ω _ μ _ X Y m hφ hκ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr hz
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ0 hmr
  obtain ⟨hcov, -, -⟩ := StatFormal.Wave29w.split_zero_level 𝒳 H P Q φ κ' κ δ z f Ω μ X Y m hφ hκ hXm hYm hXi hYi
    hXY hXl hYl hκ0 hmr hz
  have heq := eventually_boot_eq_plugin (φ := φ) (f := f) (X := X) (Y := Y) hmtop
  set Tlo : ℕ → Ω → ℝ := fun n ω => splitStat φ f X Y m 0 n ω - z * splitBootSEn φ f X Y m 0 n ω with hTlo
  set E : ℕ → Set Ω := fun n => {ω | ((Tlo n ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q)} with hE
  have hTm : ∀ n, Measurable (Tlo n) := fun n =>
    (measurable_statT hX hY hm le_rfl zero_lt_one m n).sub ((measurable_splitBootSEn_zero hXm hYm hm m n).const_mul z)
  have hEm : ∀ n, MeasurableSet (E n) := fun n => by
    have : E n = {ω | Tlo n ω ≤ ∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q} := by
      ext ω; simp only [hE, Set.mem_ofPred_eq, StatFormal.Wave29w.sep_zero hφ hκ, EReal.coe_le_coe_iff]
    rw [this]; exact measurableSet_le (hTm n) measurable_const
  have h1 : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real (E n) := by
    intro η hη
    filter_upwards [hcov η hη, heq] with n hn hen
    have : E n = {ω | ((splitStat φ f X Y m 0 n ω - z * splitSEn φ f X Y m 0 n ω : ℝ) : EReal) ≤
        sepVal f (region φ 0 P) (region φ 0 Q)} := by
      ext ω; simp only [hE, hTlo, Set.mem_ofPred_eq, hen ω]
    rw [this]; exact hn
  obtain ⟨a, b⟩ := StatFormal.Wave22c.split_level 𝒳 H P Q φ κ' 0 δ f Ω (fun _ => μ) Tlo E hφ hκ le_rfl
    zero_lt_one (fun _ => inferInstance) hEm (fun n ω hω => hω) h1
  exact ⟨h1, a, fun n ω hω hpos => b n ω hω hpos⟩

theorem split_zero_boot_percentile : Claims.split_zero_boot_percentile := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ δ z f Ω _ μ _ X Y m hφ hκ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr hz
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  obtain ⟨hδ0, hδ1⟩ := StatFormal.Wave29l.delta_mem hz
  have hsep := StatFormal.Wave29w.sep_zero (P := P) (Q := Q) hφ hκ (f := f)
  set T₀ := ∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q
  have hset : ∀ n, {ω | ((splitBootPercn φ f X Y m 0 δ n ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q)} =
      {ω | percLo n (m n) 0 δ (smp X (fun x => ⟪f, φ x⟫) n ω) (smp Y (fun x => ⟪f, φ x⟫) (m n) ω) ≤ T₀} :=
    fun n => by
      ext ω
      simp only [Set.mem_ofPred_eq, hsep, EReal.coe_le_coe_iff]
      unfold splitBootPercn
      rw [StatFormal.Wave29l.splitBootPerc_eq]
      rfl
  have hEm : ∀ n, MeasurableSet {ω | ((splitBootPercn φ f X Y m 0 δ n ω : ℝ) : EReal) ≤
      sepVal f (region φ 0 P) (region φ 0 Q)} := fun n => by
    rw [hset n]
    exact measurableSet_le (StatFormal.Wave29l.measurable_percLo hXm hYm hm le_rfl zero_lt_one δ m n)
      measurable_const
  have h1 : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
      ((splitBootPercn φ f X Y m 0 δ n ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q)} := by
    intro η hη
    have hσ0 : 0 ≤ Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ :=
      add_nonneg (variance_nonneg _ _) (div_nonneg (variance_nonneg _ _) hκ0.le)
    rcases hσ0.lt_or_eq with hσ | hσ
    · filter_upwards [perc_coverage_zero hX hY hXY hm hB hκ0 hmr hσ hδ0 hδ1 hz η hη] with n hn
      rw [hset n]; exact hn
    · filter_upwards [perc_le_degenerate hX hY hm hB hκ0 hmr hσ.symm hδ0 hδ1] with n hn
      have hm1 : μ {ω | percLo n (m n) 0 δ (smp X (fun x => ⟪f, φ x⟫) n ω)
          (smp Y (fun x => ⟪f, φ x⟫) (m n) ω) ≤ T₀} = 1 := by
        have hmeas : MeasurableSet {ω | percLo n (m n) 0 δ (smp X (fun x => ⟪f, φ x⟫) n ω)
            (smp Y (fun x => ⟪f, φ x⟫) (m n) ω) ≤ T₀} :=
          measurableSet_le (StatFormal.Wave29l.measurable_percLo hXm hYm hm le_rfl zero_lt_one δ m n)
            measurable_const
        exact (prob_compl_eq_zero_iff hmeas).1 (ae_iff.1 hn)
      rw [hset n, measureReal_def, hm1, ENNReal.toReal_one]
      linarith
  obtain ⟨a, b⟩ := StatFormal.Wave22c.split_level 𝒳 H P Q φ κ' 0 δ f Ω (fun _ => μ) (splitBootPercn φ f X Y m 0 δ)
    (fun n => {ω | ((splitBootPercn φ f X Y m 0 δ n ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q)})
    hφ hκ le_rfl zero_lt_one (fun _ => inferInstance) hEm (fun n ω hω => hω) h1
  exact ⟨h1, a, fun n ω hω hpos => b n ω hω hpos⟩

end StatFormal.Wave30d
