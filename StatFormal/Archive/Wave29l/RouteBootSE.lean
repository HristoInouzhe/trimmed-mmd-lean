import StatFormal.Archive.Wave29l.Statements
import StatFormal.Lib.Bootstrap.Consistency
import StatFormal.Archive.Wave29i.RouteSplit

/-!
# Route — TM `thm:split` with the bootstrap standard error (untrusted)

* `split_boot_se`: `Foundations/Bootstrap/{Basic,TrimVar,Consistency}` — the bootstrap replicate of each trimmed
  mean decomposes by duality at the empirical quantile into a linear bootstrap mean `A*` (exact second moment
  `varLo/n`) plus a remainder `0 ≤ D* ≤ d(|F* − F_n| + |G* − G_n|)` off a Hoeffding-small event; the plug-in
  consistency `tip0_varLo` of Wave 29i finishes.
* `split_boot_check` (route, not a target): frozen `Wave29i.split_level_boot` + `split_boot_se` ⇒
  `split_level_bootstrap`; `split_level_bootstrap` is that route applied to the certified theorems.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave29l

open StatFormal.Foundations.Bootstrap StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT
open StatFormal.TrimmedMMD.BangBang

lemma splitBootVar_eq (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) :
    splitBootVar n m α vx vy = bootVar2 n m α vx vy := by
  have hc : (Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) : ℝ) = (n : ℝ) ^ n * (m : ℝ) ^ m := by
    simp [Fintype.card_prod]
  unfold splitBootVar splitBootMean bootVar2 bVar bAvg
  rw [hc, Fintype.sum_prod_type, Fintype.sum_prod_type]
  rfl

section Meas

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {X Y : ℕ → Ω → 𝒳}

lemma measurable_bootVar2 (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i)) {h : 𝒳 → ℝ}
    (hm : Measurable h) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (m : ℕ → ℕ) (n : ℕ) :
    Measurable fun ω => bootVar2 n (m n) α (smp X h n ω) (smp Y h (m n) ω) := by
  have hF : ∀ p : (Fin n → Fin n) × (Fin (m n) → Fin (m n)), Measurable fun ω =>
      tLo n α (smp X h n ω ∘ p.1) - sSup ((fun w => ∑ j, w j * (smp Y h (m n) ω ∘ p.2) j) '' capped (m n) α) :=
    fun p => ((measurable_trimLo (n := n) hα0 hα1).comp (measurable_pi_iff.2 fun i => hm.comp (hXm (p.1 i)))).sub
      ((measurable_trimUp (n := m n) hα0 hα1).comp (measurable_pi_iff.2 fun j => hm.comp (hYm (p.2 j))))
  unfold bootVar2 bVar bAvg
  refine Measurable.const_mul (Finset.measurable_sum _ fun p _ => ((hF p).sub
    (Measurable.const_mul (Finset.measurable_sum _ fun p' _ => hF p') _)).pow_const 2) _

end Meas

/-- From `TIP0 (A − c)` to `TendstoInMeasure A → c`. -/
lemma tendstoInMeasure_of_tip0 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : ℕ → Ω → ℝ} {c : ℝ}
    (h : TIP0 μ (fun n ω => A n ω - c)) : TendstoInMeasure μ A atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simpa only [Real.norm_eq_abs] using h ε hε

theorem split_boot_se : Claims.split_boot_se := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ f Ω _ μ _ X Y m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXl hYl hκ0 hmr
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have hse : ∀ n ω, splitBootSEn φ f X Y m α n ω =
      √(bootVar2 n (m n) α (smp X (fun x => ⟪f, φ x⟫) n ω) (smp Y (fun x => ⟪f, φ x⟫) (m n) ω)) := fun n ω => by
    unfold splitBootSEn splitBootSE
    rw [splitBootVar_eq]
    rfl
  refine ⟨?_, fun hσ => ?_⟩
  · refine tendstoInMeasure_of_tip0 ((tip0_bootVar2 hX hY hm hB hα0 hα1 hκ0 hmr hP hQ).congr
      (Eventually.of_forall fun n ω => ?_))
    rw [hse, Real.sq_sqrt (show 0 ≤ bootVar2 n (m n) α _ _ from bVar_nonneg _)]
    rfl
  · have h := tip0_bootSE hX hY hm hB hα0 hα1 hκ0 hmr hP hQ hσ
    have hs : 0 < √(StatFormal.Wave29i.splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ) := Real.sqrt_pos.2 hσ
    refine tendstoInMeasure_of_tip0 ((h.const_mul (√(StatFormal.Wave29i.splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ))⁻¹).congr ?_)
    filter_upwards [eventually_gt_atTop 0] with n hn ω
    have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [hse, show StatFormal.Wave29i.splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ =
      sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ from rfl]
    change (√(sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ))⁻¹ * (√(n : ℝ) * _ - √(sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ)) = _
    have hs' : 0 < √(sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ) := hs
    field_simp

/-- Route check (not a target): the frozen conditional `Wave29i.split_level_boot` plus the bootstrap consistency
`split_boot_se` give the bootstrap-SE certificate. -/
theorem split_boot_check : StatFormal.Wave29i.Claims.split_level_boot → Claims.split_boot_se →
    Claims.split_level_bootstrap := by
  intro hboot hse 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ δ z f Ω _ μ _ X Y m hφ hκ hα0 hα1 hAP hAQ hXm hYm hXi hYi hXY hXl hYl
    hκ0 hmr hz
  have hm := measurable_inner_comp hφ f
  have hP : UQ P (fun x => ⟪f, φ x⟫) (1 - α) q := AssDens.uq hm hAP
  have hQ : UQ Q (fun x => ⟪f, φ x⟫) α q' := AssDens.uq hm hAQ
  have hσ := StatFormal.Wave29i.sigma2_pos (Q := Q) (q' := q') hm (abs_inner_le hκ f) hα0 hα1 hκ0 hAP
  obtain ⟨-, hrat⟩ := hse 𝒳 H P Q φ κ' α q q' κ f Ω μ X Y m hφ hκ hα0.le hα1 hP hQ hXm hYm hXi hYi hXl hYl hκ0 hmr
  have hsem : ∀ n, Measurable (splitBootSEn φ f X Y m α n) := fun n => by
    have : splitBootSEn φ f X Y m α n =
        fun ω => √(bootVar2 n (m n) α (smp X (fun x => ⟪f, φ x⟫) n ω) (smp Y (fun x => ⟪f, φ x⟫) (m n) ω)) := by
      funext ω
      unfold splitBootSEn splitBootSE
      rw [splitBootVar_eq]
      rfl
    rw [this]
    exact (measurable_bootVar2 hXm hYm hm hα0.le hα1 m n).sqrt
  exact hboot 𝒳 H P Q φ κ' α q q' κ δ z f Ω μ X Y m (splitBootSEn φ f X Y m α) hφ hκ hα0 hα1 hAP hAQ hXm hYm hXi
    hYi hXY hXl hYl hκ0 hmr hsem (hrat hσ) hz

theorem split_level_bootstrap : Claims.split_level_bootstrap :=
  split_boot_check StatFormal.Wave29i.split_level_boot split_boot_se

end StatFormal.Wave29l
