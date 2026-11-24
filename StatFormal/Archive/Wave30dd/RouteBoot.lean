import StatFormal.Archive.Wave30dd.Statements
import StatFormal.Archive.Wave30da.RouteSplit
import StatFormal.Archive.Wave29l.RouteBootSE

/-!
# Route — wave 30dd, part 1: trimmed-mmd `thm:split`, the bootstrap clause in the general regime (untrusted)

* `wdd_ratio_tip0`: if `u_k → a`, `v_k → b` in probability (`a, b > 0`), then
  `(u_k/n_k + v_k/m_k)/(a/n_k + b/m_k) → 1` for ANY sizes (a convex combination of `u_k/a` and `v_k/b`).
* `wdd_boot_ratio`: `ŝe*_k / se_k → 1`. By `bootVar2_eq` the bootstrap variance splits over the two independent
  resamples, `(1 − α)² Var*(T̂*) = Var*(β L_X*) + Var*(β L_{−Y}*)`; the one-sample bootstrap consistency
  `tip0_bootLo_var` (no ratio involved) gives `n Var*(β L_X*) → Var_P(q − h)_+` and `m Var*(β L_{−Y}*) →
  Var_Q(h − q')_+` along `n_k`, `m_k`; then `wdd_ratio_tip0` and a square root.
* `split_level_bootstrap_any`: the general-regime normal limit of wave 30da (`wda_normal`, by the subsequence /
  Bolzano–Weierstrass argument `wda_norm_core`), Slutsky + portmanteau (`coverage_lim`) with the ratio
  `wdd_boot_ratio`, and the frozen `Wave22c.split_level` through the wave-29i `level_of_cov`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave30dd

open StatFormal.Foundations.Bootstrap StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT
open StatFormal.TrimmedMMD.BangBang
open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.Wave29i (splitTrimLo splitTrimUp splitSE splitUQ splitAss)
open StatFormal.Wave29l (splitBootSE)
open StatFormal.Wave30da (splitSdAny)

section Core
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Ratio of two-sample variance estimates in the general regime. -/
lemma wdd_ratio_tip0 {u v : ℕ → Ω → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : TIP0 μ (fun k ω => u k ω - a))
    (hv : TIP0 μ (fun k ω => v k ω - b)) {n m : ℕ → ℕ} (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) :
    TIP0 μ (fun k ω => (u k ω / n k + v k ω / m k) / (a / n k + b / m k) - 1) := by
  refine TIP0.of_dominated ((hu.const_mul a⁻¹).abs'.add (hv.const_mul b⁻¹).abs') (Bad := fun _ => ∅) (by simp)
    (Eventually.of_forall fun k ω _ => ?_)
  have hnk : (0 : ℝ) < n k := by exact_mod_cast hn1 k
  have hmk : (0 : ℝ) < m k := by exact_mod_cast hm1 k
  set U := u k ω
  set V := v k ω
  have hS : 0 < a / n k + b / m k := by positivity
  have e : (U / n k + V / m k) / (a / n k + b / m k) - 1 =
      (a / n k) / (a / n k + b / m k) * (a⁻¹ * (U - a)) + (b / m k) / (a / n k + b / m k) * (b⁻¹ * (V - b)) := by
    field_simp; ring
  have hθ1 : (a / n k) / (a / n k + b / m k) ≤ 1 := (div_le_one hS).2 (le_add_of_nonneg_right (by positivity))
  have hθ2 : (b / m k) / (a / n k + b / m k) ≤ 1 := (div_le_one hS).2 (le_add_of_nonneg_left (by positivity))
  rw [e, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |a⁻¹ * (U - a)| + |b⁻¹ * (V - b)|)]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a / n k) / (a / n k + b / m k))]
    exact mul_le_of_le_one_left (abs_nonneg _) hθ1
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b / m k) / (a / n k + b / m k))]
    exact mul_le_of_le_one_left (abs_nonneg _) hθ2

/-- Square roots: `r_k → 1` in probability implies `√r_k → 1`. -/
lemma wdd_sqrt_tip0 {r : ℕ → Ω → ℝ} (h : TIP0 μ (fun k ω => r k ω - 1)) : TIP0 μ (fun k ω => √(r k ω) - 1) := by
  refine TIP0.of_dominated h (Bad := fun _ => ∅) (by simp) (Eventually.of_forall fun k ω _ => ?_)
  have := abs_sqrt_sub_sqrt_le (a := r k ω) one_pos
  rw [Real.sqrt_one, div_one] at this
  exact this

end Core

section Boot
variable {𝒳 : Type} [MeasurableSpace 𝒳] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : ℕ → Ω → 𝒳}

lemma wdd_splitBootSE_eq (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) :
    splitBootSE n m α vx vy = √(bootVar2 n m α vx vy) := by
  unfold splitBootSE
  rw [StatFormal.Wave29l.splitBootVar_eq]

/-- **Bootstrap standard error consistency, general regime**: `ŝe*_k / se_k → 1` in probability. -/
lemma wdd_boot_ratio (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q')
    (ha : 0 < Var[fun x => max (q - h x) 0; P]) (hb : 0 < Var[fun x => max (h x - q') 0; Q])
    {n m : ℕ → ℕ} (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) (hn : Tendsto n atTop atTop)
    (hm' : Tendsto m atTop atTop) :
    TIP0 μ (fun k ω => √(bootVar2 (n k) (m k) α (smp X h (n k) ω) (smp Y h (m k) ω)) /
      splitSdAny P Q h α q q' (n k) (m k) - 1) := by
  have hβ : 0 < 1 - α := by linarith
  have hQ' : UQ Q (fun x => -h x) (1 - α) (-q') := by
    have := hQ.neg hm; simpa only [sub_sub_cancel] using this
  have hg' : (fun x => max (-q' - -h x) 0) = fun x => max (h x - q') 0 := funext fun x => by ring_nf
  have h1 := tip0_bootLo_var hX hm hB hα0 hα1 hP
  have h2 := tip0_bootLo_var (h := fun x => -h x) hY hm.neg (B := B) (fun x => by rw [abs_neg]; exact hB x)
    hα0 hα1 hQ'
  rw [hg'] at h2
  set a := Var[fun x => max (q - h x) 0; P]
  set b := Var[fun x => max (h x - q') 0; Q]
  set u : ℕ → Ω → ℝ := fun k ω => (n k : ℝ) * bVar (fun I : Fin (n k) → Fin (n k) =>
    (1 - α) * tLo (n k) α (smp X h (n k) ω ∘ I)) with hu
  set v : ℕ → Ω → ℝ := fun k ω => (m k : ℝ) * bVar (fun J : Fin (m k) → Fin (m k) =>
    (1 - α) * tLo (m k) α (smp Y (fun x => -h x) (m k) ω ∘ J)) with hv
  have h1n : TIP0 μ (fun k ω => u k ω - a) := fun ε hε => (h1 ε hε).comp hn
  have h2m : TIP0 μ (fun k ω => v k ω - b) := fun ε hε => (h2 ε hε).comp hm'
  refine (wdd_sqrt_tip0 (wdd_ratio_tip0 ha hb h1n h2m hn1 hm1)).congr (Eventually.of_forall fun k ω => ?_)
  have hnk : 0 < n k := hn1 k
  have hmk : 0 < m k := hm1 k
  have hnk' : (0 : ℝ) < n k := by exact_mod_cast hnk
  have hmk' : (0 : ℝ) < m k := by exact_mod_cast hmk
  have hbv := bootVar2_eq hnk hmk hα0 hα1 (smp X h (n k) ω) (smp Y h (m k) ω)
  have e : (fun j => -smp Y h (m k) ω j) = smp Y (fun x => -h x) (m k) ω := rfl
  rw [e] at hbv
  have hbv' : bootVar2 (n k) (m k) α (smp X h (n k) ω) (smp Y h (m k) ω) =
      (u k ω / n k + v k ω / m k) / (1 - α) ^ 2 := by
    rw [eq_div_iff (by positivity), mul_comm, hbv]
    simp only [hu, hv]
    field_simp
  have hS : 0 < a / n k + b / m k := by positivity
  have e1 : √((u k ω / n k + v k ω / m k) / (1 - α) ^ 2) = √(u k ω / n k + v k ω / m k) / (1 - α) := by
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ (1 - α) ^ 2), Real.sqrt_sq hβ.le]
  rw [hbv', e1, Real.sqrt_div' (u k ω / n k + v k ω / m k) hS.le]
  simp only [splitSdAny]
  rw [div_div_div_cancel_right₀ hβ.ne']

end Boot

theorem split_boot_se_any : Claims.split_boot_se_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' f Ω _ μ _ X Y n m hφ hκ hα0 hα1 hP hQ ha hb hXm hYm hXi hYi hXl hYl
    hn1 hm1 hn hm
  have key := wdd_boot_ratio ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ (measurable_inner_comp hφ f) (abs_inner_le hκ f)
    hα0 hα1 hP hQ ha hb hn1 hm1 hn hm
  refine StatFormal.Wave29l.tendstoInMeasure_of_tip0 (key.congr (Eventually.of_forall fun k ω => ?_))
  rw [wdd_splitBootSE_eq]
  rfl

theorem split_level_bootstrap_any : Claims.split_level_bootstrap_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' δ z f Ω _ μ _ X Y n m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXY hXl hYl
    hn1 hm1 hn hm hz
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have hβ : 0 < 1 - α := by linarith
  have hPu : UQ P h (1 - α) q := AssDens.uq hhm hP
  have hQu : UQ Q h α q' := AssDens.uq hhm hQ
  have ha : 0 < Var[fun x => max (q - h x) 0; P] := AssDens.var_pos hhm hB hP (by linarith)
  have hb : 0 < Var[fun x => max (h x - q') 0; Q] := StatFormal.Wave30da.wda_var_pos_up hhm hB hQ hα0
  have hnorm := StatFormal.Wave30da.wda_normal hX hY hXY hhm hB hα0.le hα1 hPu hQu ha hb hn1 hm1 hn hm
  set sd : ℕ → ℝ := fun k => splitSdAny P Q h α q q' (n k) (m k) with hsddef
  set se : ℕ → Ω → ℝ := fun k ω => splitBootSE (n k) (m k) α (fun i => h (X i ω)) (fun j => h (Y j ω)) with hsedef
  have hn0 : ∀ k, (0 : ℝ) < n k := fun k => by exact_mod_cast hn1 k
  have hm0 : ∀ k, (0 : ℝ) < m k := fun k => by exact_mod_cast hm1 k
  have hsd0 : ∀ k, 0 < sd k := fun k => by
    have := hn0 k; have := hm0 k
    exact div_pos (Real.sqrt_pos.2 (by positivity)) hβ
  have hratio : TIP0 μ (fun k ω => se k ω / sd k - 1) :=
    (wdd_boot_ratio hX hY hhm hB hα0.le hα1 hPu hQu ha hb hn1 hm1 hn hm).congr
      (Eventually.of_forall fun k ω => by simp only [se, sd, wdd_splitBootSE_eq]; rfl)
  have hsem0 : ∀ k, Measurable (se k) := fun k => by
    have : se k = fun ω => √(bootVar2 (n k) (m k) α (smp X h (n k) ω) (smp Y h (m k) ω)) :=
      funext fun ω => wdd_splitBootSE_eq _ _ _ _ _
    rw [this]
    exact (StatFormal.Wave29l.measurable_bootVar2 hXm hYm hhm hα0.le hα1 (fun _ => m k) (n k)).sqrt
  set Tst : ℕ → Ω → ℝ := fun k ω => statT X Y h (fun _ => m k) α (n k) ω with hTst
  set T₀ := popLo P h α q - popUp Q h α q'
  have hsep := StatFormal.Wave29i.sep_eq_of_uq hφ hκ hα0.le hα1 hPu hQu
  have hsem : ∀ k, Measurable (fun ω => se k ω / sd k) := fun k => (hsem0 k).div_const _
  have hnorm' : TendstoInDistribution (fun k ω => (Tst k ω - T₀) / sd k) atTop id (fun _ => μ)
      (gaussianReal 0 ((1 : ℝ) ^ 2).toNNReal) := by
    rw [one_pow, Real.toNNReal_one]; exact hnorm
  have hcov0 := coverage_lim one_pos hnorm' hratio hsem z
  have hcov : Tendsto (fun k => μ.real {ω | ((Tst k ω - z * se k ω : ℝ) : EReal) ≤
      sepVal f (region φ α P) (region φ α Q)}) atTop (𝓝 ((gaussianReal 0 1).real (Iic z))) := by
    refine hcov0.congr fun k => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, hsep, EReal.coe_le_coe_iff]
    have hs := hsd0 k
    rw [show (Tst k ω - T₀) / sd k - z * (se k ω / sd k) = (Tst k ω - z * se k ω - T₀) / sd k by field_simp; ring,
      div_le_iff₀ hs, zero_mul, sub_nonpos]
  have hTm : ∀ k, Measurable (fun ω => Tst k ω - z * se k ω) := fun k =>
    (measurable_statT hX hY hhm hα0.le hα1 (fun _ => m k) (n k)).sub ((hsem0 k).const_mul z)
  exact StatFormal.Wave29i.level_of_cov StatFormal.Wave22c.split_level hφ hκ hα0.le hα1 hPu hQu hTm hz hcov

end StatFormal.Wave30dd
