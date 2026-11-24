import StatFormal.Archive.Wave30dd.RouteBoot
import StatFormal.Archive.Wave29w.RouteSplitZero
import StatFormal.Archive.Wave30d.RouteSplitBoot

/-!
# Route — wave 30dd, part 2: trimmed-mmd `thm:split` at `α = 0` in the general regime (untrusted)

* `wdd_core`: the subsequence / Bolzano–Weierstrass core of wave 30da (`wda_norm_core`) with Gaussian limits
  `N(0, s_A)`, `N(0, s_B)` of arbitrary variances and weights `w_k² s_A + w'_k² s_B = 1`, and an `o_P(1)` remainder.
* `wdd_side`: one sample, `A_k = k^{-1/2} Σ_{i<k} (h(X_i) − P h)/√Var_P h ⇒ N(0, s)` (`s = 1` if `Var_P h > 0`;
  `A ≡ 0`, `s = 0` if `Var_P h = 0`), and `Σ_{i<k}(h(X_i) − P h) = √Var_P h · √k · A_k` almost surely.
* `wdd_zero_normal`: `T̂_k − (P h − Q h) = √(a/n_k) A_{n_k} + √(b/m_k) B_{m_k}` a.s. (sample means, `statT_zero`),
  weights `w = √(a/n)/√S`, `w' = √(b/m)/√S`, `S = a/n + b/m > 0`.
* `wdd_zero_ratio`: `ŝe_k/sd_k → 1` (`tip0_varLo_zero` on each side; a side with zero variance has zero sample variance
  a.s.); `wdd_zero_degenerate`: if `a = b = 0`, the lower limit equals `P h − Q h` a.s. for every `k`.
* The claims: `coverage_lim` (Slutsky + portmanteau), the frozen `Wave22c.split_level` at `α = 0`, the frozen
  wave-29w `sep_zero` and the frozen wave-30d `splitBootSE_zero` (at `α = 0` the ideal bootstrap SE IS the plug-in SE).
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

section Core
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An almost surely vanishing sequence is `o_P(1)`. -/
lemma wdd_tip0_ae {A : ℕ → Ω → ℝ} (h : ∀ k, ∀ᵐ ω ∂μ, A k ω = 0) : TIP0 μ A := by
  refine TIP0.of_dominated (tip0_zero (P := μ)) (Bad := fun k => {ω | ¬ A k ω = 0})
    (by simp only [fun k => ae_iff.1 (h k)]; exact tendsto_const_nhds) (Eventually.of_forall fun k ω hω => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hω
  simp [hω]

lemma wdd_core {A B Y : ℕ → Ω → ℝ} {n m : ℕ → ℕ} {w w' : ℕ → ℝ} {sA sB : ℝ≥0}
    (hA : TendstoInDistribution A atTop id (fun _ => μ) (gaussianReal 0 sA))
    (hB : TendstoInDistribution B atTop id (fun _ => μ) (gaussianReal 0 sB))
    (hind : ∀ a b, IndepFun (A a) (B b) μ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hw : ∀ k, w k ∈ Icc (0 : ℝ) 1) (hw' : ∀ k, w' k ∈ Icc (0 : ℝ) 1)
    (hsum : ∀ k, w k ^ 2 * sA + w' k ^ 2 * sB = 1) (hYm : ∀ k, AEMeasurable (Y k) μ)
    (hY : TIP0 μ (fun k ω => Y k ω - (w k * A (n k) ω + w' k * B (m k) ω))) :
    TendstoInDistribution Y atTop id (fun _ => μ) (gaussianReal 0 1) := by
  refine StatFormal.Wave30da.wda_subseq hYm fun ns hns => ?_
  obtain ⟨a, -, φ1, hφ1, h1⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) 1) (fun k => hw (ns k))
  obtain ⟨b, -, φ2, hφ2, h2⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) 1) (fun k => hw' (ns (φ1 k)))
  refine ⟨fun k => φ1 (φ2 k), ?_⟩
  set idx : ℕ → ℕ := fun k => ns (φ1 (φ2 k)) with hidx
  have hidxt : Tendsto idx atTop atTop := hns.comp (hφ1.tendsto_atTop.comp hφ2.tendsto_atTop)
  have hwa : Tendsto (fun k => w (idx k)) atTop (𝓝 a) := h1.comp hφ2.tendsto_atTop
  have hwb : Tendsto (fun k => w' (idx k)) atTop (𝓝 b) := h2
  have hab : a ^ 2 * sA + b ^ 2 * sB = 1 := by
    have hl := ((hwa.pow 2).mul_const (sA : ℝ)).add ((hwb.pow 2).mul_const (sB : ℝ))
    have hc : Tendsto (fun k => w (idx k) ^ 2 * sA + w' (idx k) ^ 2 * sB) atTop (𝓝 1) := by
      simp only [hsum]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hl hc
  have hA1 := tendstoInDistribution_mul_of_tendsto (TendstoInDistribution.comp_tendsto hA (hn.comp hidxt)) hwa
  have hB1 := tendstoInDistribution_mul_of_tendsto (TendstoInDistribution.comp_tendsto hB (hm.comp hidxt)) hwb
  have hLA : HasLaw (fun x : ℝ => a * id x) (gaussianReal 0 (⟨a ^ 2, sq_nonneg _⟩ * sA)) (gaussianReal 0 sA) := by
    have := gaussianReal_const_mul (P := gaussianReal 0 sA) (X := id) ⟨aemeasurable_id, Measure.map_id⟩ a
    rw [mul_zero] at this
    exact this
  have hLB : HasLaw (fun x : ℝ => b * id x) (gaussianReal 0 (⟨b ^ 2, sq_nonneg _⟩ * sB)) (gaussianReal 0 sB) := by
    have := gaussianReal_const_mul (P := gaussianReal 0 sB) (X := id) ⟨aemeasurable_id, Measure.map_id⟩ b
    rw [mul_zero] at this
    exact this
  have hG : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (⟨a ^ 2, sq_nonneg _⟩ * sA + ⟨b ^ 2, sq_nonneg _⟩ * sB))
      (gaussianReal 0 1) := by
    have e : (⟨a ^ 2, sq_nonneg _⟩ * sA + ⟨b ^ 2, sq_nonneg _⟩ * sB : ℝ≥0) = 1 :=
      NNReal.eq (by simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]; exact hab)
    rw [e]; exact ⟨aemeasurable_id, Measure.map_id⟩
  have hmain := tendstoInDistribution_add_gaussian hA1 hB1 hLA hLB hG
    (fun k => (hind _ _).comp (measurable_const_mul _) (measurable_const_mul _))
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hmain ?_ (fun k => hYm _)
  rw [tip0_iff]
  exact (fun ε hε => (hY ε hε).comp hidxt : TIP0 μ (fun k ω => Y (idx k) ω -
    (w (idx k) * A (n (idx k)) ω + w' (idx k) * B (m (idx k)) ω)))

end Core

section Zero
variable {𝒳 : Type} [MeasurableSpace 𝒳] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : ℕ → Ω → 𝒳}

/-- Zero variance: almost surely every observation equals the mean. -/
lemma wdd_ae_const (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    (hv : Var[h; P] = 0) : ∀ᵐ ω ∂μ, ∀ i, h (X i ω) = ∫ x, h x ∂P := by
  have hB0 : ∀ x, |h x| ≤ |B| := fun x => (hB x).trans (le_abs_self B)
  have hmem : MemLp h 2 P :=
    MemLp.of_bound hm.aestronglyMeasurable |B| (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB0 x)
  have haeP := ae_eq_integral_of_variance_eq_zero hmem hv
  set c := ∫ x, h x ∂P
  rw [ae_all_iff]; intro i
  have := haeP; rw [← hS.law i] at this
  exact ae_of_ae_map (hS.meas i).aemeasurable this

/-- One sample at `α = 0`: the normalised centred sum and its Gaussian limit. -/
lemma wdd_side (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) :
    ∃ (A : ℕ → Ω → ℝ) (s : ℝ≥0), TendstoInDistribution A atTop id (fun _ => μ) (gaussianReal 0 s) ∧
      Var[h; P] * s = Var[h; P] ∧
      (∀ k, ∃ F : (ℕ → 𝒳) → ℝ, Measurable F ∧ ∀ ω, A k ω = F (fun i => X i ω)) ∧
      ∀ k, ∀ᵐ ω ∂μ, ∑ i ∈ range k, (h (X i ω) - ∫ x, h x ∂P) = √(Var[h; P]) * √(k : ℝ) * A k ω := by
  set a := Var[h; P] with hadef
  obtain ⟨hUm, hUi, hUid, hU2, hU0, hUv⟩ := clt_terms hS hm hB (√a)⁻¹
  have hcl := clt_centered hU2 hUi hUid hU0 (Z := (id : ℝ → ℝ))
    (P' := gaussianReal 0 (((√a)⁻¹) ^ 2 * a).toNNReal) (by rw [hUv]; exact ⟨aemeasurable_id, Measure.map_id⟩)
  refine ⟨_, _, hcl, ?_, fun k => ⟨fun x => (√(k : ℝ))⁻¹ * ∑ i ∈ range k, (√a)⁻¹ * (h (x i) - ∫ x, h x ∂P),
    (Finset.measurable_sum _ fun i _ => ((hm.comp (measurable_pi_apply i)).sub_const _).const_mul _).const_mul _,
    fun ω => rfl⟩, fun k => ?_⟩
  · rcases (variance_nonneg h P).lt_or_eq with ha | ha
    · rw [inv_pow, Real.sq_sqrt ha.le, inv_mul_cancel₀ ha.ne', Real.toNNReal_one, NNReal.coe_one, mul_one]
    · have ha' : a = 0 := by rw [hadef]; exact ha.symm
      rw [ha', zero_mul]
  · rcases (variance_nonneg h P).lt_or_eq with ha | ha
    · refine ae_of_all _ fun ω => ?_
      have hsa : 0 < √a := Real.sqrt_pos.2 ha
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hk)
        simp only [← Finset.mul_sum]
        field_simp
    · filter_upwards [wdd_ae_const hS hm hB ha.symm] with ω hω
      have ha' : a = 0 := by rw [hadef]; exact ha.symm
      simp only [hω, sub_self, mul_zero, sum_const_zero, ha', Real.sqrt_zero, zero_mul]

/-- `a/n + b/m > 0` when `a + b > 0`, `a, b ≥ 0`, `n, m ≥ 1`. -/
lemma wdd_S_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    0 < a / n + b / m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (div_pos ha' hn') (div_nonneg hb hm'.le)
  · have hb' : 0 < b := by rw [← ha'] at hab; linarith
    exact add_pos_of_nonneg_of_pos (div_nonneg ha hn'.le) (div_pos hb' hm')

/-- **Asymptotic normality at `α = 0`, general regime.** -/
lemma wdd_zero_normal (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) (hab : 0 < Var[h; P] + Var[h; Q])
    {n m : ℕ → ℕ} (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) (hn : Tendsto n atTop atTop)
    (hm' : Tendsto m atTop atTop) :
    TendstoInDistribution (fun k ω => (statT X Y h (fun _ => m k) 0 (n k) ω - (∫ x, h x ∂P - ∫ x, h x ∂Q)) /
      √(Var[h; P] / n k + Var[h; Q] / m k)) atTop id (fun _ => μ) (gaussianReal 0 1) := by
  obtain ⟨A, sA, hA, hsA, hAF, hAid⟩ := wdd_side hX hm hB
  obtain ⟨Bq, sB, hBq, hsB, hBF, hBid⟩ := wdd_side (h := fun x => -h x) hY hm.neg (B := B)
    (fun x => by rw [abs_neg]; exact hB x)
  have hneg : Var[fun x => -h x; Q] = Var[h; Q] := variance_fun_neg
  rw [hneg] at hsB hBid
  set a := Var[h; P] with hadef
  set b := Var[h; Q] with hbdef
  have ha0 : 0 ≤ a := variance_nonneg _ _
  have hb0 : 0 ≤ b := variance_nonneg _ _
  set S : ℕ → ℝ := fun k => a / n k + b / m k with hSdef
  have hn0 : ∀ k, (0 : ℝ) < n k := fun k => by exact_mod_cast hn1 k
  have hm0 : ∀ k, (0 : ℝ) < m k := fun k => by exact_mod_cast hm1 k
  have hS0 : ∀ k, 0 < S k := fun k => wdd_S_pos ha0 hb0 hab (hn1 k) (hm1 k)
  have hind : ∀ a' b', IndepFun (A a') (Bq b') μ := by
    intro a' b'
    obtain ⟨F, hF, hFe⟩ := hAF a'
    obtain ⟨G, hG, hGe⟩ := hBF b'
    have e1 : A a' = F ∘ (fun ω i => X i ω) := funext hFe
    have e2 : Bq b' = G ∘ (fun ω i => Y i ω) := funext hGe
    rw [e1, e2]
    exact hXY.comp hF hG
  refine wdd_core (w := fun k => √(a / n k) / √(S k)) (w' := fun k => √(b / m k) / √(S k))
    hA hBq hind hn hm' (fun k => ⟨by positivity, ?_⟩) (fun k => ⟨by positivity, ?_⟩) (fun k => ?_)
    (fun k => ?_) (wdd_tip0_ae fun k => ?_)
  · rw [div_le_one (Real.sqrt_pos.2 (hS0 k))]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by have := hm0 k; positivity))
  · rw [div_le_one (Real.sqrt_pos.2 (hS0 k))]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (by have := hn0 k; positivity))
  · have e1 : 0 ≤ a / n k := by have := hn0 k; positivity
    have e2 : 0 ≤ b / m k := by have := hm0 k; positivity
    rw [div_pow, div_pow, Real.sq_sqrt e1, Real.sq_sqrt e2, Real.sq_sqrt (hS0 k).le, div_mul_eq_mul_div,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, hsA, hsB, ← add_div, div_self (hS0 k).ne']
  · exact (((measurable_statT hX hY hm le_rfl zero_lt_one (fun _ => m k) (n k)).sub_const _).div_const _).aemeasurable
  · filter_upwards [hAid (n k), hBid (m k)] with ω hωA hωB
    have hnk : 0 < n k := hn1 k
    have hmk : 0 < m k := hm1 k
    rw [statT_zero (m := fun _ => m k) hnk hmk]
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sum_neg_distrib, integral_neg] at hωA hωB
    rw [Real.sqrt_div' a (hn0 k).le, Real.sqrt_div' b (hm0 k).le]
    have hsS : 0 < √(S k) := Real.sqrt_pos.2 (hS0 k)
    have hsn : 0 < √(n k : ℝ) := Real.sqrt_pos.2 (hn0 k)
    have hsm : 0 < √(m k : ℝ) := Real.sqrt_pos.2 (hm0 k)
    have hX' : ∑ i ∈ range (n k), h (X i ω) = n k * ∫ x, h x ∂P + √a * √(n k : ℝ) * A (n k) ω := by linarith
    have hY' : ∑ j ∈ range (m k), h (Y j ω) = m k * ∫ x, h x ∂Q - √b * √(m k : ℝ) * Bq (m k) ω := by linarith
    have ea : √a / √(n k : ℝ) = √a * √(n k : ℝ) / n k := by
      rw [div_eq_div_iff hsn.ne' (hn0 k).ne', mul_assoc, Real.mul_self_sqrt (hn0 k).le]
    have eb : √b / √(m k : ℝ) = √b * √(m k : ℝ) / m k := by
      rw [div_eq_div_iff hsm.ne' (hm0 k).ne', mul_assoc, Real.mul_self_sqrt (hm0 k).le]
    rw [hX', hY', ea, eb]
    have := hn0 k; have := hm0 k
    set r := √(S k) with hr
    clear_value r
    field_simp
    ring

/-- Per-side variance ratio: `(u_k − a)/D_k → 0` when `u_k → a`, `D_k ≥ a > 0`, or `a = 0` and `u_k = 0` a.s. -/
lemma wdd_side_ratio {u : ℕ → Ω → ℝ} {a : ℝ} {D : ℕ → ℝ} (ha : 0 ≤ a) (hu : TIP0 μ (fun k ω => u k ω - a))
    (hD : ∀ k, a ≤ D k) (hD0 : ∀ k, 0 < D k) (h0 : a = 0 → ∀ k, ∀ᵐ ω ∂μ, u k ω = 0) :
    TIP0 μ (fun k ω => (u k ω - a) / D k) := by
  rcases ha.lt_or_eq with ha' | ha'
  · refine TIP0.of_dominated (hu.const_mul a⁻¹) (Bad := fun _ => ∅) (by simp)
      (Eventually.of_forall fun k ω _ => ?_)
    rw [abs_div, abs_of_pos (hD0 k), abs_mul, abs_of_pos (inv_pos.2 ha'), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (hD0 k) ha').2 (hD k)) (abs_nonneg _)
  · refine wdd_tip0_ae fun k => ?_
    filter_upwards [h0 ha'.symm k] with ω hω
    rw [hω, ← ha']; simp

/-- The sample variance of a sample that is a.s. constant vanishes a.s. -/
lemma wdd_varLo_zero_ae (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    (hv : Var[h; P] = 0) {k : ℕ} (hk : 0 < k) : ∀ᵐ ω ∂μ, varLo k 0 (smp X h k ω) = 0 := by
  filter_upwards [wdd_ae_const hS hm hB hv] with ω hω
  have hs : smp X h k ω = fun _ => ∫ x, h x ∂P := funext fun i => hω i
  rw [hs, varLo_zero hk]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp; ring

/-- **Plug-in standard error consistency at `α = 0`, general regime**: `ŝe_k / sd_k → 1`. -/
lemma wdd_zero_ratio (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) (hab : 0 < Var[h; P] + Var[h; Q])
    {n m : ℕ → ℕ} (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) (hn : Tendsto n atTop atTop)
    (hm' : Tendsto m atTop atTop) :
    TIP0 μ (fun k ω => seHat (n k) (m k) 0 (smp X h (n k) ω) (smp Y h (m k) ω) /
      √(Var[h; P] / n k + Var[h; Q] / m k) - 1) := by
  have hBn : ∀ x, |-h x| ≤ B := fun x => by rw [abs_neg]; exact hB x
  have h1 := tip0_varLo_zero hX hm hB
  have h2 := tip0_varLo_zero (h := fun x => -h x) hY hm.neg hBn
  have hneg : Var[fun x => -h x; Q] = Var[h; Q] := variance_fun_neg
  rw [hneg] at h2
  set a := Var[h; P] with hadef
  set b := Var[h; Q] with hbdef
  have ha0 : 0 ≤ a := variance_nonneg _ _
  have hb0 : 0 ≤ b := variance_nonneg _ _
  have hn0 : ∀ k, (0 : ℝ) < n k := fun k => by exact_mod_cast hn1 k
  have hm0 : ∀ k, (0 : ℝ) < m k := fun k => by exact_mod_cast hm1 k
  have hS0 : ∀ k, 0 < a / n k + b / m k := fun k => wdd_S_pos ha0 hb0 hab (hn1 k) (hm1 k)
  set u : ℕ → Ω → ℝ := fun k ω => varLo (n k) 0 (smp X h (n k) ω) with hu
  set v : ℕ → Ω → ℝ := fun k ω => varLo (m k) 0 (smp Y (fun x => -h x) (m k) ω) with hv
  have h1n : TIP0 μ (fun k ω => u k ω - a) := fun ε hε => (h1 ε hε).comp hn
  have h2m : TIP0 μ (fun k ω => v k ω - b) := fun ε hε => (h2 ε hε).comp hm'
  have hX1 := wdd_side_ratio (D := fun k => n k * (a / n k + b / m k)) ha0 h1n
    (fun k => by
      have := hn0 k; have := hm0 k
      rw [mul_add, mul_div_cancel₀ _ (hn0 k).ne']; exact le_add_of_nonneg_right (by positivity))
    (fun k => mul_pos (hn0 k) (hS0 k))
    (fun h0 k => wdd_varLo_zero_ae hX hm hB h0 (hn1 k))
  have hY1 := wdd_side_ratio (D := fun k => m k * (a / n k + b / m k)) hb0 h2m
    (fun k => by
      have := hn0 k; have := hm0 k
      rw [mul_add, mul_div_cancel₀ _ (hm0 k).ne']; exact le_add_of_nonneg_left (by positivity))
    (fun k => mul_pos (hm0 k) (hS0 k))
    (fun h0 k => by
      have := wdd_varLo_zero_ae (h := fun x => -h x) hY hm.neg hBn (by rw [hneg]; exact h0) (hm1 k)
      exact this)
  have hsum : TIP0 μ (fun k ω => (u k ω / n k + v k ω / m k) / (a / n k + b / m k) - 1) :=
    (hX1.add hY1).congr (Eventually.of_forall fun k ω => by
      have := hn0 k; have := hm0 k
      have hSk : a * m k + n k * b ≠ 0 := by
        have e : a * m k + n k * b = (a / n k + b / m k) * (n k * m k) := by field_simp
        rw [e]; exact (mul_pos (hS0 k) (by positivity)).ne'
      field_simp; ring)
  refine (wdd_sqrt_tip0 hsum).congr (Eventually.of_forall fun k ω => ?_)
  rw [Real.sqrt_div' _ (hS0 k).le]
  simp only [seHat, sub_zero, div_one]
  rfl

/-- The degenerate case at `α = 0`, general regime: if `Var_P h = Var_Q h = 0`, the lower limit equals `P h − Q h`
almost surely at every stage. -/
lemma wdd_zero_degenerate (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) {h : 𝒳 → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, |h x| ≤ B) (hvP : Var[h; P] = 0) (hvQ : Var[h; Q] = 0) {n m : ℕ → ℕ}
    (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) (z : ℝ) (k : ℕ) :
    ∀ᵐ ω ∂μ, statT X Y h (fun _ => m k) 0 (n k) ω - z * seHat (n k) (m k) 0 (smp X h (n k) ω) (smp Y h (m k) ω) =
      ∫ x, h x ∂P - ∫ x, h x ∂Q := by
  have hBn : ∀ x, |-h x| ≤ B := fun x => by rw [abs_neg]; exact hB x
  have hneg : Var[fun x => -h x; Q] = Var[h; Q] := variance_fun_neg
  filter_upwards [wdd_ae_const hX hm hB hvP, wdd_ae_const hY hm hB hvQ,
    wdd_varLo_zero_ae hX hm hB hvP (hn1 k),
    wdd_varLo_zero_ae (h := fun x => -h x) hY hm.neg hBn (by rw [hneg]; exact hvQ) (hm1 k)] with ω hω1 hω2 hv1 hv2
  have hnk : 0 < n k := hn1 k
  have hmk : 0 < m k := hm1 k
  have hse : seHat (n k) (m k) 0 (smp X h (n k) ω) (smp Y h (m k) ω) = 0 := by
    simp only [seHat]
    rw [hv1, show (fun j => -smp Y h (m k) ω j) = smp Y (fun x => -h x) (m k) ω from rfl, hv2]
    simp
  have hn' : (n k : ℝ) ≠ 0 := by exact_mod_cast hnk.ne'
  have hm' : (m k : ℝ) ≠ 0 := by exact_mod_cast hmk.ne'
  rw [hse, statT_zero (m := fun _ => m k) hnk hmk]
  simp only [hω1, hω2, sum_const, card_range, nsmul_eq_mul, mul_zero, sub_zero]
  field_simp

end Zero

section Claims
variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Coverage at `α = 0`, general regime, `Var_P h + Var_Q h > 0`. -/
lemma wdd_zero_cov {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ' : ℝ} {f : H}
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : ℕ → Ω → 𝒳} {n m : ℕ → ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ') (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ)
    (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hab : 0 < Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q]) (z : ℝ) :
    Tendsto (fun k => μ.real {ω |
          ((splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q)}) atTop (𝓝 ((gaussianReal 0 1).real (Iic z))) := by
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have hnorm := wdd_zero_normal hX hY hXY hhm hB hab hn1 hm1 hn hm
  have hratio := wdd_zero_ratio hX hY hhm hB hab hn1 hm1 hn hm
  have hsep := StatFormal.Wave29w.sep_zero (P := P) (Q := Q) hφ hκ (f := f)
  set sd : ℕ → ℝ := fun k => √(Var[h; P] / n k + Var[h; Q] / m k) with hsddef
  set se : ℕ → Ω → ℝ := fun k ω => seHat (n k) (m k) 0 (smp X h (n k) ω) (smp Y h (m k) ω) with hsedef
  set Tst : ℕ → Ω → ℝ := fun k ω => statT X Y h (fun _ => m k) 0 (n k) ω with hTst
  set T₀ := ∫ x, h x ∂P - ∫ x, h x ∂Q
  have hsd0 : ∀ k, 0 < sd k := fun k => Real.sqrt_pos.2
    (wdd_S_pos (variance_nonneg _ _) (variance_nonneg _ _) hab (hn1 k) (hm1 k))
  have hsem : ∀ k, Measurable (fun ω => se k ω / sd k) := fun k =>
    (measurable_seHat hX hY hhm 0 (fun _ => m k) (n k)).div_const _
  have hnorm' : TendstoInDistribution (fun k ω => (Tst k ω - T₀) / sd k) atTop id (fun _ => μ)
      (gaussianReal 0 ((1 : ℝ) ^ 2).toNNReal) := by
    rw [one_pow, Real.toNNReal_one]; exact hnorm
  refine (coverage_lim one_pos hnorm' hratio hsem z).congr fun k => ?_
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, hsep, EReal.coe_le_coe_iff]
  have hs := hsd0 k
  rw [show (Tst k ω - T₀) / sd k - z * (se k ω / sd k) = (Tst k ω - z * se k ω - T₀) / sd k by field_simp; ring,
    div_le_iff₀ hs, zero_mul, sub_nonpos]
  rfl

end Claims

theorem split_zero_normal_any : Claims.split_zero_normal_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' f Ω _ μ _ X Y n m hφ hκ hXm hYm hXi hYi hXY hXl hYl hn1 hm1 hn hm hab
  exact ⟨StatFormal.Wave29w.sep_zero hφ hκ, wdd_zero_normal ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ hXY
    (measurable_inner_comp hφ f) (abs_inner_le hκ f) hab hn1 hm1 hn hm⟩

theorem split_zero_coverage_any : Claims.split_zero_coverage_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' f Ω _ μ _ X Y n m hφ hκ hXm hYm hXi hYi hXY hXl hYl hn1 hm1 hn hm hab z
  exact wdd_zero_cov hφ hκ ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ hXY hn1 hm1 hn hm hab z

theorem split_zero_level_any : Claims.split_zero_level_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' δ z f Ω _ μ _ X Y n m hφ hκ hXm hYm hXi hYi hXY hXl hYl hn1 hm1 hn hm hz
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have hsep := StatFormal.Wave29w.sep_zero (P := P) (Q := Q) hφ hκ (f := f)
  set Tlo : ℕ → Ω → ℝ := fun k ω => statT X Y h (fun _ => m k) 0 (n k) ω -
    z * seHat (n k) (m k) 0 (smp X h (n k) ω) (smp Y h (m k) ω) with hTlo
  have hTm : ∀ k, Measurable (Tlo k) := fun k =>
    (measurable_statT hX hY hhm le_rfl zero_lt_one (fun _ => m k) (n k)).sub
      ((measurable_seHat hX hY hhm 0 (fun _ => m k) (n k)).const_mul z)
  set E : ℕ → Set Ω := fun k => {ω | ((Tlo k ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q)} with hE
  have hEeq : ∀ k, E k = {ω | Tlo k ω ≤ ∫ x, h x ∂P - ∫ x, h x ∂Q} := fun k => by
    ext ω; simp only [hE, Set.mem_ofPred_eq, hsep, EReal.coe_le_coe_iff]; exact Iff.rfl
  have hEm : ∀ k, MeasurableSet (E k) := fun k => by
    rw [hEeq]; exact measurableSet_le (hTm k) measurable_const
  have h1 : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, 1 - δ - η ≤ μ.real (E k) := by
    intro η hη
    have hσ0 : 0 ≤ Var[h; P] + Var[h; Q] := add_nonneg (variance_nonneg _ _) (variance_nonneg _ _)
    rcases hσ0.lt_or_eq with hσ | hσ
    · have hcov := wdd_zero_cov hφ hκ hX hY hXY hn1 hm1 hn hm hσ z
      have hΦ : (gaussianReal 0 1).real (Iic z) = 1 - δ := by
        rw [← hz, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; ring
      rw [hΦ] at hcov
      filter_upwards [hcov.eventually (Ioi_mem_nhds (show 1 - δ - η < 1 - δ by linarith))] with k hk
      exact le_of_lt hk
    · have hvP : Var[h; P] = 0 := by
        have := variance_nonneg h P; have := variance_nonneg h Q; linarith
      have hvQ : Var[h; Q] = 0 := by
        have := variance_nonneg h P; have := variance_nonneg h Q; linarith
      have hδ0 : 0 ≤ δ := hz ▸ measureReal_nonneg
      refine Eventually.of_forall fun k => ?_
      have hae : ∀ᵐ ω ∂μ, ω ∈ E k := by
        filter_upwards [wdd_zero_degenerate hX hY hhm hB hvP hvQ hn1 hm1 z k] with ω hω
        rw [hEeq]
        exact le_of_eq hω
      have h1 : μ (E k) = 1 := (prob_compl_eq_zero_iff (hEm k)).1 (ae_iff.1 hae)
      rw [measureReal_def, h1, ENNReal.toReal_one]
      linarith
  obtain ⟨a, b⟩ := StatFormal.Wave22c.split_level 𝒳 H P Q φ κ' 0 δ f Ω (fun _ => μ) Tlo E hφ hκ le_rfl
    zero_lt_one (fun _ => inferInstance) hEm (fun n ω hω => hω) h1
  exact ⟨h1, a, fun k ω hω hpos => b k ω hω hpos⟩

theorem split_zero_boot_se_any : Claims.split_zero_boot_se_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' f Ω _ μ _ X Y n m hφ hκ hXm hYm hXi hYi hXl hYl hn1 hm1 hn hm hab
  have key := wdd_zero_ratio ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ (measurable_inner_comp hφ f) (abs_inner_le hκ f) hab
    hn1 hm1 hn hm
  refine StatFormal.Wave29l.tendstoInMeasure_of_tip0 (key.congr (Eventually.of_forall fun k ω => ?_))
  rw [StatFormal.Wave30d.splitBootSE_zero (hn1 k) (hm1 k)]
  rfl

theorem split_zero_level_bootstrap_any : Claims.split_zero_level_bootstrap_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' δ z f Ω _ μ _ X Y n m hφ hκ hXm hYm hXi hYi hXY hXl hYl hn1 hm1 hn hm hz
  have e : ∀ k (vx : Fin (n k) → ℝ) (vy : Fin (m k) → ℝ), splitBootSE (n k) (m k) 0 vx vy = splitSE (n k) (m k) 0 vx vy :=
    fun k vx vy => StatFormal.Wave30d.splitBootSE_zero (hn1 k) (hm1 k) vx vy
  simp only [e]
  exact split_zero_level_any 𝒳 H P Q φ κ' δ z f Ω μ X Y n m hφ hκ hXm hYm hXi hYi hXY hXl hYl hn1 hm1 hn hm hz

end StatFormal.Wave30dd
