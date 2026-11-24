import StatFormal.Lib.TrimmedMean.Empirical
import StatFormal.Lib.CLT.AsympLinear

/-!
# Asymptotic linearity of the empirical extreme trimmed mean (library)

`X` i.i.d. `P` on `𝒳`, `h : 𝒳 → ℝ` bounded measurable, `β = 1 − α`, `q` the unique `β`-quantile of `h` under `P`
(`UQ`: `P(h < q) ≤ β ≤ P(h ≤ q)`, `P(h < q − d) < β < P(h ≤ q + d)` for every `d > 0`; Stigler's condition).
No empirical-process theory: the deterministic inequality `al_bound` plus Chebyshev give

* `tip0_trimLo`: `√n (L_n − L) + β⁻¹ n^{−1/2} Σ_{i<n} (g(X_i) − P g) → 0` in probability, with
  `L_n = min_{capped} Σ w_i h(X_i)`, `g = (q − h)_+`, `L = q − β⁻¹ P g`;
* `tip0_quantLo`: the empirical quantile `ĉ_n → q` in probability;
* `tip0_varLo`: the plug-in variance `P_n g_{ĉ}² − (P_n g_{ĉ})² → Var_P(g)` in probability.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Foundations.TrimmedMean

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.CLT

/-- `q` is the unique `p`-quantile of `h` under `P`. -/
def UQ {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) (h : 𝒳 → ℝ) (p q : ℝ) : Prop :=
  P.real {x | h x < q} ≤ p ∧ p ≤ P.real {x | h x ≤ q} ∧ (∀ d > 0, P.real {x | h x < q - d} < p) ∧
    (∀ d > 0, p < P.real {x | h x ≤ q + d})

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Measure 𝒳} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳}

lemma UQ.neg {Q : Measure 𝒳} [IsProbabilityMeasure Q] {h : 𝒳 → ℝ} (hm : Measurable h) {p q : ℝ}
    (hq : UQ Q h p q) : UQ Q (fun x => -h x) (1 - p) (-q) := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have e1 : ∀ c, {x | -h x < -c} = {x | h x ≤ c}ᶜ := fun c => by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le, neg_lt_neg_iff]
  have e2 : ∀ c, {x | -h x ≤ -c} = {x | h x < c}ᶜ := fun c => by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt, neg_le_neg_iff]
  have c1 : ∀ c, Q.real {x | h x ≤ c}ᶜ = 1 - Q.real {x | h x ≤ c} := fun c =>
    probReal_compl_eq_one_sub (measurableSet_le hm measurable_const)
  have c2 : ∀ c, Q.real {x | h x < c}ᶜ = 1 - Q.real {x | h x < c} := fun c =>
    probReal_compl_eq_one_sub (measurableSet_lt hm measurable_const)
  refine ⟨?_, ?_, fun d hd => ?_, fun d hd => ?_⟩
  · rw [e1, c1]; linarith
  · rw [e2, c2]; linarith
  · rw [show -q - d = -(q + d) by ring, e1, c1]; linarith [h4 d hd]
  · rw [show -q + d = -(q - d) by ring, e2, c2]; linarith [h3 d hd]

/-- An i.i.d. `P` sequence. -/
structure IIDSample (μ : Measure Ω) (P : Measure 𝒳) (X : ℕ → Ω → 𝒳) : Prop where
  meas : ∀ i, Measurable (X i)
  indep : iIndepFun X μ
  law : ∀ i, μ.map (X i) = P

/-- The sample vector `(h(X_0), …, h(X_{n−1}))`. -/
def smp (X : ℕ → Ω → 𝒳) (h : 𝒳 → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ := fun i => h (X i ω)

lemma measurable_smp (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) (n : ℕ) :
    Measurable fun ω => smp X h n ω :=
  measurable_pi_iff.2 fun i => hm.comp (hS.meas i)

lemma sum_smp (X : ℕ → Ω → 𝒳) (h : 𝒳 → ℝ) (n : ℕ) (ω : Ω) (F : ℝ → ℝ) :
    ∑ i, F (smp X h n ω i) = ∑ i ∈ range n, F (h (X i ω)) :=
  Fin.sum_univ_eq_sum_range (fun i => F (h (X i ω))) n

/-! ### Chebyshev for sample averages -/

lemma cheb_avg (hS : IIDSample μ P X) {ψ : 𝒳 → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ |(∑ i ∈ range n, ψ (X i ω)) / n - ∫ x, ψ x ∂P|} ≤ ENNReal.ofReal (4 * C ^ 2 / (n * t ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set m := ∫ x, ψ x ∂P
  set φ : 𝒳 → ℝ := fun x => ψ x - m
  have hm : |m| ≤ C := abs_integral_le_of_abs_le hC
  have hφb : ∀ x, |φ x| ≤ 2 * C := fun x => (abs_sub _ _).trans (by linarith [hC x])
  have hφm : Measurable φ := hψ.sub_const _
  have hφ0 : ∫ x, φ x ∂P = 0 := by
    simp only [φ]
    rw [integral_sub (integrable_of_abs_le hψ hC) (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_self]
  have hrw : ∀ ω, (∑ i ∈ range n, ψ (X i ω)) / n - m = (∑ i ∈ range n, φ (X i ω)) / n := fun ω => by
    simp only [φ, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hsq := integral_sq_sum_comp hS.meas hS.indep hS.law hφm hφb hφ0 (range n)
  rw [card_range] at hsq
  have hφ2 : ∫ x, φ x ^ 2 ∂P ≤ (2 * C) ^ 2 := by
    calc ∫ x, φ x ^ 2 ∂P ≤ ∫ _x, (2 * C) ^ 2 ∂P := by
          refine integral_mono (integrable_of_abs_le (hφm.pow_const 2) (C := (2 * C) ^ 2) fun x => ?_)
            (integrable_const _) fun x => ?_
          · rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2
          · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2
      _ = (2 * C) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  set f : Ω → ℝ := fun ω => ((∑ i ∈ range n, φ (X i ω)) / n) ^ 2
  have hfm : Measurable f :=
    ((Finset.measurable_sum _ fun i _ => hφm.comp (hS.meas i)).div_const _).pow_const 2
  have hfb : ∀ ω, |f ω| ≤ (2 * C) ^ 2 := fun ω => by
    simp only [f]
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range n, |φ (X i ω)| ≤ ∑ _i ∈ range n, 2 * C := sum_le_sum fun i _ => hφb _
      _ = 2 * C * n := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hfi : Integrable f μ := integrable_of_abs_le hfm hfb
  have hfint : ∫ ω, f ω ∂μ ≤ 4 * C ^ 2 / n := by
    have : ∫ ω, f ω ∂μ = (∫ ω, (∑ i ∈ range n, φ (X i ω)) ^ 2 ∂μ) / n ^ 2 := by
      simp only [f, div_pow]; rw [integral_div]
    rw [this, hsq, div_le_div_iff₀ (by positivity) hn']
    nlinarith
  refine (measure_mono fun ω hω => ?_).trans ((measure_ge_le_ofReal (ε := t ^ 2) (fun ω => sq_nonneg _) hfi
    (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_))
  · simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hrw] at hω
    show t ^ 2 ≤ ((∑ i ∈ range n, φ (X i ω)) / n) ^ 2
    rw [← sq_abs ((∑ i ∈ range n, φ (X i ω)) / n)]
    exact pow_le_pow_left₀ ht.le hω 2
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (∫ ω, f ω ∂μ) * (n * t ^ 2) ≤ 4 * C ^ 2 / n * (n * t ^ 2) :=
          mul_le_mul_of_nonneg_right hfint (by positivity)
      _ = 4 * C ^ 2 * t ^ 2 := by field_simp
      _ ≤ 4 * C ^ 2 * t ^ 2 := le_rfl

lemma tendsto_cheb (hS : IIDSample μ P X) {ψ : 𝒳 → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => μ {ω | t ≤ |(∑ i ∈ range n, ψ (X i ω)) / n - ∫ x, ψ x ∂P|}) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (4 * C ^ 2 / (n * t ^ 2))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 4 * C ^ 2 / ((n : ℝ) * t ^ 2)) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (show 0 < t ^ 2 by positivity)
      exact this.const_div_atTop _ |>.congr fun n => rfl
    simpa using ENNReal.tendsto_ofReal this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact cheb_avg hS hψ hC hn ht

lemma tip0_avg (hS : IIDSample μ P X) {ψ : 𝒳 → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    TIP0 μ (fun n ω => (∑ i ∈ range n, ψ (X i ω)) / n - ∫ x, ψ x ∂P) :=
  fun ε hε => tendsto_cheb hS hψ hC hε

/-! ### Empirical cdf tails -/

lemma ind_le_meas {h : 𝒳 → ℝ} (hm : Measurable h) (x : ℝ) :
    Measurable fun z => if h z ≤ x then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_le hm measurable_const) measurable_const measurable_const

lemma ind_lt_meas {h : 𝒳 → ℝ} (hm : Measurable h) (x : ℝ) :
    Measurable fun z => if h z < x then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_lt hm measurable_const) measurable_const measurable_const

lemma integral_ind_le {h : 𝒳 → ℝ} (hm : Measurable h) (x : ℝ) :
    ∫ z, (if h z ≤ x then (1 : ℝ) else 0) ∂P = P.real {z | h z ≤ x} := by
  have : (fun z => if h z ≤ x then (1 : ℝ) else 0) = {z | h z ≤ x}.indicator fun _ => 1 := by
    funext z; simp [Set.indicator_apply]
  rw [this, integral_indicator_const _ (measurableSet_le hm measurable_const), smul_eq_mul, mul_one]

lemma integral_ind_lt {h : 𝒳 → ℝ} (hm : Measurable h) (x : ℝ) :
    ∫ z, (if h z < x then (1 : ℝ) else 0) ∂P = P.real {z | h z < x} := by
  have : (fun z => if h z < x then (1 : ℝ) else 0) = {z | h z < x}.indicator fun _ => 1 := by
    funext z; simp [Set.indicator_apply]
  rw [this, integral_indicator_const _ (measurableSet_lt hm measurable_const), smul_eq_mul, mul_one]

lemma ecdf_smp (X : ℕ → Ω → 𝒳) (h : 𝒳 → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    ecdf (smp X h n ω) x = (∑ i ∈ range n, (fun z => if h z ≤ x then (1 : ℝ) else 0) (X i ω)) / n := by
  unfold ecdf
  rw [sum_smp X h n ω (fun y => if y ≤ x then (1 : ℝ) else 0)]

lemma ecdfLt_smp (X : ℕ → Ω → 𝒳) (h : 𝒳 → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    ecdfLt (smp X h n ω) x = (∑ i ∈ range n, (fun z => if h z < x then (1 : ℝ) else 0) (X i ω)) / n := by
  unfold ecdfLt
  rw [sum_smp X h n ω (fun y => if y < x then (1 : ℝ) else 0)]

lemma abs_ind_le (p : Prop) [Decidable p] : |(if p then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

lemma tail_ecdf (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {x p : ℝ}
    (hp : p < P.real {z | h z ≤ x}) :
    Tendsto (fun n : ℕ => μ {ω | ecdf (smp X h n ω) x < p}) atTop (𝓝 0) := by
  have ht : 0 < P.real {z | h z ≤ x} - p := by linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_cheb hS (ind_le_meas hm x) (fun z => abs_ind_le _) ht) (fun _ => zero_le) fun n => ?_
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [ecdf_smp, integral_ind_le hm] at *
  rw [abs_sub_comm, le_abs]
  left; linarith

lemma tail_ecdfLt (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {x p : ℝ}
    (hp : P.real {z | h z < x} < p) :
    Tendsto (fun n : ℕ => μ {ω | p ≤ ecdfLt (smp X h n ω) x}) atTop (𝓝 0) := by
  have ht : 0 < p - P.real {z | h z < x} := by linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_cheb hS (ind_lt_meas hm x) (fun z => abs_ind_le _) ht) (fun _ => zero_le) fun n => ?_
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [ecdfLt_smp, integral_ind_lt hm] at *
  rw [le_abs]
  left; linarith

/-! ### Convergence to zero in probability from `η`-bounds -/

lemma tendsto_zero_of_forall_real {a : ℕ → ℝ≥0∞} (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, a n ≤ ENNReal.ofReal η) :
    Tendsto a atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  obtain ⟨r, -, hr0, hrγ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hγ
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
  filter_upwards [h r hr] with n hn
  exact hn.trans hrγ.le

lemma card_filter_eq_ecdf (v : Fin n → ℝ) (x : ℝ) (hn : 0 < n) :
    ((univ.filter fun j => v j ≤ x).card : ℝ) = n * ecdf v x := by
  unfold ecdf
  rw [natCast_card_filter]
  have : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

lemma card_filter_eq_ecdfLt (v : Fin n → ℝ) (x : ℝ) (hn : 0 < n) :
    ((univ.filter fun j => v j < x).card : ℝ) = n * ecdfLt v x := by
  unfold ecdfLt
  rw [natCast_card_filter]
  have : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

/-! ### The empirical quantile is consistent -/

theorem tip0_quantLo (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {α q : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hq : UQ P h (1 - α) q) :
    TIP0 μ (fun n ω => quantLo n α (smp X h n ω) - q) := by
  obtain ⟨-, -, hl, hr⟩ := hq
  intro ε hε
  have h1 := tail_ecdf hS hm (hr (ε / 2) (by linarith))
  have h2 := tail_ecdfLt hS hm (hl (ε / 2) (by linarith))
  have hs := h1.add h2
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  rcases le_abs'.1 hω with hneg | hpos
  · right
    by_contra hc
    push_neg at hc
    have := le_quantLo (x := q - ε / 2) hn hα0 hα1 (smp X h n ω) (by
      rw [card_filter_eq_ecdfLt _ _ hn]; exact mul_lt_mul_of_pos_left hc hn')
    linarith
  · left
    by_contra hc
    push_neg at hc
    have := quantLo_le (x := q + ε / 2) hn hα0 hα1 (smp X h n ω) (by
      rw [card_filter_eq_ecdf _ _ hn]; exact mul_le_mul_of_nonneg_left hc hn'.le)
    linarith

/-! ### Asymptotic linearity of the lower trimmed mean -/

lemma alg_identity {s β L q E S n : ℝ} (hs : s ≠ 0) (hβ : β ≠ 0) (hn : s * s = n) :
    s * (L - (q - β⁻¹ * E)) + β⁻¹ * (s⁻¹ * (S - n * E)) = s / β * (β * L - (β * q - S / n)) := by
  subst hn
  field_simp
  ring

/-- The remainder `√n (L_n − L) + β⁻¹ n^{−1/2} Σ_{i<n} (g(X_i) − P g)`. -/
def alRem (X : ℕ → Ω → 𝒳) (P : Measure 𝒳) (h : 𝒳 → ℝ) (α q : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  √(n : ℝ) * (sInf ((fun w => ∑ i, w i * smp X h n ω i) '' capped n α) -
      (q - (1 - α)⁻¹ * ∫ x, max (q - h x) 0 ∂P)) +
    (1 - α)⁻¹ * ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, (max (q - h (X i ω)) 0 - ∫ x, max (q - h x) 0 ∂P))

theorem tip0_trimLo (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {α q : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hq : UQ P h (1 - α) q) :
    TIP0 μ (alRem X P h α q) := by
  obtain ⟨hq1, hq2, hl, hr⟩ := hq
  have hβ : 0 < 1 - α := by linarith
  set β := 1 - α with hβdef
  intro ε hε
  refine tendsto_zero_of_forall_real fun η hη => ?_
  set d : ℝ := ε * β * √η / 8 with hd
  have hd0 : 0 < d := by positivity
  have hB1 := tail_ecdf hS hm (hr d hd0)
  have hB2 := tail_ecdfLt hS hm (hl d hd0)
  have hη4 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 4) := ENNReal.ofReal_pos.2 (by linarith)
  filter_upwards [eventually_gt_atTop 0, (ENNReal.tendsto_nhds_zero.1 hB1) _ hη4,
    (ENNReal.tendsto_nhds_zero.1 hB2) _ hη4] with n hn hb1 hb2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  set t : ℝ := ε * β / (2 * d * √(n : ℝ)) with ht
  have ht0 : 0 < t := by positivity
  set Fq := P.real {z | h z ≤ q}
  set Gq := P.real {z | h z < q}
  set C1 := {ω | t ≤ |(∑ i ∈ range n, (fun z => if h z ≤ q then (1 : ℝ) else 0) (X i ω)) / n -
    ∫ z, (if h z ≤ q then (1 : ℝ) else 0) ∂P|}
  set C2 := {ω | t ≤ |(∑ i ∈ range n, (fun z => if h z < q then (1 : ℝ) else 0) (X i ω)) / n -
    ∫ z, (if h z < q then (1 : ℝ) else 0) ∂P|}
  have hcheb : ENNReal.ofReal (4 * 1 ^ 2 / (n * t ^ 2)) = ENNReal.ofReal (η / 4) := by
    congr 1
    simp only [ht, hd]
    have hs : √η ^ 2 = η := Real.sq_sqrt hη.le
    have hsn2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
    field_simp
    rw [hs, hsn2]
    ring
  have hc1 : μ C1 ≤ ENNReal.ofReal (η / 4) :=
    hcheb ▸ cheb_avg hS (ind_le_meas hm q) (fun z => abs_ind_le _) hn ht0
  have hc2 : μ C2 ≤ ENNReal.ofReal (η / 4) :=
    hcheb ▸ cheb_avg hS (ind_lt_meas hm q) (fun z => abs_ind_le _) hn ht0
  have hsub : {ω | ε ≤ |alRem X P h α q n ω|} ⊆
      (({ω | ecdf (smp X h n ω) (q + d) < β} ∪ {ω | β ≤ ecdfLt (smp X h n ω) (q - d)}) ∪ C1) ∪ C2 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_le, C1, C2] at hc
    obtain ⟨⟨⟨hF, hG⟩, hC1⟩, hC2⟩ := hc
    rw [integral_ind_le hm, ← ecdf_smp] at hC1
    rw [integral_ind_lt hm, ← ecdfLt_smp] at hC2
    obtain ⟨b1, b2⟩ := al_bound (q := q) hn hα0 hα1 hd0.le (smp X h n ω) hF hG.le
    set D := (1 - α) * sInf ((fun w => ∑ i, w i * smp X h n ω i) '' capped n α) - ((1 - α) * q - emean (smp X h n ω) q)
    have hR : alRem X P h α q n ω = √(n : ℝ) / β * D := by
      simp only [alRem, D, emean]
      rw [sum_smp X h n ω (fun y => max (q - y) 0), sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      exact alg_identity hsn.ne' hβ.ne' (Real.mul_self_sqrt hn'.le)
    have hm1 : max (β - ecdf (smp X h n ω) q) 0 ≤ |ecdf (smp X h n ω) q - Fq| := by
      refine max_le ?_ (abs_nonneg _)
      rw [abs_sub_comm]
      have : β - ecdf (smp X h n ω) q ≤ Fq - ecdf (smp X h n ω) q := by linarith
      exact this.trans (le_abs_self _)
    have hm2 : max (ecdfLt (smp X h n ω) q - β) 0 ≤ |ecdfLt (smp X h n ω) q - Gq| := by
      refine max_le ?_ (abs_nonneg _)
      have : ecdfLt (smp X h n ω) q - β ≤ ecdfLt (smp X h n ω) q - Gq := by linarith
      exact this.trans (le_abs_self _)
    have hD : D < d * (2 * t) := by
      calc D ≤ d * (max (1 - α - ecdf (smp X h n ω) q) 0 + max (ecdfLt (smp X h n ω) q - (1 - α)) 0) := b2
        _ ≤ d * (|ecdf (smp X h n ω) q - Fq| + |ecdfLt (smp X h n ω) q - Gq|) :=
            mul_le_mul_of_nonneg_left (add_le_add hm1 hm2) hd0.le
        _ < d * (2 * t) := mul_lt_mul_of_pos_left (by linarith) hd0
    have hdt : d * (2 * t) = ε * β / √(n : ℝ) := by
      simp only [ht]; field_simp
    rw [hR, abs_of_nonneg (by positivity)] at hω
    have : √(n : ℝ) / β * D < ε := by
      calc √(n : ℝ) / β * D < √(n : ℝ) / β * (ε * β / √(n : ℝ)) :=
            mul_lt_mul_of_pos_left (hdt ▸ hD) (by positivity)
        _ = ε := by field_simp
    linarith
  calc μ {ω | ε ≤ |alRem X P h α q n ω|}
      ≤ μ ((({ω | ecdf (smp X h n ω) (q + d) < β} ∪ {ω | β ≤ ecdfLt (smp X h n ω) (q - d)}) ∪ C1) ∪ C2) :=
        measure_mono hsub
    _ ≤ μ {ω | ecdf (smp X h n ω) (q + d) < β} + μ {ω | β ≤ ecdfLt (smp X h n ω) (q - d)} + μ C1 + μ C2 :=
        (measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
          (add_le_add_left (measure_union_le _ _) _)) _)
    _ ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) := by
        gcongr
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring

end StatFormal.Foundations.TrimmedMean
