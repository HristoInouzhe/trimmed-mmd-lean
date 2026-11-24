import StatFormal.Lib.Donsker.Chaining
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic

/-!
# The two-sample empirical process of a Lipschitz-parametrised bounded class (untrusted library code)

`tsProc F G P Q n m r x y z = r ((P_n − P) F_z) + r ((Q_m − Q) G_z)` for classes `F, G : X → 𝒳 → ℝ` that are
measurable, bounded by `B` and `L`-Lipschitz in the index. For i.i.d. samples:
* `hoeffding_abs`: two-sided Hoeffding for a centred sum of bounded i.i.d. terms (Mathlib
  `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` + `hasSubgaussianMGF_of_mem_Icc`);
* `tsProc_tail_inc`, `tsProc_tail_pt`: uniform (in the sizes, given `r²/n, r²/m ≤ R²`) sub-Gaussian tails of the
  increments and of the values — the hypotheses of `isTightMeasureSet_of_subgaussian`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace StatFormal.Foundations.Donsker

section Hoeffding
variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

/-- Two-sided Hoeffding for `Σ_{i<n} (h(ξ_i) − P h)`, `|h| ≤ b`. -/
lemma hoeffding_abs (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → 𝒳) (hξ : ∀ i, Measurable (ξ i))
    (hi : iIndepFun ξ μ) (P : Measure 𝒳) (hl : ∀ i, μ.map (ξ i) = P) (h : 𝒳 → ℝ) (hh : Measurable h)
    {b : ℝ} (hb : 0 ≤ b) (hhb : ∀ w, |h w| ≤ b) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i ∈ Finset.range n, (h (ξ i ω) - ∫ w, h w ∂P)|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * n * b ^ 2))) := by
  have hP : ∀ i, ∫ w, h w ∂P = μ[fun ω => h (ξ i ω)] := by
    intro i
    rw [← hl i, integral_map (hξ i).aemeasurable hh.aestronglyMeasurable]
  set Y : ℕ → Ω → ℝ := fun i ω => h (ξ i ω) - ∫ w, h w ∂P with hY
  have hYi : iIndepFun Y μ := hi.comp (fun _ w => h w - ∫ w, h w ∂P) (fun _ => hh.sub_const _)
  set cc : ℝ≥0 := (‖b - -b‖₊ / 2) ^ 2 with hcc
  have hc : (cc : ℝ) = b ^ 2 := by
    rw [hcc]
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [show b - -b = 2 * b by ring, abs_of_nonneg (by linarith)]
    ring
  have hsub : ∀ i, HasSubgaussianMGF (Y i) cc μ := by
    intro i
    have := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ω => h (ξ i ω)) (a := -b) (b := b)
      (hh.comp (hξ i)).aemeasurable (ae_of_all _ fun ω => abs_le.1 (hhb _))
    have e : (fun ω => h (ξ i ω) - μ[fun ω => h (ξ i ω)]) = Y i := by
      funext ω; simp only [hY, hP i]
    rw [e] at this
    exact this
  have h1 := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hYi (fun i _ => hsub i) ht (n := n)
  have hYn : iIndepFun (fun i ω => -Y i ω) μ := hYi.comp (fun _ y => -y) (fun _ => measurable_neg)
  have h2 := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hYn (fun i _ => (hsub i).neg) ht (n := n)
  rw [hc] at h1 h2
  have hsub' : {ω | t ≤ |∑ i ∈ Finset.range n, Y i ω|} ⊆
      {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω} ∪ {ω | t ≤ ∑ i ∈ Finset.range n, -Y i ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, Finset.sum_neg_distrib] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; exact h
  calc μ {ω | t ≤ |∑ i ∈ Finset.range n, (h (ξ i ω) - ∫ w, h w ∂P)|}
      ≤ μ {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω} + μ {ω | t ≤ ∑ i ∈ Finset.range n, -Y i ω} :=
        (measure_mono hsub').trans (measure_union_le _ _)
    _ = ENNReal.ofReal (μ.real {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω}) +
          ENNReal.ofReal (μ.real {ω | t ≤ ∑ i ∈ Finset.range n, -Y i ω}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * n * b ^ 2))) + ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * n * b ^ 2))) :=
        add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * n * b ^ 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end Hoeffding

section Proc
variable {X 𝒳 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Ω] [PseudoMetricSpace X]

/-- The two-sample empirical process `z ↦ r ((P_n − P) F_z) + r ((Q_m − Q) G_z)`. -/
def tsProc (F G : X → 𝒳 → ℝ) (P Q : Measure 𝒳) (n m : ℕ) (r : ℝ) (x y : ℕ → 𝒳) (z : X) : ℝ :=
  r * ((∑ i ∈ Finset.range n, F z (x i)) / n - ∫ w, F z w ∂P)
    + r * ((∑ j ∈ Finset.range m, G z (y j)) / m - ∫ w, G z w ∂Q)

/-- A bounded, measurable class, Lipschitz in the index. -/
structure IsLipClass (F : X → 𝒳 → ℝ) (B L : ℝ) : Prop where
  meas : ∀ z, Measurable (F z)
  bound : ∀ z w, |F z w| ≤ B
  lip : ∀ z z' w, |F z w - F z' w| ≤ L * dist z z'

/-- The one-sample term `r ((P_n − P) h)`. -/
def oneTerm (h : 𝒳 → ℝ) (P : Measure 𝒳) (n : ℕ) (r : ℝ) (x : ℕ → 𝒳) : ℝ :=
  r * ((∑ i ∈ Finset.range n, h (x i)) / n - ∫ w, h w ∂P)

lemma tsProc_eq (F G : X → 𝒳 → ℝ) (P Q : Measure 𝒳) (n m : ℕ) (r : ℝ) (x y : ℕ → 𝒳) (z : X) :
    tsProc F G P Q n m r x y z = oneTerm (F z) P n r x + oneTerm (G z) Q m r y := rfl

lemma oneTerm_sub {h h' : 𝒳 → ℝ} (P : Measure 𝒳) (hi : Integrable h P) (hi' : Integrable h' P) (n : ℕ) (r : ℝ)
    (x : ℕ → 𝒳) : oneTerm h P n r x - oneTerm h' P n r x = oneTerm (fun w => h w - h' w) P n r x := by
  simp only [oneTerm, integral_sub hi hi', Finset.sum_sub_distrib]
  ring

lemma integrable_of_abs_le [IsFiniteMeasure (P : Measure 𝒳)] {h : 𝒳 → ℝ} (hm : Measurable h) {b : ℝ}
    (hb : ∀ w, |h w| ≤ b) : Integrable h P :=
  Integrable.of_bound hm.aestronglyMeasurable b (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hb w)

/-- Sub-Gaussian tail of one term, uniformly in `n` given `r²/n ≤ R²`. -/
lemma oneTerm_tail (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → 𝒳) (hξ : ∀ i, Measurable (ξ i))
    (hi : iIndepFun ξ μ) (P : Measure 𝒳) (hl : ∀ i, μ.map (ξ i) = P) (h : 𝒳 → ℝ) (hh : Measurable h)
    {b : ℝ} (hb : 0 < b) (hhb : ∀ w, |h w| ≤ b) {n : ℕ} (hn : 1 ≤ n) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrR : r ^ 2 / n ≤ R ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ |oneTerm h P n r (fun i => ξ i ω)|} ≤ ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (2 * R ^ 2 * b ^ 2)))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : ∀ ω, oneTerm h P n r (fun i => ξ i ω) = r / n * ∑ i ∈ Finset.range n, (h (ξ i ω) - ∫ w, h w ∂P) := by
    intro ω
    simp only [oneTerm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hset : {ω | u ≤ |oneTerm h P n r (fun i => ξ i ω)|} =
      {ω | u * n / r ≤ |∑ i ∈ Finset.range n, (h (ξ i ω) - ∫ w, h w ∂P)|} := by
    ext ω
    simp only [mem_ofPred_eq, heq, abs_mul, abs_of_pos (div_pos hr hn')]
    rw [div_le_iff₀ hr, div_mul_eq_mul_div, le_div_iff₀ hn', mul_comm r]
  rw [hset]
  refine (hoeffding_abs μ ξ hξ hi P hl h hh hb.le hhb n (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  -- (u n / r)² / (2 n b²) ≥ u² / (2 R² b²)
  have hrn : r ^ 2 ≤ R ^ 2 * n := by rwa [div_le_iff₀ hn'] at hrR
  rw [neg_div, neg_le_neg_iff, div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : u ^ 2 * (r ^ 2 * (2 * n * b ^ 2)) ≤ u ^ 2 * (R ^ 2 * n * (2 * n * b ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg u)
    exact mul_le_mul_of_nonneg_right hrn (by positivity)
  nlinarith [this]

lemma tail_add (μ : Measure Ω) (A B : Ω → ℝ) (u : ℝ) :
    μ {ω | u ≤ |A ω + B ω|} ≤ μ {ω | u / 2 ≤ |A ω|} + μ {ω | u / 2 ≤ |B ω|} := by
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hc
  push_neg at hc
  have := abs_add_le (A ω) (B ω)
  linarith [hc.1, hc.2]

/-- Uniform sub-Gaussian tails of the two-sample process at a point. -/
lemma tsProc_tail_pt (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ j, Measurable (η j)) (hiξ : iIndepFun ξ μ) (hiη : iIndepFun η μ)
    (P Q : Measure 𝒳) (hlξ : ∀ i, μ.map (ξ i) = P) (hlη : ∀ j, μ.map (η j) = Q)
    {F G : X → 𝒳 → ℝ} {B L : ℝ} (hF : IsLipClass F B L) (hG : IsLipClass G B L) (hB : 0 < B)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrn : r ^ 2 / n ≤ R ^ 2) (hrm : r ^ 2 / m ≤ R ^ 2) (z : X) {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ |tsProc F G P Q n m r (fun i => ξ i ω) (fun j => η j ω) z|} ≤
      ENNReal.ofReal (4 * Real.exp (-(u ^ 2 / (3 * R * B) ^ 2))) := by
  simp only [tsProc_eq]
  refine (tail_add μ _ _ u).trans ?_
  have h1 := oneTerm_tail μ ξ hξ hiξ P hlξ (F z) (hF.meas z) hB (hF.bound z) hn hr hR hrn (u := u / 2) (by positivity)
  have h2 := oneTerm_tail μ η hη hiη Q hlη (G z) (hG.meas z) hB (hG.bound z) hm hr hR hrm (u := u / 2) (by positivity)
  have hexp : Real.exp (-((u / 2) ^ 2 / (2 * R ^ 2 * B ^ 2))) ≤ Real.exp (-(u ^ 2 / (3 * R * B) ^ 2)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff, div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u, sq_nonneg (R * B), mul_nonneg (sq_nonneg u) (sq_nonneg (R * B))]
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-((u / 2) ^ 2 / (2 * R ^ 2 * B ^ 2)))) +
        ENNReal.ofReal (2 * Real.exp (-((u / 2) ^ 2 / (2 * R ^ 2 * B ^ 2)))) := add_le_add h1 h2
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (3 * R * B) ^ 2))) +
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (3 * R * B) ^ 2))) := by
        gcongr
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- Uniform sub-Gaussian tails of the increments of the two-sample process. -/
lemma tsProc_tail_inc (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ j, Measurable (η j)) (hiξ : iIndepFun ξ μ) (hiη : iIndepFun η μ)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hlξ : ∀ i, μ.map (ξ i) = P) (hlη : ∀ j, μ.map (η j) = Q)
    {F G : X → 𝒳 → ℝ} {B L : ℝ} (hF : IsLipClass F B L) (hG : IsLipClass G B L) (hL : 0 < L)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrn : r ^ 2 / n ≤ R ^ 2) (hrm : r ^ 2 / m ≤ R ^ 2) (z z' : X) {ρ : ℝ} (hρ : 0 < ρ) (hd : dist z z' ≤ ρ)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ |tsProc F G P Q n m r (fun i => ξ i ω) (fun j => η j ω) z -
        tsProc F G P Q n m r (fun i => ξ i ω) (fun j => η j ω) z'|} ≤
      ENNReal.ofReal (4 * Real.exp (-(u ^ 2 / (3 * R * L * ρ) ^ 2))) := by
  have hb : 0 < L * ρ := mul_pos hL hρ
  have hFb : ∀ w, |F z w - F z' w| ≤ L * ρ := fun w =>
    (hF.lip z z' w).trans (mul_le_mul_of_nonneg_left hd hL.le)
  have hGb : ∀ w, |G z w - G z' w| ≤ L * ρ := fun w =>
    (hG.lip z z' w).trans (mul_le_mul_of_nonneg_left hd hL.le)
  have hiF := fun z => integrable_of_abs_le (P := P) (hF.meas z) (hF.bound z)
  have hiG := fun z => integrable_of_abs_le (P := Q) (hG.meas z) (hG.bound z)
  have heq : ∀ ω, tsProc F G P Q n m r (fun i => ξ i ω) (fun j => η j ω) z -
      tsProc F G P Q n m r (fun i => ξ i ω) (fun j => η j ω) z' =
      oneTerm (fun w => F z w - F z' w) P n r (fun i => ξ i ω) +
        oneTerm (fun w => G z w - G z' w) Q m r (fun j => η j ω) := by
    intro ω
    simp only [tsProc_eq]
    rw [← oneTerm_sub P (hiF z) (hiF z'), ← oneTerm_sub Q (hiG z) (hiG z')]
    ring
  simp only [heq]
  refine (tail_add μ _ _ u).trans ?_
  have h1 := oneTerm_tail μ ξ hξ hiξ P hlξ _ ((hF.meas z).sub (hF.meas z')) hb hFb hn hr hR hrn (u := u / 2) (by positivity)
  have h2 := oneTerm_tail μ η hη hiη Q hlη _ ((hG.meas z).sub (hG.meas z')) hb hGb hm hr hR hrm (u := u / 2) (by positivity)
  have hexp : Real.exp (-((u / 2) ^ 2 / (2 * R ^ 2 * (L * ρ) ^ 2))) ≤ Real.exp (-(u ^ 2 / (3 * R * L * ρ) ^ 2)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff, div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u, sq_nonneg (R * L * ρ), mul_nonneg (sq_nonneg u) (sq_nonneg (R * L * ρ))]
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-((u / 2) ^ 2 / (2 * R ^ 2 * (L * ρ) ^ 2)))) +
        ENNReal.ofReal (2 * Real.exp (-((u / 2) ^ 2 / (2 * R ^ 2 * (L * ρ) ^ 2)))) := add_le_add h1 h2
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (3 * R * L * ρ) ^ 2))) +
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (3 * R * L * ρ) ^ 2))) := by
        gcongr
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end Proc

end StatFormal.Foundations.Donsker
