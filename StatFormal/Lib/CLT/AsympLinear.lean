import StatFormal.Lib.CLT.Hoeffding
import StatFormal.Lib.CLT.TwoSample
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Asymptotic linearity in two independent samples (library)

For two independent i.i.d. `P₀` samples (pool `X`, validation `Y`, sizes `n`, `m(n)` with `m(n)/n → κ > 0`) a
real statistic `Q_n` is *asymptotically linear with centre `q`* (`IsAL`) if, for bounded measurable centred
influence functions `α`, `β`,
`√n (Q_n − q) − (n^{−1/2} Σ_{i<n} α(X_i) + √n m^{−1} Σ_{i<m} β(Y_i)) → 0` in probability.

* toolkit for convergence to `0` in probability (`TIP0`) and boundedness in probability (`BIP`), Markov and
  Chebyshev bounds;
* the linear statistic is bounded in probability (`bip_linStat`);
* closure of `IsAL` under sums, constant and convergent deterministic multiples (`IsAL.seq_mul`, which needs
  `√n(a_n − a) → 0`), products, inverses (`q ≠ 0`, the delta method) and powers;
* pool and validation averages are `IsAL`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Foundations.CLT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Convergence to zero and boundedness in probability -/

/-- `A_n → 0` in probability. -/
def TIP0 (P : Measure Ω) (A : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ |A n ω|}) atTop (𝓝 0)

/-- `S_n = O_P(1)`. -/
def BIP (P : Measure Ω) (S : ℕ → Ω → ℝ) : Prop :=
  ∀ γ > (0 : ℝ≥0∞), ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, P {ω | K ≤ |S n ω|} ≤ γ

lemma tip0_iff {A : ℕ → Ω → ℝ} : TendstoInMeasure P A atTop 0 ↔ TIP0 P A := by
  rw [tendstoInMeasure_iff_norm]
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, TIP0]

lemma TIP0.congr {A B : ℕ → Ω → ℝ} (hA : TIP0 P A) (h : ∀ᶠ n in atTop, ∀ ω, A n ω = B n ω) : TIP0 P B := by
  intro ε hε
  refine (hA ε hε).congr' ?_
  filter_upwards [h] with n hn
  congr 1; ext ω; simp only [Set.mem_setOf_eq, hn ω]

lemma tip0_zero : TIP0 P (fun _ _ => (0 : ℝ)) := by
  intro ε hε
  have : {ω : Ω | ε ≤ |(0 : ℝ)|} = ∅ :=
    Set.eq_empty_of_forall_notMem fun ω h => absurd (show ε ≤ |(0 : ℝ)| from h) (by simp [not_le.2 hε])
  simp only [this, measure_empty]
  exact tendsto_const_nhds

lemma TIP0.add {A B : ℕ → Ω → ℝ} (hA : TIP0 P A) (hB : TIP0 P B) : TIP0 P (fun n ω => A n ω + B n ω) := by
  intro ε hε
  have h := (hA (ε / 2) (by linarith)).add (hB (ε / 2) (by linarith))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) fun n => ?_
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_contra hc
  push_neg at hc
  have := abs_add_le (A n ω) (B n ω)
  linarith [hc.1, hc.2]

lemma TIP0.const_mul {A : ℕ → Ω → ℝ} (hA : TIP0 P A) (c : ℝ) : TIP0 P (fun n ω => c * A n ω) := by
  intro ε hε
  by_cases hc : c = 0
  · subst hc
    have : ∀ n, {ω : Ω | ε ≤ |0 * A n ω|} = ∅ := fun n =>
      Set.eq_empty_of_forall_notMem fun ω h => absurd (show ε ≤ |0 * A n ω| from h) (by simp [not_le.2 hε])
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  · have hc' : 0 < |c| := abs_pos.2 hc
    refine (hA (ε / |c|) (div_pos hε hc')).congr fun n => ?_
    congr 1; ext ω
    simp only [Set.mem_setOf_eq, abs_mul]
    rw [div_le_iff₀ hc', mul_comm]

lemma TIP0.neg {A : ℕ → Ω → ℝ} (hA : TIP0 P A) : TIP0 P (fun n ω => -A n ω) :=
  (hA.const_mul (-1)).congr (Eventually.of_forall fun n ω => by ring)

lemma TIP0.sub {A B : ℕ → Ω → ℝ} (hA : TIP0 P A) (hB : TIP0 P B) : TIP0 P (fun n ω => A n ω - B n ω) :=
  (hA.add hB.neg).congr (Eventually.of_forall fun n ω => by ring)

/-- Deterministic sequences tending to `0`. -/
lemma tip0_det {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) : TIP0 P (fun n _ => a n) := by
  intro ε hε
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [(ha.abs.eventually (gt_mem_nhds (by simpa using hε)))] with n hn
  have : {ω : Ω | ε ≤ |a n|} = ∅ := by
    ext; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]; simpa using hn
  simp [this]

/-- Domination off a vanishing bad set. -/
lemma TIP0.of_dominated {A W : ℕ → Ω → ℝ} {Bad : ℕ → Set Ω} (hW : TIP0 P W)
    (hBad : Tendsto (fun n => P (Bad n)) atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, ∀ ω, ω ∉ Bad n → |A n ω| ≤ |W n ω|) : TIP0 P A := by
  intro ε hε
  have hs := (hW ε hε).add hBad
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs (Eventually.of_forall fun _ => zero_le)
    ?_
  filter_upwards [h] with n hn
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_cases hb : ω ∈ Bad n
  · exact Or.inr hb
  · exact Or.inl (hω.trans (hn ω hb))

lemma BIP.of_tip0 {A : ℕ → Ω → ℝ} (hA : TIP0 P A) : BIP P A := by
  intro γ hγ
  exact ⟨1, one_pos, (ENNReal.tendsto_nhds_zero.1 (hA 1 one_pos)) γ hγ⟩

lemma BIP.add {S T : ℕ → Ω → ℝ} (hS : BIP P S) (hT : BIP P T) : BIP P (fun n ω => S n ω + T n ω) := by
  intro γ hγ
  have hγ2 : 0 < γ / 2 := ENNReal.div_pos hγ.ne' (by norm_num)
  obtain ⟨K1, hK1, h1⟩ := hS (γ / 2) hγ2
  obtain ⟨K2, hK2, h2⟩ := hT (γ / 2) hγ2
  refine ⟨K1 + K2, by positivity, ?_⟩
  filter_upwards [h1, h2] with n hn1 hn2
  calc P {ω | K1 + K2 ≤ |S n ω + T n ω|} ≤ P ({ω | K1 ≤ |S n ω|} ∪ {ω | K2 ≤ |T n ω|}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
        by_contra hc; push_neg at hc
        have := abs_add_le (S n ω) (T n ω)
        linarith [hc.1, hc.2]
    _ ≤ γ / 2 + γ / 2 := (measure_union_le _ _).trans (add_le_add hn1 hn2)
    _ = γ := ENNReal.add_halves γ

lemma BIP.const_mul {S : ℕ → Ω → ℝ} (hS : BIP P S) (c : ℝ) : BIP P (fun n ω => c * S n ω) := by
  intro γ hγ
  obtain ⟨K, hK, h⟩ := hS γ hγ
  refine ⟨(|c| + 1) * K, by positivity, ?_⟩
  filter_upwards [h] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  simp only [Set.mem_setOf_eq, abs_mul] at hω ⊢
  by_contra hc; push_neg at hc
  have : |c| * |S n ω| ≤ |c| * K := mul_le_mul_of_nonneg_left hc.le (abs_nonneg _)
  nlinarith [abs_nonneg c, abs_nonneg (S n ω)]

/-- `o_P(1) · O_P(1) = o_P(1)`. -/
lemma TIP0.mul_bip {A S : ℕ → Ω → ℝ} (hA : TIP0 P A) (hS : BIP P S) : TIP0 P (fun n ω => A n ω * S n ω) := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  have hγ2 : 0 < γ / 2 := ENNReal.div_pos hγ.ne' (by norm_num)
  obtain ⟨K, hK, hS'⟩ := hS (γ / 2) hγ2
  filter_upwards [hS', ENNReal.tendsto_nhds_zero.1 (hA (ε / K) (div_pos hε hK)) (γ / 2) hγ2] with n h1 h2
  calc P {ω | ε ≤ |A n ω * S n ω|} ≤ P ({ω | ε / K ≤ |A n ω|} ∪ {ω | K ≤ |S n ω|}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq, Set.mem_union, abs_mul] at hω ⊢
        by_contra hc; push_neg at hc
        have : |A n ω| * |S n ω| < ε / K * K :=
          mul_lt_mul'' hc.1 hc.2 (abs_nonneg _) (abs_nonneg _)
        rw [div_mul_cancel₀ _ hK.ne'] at this
        linarith
    _ ≤ γ / 2 + γ / 2 := (measure_union_le _ _).trans (add_le_add h2 h1)
    _ = γ := ENNReal.add_halves γ

lemma TIP0.bip_mul {A S : ℕ → Ω → ℝ} (hA : TIP0 P A) (hS : BIP P S) : TIP0 P (fun n ω => S n ω * A n ω) :=
  (hA.mul_bip hS).congr (Eventually.of_forall fun n ω => mul_comm _ _)

/-- A convergent deterministic sequence is `O_P(1)`. -/
lemma bip_det {a : ℕ → ℝ} {a0 : ℝ} (ha : Tendsto a atTop (𝓝 a0)) : BIP P (fun n _ => a n) := by
  intro γ hγ
  refine ⟨|a0| + 1, by positivity, ?_⟩
  filter_upwards [ha.abs.eventually (gt_mem_nhds (show |a0| < |a0| + 1 by linarith))] with n hn
  have : {ω : Ω | |a0| + 1 ≤ |a n|} = ∅ := by
    ext; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]; exact hn
  simp [this]

lemma BIP.congr {S T : ℕ → Ω → ℝ} (hS : BIP P S) (h : ∀ᶠ n in atTop, ∀ ω, S n ω = T n ω) : BIP P T := by
  intro γ hγ
  obtain ⟨K, hK, h'⟩ := hS γ hγ
  refine ⟨K, hK, ?_⟩
  filter_upwards [h', h] with n hn hn'
  simpa only [hn'] using hn

/-! ### Markov and Chebyshev -/

lemma measure_ge_le_ofReal {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfi : Integrable f P) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂P) / ε) := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := P) (ae_of_all _ hf0) hfi ε
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hε, mul_comm]
  exact h

/-- `E|A_n| → 0` gives `A_n → 0` in probability. -/
lemma tip0_of_integral_abs {A : ℕ → Ω → ℝ} (hi : ∀ᶠ n in atTop, Integrable (A n) P)
    (h : Tendsto (fun n => ∫ ω, |A n ω| ∂P) atTop (𝓝 0)) : TIP0 P A := by
  intro ε hε
  have h2 : Tendsto (fun n => ENNReal.ofReal ((∫ ω, |A n ω| ∂P) / ε)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (h.div_const ε)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hi] with n hn
  exact measure_ge_le_ofReal (fun ω => abs_nonneg _) hn.abs hε

/-- `E A_n² → 0` gives `A_n → 0` in probability. -/
lemma tip0_of_integral_sq {A : ℕ → Ω → ℝ} (hi : ∀ᶠ n in atTop, Integrable (fun ω => A n ω ^ 2) P)
    (h : Tendsto (fun n => ∫ ω, A n ω ^ 2 ∂P) atTop (𝓝 0)) : TIP0 P A := by
  intro ε hε
  have h2 : Tendsto (fun n => ENNReal.ofReal ((∫ ω, A n ω ^ 2 ∂P) / ε ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (h.div_const (ε ^ 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hi] with n hn
  refine (measure_mono fun ω hω => ?_).trans (measure_ge_le_ofReal (fun ω => sq_nonneg _) hn (by positivity))
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [← sq_abs (A n ω)]
  exact pow_le_pow_left₀ hε.le hω 2

/-- Bounded second moments give boundedness in probability. -/
lemma bip_of_integral_sq {S : ℕ → Ω → ℝ} {C : ℝ}
    (h : ∀ᶠ n in atTop, Integrable (fun ω => S n ω ^ 2) P ∧ ∫ ω, S n ω ^ 2 ∂P ≤ C) : BIP P S := by
  intro γ hγ
  by_cases htop : γ = ⊤
  · exact ⟨1, one_pos, Eventually.of_forall fun n => htop ▸ le_top⟩
  have hγr : 0 < γ.toReal := ENNReal.toReal_pos hγ.ne' htop
  set K := √((|C| + 1) / γ.toReal) + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K, hK0, ?_⟩
  filter_upwards [h] with n ⟨hn1, hn2⟩
  refine (measure_mono fun ω hω => ?_).trans ((measure_ge_le_ofReal (ε := K ^ 2) (fun ω => sq_nonneg (S n ω)) hn1
    (by positivity)).trans ?_)
  · simp only [Set.mem_setOf_eq] at hω ⊢
    rw [← sq_abs (S n ω)]
    exact pow_le_pow_left₀ hK0.le hω 2
  · rw [← ENNReal.ofReal_toReal htop]
    refine ENNReal.ofReal_le_ofReal ?_
    have hK2 : (|C| + 1) / γ.toReal ≤ K ^ 2 := by
      have hs : √((|C| + 1) / γ.toReal) ^ 2 = (|C| + 1) / γ.toReal := Real.sq_sqrt (by positivity)
      nlinarith [Real.sqrt_nonneg ((|C| + 1) / γ.toReal)]
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hγr] at hK2
    nlinarith [le_abs_self C]

/-! ### Sums of independent centred variables -/

variable {Z : Type*} [MeasurableSpace Z] {P0 : Measure Z}

/-- `E(Σ_{i∈s} U_i)² = Σ_{i∈s} E U_i²` for independent centred bounded `U_i`. -/
lemma integral_sq_sum_indep {U : ℕ → Ω → ℝ} (hUm : ∀ i, Measurable (U i)) (hUi : iIndepFun U P)
    (hU0 : ∀ i, ∫ ω, U i ω ∂P = 0) {C : ℝ} (hUb : ∀ i ω, |U i ω| ≤ C) (s : Finset ℕ) :
    ∫ ω, (∑ i ∈ s, U i ω) ^ 2 ∂P = ∑ i ∈ s, ∫ ω, U i ω ^ 2 ∂P := by
  have hint : ∀ i j, Integrable (fun ω => U i ω * U j ω) P := fun i j =>
    integrable_of_abs_le ((hUm i).mul (hUm j)) (C := C * C) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hUb i ω) (hUb j ω) (abs_nonneg _) ((abs_nonneg _).trans (hUb i ω))
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j, Finset.sum_eq_single i]
  · intro j _ hji
    have := (hUi.indepFun (Ne.symm hji)).integral_fun_mul_eq_mul_integral (hUm i).aestronglyMeasurable
      (hUm j).aestronglyMeasurable
    rw [this, hU0 i, zero_mul]
  · intro h; exact absurd ‹i ∈ s› h

/-- For `X` i.i.d. `P₀` and bounded measurable `f`, `E(Σ_{i∈s} (f(X_i) − P₀ f))² ≤ |s| · ∫ f² dP₀`... in the form
`E(Σ_{i∈s} φ(X_i))² = |s| ∫ φ² dP₀` for centred `φ`. -/
lemma integral_sq_sum_comp {X : ℕ → Ω → Z} (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXl : ∀ i, P.map (X i) = P0) {φ : Z → ℝ} (hφ : Measurable φ) {C : ℝ} (hφb : ∀ z, |φ z| ≤ C)
    (hφ0 : ∫ z, φ z ∂P0 = 0) (s : Finset ℕ) :
    ∫ ω, (∑ i ∈ s, φ (X i ω)) ^ 2 ∂P = s.card * ∫ z, φ z ^ 2 ∂P0 := by
  have hmap : ∀ i (g : Z → ℝ), Measurable g → ∫ ω, g (X i ω) ∂P = ∫ z, g z ∂P0 := fun i g hg => by
    rw [← hXl i, integral_map (hXm i).aemeasurable hg.aestronglyMeasurable]
  rw [integral_sq_sum_indep (U := fun i ω => φ (X i ω)) (fun i => hφ.comp (hXm i))
    (hXi.comp (fun _ => φ) fun _ => hφ) (fun i => by rw [hmap i φ hφ, hφ0]) (fun i ω => hφb _) s]
  rw [Finset.sum_congr rfl fun i _ => hmap i (fun z => φ z ^ 2) (hφ.pow_const 2), Finset.sum_const, nsmul_eq_mul]

/-! ### The linear statistic and `IsAL` -/

/-- `n^{−1/2} Σ_{i<n} α(X_i) + √n m(n)^{−1} Σ_{i<m(n)} β(Y_i)`. -/
def linStat (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (α β : Z → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, α (X i ω) + √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), β (Y i ω)

/-- Two independent i.i.d. `P₀` samples with `m(n)/n → κ > 0`. -/
structure TwoSampleIID (P : Measure Ω) (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (κ : ℝ) : Prop where
  hXm : ∀ i, Measurable (X i)
  hYm : ∀ i, Measurable (Y i)
  hXi : iIndepFun X P
  hYi : iIndepFun Y P
  hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P
  hXl : ∀ i, P.map (X i) = P0
  hYl : ∀ i, P.map (Y i) = P0
  hκ : 0 < κ
  hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)

/-- Bounded measurable centred influence function. -/
def IsInfl (P0 : Measure Z) (α : Z → ℝ) : Prop :=
  Measurable α ∧ (∃ C, ∀ z, |α z| ≤ C) ∧ ∫ z, α z ∂P0 = 0

/-- `Q_n` is asymptotically linear with centre `q`. -/
def IsAL (P : Measure Ω) (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (Q : ℕ → Ω → ℝ) (q : ℝ) : Prop :=
  ∃ α β : Z → ℝ, IsInfl P0 α ∧ IsInfl P0 β ∧
    TIP0 P (fun n ω => √(n : ℝ) * (Q n ω - q) - linStat X Y m α β n ω)

lemma IsInfl.zero : IsInfl P0 (fun _ => 0) := ⟨measurable_const, ⟨0, fun _ => by simp⟩, by simp⟩

lemma IsInfl.add {α β : Z → ℝ} (hα : IsInfl P0 α) (hβ : IsInfl P0 β) [IsFiniteMeasure P0] :
    IsInfl P0 (fun z => α z + β z) := by
  obtain ⟨hα1, ⟨C1, hC1⟩, hα0⟩ := hα
  obtain ⟨hβ1, ⟨C2, hC2⟩, hβ0⟩ := hβ
  refine ⟨hα1.add hβ1, ⟨C1 + C2, fun z => (abs_add_le _ _).trans (add_le_add (hC1 z) (hC2 z))⟩, ?_⟩
  rw [integral_add (integrable_of_abs_le hα1 hC1) (integrable_of_abs_le hβ1 hC2), hα0, hβ0, add_zero]

lemma IsInfl.const_mul {α : Z → ℝ} (hα : IsInfl P0 α) (c : ℝ) : IsInfl P0 (fun z => c * α z) := by
  obtain ⟨hα1, ⟨C1, hC1⟩, hα0⟩ := hα
  have hb : ∀ z, |c * α z| ≤ |c| * C1 := fun z => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC1 z) (abs_nonneg c)
  refine ⟨hα1.const_mul c, ⟨|c| * C1, hb⟩, ?_⟩
  rw [integral_const_mul, hα0, mul_zero]

lemma linStat_add (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (α1 β1 α2 β2 : Z → ℝ) (n : ℕ) (ω : Ω) :
    linStat X Y m (fun z => α1 z + α2 z) (fun z => β1 z + β2 z) n ω =
      linStat X Y m α1 β1 n ω + linStat X Y m α2 β2 n ω := by
  unfold linStat
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

lemma linStat_const_mul (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (α β : Z → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) :
    linStat X Y m (fun z => c * α z) (fun z => c * β z) n ω = c * linStat X Y m α β n ω := by
  unfold linStat
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

variable {X Y : ℕ → Ω → Z} {m : ℕ → ℕ} {κ : ℝ}

/-- The linear statistic is `O_P(1)`. -/
lemma bip_linStat (hS : TwoSampleIID P P0 X Y m κ) {α β : Z → ℝ} (hα : IsInfl P0 α) (hβ : IsInfl P0 β) :
    BIP P (linStat X Y m α β) := by
  have hP0 : IsProbabilityMeasure P0 := by
    rw [← hS.hXl 0]; exact (Measure.isProbabilityMeasure_map_iff (hS.hXm 0).aemeasurable).2 inferInstance
  obtain ⟨hα1, ⟨C1, hC1⟩, hα0⟩ := hα
  obtain ⟨hβ1, ⟨C2, hC2⟩, hβ0⟩ := hβ
  set A : ℕ → Ω → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, α (X i ω)
  set B : ℕ → Ω → ℝ := fun n ω => √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), β (Y i ω)
  have hsqα : ∫ z, α z ^ 2 ∂P0 ≤ C1 ^ 2 := by
    have hle : ∀ z, α z ^ 2 ≤ C1 ^ 2 := fun z => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC1 z) 2
    calc ∫ z, α z ^ 2 ∂P0 ≤ ∫ _z, C1 ^ 2 ∂P0 :=
          integral_mono (integrable_of_abs_le (hα1.pow_const 2) (C := C1 ^ 2) fun z => by
            rw [abs_of_nonneg (sq_nonneg _)]; exact hle z) (integrable_const _) hle
      _ = C1 ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  have hsqβ : ∫ z, β z ^ 2 ∂P0 ≤ C2 ^ 2 := by
    have hle : ∀ z, β z ^ 2 ≤ C2 ^ 2 := fun z => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC2 z) 2
    calc ∫ z, β z ^ 2 ∂P0 ≤ ∫ _z, C2 ^ 2 ∂P0 :=
          integral_mono (integrable_of_abs_le (hβ1.pow_const 2) (C := C2 ^ 2) fun z => by
            rw [abs_of_nonneg (sq_nonneg _)]; exact hle z) (integrable_const _) hle
      _ = C2 ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  have hsumbd : ∀ (s : Finset ℕ) (U : ℕ → Ω → Z) (φ : Z → ℝ) (C : ℝ), (∀ i, Measurable (U i)) →
      Measurable φ → (∀ z, |φ z| ≤ C) → Integrable (fun ω => (∑ i ∈ s, φ (U i ω)) ^ 2) P := by
    intro s U φ C hU hφ hb
    refine integrable_of_abs_le ((Finset.measurable_sum _ fun i _ => hφ.comp (hU i)).pow_const 2)
      (C := (s.card * C) ^ 2) fun ω => ?_
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => hb _
  have hA : BIP P A := by
    refine bip_of_integral_sq (C := C1 ^ 2) (Eventually.of_forall fun n => ⟨?_, ?_⟩)
    · simp_rw [A, mul_pow]
      exact (hsumbd _ X α C1 hS.hXm hα1 hC1).const_mul _
    · simp_rw [A, mul_pow]
      rw [integral_const_mul, integral_sq_sum_comp hS.hXm hS.hXi hS.hXl hα1 hC1 hα0, Finset.card_range]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp; positivity
      · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
        rw [inv_pow, Real.sq_sqrt hn.le, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
        exact hsqα
  have hmr : ∀ᶠ n : ℕ in atTop, (n : ℝ) / m n ≤ 2 / κ ∧ 0 < m n := by
    have h1 : Tendsto (fun n : ℕ => ((m n : ℝ) / n)⁻¹) atTop (𝓝 κ⁻¹) := hS.hm.inv₀ hS.hκ.ne'
    filter_upwards [h1.eventually (ge_mem_nhds (show κ⁻¹ < 2 / κ by
      rw [inv_eq_one_div]; exact div_lt_div_of_pos_right (by norm_num) hS.hκ)),
      (tendsto_atTop_of_ratio hS.hκ hS.hm).eventually_gt_atTop 0, eventually_gt_atTop 0] with n hn hm0 hn0
    refine ⟨?_, hm0⟩
    rwa [inv_div] at hn
  have hB : BIP P B := by
    refine bip_of_integral_sq (C := 2 / κ * C2 ^ 2) ?_
    filter_upwards [hmr] with n ⟨hn1, hn2⟩
    refine ⟨?_, ?_⟩
    · simp_rw [B, mul_pow]
      exact (hsumbd _ Y β C2 hS.hYm hβ1 hC2).const_mul _
    · simp_rw [B, mul_pow]
      rw [integral_const_mul, integral_sq_sum_comp hS.hYm hS.hYi hS.hYl hβ1 hC2 hβ0, Finset.card_range]
      have hm : (0 : ℝ) < m n := by exact_mod_cast hn2
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      calc (n : ℝ) / (m n : ℝ) ^ 2 * ((m n : ℝ) * ∫ z, β z ^ 2 ∂P0) = (n : ℝ) / m n * ∫ z, β z ^ 2 ∂P0 := by
            field_simp
        _ ≤ 2 / κ * C2 ^ 2 := mul_le_mul hn1 hsqβ (integral_nonneg fun _ => sq_nonneg _) (by
            have := hS.hκ; positivity)
  exact hA.add hB

namespace IsAL

lemma tendsto (hS : TwoSampleIID P P0 X Y m κ) {Q : ℕ → Ω → ℝ} {q : ℝ} (h : IsAL P P0 X Y m Q q) :
    TIP0 P (fun n ω => Q n ω - q) := by
  obtain ⟨α, β, hα, hβ, hr⟩ := h
  have hb : BIP P (fun n ω => √(n : ℝ) * (Q n ω - q)) :=
    ((BIP.of_tip0 hr).add (bip_linStat hS hα hβ)).congr (Eventually.of_forall fun n ω => by ring)
  have hd : TIP0 P (fun n (_ : Ω) => (√(n : ℝ))⁻¹) :=
    tip0_det (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  refine (hd.mul_bip hb).congr (eventually_atTop.2 ⟨1, fun n hn ω => ?_⟩)
  have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp

lemma bip (hS : TwoSampleIID P P0 X Y m κ) {Q : ℕ → Ω → ℝ} {q : ℝ} (h : IsAL P P0 X Y m Q q) :
    BIP P (fun n ω => √(n : ℝ) * (Q n ω - q)) := by
  obtain ⟨α, β, hα, hβ, hr⟩ := h
  exact ((BIP.of_tip0 hr).add (bip_linStat hS hα hβ)).congr (Eventually.of_forall fun n ω => by ring)

lemma congr {Q Q' : ℕ → Ω → ℝ} {q : ℝ} (h : IsAL P P0 X Y m Q q) (he : ∀ᶠ n in atTop, ∀ ω, Q n ω = Q' n ω) :
    IsAL P P0 X Y m Q' q := by
  obtain ⟨α, β, hα, hβ, hr⟩ := h
  exact ⟨α, β, hα, hβ, hr.congr (he.mono fun n hn ω => by rw [hn ω])⟩

lemma congr_center {Q : ℕ → Ω → ℝ} {q q' : ℝ} (h : IsAL P P0 X Y m Q q) (he : q = q') : IsAL P P0 X Y m Q q' :=
  he ▸ h

lemma const (q : ℝ) : IsAL P P0 X Y m (fun _ _ => q) q :=
  ⟨fun _ => 0, fun _ => 0, IsInfl.zero, IsInfl.zero, tip0_zero.congr (Eventually.of_forall fun n ω => by
    simp [linStat])⟩

lemma add [IsFiniteMeasure P0] {Q R : ℕ → Ω → ℝ} {q r : ℝ} (hQ : IsAL P P0 X Y m Q q) (hR : IsAL P P0 X Y m R r) :
    IsAL P P0 X Y m (fun n ω => Q n ω + R n ω) (q + r) := by
  obtain ⟨α1, β1, hα1, hβ1, h1⟩ := hQ
  obtain ⟨α2, β2, hα2, hβ2, h2⟩ := hR
  refine ⟨fun z => α1 z + α2 z, fun z => β1 z + β2 z, hα1.add hα2, hβ1.add hβ2, (h1.add h2).congr
    (Eventually.of_forall fun n ω => ?_)⟩
  rw [linStat_add]; ring

lemma const_mul {Q : ℕ → Ω → ℝ} {q : ℝ} (hQ : IsAL P P0 X Y m Q q) (c : ℝ) :
    IsAL P P0 X Y m (fun n ω => c * Q n ω) (c * q) := by
  obtain ⟨α, β, hα, hβ, h⟩ := hQ
  refine ⟨fun z => c * α z, fun z => c * β z, hα.const_mul c, hβ.const_mul c, (h.const_mul c).congr
    (Eventually.of_forall fun n ω => ?_)⟩
  rw [linStat_const_mul]; ring

lemma neg {Q : ℕ → Ω → ℝ} {q : ℝ} (hQ : IsAL P P0 X Y m Q q) : IsAL P P0 X Y m (fun n ω => -Q n ω) (-q) :=
  ((hQ.const_mul (-1)).congr (Eventually.of_forall fun n ω => by ring)).congr_center (by ring)

lemma sub [IsFiniteMeasure P0] {Q R : ℕ → Ω → ℝ} {q r : ℝ} (hQ : IsAL P P0 X Y m Q q)
    (hR : IsAL P P0 X Y m R r) : IsAL P P0 X Y m (fun n ω => Q n ω - R n ω) (q - r) :=
  ((hQ.add hR.neg).congr (Eventually.of_forall fun n ω => by ring)).congr_center (by ring)

/-- Deterministic factors `a_n → a` with `√n (a_n − a) → 0`. -/
lemma seq_mul (hS : TwoSampleIID P P0 X Y m κ) {Q : ℕ → Ω → ℝ} {q : ℝ} (hQ : IsAL P P0 X Y m Q q) {a : ℕ → ℝ}
    {a0 : ℝ} (ha : Tendsto a atTop (𝓝 a0)) (hsa : Tendsto (fun n : ℕ => √(n : ℝ) * (a n - a0)) atTop (𝓝 0)) :
    IsAL P P0 X Y m (fun n ω => a n * Q n ω) (a0 * q) := by
  obtain ⟨α, β, hα, hβ, h⟩ := hQ
  refine ⟨fun z => a0 * α z, fun z => a0 * β z, hα.const_mul a0, hβ.const_mul a0, ?_⟩
  -- a_n (√n(Q−q) − L) + (a_n − a0) L + √n(a_n − a0) q
  have h1 : TIP0 P (fun n ω => a n * (√(n : ℝ) * (Q n ω - q) - linStat X Y m α β n ω)) :=
    h.bip_mul (bip_det ha)
  have h2 : TIP0 P (fun n ω => (a n - a0) * linStat X Y m α β n ω) :=
    (tip0_det (by simpa using ha.sub_const a0)).mul_bip (bip_linStat hS hα hβ)
  have h3 : TIP0 P (fun n (_ : Ω) => √(n : ℝ) * (a n - a0) * q) := tip0_det (by simpa using hsa.mul_const q)
  refine ((h1.add h2).add h3).congr (Eventually.of_forall fun n ω => ?_)
  rw [linStat_const_mul]; ring

lemma mul (hS : TwoSampleIID P P0 X Y m κ) [IsFiniteMeasure P0] {Q R : ℕ → Ω → ℝ} {q r : ℝ}
    (hQ : IsAL P P0 X Y m Q q) (hR : IsAL P P0 X Y m R r) :
    IsAL P P0 X Y m (fun n ω => Q n ω * R n ω) (q * r) := by
  have hQt := hQ.tendsto hS
  have hRb := hR.bip hS
  obtain ⟨α1, β1, hα1, hβ1, h1⟩ := hQ
  obtain ⟨α2, β2, hα2, hβ2, h2⟩ := hR
  refine ⟨fun z => r * α1 z + q * α2 z, fun z => r * β1 z + q * β2 z, (hα1.const_mul r).add (hα2.const_mul q),
    (hβ1.const_mul r).add (hβ2.const_mul q), ?_⟩
  have h3 : TIP0 P (fun n ω => (Q n ω - q) * (√(n : ℝ) * (R n ω - r))) := hQt.mul_bip hRb
  refine (((h1.const_mul r).add (h2.const_mul q)).add h3).congr (Eventually.of_forall fun n ω => ?_)
  rw [linStat_add, linStat_const_mul, linStat_const_mul]; ring

lemma pow (hS : TwoSampleIID P P0 X Y m κ) [IsFiniteMeasure P0] {Q : ℕ → Ω → ℝ} {q : ℝ}
    (hQ : IsAL P P0 X Y m Q q) (k : ℕ) : IsAL P P0 X Y m (fun n ω => Q n ω ^ k) (q ^ k) := by
  induction k with
  | zero => simpa using IsAL.const (P := P) (P0 := P0) (X := X) (Y := Y) (m := m) 1
  | succ k ih => exact ((ih.mul hS hQ).congr (Eventually.of_forall fun n ω => by ring)).congr_center (by ring)

/-- The delta method for `x ↦ x⁻¹` at `q ≠ 0`. -/
lemma inv (hS : TwoSampleIID P P0 X Y m κ) {Q : ℕ → Ω → ℝ} {q : ℝ} (hq : q ≠ 0) (hQ : IsAL P P0 X Y m Q q) :
    IsAL P P0 X Y m (fun n ω => (Q n ω)⁻¹) q⁻¹ := by
  have hQt := hQ.tendsto hS
  have hQb := hQ.bip hS
  obtain ⟨α, β, hα, hβ, h⟩ := hQ
  have hq2 : 0 < q ^ 2 := by positivity
  have hqa : 0 < |q| := abs_pos.2 hq
  refine ⟨fun z => -(q ^ 2)⁻¹ * α z, fun z => -(q ^ 2)⁻¹ * β z, hα.const_mul _, hβ.const_mul _, ?_⟩
  -- E_n = √n(Q⁻¹ − q⁻¹) + √n(Q − q)/q²
  set E : ℕ → Ω → ℝ := fun n ω => √(n : ℝ) * ((Q n ω)⁻¹ - q⁻¹) + √(n : ℝ) * (Q n ω - q) / q ^ 2 with hE
  have hW : TIP0 P (fun n ω => (2 / |q| ^ 3) * ((Q n ω - q) * (√(n : ℝ) * (Q n ω - q)))) :=
    (hQt.mul_bip hQb).const_mul _
  have hBad : Tendsto (fun n => P {ω | |q| / 2 ≤ |Q n ω - q|}) atTop (𝓝 0) := hQt (|q| / 2) (by positivity)
  have hEt : TIP0 P E := by
    refine TIP0.of_dominated hW hBad (Eventually.of_forall fun n ω hω => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hω
    have hQ0 : |q| / 2 < |Q n ω| := by
      have := abs_sub_abs_le_abs_sub q (Q n ω)
      rw [abs_sub_comm] at this
      linarith
    have hQne : Q n ω ≠ 0 := by intro h0; rw [h0, abs_zero] at hQ0; linarith
    have hid : E n ω = √(n : ℝ) * (Q n ω - q) * (Q n ω - q) / (q ^ 2 * Q n ω) := by
      simp only [hE]; field_simp; ring
    set a := |√(n : ℝ)| * |Q n ω - q| * |Q n ω - q| with ha
    have ha0 : 0 ≤ a := by positivity
    have hEa : |E n ω| = a / (|q| ^ 2 * |Q n ω|) := by
      rw [hid, abs_div, abs_mul, abs_mul, abs_mul, abs_pow]
    have hWa : |2 / |q| ^ 3 * ((Q n ω - q) * (√(n : ℝ) * (Q n ω - q)))| = 2 / |q| ^ 3 * a := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / |q| ^ 3), ha]; ring
    have hden : |q| ^ 2 * (|q| / 2) ≤ |q| ^ 2 * |Q n ω| := mul_le_mul_of_nonneg_left hQ0.le (by positivity)
    rw [hEa, hWa]
    calc a / (|q| ^ 2 * |Q n ω|) ≤ a / (|q| ^ 2 * (|q| / 2)) :=
          div_le_div_of_nonneg_left ha0 (by positivity) hden
      _ = 2 / |q| ^ 3 * a := by field_simp
  refine (hEt.add (h.const_mul (-(q ^ 2)⁻¹))).congr (Eventually.of_forall fun n ω => ?_)
  rw [linStat_const_mul]
  simp only [hE]
  ring

lemma div (hS : TwoSampleIID P P0 X Y m κ) [IsFiniteMeasure P0] {Q R : ℕ → Ω → ℝ} {q r : ℝ} (hr : r ≠ 0)
    (hQ : IsAL P P0 X Y m Q q) (hR : IsAL P P0 X Y m R r) :
    IsAL P P0 X Y m (fun n ω => Q n ω / R n ω) (q / r) :=
  ((hQ.mul hS (hR.inv hS hr)).congr (Eventually.of_forall fun n ω => by rw [div_eq_mul_inv])).congr_center
    (by rw [div_eq_mul_inv])

end IsAL

/-! ### Pool and validation averages -/

lemma isInfl_center [IsProbabilityMeasure P0] {f : Z → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ z, |f z| ≤ C) :
    IsInfl P0 (fun z => f z - ∫ z, f z ∂P0) := by
  refine ⟨hf.sub_const _, ⟨C + C, fun z => (abs_sub _ _).trans (add_le_add (hb z)
    (abs_integral_le_of_abs_le hb))⟩, ?_⟩
  rw [integral_sub (integrable_of_abs_le hf hb) (integrable_const _), integral_const, probReal_univ, one_smul,
    sub_self]

/-- Pool averages `n^{−1} Σ_{i<n} f(X_i)` are `IsAL` with centre `P₀ f`. -/
lemma isAL_poolAvg [IsProbabilityMeasure P0] {f : Z → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ z, |f z| ≤ C) :
    IsAL P P0 X Y m (fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (X i ω)) (∫ z, f z ∂P0) := by
  refine ⟨fun z => f z - ∫ z, f z ∂P0, fun _ => 0, isInfl_center hf hb, IsInfl.zero, tip0_zero.congr
    (Eventually.of_forall fun n ω => ?_)⟩
  unfold linStat
  simp only [Finset.sum_const_zero, mul_zero, add_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
    have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn.le
    have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 hn
    set t := √(n : ℝ)
    rw [← hs]
    field_simp
    ring

/-- Validation averages `m^{−1} Σ_{i<m} f(Y_i)` are `IsAL` with centre `P₀ f`. -/
lemma isAL_valAvg [IsProbabilityMeasure P0] (hS : TwoSampleIID P P0 X Y m κ) {f : Z → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ z, |f z| ≤ C) :
    IsAL P P0 X Y m (fun n ω => (m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n), f (Y i ω)) (∫ z, f z ∂P0) := by
  refine ⟨fun _ => 0, fun z => f z - ∫ z, f z ∂P0, IsInfl.zero, isInfl_center hf hb, tip0_zero.congr ?_⟩
  filter_upwards [(tendsto_atTop_of_ratio hS.hκ hS.hm).eventually_gt_atTop 0] with n hn ω
  unfold linStat
  simp only [Finset.sum_const_zero, mul_zero, zero_add]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm : (0 : ℝ) < m n := by exact_mod_cast hn
  field_simp
  ring

end StatFormal.Foundations.CLT
