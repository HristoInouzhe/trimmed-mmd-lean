import Mathlib.Probability.Moments.Variance
import StatFormal.Lib.CovPerturb.Folds

/-!
# The `O_P(n^{-1/2})` rate of the empirical covariance operator under a fourth moment (untrusted library)

* `ofReal_opNorm_sq_le_hs`: `‖A‖²_op ≤ Σ_{a,b} ⟪A e_a, e_b⟫²` (Hilbert–Schmidt sum in `ℝ≥0∞`, complete `(e_a)`).
* `cCov_emp_sub_eq`: `Γ̂ − Γ = (Σ_{emp(z − 𝔪)} − Γ) − ȳ ⊗ ȳ`, `ȳ = z̄ − 𝔪`.
* `lintegral_sq_mean_pi`: for `g ∈ L²(P)` with `E g = 0`, `E_{P^{⊗n}}[(n⁻¹Σ_i g(z_i))²] = E g²/n`.
* `prob_norm_cCov_emp_sub_le`: `P^{⊗n}{‖Γ̂ − Γ‖ > 2c/√n} ≤ E‖X − 𝔪‖⁴/c² + E‖X − 𝔪‖²/c` (Markov), hence `O_P(n^{-1/2})`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped RealInnerProductSpace ENNReal

namespace StatFormal.CovPerturb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- **Operator norm below the Hilbert–Schmidt sum.** -/
theorem ofReal_opNorm_sq_le_hs {e : ℕ → H} (he : Orthonormal ℝ e)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) (A : H →L[ℝ] H) :
    ENNReal.ofReal (‖A‖ ^ 2) ≤ ∑' b, ∑' a, ENNReal.ofReal (⟪A (e a), e b⟫ ^ 2) := by
  set S := ∑' b, ∑' a, ENNReal.ofReal (⟪A (e a), e b⟫ ^ 2) with hSdef
  -- step 1: one coordinate of `A u`
  have h1 : ∀ u b, ENNReal.ofReal (⟪A u, e b⟫ ^ 2) ≤
      ENNReal.ofReal (‖u‖ ^ 2) * ∑' a, ENNReal.ofReal (⟪A (e a), e b⟫ ^ 2) := by
    intro u b
    have hs : HasSum (fun a => ⟪e a, u⟫ * ⟪A (e a), e b⟫) ⟪A u, e b⟫ := by
      have := ((hasSum_repr_of he hsp u).mapL A).mapL (innerSL ℝ (e b))
      rw [innerSL_apply_apply, real_inner_comm] at this
      refine this.congr_fun fun a => ?_
      simp only [map_smul, innerSL_apply_apply, inner_smul_right, smul_eq_mul]
      rw [real_inner_comm (e b)]
    have hlim := (ENNReal.continuous_ofReal.tendsto _).comp (hs.tendsto_sum_nat.pow 2)
    refine le_of_tendsto' hlim fun N => ?_
    simp only [Function.comp_apply]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range N) (fun a => ⟪e a, u⟫) (fun a => ⟪A (e a), e b⟫)
    have hb := sum_sq_le he N u
    calc ENNReal.ofReal ((∑ a ∈ range N, ⟪e a, u⟫ * ⟪A (e a), e b⟫) ^ 2)
        ≤ ENNReal.ofReal (‖u‖ ^ 2 * ∑ a ∈ range N, ⟪A (e a), e b⟫ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal (hcs.trans ?_)
          exact mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = ENNReal.ofReal (‖u‖ ^ 2) * ∑ a ∈ range N, ENNReal.ofReal (⟪A (e a), e b⟫ ^ 2) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
      _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum _
  -- step 2: Parseval for `A u`
  have h2 : ∀ u, ENNReal.ofReal (‖A u‖ ^ 2) ≤ ENNReal.ofReal (‖u‖ ^ 2) * S := by
    intro u
    have hp := hasSum_sq_inner he hsp (A u)
    rw [← hp.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hp.summable, hSdef, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun b => ?_
    rw [real_inner_comm]; exact h1 u b
  rcases eq_or_ne S ⊤ with hS | hS
  · rw [hS]; exact le_top
  have h3 : ∀ u, ‖A u‖ ≤ √S.toReal * ‖u‖ := by
    intro u
    have := h2 u
    rw [← ENNReal.ofReal_toReal hS, ← ENNReal.ofReal_mul (sq_nonneg _)] at this
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    rw [← Real.sqrt_sq (norm_nonneg (A u)), ← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul ENNReal.toReal_nonneg]
    exact Real.sqrt_le_sqrt (by linarith)
  have h5 : ‖A‖ ≤ √S.toReal := A.opNorm_le_bound (Real.sqrt_nonneg _) h3
  rw [← ENNReal.ofReal_toReal hS]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖A‖ ^ 2 ≤ (√S.toReal) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
    _ = S.toReal := Real.sq_sqrt ENNReal.toReal_nonneg

/-- The rank-one operator `u ↦ ⟪y, u⟫ y`. -/
def rankOne (y : H) : H →L[ℝ] H := (innerSL ℝ y).smulRight y

lemma rankOne_apply (y u : H) : rankOne y u = ⟪y, u⟫ • y := rfl

lemma norm_rankOne_le (y : H) : ‖rankOne y‖ ≤ ‖y‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) fun u => ?_
  rw [rankOne_apply, norm_smul, Real.norm_eq_abs]
  calc |⟪y, u⟫| * ‖y‖ ≤ ‖y‖ * ‖u‖ * ‖y‖ := by gcongr; exact abs_real_inner_le_norm _ _
    _ = ‖y‖ ^ 2 * ‖u‖ := by ring

lemma alg_center {n : ℕ} (hn : n ≠ 0) (a b : Fin n → ℝ) (α β : ℝ) :
    (n : ℝ)⁻¹ * ∑ i, a i * b i - ((n : ℝ)⁻¹ * ∑ i, a i) * ((n : ℝ)⁻¹ * ∑ i, b i) =
      (n : ℝ)⁻¹ * ∑ i, (a i - α) * (b i - β) - ((n : ℝ)⁻¹ * ∑ i, a i - α) * ((n : ℝ)⁻¹ * ∑ i, b i - β) := by
  have h : ∑ i, (a i - α) * (b i - β) = ∑ i, a i * b i - β * ∑ i, a i - α * ∑ i, b i + n * (α * β) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    have : ∑ i : Fin n, a i * β = ∑ i, β * a i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]; ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [h]; field_simp; ring

/-- `Γ̂ − Γ = (Σ_{emp(z − 𝔪)} − Γ) − ȳ ⊗ ȳ`. -/
theorem cCov_emp_sub_eq {P : Measure H} [IsProbabilityMeasure P] (h2 : MemLp id 2 P) {n : ℕ} (hn : n ≠ 0)
    (z : Fin n → H) :
    cCov (empMeasure z) - cCov P =
      (covarianceOperator (empMeasure fun i => z i - ∫ x, x ∂P) - cCov P) -
        rankOne ((n : ℝ)⁻¹ • ∑ i, z i - ∫ x, x ∂P) := by
  haveI := empMeasure_isProb z hn
  ext u
  refine ext_inner_right ℝ fun v => ?_
  set m := ∫ x, x ∂P
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, cCov_inner (memLp_empMeasure z), covOp_emp_inner,
    mean_emp, rankOne_apply, inner_smul_left, inner_smul_right, inner_sum, conj_trivial]
  have key := alg_center hn (fun i => ⟪u, z i⟫) (fun i => ⟪v, z i⟫) ⟪u, m⟫ ⟪v, m⟫
  have e1 : ∀ i, ⟪u, z i - m⟫ = ⟪u, z i⟫ - ⟪u, m⟫ := fun i => inner_sub_right _ _ _
  have e2 : ∀ i, ⟪v, z i - m⟫ = ⟪v, z i⟫ - ⟪v, m⟫ := fun i => inner_sub_right _ _ _
  have e3 : ⟪(n : ℝ)⁻¹ • ∑ i, z i - m, u⟫ = (n : ℝ)⁻¹ * ∑ i, ⟪u, z i⟫ - ⟪u, m⟫ := by
    rw [inner_sub_left, inner_smul_left, sum_inner, real_inner_comm m u]
    simp only [conj_trivial]
    congr 2
    exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  have e4 : ⟪(n : ℝ)⁻¹ • ∑ i, z i - m, v⟫ = (n : ℝ)⁻¹ * ∑ i, ⟪v, z i⟫ - ⟪v, m⟫ := by
    rw [inner_sub_left, inner_smul_left, sum_inner, real_inner_comm m v]
    simp only [conj_trivial]
    congr 2
    exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  simp only [e1, e2] at key ⊢
  have s1 : ⟪∑ i, z i, u⟫ = ∑ i, ⟪u, z i⟫ := by
    rw [sum_inner]; exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  have s2 : ⟪∑ i, z i, v⟫ = ∑ i, ⟪v, z i⟫ := by
    rw [sum_inner]; exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  rw [s1, s2, real_inner_comm u m, real_inner_comm v m]
  linear_combination key

/-- `‖Γ̂ − Γ‖ ≤ ‖Σ_{emp(z − 𝔪)} − Γ‖ + ‖z̄ − 𝔪‖²`. -/
lemma norm_cCov_emp_sub_le_split {P : Measure H} [IsProbabilityMeasure P] (h2 : MemLp id 2 P) {n : ℕ} (hn : n ≠ 0)
    (z : Fin n → H) :
    ‖cCov (empMeasure z) - cCov P‖ ≤
      ‖covarianceOperator (empMeasure fun i => z i - ∫ x, x ∂P) - cCov P‖ + ‖(n : ℝ)⁻¹ • ∑ i, z i - ∫ x, x ∂P‖ ^ 2 := by
  rw [cCov_emp_sub_eq h2 hn z]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_rankOne_le _))

section Pi

variable {P : Measure H} [IsProbabilityMeasure P]

/-- `E_{P^{⊗n}}[(n⁻¹ Σ_i g(z_i))²] = E g²/n` for centred `g ∈ L²`. -/
theorem integral_sq_mean_pi {g : H → ℝ} (hg : MemLp g 2 P) (h0 : ∫ x, g x ∂P = 0) {n : ℕ} (hn : n ≠ 0) :
    ∫ z, ((n : ℝ)⁻¹ * ∑ i, g (z i)) ^ 2 ∂(Measure.pi fun _ : Fin n => P) = (∫ x, g x ^ 2 ∂P) / n := by
  set μ := Measure.pi fun _ : Fin n => P
  have hvar := variance_sum_pi (μ := fun _ : Fin n => P) (X := fun _ => g) (fun _ => hg)
  have hS : MemLp (∑ i : Fin n, fun ω : Fin n → H => g (ω i)) 2 μ :=
    memLp_finsetSum' _ fun i _ => hg.comp_measurePreserving (measurePreserving_eval _ i)
  have hmeanS : μ[∑ i : Fin n, fun ω : Fin n → H => g (ω i)] = 0 := by
    simp only [Finset.sum_apply]
    rw [integral_finset_sum (f := fun i (x : Fin n → H) => g (x i)) _ fun i _ => by
      simpa [Function.comp_def] using (hg.comp_measurePreserving (measurePreserving_eval _ i)).integrable one_le_two]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_comp_eval (μ := fun _ : Fin n => P) hg.aestronglyMeasurable]; exact h0
  rw [variance_eq_sub hS, hmeanS, variance_eq_sub hg, h0] at hvar
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hvar
  have hfun : (fun z : Fin n → H => ((n : ℝ)⁻¹ * ∑ i, g (z i)) ^ 2) =
      fun z => ((n : ℝ)⁻¹) ^ 2 * ((∑ i : Fin n, fun ω : Fin n → H => g (ω i)) ^ 2) z := by
    funext z; simp [Finset.sum_apply, mul_pow]
  rw [hfun, integral_const_mul, hvar]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  simp [Pi.pow_apply]

/-- The same as a lower integral. -/
theorem lintegral_sq_mean_pi {g : H → ℝ} (hg : MemLp g 2 P) (h0 : ∫ x, g x ∂P = 0) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ z, ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i, g (z i)) ^ 2) ∂(Measure.pi fun _ : Fin n => P) =
      ENNReal.ofReal ((∫ x, g x ^ 2 ∂P) / n) := by
  have hS : MemLp (fun z : Fin n → H => (n : ℝ)⁻¹ * ∑ i, g (z i)) 2 (Measure.pi fun _ : Fin n => P) := by
    have := memLp_finsetSum' (μ := Measure.pi fun _ : Fin n => P) (Finset.univ : Finset (Fin n))
      (f := fun i (ω : Fin n → H) => g (ω i)) fun i _ => hg.comp_measurePreserving (measurePreserving_eval _ i)
    have h2 := this.const_mul ((n : ℝ)⁻¹)
    have hfe : (fun z : Fin n → H => (n : ℝ)⁻¹ * ∑ i, g (z i)) =
        fun x => (n : ℝ)⁻¹ * (∑ i : Fin n, fun ω : Fin n → H => g (ω i)) x := by
      funext z; simp [Finset.sum_apply]
    rw [hfe]; exact h2
  rw [← integral_sq_mean_pi hg h0 hn, ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq hS.aestronglyMeasurable).1 hS) (Eventually.of_forall fun _ => sq_nonneg _)]

end Pi

section Rate

variable {P : Measure H} [IsProbabilityMeasure P] {e : ℕ → H}

lemma cCov_inner' (h2 : MemLp id 2 P) (u v : H) :
    ⟪cCov P u, v⟫ = ∫ x, ⟪u, x - ∫ y, y ∂P⟫ * ⟪v, x - ∫ y, y ∂P⟫ ∂P := by
  set m := ∫ y, y ∂P
  have hmeas : Measurable fun x : H => x - m := measurable_id.sub_const m
  have h2' : MemLp id 2 (P.map fun x => x - m) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hmeas.aemeasurable]
    exact h2.sub (memLp_const m)
  rw [cCov, covarianceOperator_inner h2', integral_map hmeas.aemeasurable (by fun_prop)]

/-- The Hilbert–Schmidt sum of `Σ_{emp(z − 𝔪)} − Γ`. -/
def hsF (P : Measure H) (e : ℕ → H) {n : ℕ} (z : Fin n → H) : ℝ≥0∞ :=
  ∑' b, ∑' a, ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i, (⟪e a, z i - ∫ x, x ∂P⟫ * ⟪e b, z i - ∫ x, x ∂P⟫ -
    ⟪cCov P (e a), e b⟫)) ^ 2)

lemma measurable_hsF (n : ℕ) : Measurable (fun z : Fin n → H => hsF P e z) := by
  unfold hsF
  refine Measurable.ennreal_tsum fun b => Measurable.ennreal_tsum fun a => ?_
  exact (Continuous.measurable (by fun_prop)).ennreal_ofReal

lemma ofReal_norm_sq_le_hsF (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (h2 : MemLp id 2 P) {n : ℕ} (hn : n ≠ 0) (z : Fin n → H) :
    ENNReal.ofReal (‖covarianceOperator (empMeasure fun i => z i - ∫ x, x ∂P) - cCov P‖ ^ 2) ≤ hsF P e z := by
  refine (ofReal_opNorm_sq_le_hs he hsp _).trans (le_of_eq ?_)
  unfold hsF
  congr 1; funext b; congr 1; funext a
  congr 2
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, covOp_emp_inner, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn),
    one_mul]

lemma parseval_ennreal (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (y : H) : ∑' a, ENNReal.ofReal (⟪e a, y⟫ ^ 2) = ENNReal.ofReal (‖y‖ ^ 2) := by
  have hp := hasSum_sq_inner he hsp y
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hp.summable, hp.tsum_eq]

lemma integral_sq_sub_mean_le {w : H → ℝ} (hw : MemLp w 2 P) :
    ∫ x, (w x - ∫ y, w y ∂P) ^ 2 ∂P ≤ ∫ x, w x ^ 2 ∂P := by
  have h1 := variance_eq_integral (μ := P) hw.aestronglyMeasurable.aemeasurable
  have h2 := variance_le_expectation_sq (μ := P) hw.aestronglyMeasurable
  rw [h1] at h2; simpa using h2

/-- `E_{P^{⊗n}} HS² ≤ E‖X − 𝔪‖⁴/n`. -/
theorem lintegral_hsF_le (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (h4 : MemLp (fun x : H => x - ∫ y, y ∂P) 4 P) (h2 : MemLp id 2 P) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ z, hsF P e z ∂(Measure.pi fun _ : Fin n => P) ≤
      (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖x - ∫ y, y ∂P‖ₑ ^ 4 ∂P := by
  set m := ∫ y, y ∂P
  -- the products `w_ab = ⟪e_a, X − 𝔪⟫⟪e_b, X − 𝔪⟫` are in `L²`
  have hw : ∀ a b, MemLp (fun x : H => ⟪e a, x - m⟫ * ⟪e b, x - m⟫) 2 P := by
    intro a b
    have hn2 : MemLp (fun x : H => ‖x - m‖ ^ 2) 2 P := by
      have := h4.norm_rpow_div 2
      have h42 : (4 : ℝ≥0∞) / 2 = 2 := by
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
        first
          | exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
          | exact ENNReal.mul_div_cancel_left (by norm_num) (by norm_num)
          | simp
      rw [h42] at this
      simpa using this
    refine hn2.of_le (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖x - m‖)]
    have i1 := abs_real_inner_le_norm (e a) (x - m)
    have i2 := abs_real_inner_le_norm (e b) (x - m)
    rw [he.1 a, one_mul] at i1; rw [he.1 b, one_mul] at i2
    rw [sq]; exact mul_le_mul i1 i2 (abs_nonneg _) (norm_nonneg _)
  have hc : ∀ a b, ⟪cCov P (e a), e b⟫ = ∫ x, ⟪e a, x - m⟫ * ⟪e b, x - m⟫ ∂P := fun a b => cCov_inner' h2 _ _
  -- each entry
  have hentry : ∀ a b, ∫⁻ z, ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i, (⟪e a, z i - m⟫ * ⟪e b, z i - m⟫ -
      ⟪cCov P (e a), e b⟫)) ^ 2) ∂(Measure.pi fun _ : Fin n => P) ≤
        (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) * ENNReal.ofReal (⟪e b, x - m⟫ ^ 2) ∂P := by
    intro a b
    have hg : MemLp (fun x : H => ⟪e a, x - m⟫ * ⟪e b, x - m⟫ - ⟪cCov P (e a), e b⟫) 2 P :=
      (hw a b).sub (memLp_const _)
    have hg0 : ∫ x, (⟪e a, x - m⟫ * ⟪e b, x - m⟫ - ⟪cCov P (e a), e b⟫) ∂P = 0 := by
      rw [integral_sub ((hw a b).integrable one_le_two) (integrable_const _), integral_const, hc a b]
      simp
    rw [lintegral_sq_mean_pi (g := fun x => ⟪e a, x - m⟫ * ⟪e b, x - m⟫ - ⟪cCov P (e a), e b⟫) hg hg0 hn]
    have hle := integral_sq_sub_mean_le (hw a b)
    rw [← hc a b] at hle
    have hint : Integrable (fun x : H => (⟪e a, x - m⟫ * ⟪e b, x - m⟫) ^ 2) P :=
      (memLp_two_iff_integrable_sq (hw a b).aestronglyMeasurable).1 (hw a b)
    calc ENNReal.ofReal ((∫ x, (⟪e a, x - m⟫ * ⟪e b, x - m⟫ - ⟪cCov P (e a), e b⟫) ^ 2 ∂P) / n)
        ≤ ENNReal.ofReal ((∫ x, (⟪e a, x - m⟫ * ⟪e b, x - m⟫) ^ 2 ∂P) / n) := by
          gcongr
      _ = (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ENNReal.ofReal ((⟪e a, x - m⟫ * ⟪e b, x - m⟫) ^ 2) ∂P := by
          rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
            ENNReal.ofReal_natCast, ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
      _ = _ := by
          congr 1; refine lintegral_congr fun x => ?_
          rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  -- sum over `a, b`
  have hmeas : ∀ a b, Measurable fun z : Fin n → H => ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i,
      (⟪e a, z i - m⟫ * ⟪e b, z i - m⟫ - ⟪cCov P (e a), e b⟫)) ^ 2) := fun a b =>
    (Continuous.measurable (by fun_prop)).ennreal_ofReal
  unfold hsF
  rw [lintegral_tsum fun b => (Measurable.ennreal_tsum fun a => hmeas a b).aemeasurable]
  calc ∑' b, ∫⁻ z, ∑' a, ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i,
        (⟪e a, z i - m⟫ * ⟪e b, z i - m⟫ - ⟪cCov P (e a), e b⟫)) ^ 2) ∂(Measure.pi fun _ : Fin n => P)
      = ∑' b, ∑' a, ∫⁻ z, ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i,
        (⟪e a, z i - m⟫ * ⟪e b, z i - m⟫ - ⟪cCov P (e a), e b⟫)) ^ 2) ∂(Measure.pi fun _ : Fin n => P) := by
        congr 1; funext b; exact lintegral_tsum fun a => (hmeas a b).aemeasurable
    _ ≤ ∑' b, ∑' a, (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) * ENNReal.ofReal (⟪e b, x - m⟫ ^ 2) ∂P :=
        ENNReal.tsum_le_tsum fun b => ENNReal.tsum_le_tsum fun a => hentry a b
    _ = (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖x - m‖ₑ ^ 4 ∂P := by
        simp_rw [ENNReal.tsum_mul_left]
        congr 1
        have hm2 : ∀ a, Measurable fun x : H => ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) := fun a =>
          (Continuous.measurable (by fun_prop)).ennreal_ofReal
        have h1 : ∀ b, ∑' a, ∫⁻ x, ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) * ENNReal.ofReal (⟪e b, x - m⟫ ^ 2) ∂P =
            ∫⁻ x, ∑' a, ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) * ENNReal.ofReal (⟪e b, x - m⟫ ^ 2) ∂P := fun b =>
          (lintegral_tsum fun a => ((hm2 a).mul (hm2 b)).aemeasurable).symm
        simp_rw [h1]
        have h3 : ∀ b, Measurable fun x : H =>
            ∑' a, ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) * ENNReal.ofReal (⟪e b, x - m⟫ ^ 2) := fun b =>
          Measurable.ennreal_tsum fun a => (hm2 a).mul (hm2 b)
        rw [← lintegral_tsum fun b => (h3 b).aemeasurable]
        refine lintegral_congr fun x => ?_
        simp_rw [ENNReal.tsum_mul_right, parseval_ennreal he hsp, ENNReal.tsum_mul_left, parseval_ennreal he hsp]
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1; ring

end Rate

section Rate2

variable {P : Measure H} [IsProbabilityMeasure P] {e : ℕ → H}

/-- `E_{P^{⊗n}} ‖z̄ − 𝔪‖² ≤ E‖X − 𝔪‖²/n`. -/
theorem lintegral_mean_sq_le (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (h2 : MemLp id 2 P) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ z, ENNReal.ofReal (‖(n : ℝ)⁻¹ • ∑ i, z i - ∫ x, x ∂P‖ ^ 2) ∂(Measure.pi fun _ : Fin n => P) ≤
      (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖x - ∫ y, y ∂P‖ₑ ^ 2 ∂P := by
  set m := ∫ y, y ∂P
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hcoord : ∀ (z : Fin n → H) a, ⟪e a, (n : ℝ)⁻¹ • ∑ i, z i - m⟫ = (n : ℝ)⁻¹ * ∑ i, ⟪e a, z i - m⟫ := by
    intro z a
    simp only [inner_sub_right, inner_smul_right, inner_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub]
    rw [← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  have hg : ∀ a, MemLp (fun x : H => ⟪e a, x - m⟫) 2 P := fun a => (h2.sub (memLp_const m)).const_inner (e a)
  have hi1 : Integrable id P := memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))
  have hg0 : ∀ a, ∫ x, ⟪e a, x - m⟫ ∂P = 0 := by
    intro a
    have hint : Integrable (fun x : H => x - m) P := hi1.sub (integrable_const m)
    have hi1' : Integrable (fun x : H => x) P := hi1
    rw [integral_inner hint (e a), integral_sub hi1' (integrable_const m), integral_const]
    simp [m]
  have hm2 : ∀ a, Measurable fun x : H => ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) := fun a =>
    (Continuous.measurable (by fun_prop)).ennreal_ofReal
  calc ∫⁻ z, ENNReal.ofReal (‖(n : ℝ)⁻¹ • ∑ i, z i - m‖ ^ 2) ∂(Measure.pi fun _ : Fin n => P)
      = ∫⁻ z, ∑' a, ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i, ⟪e a, z i - m⟫) ^ 2) ∂(Measure.pi fun _ : Fin n => P) := by
        refine lintegral_congr fun z => ?_
        rw [← parseval_ennreal he hsp]; simp_rw [hcoord]
    _ = ∑' a, ∫⁻ z, ENNReal.ofReal (((n : ℝ)⁻¹ * ∑ i, ⟪e a, z i - m⟫) ^ 2) ∂(Measure.pi fun _ : Fin n => P) :=
        lintegral_tsum fun a => (Continuous.measurable (by fun_prop)).ennreal_ofReal.aemeasurable
    _ = ∑' a, (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ENNReal.ofReal (⟪e a, x - m⟫ ^ 2) ∂P := by
        congr 1; funext a
        rw [lintegral_sq_mean_pi (g := fun x => ⟪e a, x - m⟫) (hg a) (hg0 a) hn, div_eq_inv_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast,
          ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq (hg a).aestronglyMeasurable).1 (hg a))
            (Eventually.of_forall fun _ => sq_nonneg _)]
    _ = (n : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖x - m‖ₑ ^ 2 ∂P := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum fun a => (hm2 a).aemeasurable]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [parseval_ennreal he hsp, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ _ := le_rfl

/-- **The rate bound.** -/
theorem cov_rate_bound (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (h2 : MemLp id 2 P) (h4 : MemLp (fun x : H => x - ∫ y, y ∂P) 4 P) {n : ℕ} (hn : n ≠ 0) {c : ℝ} (hc : 0 < c) :
    ∃ B : Set (Fin n → H), MeasurableSet B ∧
      {z : Fin n → H | 2 * c / √n < ‖cCov (empMeasure z) - cCov P‖} ⊆ B ∧
      (Measure.pi fun _ : Fin n => P) B ≤
        (∫⁻ x, ‖x - ∫ y, y ∂P‖ₑ ^ 4 ∂P) / ENNReal.ofReal (c ^ 2) +
          (∫⁻ x, ‖x - ∫ y, y ∂P‖ₑ ^ 2 ∂P) / ENNReal.ofReal c := by
  set m := ∫ y, y ∂P
  set μ := Measure.pi fun _ : Fin n => P
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  set ybar : (Fin n → H) → H := fun z => (n : ℝ)⁻¹ • ∑ i, z i - m
  set B1 := {z : Fin n → H | ENNReal.ofReal (c ^ 2 / n) ≤ hsF P e z}
  set B2 := {z : Fin n → H | ENNReal.ofReal (c / √n) ≤ ENNReal.ofReal (‖ybar z‖ ^ 2)}
  have hyb : Continuous ybar := by fun_prop
  have hB2m : MeasurableSet B2 :=
    measurableSet_le measurable_const (hyb.norm.pow 2).measurable.ennreal_ofReal
  have hB1m : MeasurableSet B1 := measurableSet_le measurable_const (measurable_hsF n)
  refine ⟨B1 ∪ B2, hB1m.union hB2m, fun z hz => ?_, ?_⟩
  · simp only [Set.mem_setOf_eq] at hz
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, B1, B2] at hnot
    obtain ⟨h1, h2'⟩ := hnot
    have hA := (ofReal_norm_sq_le_hsF he hsp h2 hn z).trans_lt h1
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hA
    have hA' : ‖covarianceOperator (empMeasure fun i => z i - m) - cCov P‖ < c / √n := by
      have : (c / √n) ^ 2 = c ^ 2 / n := by rw [div_pow, Real.sq_sqrt (by linarith)]
      rw [← this] at hA
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hA
    have hy := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h2'
    have hsplit := norm_cCov_emp_sub_le_split h2 hn z
    have : 2 * c / √n = c / √n + c / √n := by ring
    linarith
  · have hm1 := meas_ge_le_lintegral_div (μ := μ) (measurable_hsF (P := P) (e := e) n).aemeasurable
      (ε := ENNReal.ofReal (c ^ 2 / n)) (by simp; positivity) ENNReal.ofReal_ne_top
    have hm2 := meas_ge_le_lintegral_div (μ := μ) (hyb.norm.pow 2).measurable.ennreal_ofReal.aemeasurable
      (ε := ENNReal.ofReal (c / √n)) (by simp; positivity) ENNReal.ofReal_ne_top
    have hninv : (n : ℝ≥0∞)⁻¹ ≠ 0 := by simp
    have hninv' : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [hn]
    have eq1 : ENNReal.ofReal (c ^ 2 / n) = (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (c ^ 2) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
    have le2 : (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal c ≤ ENNReal.ofReal (c / √n) := by
      have hsq : √(n : ℝ) ≤ n := by
        calc √(n : ℝ) ≤ √((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = n := Real.sqrt_sq (by linarith)
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_left hc.le hsn hsq
    calc μ (B1 ∪ B2) ≤ μ B1 + μ B2 := measure_union_le _ _
      _ ≤ (∫⁻ z, hsF P e z ∂μ) / ENNReal.ofReal (c ^ 2 / n) +
          (∫⁻ z, ENNReal.ofReal (‖ybar z‖ ^ 2) ∂μ) / ENNReal.ofReal (c / √n) := add_le_add hm1 hm2
      _ ≤ ((n : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖x - m‖ₑ ^ 4 ∂P) / ((n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (c ^ 2)) +
          ((n : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖x - m‖ₑ ^ 2 ∂P) / ((n : ℝ≥0∞)⁻¹ * ENNReal.ofReal c) := by
          rw [eq1]
          gcongr
          · exact lintegral_hsF_le he hsp h4 h2 hn
          · exact lintegral_mean_sq_le he hsp h2 hn
      _ = _ := by
          rw [ENNReal.mul_div_mul_left _ _ hninv hninv', ENNReal.mul_div_mul_left _ _ hninv hninv']

end Rate2

end StatFormal.CovPerturb
