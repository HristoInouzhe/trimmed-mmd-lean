import Mathlib.Probability.Moments.CovarianceBilin
import StatFormal.Lib.CovPerturb.Weyl

/-!
# Centred covariance operators: empirical formulas and an operator-norm bound (untrusted library)

* `cCov P = covarianceOperator (P.map (· − m))`, `m = ∫ x dP`: the centred covariance operator, with
  `cCov_inner : ⟪cCov P u, v⟫ = ⟪Σ_P u, v⟫ − ⟪u, m⟫⟪v, m⟫` (`Σ_P` Mathlib's uncentred `covarianceOperator`).
* `empMeasure z = Σ_i n⁻¹ δ_{z_i}` and its integrals.
* `norm_cCov_sub_le`: for two laws with finite second moments and an orthonormal family `e`, for every `N`,
  `‖cCov ν' − cCov ν‖ ≤ Σ_{a,b<N} |S'(e_a,e_b) − S(e_a,e_b)| + 2T'_N + 2T_N + ‖m' − m‖(‖m'‖ + ‖m‖)`, with
  `T_N = ∫ ‖x − P_N x‖ ‖x‖ dν` (no Hilbert–Schmidt space needed).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped RealInnerProductSpace ENNReal

namespace StatFormal.CovPerturb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The centred covariance operator. -/
def cCov (P : Measure H) : H →L[ℝ] H := covarianceOperator (P.map fun x => x - ∫ y, y ∂P)

/-- The empirical law of a sample. -/
def empMeasure {n : ℕ} (z : Fin n → H) : Measure H := ∑ i, ((n : ℝ≥0∞)⁻¹) • Measure.dirac (z i)

lemma memLp_two_of_lintegral {P : Measure H} (h : ∫⁻ x, ‖x‖ₑ ^ 2 ∂P < ⊤) : MemLp id 2 P := by
  have hlt : eLpNorm id 2 P < ∞ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      aestronglyMeasurable_id]
    simpa [ENNReal.rpow_two] using h
  exact hlt

lemma integrable_inner_mul {P : Measure H} (h2 : MemLp id 2 P) (u v : H) :
    Integrable (fun x => ⟪u, x⟫ * ⟪v, x⟫) P :=
  (h2.const_inner u).integrable_mul (h2.const_inner v)

lemma integrable_id_of_memLp {P : Measure H} [IsFiniteMeasure P] (h2 : MemLp id 2 P) : Integrable id P :=
  memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))

lemma integrable_sq_norm {P : Measure H} (h2 : MemLp id 2 P) : Integrable (fun x => ‖x‖ ^ 2) P := by
  have := h2.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  simpa using this

lemma covOp_inner {P : Measure H} (h2 : MemLp id 2 P) (u v : H) :
    ⟪covarianceOperator P u, v⟫ = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂P := covarianceOperator_inner h2 u v

/-- `⟪Γ u, v⟫ = ⟪Σ u, v⟫ − ⟪u, m⟫⟪v, m⟫`. -/
lemma cCov_inner {P : Measure H} [IsProbabilityMeasure P] (h2 : MemLp id 2 P) (u v : H) :
    ⟪cCov P u, v⟫ = ⟪covarianceOperator P u, v⟫ - ⟪u, ∫ y, y ∂P⟫ * ⟪v, ∫ y, y ∂P⟫ := by
  set m := ∫ y, y ∂P with hm
  have hmeas : Measurable fun x : H => x - m := measurable_id.sub_const m
  have h2' : MemLp id 2 (P.map fun x => x - m) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hmeas.aemeasurable]
    exact h2.sub (memLp_const m)
  rw [cCov, covarianceOperator_inner h2', covarianceOperator_inner h2,
    integral_map hmeas.aemeasurable (by fun_prop)]
  have hi1 : Integrable id P := integrable_id_of_memLp h2
  have hu : Integrable (fun x => ⟪u, x⟫) P := hi1.const_inner u
  have hv : Integrable (fun x => ⟪v, x⟫) P := hi1.const_inner v
  have huv := integrable_inner_mul h2 u v
  have hexp : ∀ x, ⟪u, x - m⟫ * ⟪v, x - m⟫ =
      (⟪u, x⟫ * ⟪v, x⟫ - ⟪v, m⟫ * ⟪u, x⟫) - (⟪u, m⟫ * ⟪v, x⟫ - ⟪u, m⟫ * ⟪v, m⟫) := by
    intro x; rw [inner_sub_right, inner_sub_right]; ring
  simp_rw [hexp]
  have e1 := integral_sub (μ := P) (f := fun x => ⟪u, x⟫ * ⟪v, x⟫ - ⟪v, m⟫ * ⟪u, x⟫)
    (g := fun x => ⟪u, m⟫ * ⟪v, x⟫ - ⟪u, m⟫ * ⟪v, m⟫) (huv.sub (hu.const_mul _))
    ((hv.const_mul _).sub (integrable_const _))
  have e2 := integral_sub (μ := P) (f := fun x => ⟪u, x⟫ * ⟪v, x⟫) (g := fun x => ⟪v, m⟫ * ⟪u, x⟫) huv
    (hu.const_mul _)
  have e3 := integral_sub (μ := P) (f := fun x => ⟪u, m⟫ * ⟪v, x⟫) (g := fun _ => ⟪u, m⟫ * ⟪v, m⟫)
    (hv.const_mul _) (integrable_const _)
  rw [e1, e2, e3, integral_const_mul, integral_const_mul, integral_const]
  have i1 : ∫ x, ⟪u, x⟫ ∂P = ⟪u, m⟫ := integral_inner hi1 u
  have i2 : ∫ x, ⟪v, x⟫ ∂P = ⟪v, m⟫ := integral_inner hi1 v
  rw [i1, i2]
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
  ring

/-! ### Empirical laws -/

section Emp

variable {n : ℕ}

lemma empMeasure_isProb (z : Fin n → H) (hn : n ≠ 0) : IsProbabilityMeasure (empMeasure z) := by
  constructor
  simp only [empMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)

lemma lintegral_empMeasure (z : Fin n → H) (f : H → ℝ≥0∞) :
    ∫⁻ x, f x ∂(empMeasure z) = ∑ i, (n : ℝ≥0∞)⁻¹ * f (z i) := by
  simp [empMeasure, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

lemma integrable_empMeasure (z : Fin n → H) {E : Type*} [NormedAddCommGroup E] (f : H → E) :
    Integrable f (empMeasure z) := by
  refine (integrable_finsetSum_measure).2 fun i _ => ?_
  refine Integrable.smul_measure (integrable_dirac enorm_lt_top) ?_
  exact ENNReal.inv_ne_top.2 (by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact (Fin.elim0 (h ▸ i))
    · exact_mod_cast h.ne')

lemma integral_empMeasure (z : Fin n → H) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : H → E) :
    ∫ x, f x ∂(empMeasure z) = (n : ℝ)⁻¹ • ∑ i, f (z i) := by
  rw [empMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp
  · intro i _
    refine Integrable.smul_measure (integrable_dirac enorm_lt_top) ?_
    exact ENNReal.inv_ne_top.2 (by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact (Fin.elim0 (h ▸ i))
      · exact_mod_cast h.ne')

lemma memLp_empMeasure (z : Fin n → H) : MemLp id 2 (empMeasure z) := by
  refine memLp_two_of_lintegral ?_
  rw [lintegral_empMeasure]
  refine ENNReal.sum_lt_top.2 fun i _ => ENNReal.mul_lt_top ?_ ?_
  · rcases Nat.eq_zero_or_pos n with h | h
    · exact (Fin.elim0 (h ▸ i))
    · exact ENNReal.inv_lt_top.2 (by exact_mod_cast h)
  · exact ENNReal.pow_lt_top enorm_lt_top

lemma covOp_emp_inner (z : Fin n → H) (u v : H) :
    ⟪covarianceOperator (empMeasure z) u, v⟫ = (n : ℝ)⁻¹ * ∑ i, ⟪u, z i⟫ * ⟪v, z i⟫ := by
  rw [covOp_inner (memLp_empMeasure z), integral_empMeasure, smul_eq_mul]

lemma mean_emp (z : Fin n → H) : ∫ y, y ∂(empMeasure z) = (n : ℝ)⁻¹ • ∑ i, z i := by
  rw [integral_empMeasure]

end Emp

/-! ### Truncations -/

/-- `P_N x = Σ_{a<N} ⟪e_a, x⟫ e_a`. -/
def projN (e : ℕ → H) (N : ℕ) (x : H) : H := ∑ a ∈ range N, ⟪e a, x⟫ • e a

/-- The tail integrand `‖x − P_N x‖ ‖x‖`. -/
def tailF (e : ℕ → H) (N : ℕ) (x : H) : ℝ := ‖x - projN e N x‖ * ‖x‖

variable {e : ℕ → H}

lemma inner_projN_self (he : Orthonormal ℝ e) (N : ℕ) (x : H) :
    ⟪x, projN e N x⟫ = ∑ a ∈ range N, ⟪e a, x⟫ ^ 2 := by
  simp only [projN, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [real_inner_comm, sq]

lemma norm_projN_sq (he : Orthonormal ℝ e) (N : ℕ) (x : H) :
    ‖projN e N x‖ ^ 2 = ∑ a ∈ range N, ⟪e a, x⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, projN, he.inner_sum]
  simp [sq]

lemma sum_sq_le (he : Orthonormal ℝ e) (N : ℕ) (x : H) : ∑ a ∈ range N, ⟪e a, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have := he.sum_inner_products_le (x := x) (s := range N)
  simpa [Real.norm_eq_abs, sq_abs] using this

lemma norm_projN_le (he : Orthonormal ℝ e) (N : ℕ) (x : H) : ‖projN e N x‖ ≤ ‖x‖ := by
  have h := (norm_projN_sq he N x).trans_le (sum_sq_le he N x)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma norm_sub_projN_le (he : Orthonormal ℝ e) (N : ℕ) (x : H) : ‖x - projN e N x‖ ≤ ‖x‖ := by
  have h1 : ‖x - projN e N x‖ ^ 2 = ‖x‖ ^ 2 - ∑ a ∈ range N, ⟪e a, x⟫ ^ 2 := by
    rw [@norm_sub_sq_real, inner_projN_self he, norm_projN_sq he]; ring
  have h2 : ‖x - projN e N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h1]; linarith [Finset.sum_nonneg fun a (_ : a ∈ range N) => sq_nonneg ⟪e a, x⟫]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

lemma inner_sub_projN_comm (N : ℕ) (x y : H) :
    ⟪x - projN e N x, y⟫ = ⟪x, y - projN e N y⟫ := by
  simp only [projN, inner_sub_left, inner_sub_right, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, conj_trivial]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [real_inner_comm x (e a)]; ring

lemma continuous_projN (N : ℕ) : Continuous (projN e N) := by
  unfold projN; fun_prop

lemma continuous_tailF (N : ℕ) : Continuous (tailF e N) := by
  unfold tailF; have := continuous_projN (e := e) N; fun_prop

lemma tailF_nonneg (N : ℕ) (x : H) : 0 ≤ tailF e N x := mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma tailF_le (he : Orthonormal ℝ e) (N : ℕ) (x : H) : tailF e N x ≤ ‖x‖ ^ 2 := by
  unfold tailF; rw [sq]; exact mul_le_mul_of_nonneg_right (norm_sub_projN_le he N x) (norm_nonneg _)

lemma integrable_tailF (he : Orthonormal ℝ e) {P : Measure H} (h2 : MemLp id 2 P) (N : ℕ) :
    Integrable (tailF e N) P := by
  refine (integrable_sq_norm h2).mono' (continuous_tailF N).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailF_nonneg N x)]; exact tailF_le he N x

/-- `|⟪Σ(u − P_N u), v⟫| ≤ ‖u‖ ‖v‖ T_N`. -/
lemma abs_covOp_tail_left (he : Orthonormal ℝ e) {P : Measure H} (h2 : MemLp id 2 P) (N : ℕ) (u v : H) :
    |⟪covarianceOperator P (u - projN e N u), v⟫| ≤ ‖u‖ * ‖v‖ * ∫ x, tailF e N x ∂P := by
  rw [covOp_inner h2, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrable_tailF he h2 N).const_mul _) (Eventually.of_forall fun x => ?_)
  rw [inner_sub_projN_comm, Real.norm_eq_abs, abs_mul, tailF]
  have h1 := abs_real_inner_le_norm u (x - projN e N x)
  have h3 := abs_real_inner_le_norm v x
  calc |⟪u, x - projN e N x⟫| * |⟪v, x⟫| ≤ (‖u‖ * ‖x - projN e N x‖) * (‖v‖ * ‖x‖) :=
        mul_le_mul h1 h3 (abs_nonneg _) (by positivity)
    _ = ‖u‖ * ‖v‖ * (‖x - projN e N x‖ * ‖x‖) := by ring

/-- `|⟪Σ(P_N u), v − P_N v⟫| ≤ ‖u‖ ‖v‖ T_N`. -/
lemma abs_covOp_tail_right (he : Orthonormal ℝ e) {P : Measure H} (h2 : MemLp id 2 P) (N : ℕ) (u v : H) :
    |⟪covarianceOperator P (projN e N u), v - projN e N v⟫| ≤ ‖u‖ * ‖v‖ * ∫ x, tailF e N x ∂P := by
  rw [covOp_inner h2, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrable_tailF he h2 N).const_mul _) (Eventually.of_forall fun x => ?_)
  rw [inner_sub_projN_comm (e := e) N v x, Real.norm_eq_abs, abs_mul, tailF]
  have h1 := abs_real_inner_le_norm (projN e N u) x
  have h3 := abs_real_inner_le_norm v (x - projN e N x)
  have hP := norm_projN_le he N u
  calc |⟪projN e N u, x⟫| * |⟪v, x - projN e N x⟫| ≤ (‖u‖ * ‖x‖) * (‖v‖ * ‖x - projN e N x‖) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))) h3 (abs_nonneg _) (by positivity)
    _ = ‖u‖ * ‖v‖ * (‖x - projN e N x‖ * ‖x‖) := by ring

/-- The finite block: `|⟪U(P_N u), P_N v⟫| ≤ ‖u‖‖v‖ Σ_{a,b<N} |⟪U e_a, e_b⟫|`. -/
lemma abs_block_le (he : Orthonormal ℝ e) (U : H →L[ℝ] H) (N : ℕ) (u v : H) :
    |⟪U (projN e N u), projN e N v⟫| ≤ ‖u‖ * ‖v‖ * ∑ a ∈ range N, ∑ b ∈ range N, |⟪U (e a), e b⟫| := by
  have hexp : ⟪U (projN e N u), projN e N v⟫ =
      ∑ a ∈ range N, ∑ b ∈ range N, ⟪e a, u⟫ * ⟪e b, v⟫ * ⟪U (e a), e b⟫ := by
    simp only [projN, map_sum, map_smul, sum_inner, inner_smul_left, conj_trivial]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [inner_sum, inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hexp, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have h1 : |⟪e a, u⟫| ≤ ‖u‖ := by
    have := abs_real_inner_le_norm (e a) u; rwa [he.1 a, one_mul] at this
  have h2 : |⟪e b, v⟫| ≤ ‖v‖ := by
    have := abs_real_inner_le_norm (e b) v; rwa [he.1 b, one_mul] at this
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)

/-- An operator bound from a bilinear bound. -/
lemma opNorm_le_of_inner {D : H →L[ℝ] H} {c : ℝ} (hc : 0 ≤ c) (h : ∀ u v, |⟪D u, v⟫| ≤ c * ‖u‖ * ‖v‖) :
    ‖D‖ ≤ c := by
  refine D.opNorm_le_bound hc fun u => ?_
  have h1 := h u (D u)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h1
  rcases (norm_nonneg (D u)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- **The operator-norm bound.** -/
theorem norm_cCov_sub_le (he : Orthonormal ℝ e) {ν ν' : Measure H} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (h2 : MemLp id 2 ν) (h2' : MemLp id 2 ν') (N : ℕ) :
    ‖cCov ν' - cCov ν‖ ≤
      (∑ a ∈ range N, ∑ b ∈ range N, |⟪covarianceOperator ν' (e a), e b⟫ - ⟪covarianceOperator ν (e a), e b⟫|)
      + 2 * ∫ x, tailF e N x ∂ν' + 2 * ∫ x, tailF e N x ∂ν
      + ‖∫ y, y ∂ν' - ∫ y, y ∂ν‖ * (‖∫ y, y ∂ν'‖ + ‖∫ y, y ∂ν‖) := by
  set m := ∫ y, y ∂ν
  set m' := ∫ y, y ∂ν'
  set U := covarianceOperator ν' - covarianceOperator ν
  set F := ∑ a ∈ range N, ∑ b ∈ range N, |⟪covarianceOperator ν' (e a), e b⟫ - ⟪covarianceOperator ν (e a), e b⟫|
  set T' := ∫ x, tailF e N x ∂ν'
  set T := ∫ x, tailF e N x ∂ν
  have hT' : 0 ≤ T' := integral_nonneg (tailF_nonneg N)
  have hT : 0 ≤ T := integral_nonneg (tailF_nonneg N)
  have hF : F = ∑ a ∈ range N, ∑ b ∈ range N, |⟪U (e a), e b⟫| := by
    simp only [F, U, sub_apply, inner_sub_left]
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  refine opNorm_le_of_inner (by positivity) fun u v => ?_
  set Pu := projN e N u
  set Pv := projN e N v
  have hsplit : ⟪(cCov ν' - cCov ν) u, v⟫ =
      (⟪U Pu, Pv⟫ + ⟪U Pu, v - Pv⟫ + (⟪covarianceOperator ν' (u - Pu), v⟫ - ⟪covarianceOperator ν (u - Pu), v⟫))
      - (⟪u, m' - m⟫ * ⟪v, m'⟫ + ⟪u, m⟫ * ⟪v, m' - m⟫) := by
    rw [sub_apply, inner_sub_left, cCov_inner h2', cCov_inner h2]
    have hU : ⟪U u, v⟫ = ⟪U Pu, Pv⟫ + ⟪U Pu, v - Pv⟫ + ⟪U (u - Pu), v⟫ := by
      rw [map_sub, inner_sub_left, inner_sub_right]; ring
    have hU' : ⟪U u, v⟫ = ⟪covarianceOperator ν' u, v⟫ - ⟪covarianceOperator ν u, v⟫ := by
      simp only [U, sub_apply, inner_sub_left]
    have hU'' : ⟪U (u - Pu), v⟫ = ⟪covarianceOperator ν' (u - Pu), v⟫ - ⟪covarianceOperator ν (u - Pu), v⟫ := by
      simp only [U, sub_apply, inner_sub_left]
    have key : ⟪covarianceOperator ν' u, v⟫ - ⟪covarianceOperator ν u, v⟫ = ⟪U Pu, Pv⟫ + ⟪U Pu, v - Pv⟫ +
        (⟪covarianceOperator ν' (u - Pu), v⟫ - ⟪covarianceOperator ν (u - Pu), v⟫) := by
      rw [← hU', hU, hU'']
    rw [inner_sub_right u m' m, inner_sub_right v m' m]
    linear_combination key
  have hb1 := abs_block_le he U N u v
  rw [← hF] at hb1
  have hb2 : |⟪U Pu, v - Pv⟫| ≤ ‖u‖ * ‖v‖ * (T' + T) := by
    have e1 := abs_covOp_tail_right he h2' N u v
    have e2 := abs_covOp_tail_right he h2 N u v
    simp only [U, sub_apply, inner_sub_left]
    calc _ ≤ |⟪covarianceOperator ν' Pu, v - Pv⟫| + |⟪covarianceOperator ν Pu, v - Pv⟫| := abs_sub _ _
      _ ≤ _ := by nlinarith
  have hb3 : |⟪covarianceOperator ν' (u - Pu), v⟫ - ⟪covarianceOperator ν (u - Pu), v⟫| ≤ ‖u‖ * ‖v‖ * (T' + T) := by
    have e1 := abs_covOp_tail_left he h2' N u v
    have e2 := abs_covOp_tail_left he h2 N u v
    calc _ ≤ |⟪covarianceOperator ν' (u - Pu), v⟫| + |⟪covarianceOperator ν (u - Pu), v⟫| := abs_sub _ _
      _ ≤ _ := by nlinarith
  have hb4 : |⟪u, m' - m⟫ * ⟪v, m'⟫ + ⟪u, m⟫ * ⟪v, m' - m⟫| ≤ ‖u‖ * ‖v‖ * (‖m' - m‖ * (‖m'‖ + ‖m‖)) := by
    have i1 := abs_real_inner_le_norm u (m' - m)
    have i2 := abs_real_inner_le_norm v m'
    have i3 := abs_real_inner_le_norm u m
    have i4 := abs_real_inner_le_norm v (m' - m)
    calc _ ≤ |⟪u, m' - m⟫ * ⟪v, m'⟫| + |⟪u, m⟫ * ⟪v, m' - m⟫| := abs_add_le _ _
      _ = |⟪u, m' - m⟫| * |⟪v, m'⟫| + |⟪u, m⟫| * |⟪v, m' - m⟫| := by rw [abs_mul, abs_mul]
      _ ≤ (‖u‖ * ‖m' - m‖) * (‖v‖ * ‖m'‖) + (‖u‖ * ‖m‖) * (‖v‖ * ‖m' - m‖) := by
          gcongr
      _ = _ := by ring
  rw [hsplit]
  have hnn : 0 ≤ ‖u‖ * ‖v‖ := by positivity
  calc _ ≤ |⟪U Pu, Pv⟫ + ⟪U Pu, v - Pv⟫ + (⟪covarianceOperator ν' (u - Pu), v⟫ - ⟪covarianceOperator ν (u - Pu), v⟫)|
        + |⟪u, m' - m⟫ * ⟪v, m'⟫ + ⟪u, m⟫ * ⟪v, m' - m⟫| := abs_sub _ _
    _ ≤ (|⟪U Pu, Pv⟫| + |⟪U Pu, v - Pv⟫| + |⟪covarianceOperator ν' (u - Pu), v⟫ - ⟪covarianceOperator ν (u - Pu), v⟫|)
        + |⟪u, m' - m⟫ * ⟪v, m'⟫ + ⟪u, m⟫ * ⟪v, m' - m⟫| := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (‖u‖ * ‖v‖ * F + ‖u‖ * ‖v‖ * (T' + T) + ‖u‖ * ‖v‖ * (T' + T)) + ‖u‖ * ‖v‖ * (‖m' - m‖ * (‖m'‖ + ‖m‖)) := by
        gcongr
    _ = _ := by ring

end StatFormal.CovPerturb
