import StatFormal.Lib.CovPerturb.Rate
import StatFormal.Lib.MatrixSqrtPerturb.BigOPCalc
import StatFormal.Lib.MatrixSqrtPerturb.Basic
import StatFormal.Archive.Wave24d.Statements

/-!
# Sample mean and sample covariance at rate `n^{-1/2}` under a fourth moment (untrusted library)

For an i.i.d. sequence `X_j` with law `μ` on `ℝ^d`:
* `prob_avg_gt_le`, `bigOP_avg`: for a centred `g ∈ L²(μ)`, `P(|n⁻¹ Σ_{j<n} g(X_j)| > c/√n) ≤ E g²/c²`
  (Chebyshev through the product law of the first `n` terms), hence `n⁻¹ Σ_{j<n} g(X_j) = O_P(n^{-1/2})`.
* `bigOP_smean`: `‖m̂_n − Eμ‖ = O_P(n^{-1/2})` (`E‖X‖⁴ < ∞` is assumed, `E‖X‖² < ∞` would do).
* `bigOP_scov`: `‖Σ̂_n − Cov(μ)‖_op = O_P(n^{-1/2})` for the `1/n` sample covariance (entrywise; the operator norm
  is at most the sum of the absolute entries), under `E‖X‖⁴ < ∞`.
The estimators `smean`, `scov` are written exactly as the draft's `sMean`, `sCov`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace StatFormal.MatrixSqrtPerturb

open StatFormal.Wave9b (BigOP)
open StatFormal.Wave24d (meanVec covMat)

/-! ### Averages of a centred square-integrable function -/

section Avg
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure H} [IsProbabilityMeasure μ] {X : ℕ → Ω → H}

/-- **Chebyshev for the sample average.** -/
theorem prob_avg_gt_le (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P) (hlaw : ∀ j, P.map (X j) = μ)
    {g : H → ℝ} (hgm : Measurable g) (hg : MemLp g 2 μ) (h0 : ∫ x, g x ∂μ = 0) {n : ℕ} (hn : n ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    P {ω | c / Real.sqrt n < |(n : ℝ)⁻¹ * ∑ j : Fin n, g (X j ω)|} ≤
      ENNReal.ofReal ((∫ x, g x ^ 2 ∂μ) / c ^ 2) := by
  set F : (Fin n → H) → ℝ := fun z => (n : ℝ)⁻¹ * ∑ i, g (z i) with hF
  have hFm : Measurable F :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hgm.comp (measurable_pi_apply i))
  have hπ : Measurable fun ω (i : Fin n) => X i ω := measurable_pi_iff.mpr fun i => hX i
  set B := {z : Fin n → H | c / Real.sqrt n < |F z|} with hBdef
  have hB : MeasurableSet B := measurableSet_lt measurable_const (continuous_abs.measurable.comp hFm)
  have hpre : {ω | c / Real.sqrt n < |(n : ℝ)⁻¹ * ∑ j : Fin n, g (X j ω)|} =
      (fun ω (i : Fin n) => X i ω) ⁻¹' B := rfl
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hε : 0 < c ^ 2 / n := by positivity
  rw [hpre, ← Measure.map_apply hπ hB, CovPerturb.map_prefix_eq_pi hX hind hlaw n]
  calc (Measure.pi fun _ : Fin n => μ) B
      ≤ (Measure.pi fun _ : Fin n => μ) {z | ENNReal.ofReal (c ^ 2 / n) ≤ ENNReal.ofReal (F z ^ 2)} := by
        refine measure_mono fun z hz => ?_
        simp only [Set.mem_setOf_eq, hBdef] at hz ⊢
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : (c / Real.sqrt n) ^ 2 ≤ |F z| ^ 2 := pow_le_pow_left₀ (by positivity) hz.le 2
        rwa [div_pow, Real.sq_sqrt hn'.le, sq_abs] at h2
    _ ≤ (∫⁻ z, ENNReal.ofReal (F z ^ 2) ∂(Measure.pi fun _ : Fin n => μ)) / ENNReal.ofReal (c ^ 2 / n) :=
        meas_ge_le_lintegral_div (hFm.pow_const 2).ennreal_ofReal.aemeasurable
          (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((∫ x, g x ^ 2 ∂μ) / n) / ENNReal.ofReal (c ^ 2 / n) := by
        rw [hF, CovPerturb.lintegral_sq_mean_pi hg h0 hn]
    _ = ENNReal.ofReal ((∫ x, g x ^ 2 ∂μ) / c ^ 2) := by
        rw [← ENNReal.ofReal_div_of_pos hε]; congr 1; field_simp

/-- **The sample average of a centred `L²` function is `O_P(n^{-1/2})`.** -/
theorem bigOP_avg (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P) (hlaw : ∀ j, P.map (X j) = μ)
    {g : H → ℝ} (hgm : Measurable g) (hg : MemLp g 2 μ) (h0 : ∫ x, g x ∂μ = 0) :
    BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n, g (X j ω)|) := by
  intro η hη
  set V := ∫ x, g x ^ 2 ∂μ
  have hV : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  set c := Real.sqrt (V / η) + 1
  have hc : 0 < c := by positivity
  have hcV : V / c ^ 2 ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Real.sqrt (V / η) < c := by linarith
    have h2 : V / η < c ^ 2 := by
      calc V / η = Real.sqrt (V / η) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ < c ^ 2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) two_ne_zero
    rw [div_lt_iff₀ hη] at h2; linarith
  refine ⟨c, 1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hmeas : Measurable fun ω => (n : ℝ)⁻¹ * ∑ j : Fin n, g (X j ω) :=
    measurable_const.mul (Finset.measurable_sum _ fun j _ => hgm.comp (hX j))
  have hAm : MeasurableSet {ω | |(n : ℝ)⁻¹ * ∑ j : Fin n, g (X j ω)| ≤ c * (1 / Real.sqrt n)} :=
    measurableSet_le (continuous_abs.measurable.comp hmeas) measurable_const
  refine ⟨_, hAm, ?_, fun ω hω => ENNReal.ofReal_le_ofReal hω⟩
  refine prob_ge_of_compl_le hAm hη.le ?_
  have hcompl : {ω | |(n : ℝ)⁻¹ * ∑ j : Fin n, g (X j ω)| ≤ c * (1 / Real.sqrt n)}ᶜ =
      {ω | c / Real.sqrt n < |(n : ℝ)⁻¹ * ∑ j : Fin n, g (X j ω)|} := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, mul_one_div]
  rw [hcompl]
  exact (prob_avg_gt_le hX hind hlaw hgm hg h0 hn0 hc).trans (ENNReal.ofReal_le_ofReal hcV)

end Avg

/-! ### Euclidean estimators -/

section Euclid
variable {d : ℕ}

/-- The sample mean `m̂ = n⁻¹ Σ_j X_j` (as the draft's `sMean`). -/
def smean {n : ℕ} (X : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := (n : ℝ)⁻¹ • ∑ j, X j

/-- The `1/n` sample covariance (as the draft's `sCov`). -/
def scov {n : ℕ} (X : Fin n → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i k => (n : ℝ)⁻¹ * ∑ j, (X j i - smean X i) * (X j k - smean X k)

lemma smean_apply {n : ℕ} (X : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    smean X i = (n : ℝ)⁻¹ * ∑ j, X j i := by
  simp [smean]

lemma scov_isHermitian {n : ℕ} (X : Fin n → EuclideanSpace ℝ (Fin d)) : (scov X).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply, star_trivial, scov]
  congr 1; exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma coord_abs_le (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

lemma norm_le_sum_abs (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ ≤ ∑ i, |v i| := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ i, ‖v i‖ ^ 2 ≤ (∑ i, |v i|) ^ 2 := by
    simp only [Real.norm_eq_abs]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt ((∑ i, |v i|) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ∑ i, |v i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

lemma enorm_le_sum_abs (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ₑ ≤ ∑ i, ENNReal.ofReal |v i| := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
  exact ENNReal.ofReal_le_ofReal (norm_le_sum_abs v)

open scoped Matrix.Norms.L2Operator in
/-- The operator norm is at most the sum of the absolute entries. -/
lemma opNorm_le_sum_abs (M : Matrix (Fin d) (Fin d) ℝ) : ‖M‖ ≤ ∑ i, ∑ k, |M i k| := by
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => abs_nonneg _) fun v => ?_
  refine (norm_le_sum_abs _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hcoord : (toEuclideanCLM (𝕜 := ℝ) M v) i = ∑ k, M i k * v k := by
    simp [ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
  rw [hcoord, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (coord_abs_le v k) (abs_nonneg _)

open scoped Matrix.Norms.L2Operator in
lemma opEnorm_le_sum_abs (M : Matrix (Fin d) (Fin d) ℝ) : ‖M‖ₑ ≤ ∑ i, ∑ k, ENNReal.ofReal |M i k| := by
  rw [← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖M‖ ≤ ENNReal.ofReal (∑ i, ∑ k, |M i k|) := ENNReal.ofReal_le_ofReal (opNorm_le_sum_abs M)
    _ = ∑ i, ENNReal.ofReal (∑ k, |M i k|) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _
    _ = ∑ i, ∑ k, ENNReal.ofReal |M i k| :=
        Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun k _ => abs_nonneg _

/-! #### Moments from `E‖X‖⁴ < ∞` -/

section Moments
variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]

lemma le_one_add_pow4 {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t ^ 4 := by
  nlinarith [sq_nonneg (t ^ 2 - 1), sq_nonneg (t - 1), sq_nonneg t, mul_nonneg ht (sq_nonneg (t - 1))]

lemma sq_le_one_add_pow4 (t : ℝ) : t ^ 2 ≤ 1 + t ^ 4 := by
  nlinarith [sq_nonneg (t ^ 2 - 1)]

lemma integrable_of_le_poly (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) {C : ℝ} (h : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 4)) :
    Integrable f μ := by
  have hg : Integrable (fun x : EuclideanSpace ℝ (Fin d) => C * (1 + ‖x‖ ^ 4)) μ :=
    ((integrable_const 1).add h4).const_mul C
  exact hg.mono' hf.aestronglyMeasurable (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)

lemma memLp_two_of_sq_le_poly (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) {C : ℝ} (h : ∀ x, f x ^ 2 ≤ C * (1 + ‖x‖ ^ 4)) :
    MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  refine integrable_of_le_poly h4 (hf.pow 2) (C := C) fun x => ?_
  rw [abs_of_nonneg (sq_nonneg _)]; exact h x

lemma integrable_coord (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ) (i : Fin d) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x i) μ :=
  integrable_of_le_poly h4 (PiLp.continuous_apply 2 _ i) (C := 1) fun x => by
    rw [one_mul]; exact (coord_abs_le x i).trans (le_one_add_pow4 (norm_nonneg x))

lemma abs_coord_sub_le (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (a : ℝ) : |x i - a| ≤ ‖x‖ + |a| :=
  (abs_sub _ _).trans (add_le_add (coord_abs_le x i) le_rfl)

lemma sq_coord_sub_le (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (a : ℝ) :
    (x i - a) ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * a ^ 2 := by
  have h := abs_coord_sub_le x i a
  have h' : (x i - a) ^ 2 ≤ (‖x‖ + |a|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (‖x‖ - |a|), sq_abs a]

lemma memLp_coord_sub (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ) (i : Fin d) (a : ℝ) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) => x i - a) 2 μ :=
  memLp_two_of_sq_le_poly h4 ((PiLp.continuous_apply 2 _ i).sub continuous_const) (C := 2 + 2 * a ^ 2)
    fun x => by
      have h1 := sq_coord_sub_le x i a
      have h2 := sq_le_one_add_pow4 ‖x‖
      have h4' : 0 ≤ a ^ 2 * ‖x‖ ^ 4 := by positivity
      nlinarith

lemma integrable_coord_mul (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ) (i k : Fin d)
    (a b : ℝ) : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (x i - a) * (x k - b)) μ :=
  integrable_of_le_poly h4 (((PiLp.continuous_apply 2 _ i).sub continuous_const).mul
    ((PiLp.continuous_apply 2 _ k).sub continuous_const)) (C := 2 + a ^ 2 + b ^ 2) fun x => by
      have h1 := sq_coord_sub_le x i a
      have h2 := sq_coord_sub_le x k b
      have h3 := sq_le_one_add_pow4 ‖x‖
      have h5 : |(x i - a) * (x k - b)| ≤ ((x i - a) ^ 2 + (x k - b) ^ 2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|x i - a| - |x k - b|), sq_abs (x i - a), sq_abs (x k - b)]
      have h6 : 0 ≤ a ^ 2 * ‖x‖ ^ 4 := by positivity
      have h7 : 0 ≤ b ^ 2 * ‖x‖ ^ 4 := by positivity
      nlinarith

lemma memLp_cov_term (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ) (i k : Fin d)
    (a b s : ℝ) : MemLp (fun x : EuclideanSpace ℝ (Fin d) => (x i - a) * (x k - b) - s) 2 μ := by
  refine memLp_two_of_sq_le_poly h4 ((((PiLp.continuous_apply 2 _ i).sub continuous_const).mul
    ((PiLp.continuous_apply 2 _ k).sub continuous_const)).sub continuous_const)
    (C := 2 * (4 + 4 * (a ^ 2 + b ^ 2) + 4 * a ^ 2 * b ^ 2) + 2 * s ^ 2) fun x => ?_
  have h1 := sq_coord_sub_le x i a
  have h2 := sq_coord_sub_le x k b
  have h3 := sq_le_one_add_pow4 ‖x‖
  set t := ‖x‖
  set u := (x i - a) ^ 2
  set w := (x k - b) ^ 2
  have hu : 0 ≤ u := sq_nonneg _
  have hw : 0 ≤ w := sq_nonneg _
  have hprod : u * w ≤ (2 * t ^ 2 + 2 * a ^ 2) * (2 * t ^ 2 + 2 * b ^ 2) :=
    mul_le_mul h1 h2 hw (by positivity)
  have hexp : (2 * t ^ 2 + 2 * a ^ 2) * (2 * t ^ 2 + 2 * b ^ 2) ≤
      (4 + 4 * (a ^ 2 + b ^ 2) + 4 * a ^ 2 * b ^ 2) * (1 + t ^ 4) := by
    have e1 : (a ^ 2 + b ^ 2) * t ^ 2 ≤ (a ^ 2 + b ^ 2) * (1 + t ^ 4) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e2 : 0 ≤ a ^ 2 * b ^ 2 * t ^ 4 := by positivity
    have e3 : 0 ≤ t ^ 4 := by positivity
    have e4 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    nlinarith
  have hsq : ((x i - a) * (x k - b) - s) ^ 2 ≤ 2 * (u * w) + 2 * s ^ 2 := by
    have : ((x i - a) * (x k - b)) ^ 2 = u * w := by rw [mul_pow]
    nlinarith [sq_nonneg ((x i - a) * (x k - b) + s)]
  have h1t : 0 ≤ s ^ 2 * t ^ 4 := by positivity
  nlinarith

end Moments

/-! #### The rates -/

section Rates
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ] {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

lemma meanVec_apply' (μ : Measure (EuclideanSpace ℝ (Fin d))) (i : Fin d) : meanVec μ i = ∫ x, x i ∂μ := by
  simp [meanVec]

lemma centred_coord (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ) (i : Fin d) :
    ∫ x, (x i - meanVec μ i) ∂μ = 0 := by
  rw [integral_sub (integrable_coord h4 i) (integrable_const _), integral_const, meanVec_apply']
  simp

lemma centred_cov (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ) (i k : Fin d) :
    ∫ x, ((x i - meanVec μ i) * (x k - meanVec μ k) - covMat μ i k) ∂μ = 0 := by
  rw [integral_sub (integrable_coord_mul h4 i k _ _) (integrable_const _), integral_const]
  simp [covMat]

lemma smean_sub_apply {n : ℕ} (hn : n ≠ 0) (Y : Fin n → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d))
    (i : Fin d) : (smean Y - m) i = (n : ℝ)⁻¹ * ∑ j, (Y j i - m i) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [PiLp.sub_apply, smean_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_sub]
  field_simp

/-- **Sample mean.** -/
theorem bigOP_smean (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ)
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P) (hlaw : ∀ j, P.map (X j) = μ) :
    BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖smean (fun j : Fin n => X j ω) - meanVec μ‖ₑ) := by
  have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin d)), BigOP P (fun n => 1 / Real.sqrt n)
      (fun n ω => ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n, (X j ω i - meanVec μ i)|) := fun i _ =>
    bigOP_avg hX hind hlaw (g := fun x => x i - meanVec μ i)
      ((PiLp.continuous_apply 2 _ i).sub continuous_const).measurable (memLp_coord_sub h4 i _) (centred_coord h4 i)
  refine bigOP_mono_of_ge rate_nonneg rate_tendsto (bigOP_finset_sum rate_nonneg rate_tendsto _ hcoord) 1
    fun n hn ω => ?_
  refine (enorm_le_sum_abs _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [smean_sub_apply (by omega)]

/-- The entries of `Σ̂ − Σ`: `n⁻¹ Σ_j [(X_ji − m_i)(X_jk − m_k) − Σ_ik] − (m̂_i − m_i)(m̂_k − m_k)`. -/
lemma scov_sub_apply {n : ℕ} (hn : n ≠ 0) (Y : Fin n → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d))
    (C : Matrix (Fin d) (Fin d) ℝ) (i k : Fin d) :
    (scov Y - C) i k = (n : ℝ)⁻¹ * ∑ j, ((Y j i - m i) * (Y j k - m k) - C i k) -
      ((n : ℝ)⁻¹ * ∑ j, (Y j i - m i)) * ((n : ℝ)⁻¹ * ∑ j, (Y j k - m k)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  set a : Fin n → ℝ := fun j => Y j i
  set b : Fin n → ℝ := fun j => Y j k
  have e1 := CovPerturb.alg_center hn a b ((n : ℝ)⁻¹ * ∑ j, a j) ((n : ℝ)⁻¹ * ∑ j, b j)
  have e2 := CovPerturb.alg_center hn a b (m i) (m k)
  have e3 : ∀ (c : Fin n → ℝ) (α : ℝ), (n : ℝ)⁻¹ * ∑ j, (c j - α) = (n : ℝ)⁻¹ * ∑ j, c j - α := by
    intro c α
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub]
    field_simp
  have e4 : (n : ℝ)⁻¹ * ∑ j, ((a j - m i) * (b j - m k) - C i k) =
      (n : ℝ)⁻¹ * ∑ j, (a j - m i) * (b j - m k) - C i k := e3 (fun j => (a j - m i) * (b j - m k)) (C i k)
  have hs : scov Y i k = (n : ℝ)⁻¹ * ∑ j, (a j - (n : ℝ)⁻¹ * ∑ j, a j) * (b j - (n : ℝ)⁻¹ * ∑ j, b j) := by
    simp only [scov, smean_apply, a, b]
  rw [Matrix.sub_apply, hs]
  change _ = (n : ℝ)⁻¹ * ∑ j, ((a j - m i) * (b j - m k) - C i k) -
      ((n : ℝ)⁻¹ * ∑ j, (a j - m i)) * ((n : ℝ)⁻¹ * ∑ j, (b j - m k))
  rw [e4, e3 a (m i), e3 b (m k)]
  simp only [sub_self, mul_zero, sub_zero] at e1
  linarith

open scoped Matrix.Norms.L2Operator in
/-- **Sample covariance** in operator norm. -/
theorem bigOP_scov (h4 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 4) μ)
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P) (hlaw : ∀ j, P.map (X j) = μ) :
    BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖scov (fun j : Fin n => X j ω) - covMat μ‖ₑ) := by
  have hmean : ∀ i, BigOP P (fun n => 1 / Real.sqrt n)
      (fun n ω => ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n, (X j ω i - meanVec μ i)|) := fun i =>
    bigOP_avg hX hind hlaw (g := fun x => x i - meanVec μ i)
      ((PiLp.continuous_apply 2 _ i).sub continuous_const).measurable (memLp_coord_sub h4 i _) (centred_coord h4 i)
  have hcov : ∀ i k, BigOP P (fun n => 1 / Real.sqrt n)
      (fun n ω => ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n,
        ((X j ω i - meanVec μ i) * (X j ω k - meanVec μ k) - covMat μ i k)|) := fun i k =>
    bigOP_avg hX hind hlaw (g := fun x => (x i - meanVec μ i) * (x k - meanVec μ k) - covMat μ i k)
      ((((PiLp.continuous_apply 2 _ i).sub continuous_const).mul
        ((PiLp.continuous_apply 2 _ k).sub continuous_const)).sub continuous_const).measurable
      (memLp_cov_term h4 i k _ _ _) (centred_cov h4 i k)
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), BigOP P (fun n => 1 / Real.sqrt n) (fun n ω =>
      ∑ k, (ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n,
        ((X j ω i - meanVec μ i) * (X j ω k - meanVec μ k) - covMat μ i k)| +
        ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n, (X j ω i - meanVec μ i)| *
          ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n, (X j ω k - meanVec μ k)|)) := fun i _ =>
    bigOP_finset_sum rate_nonneg rate_tendsto _ fun k _ =>
      bigOP_add rate_nonneg rate_tendsto (hcov i k) (bigOP_mul rate_nonneg rate_tendsto (hmean i) (hmean k))
  refine bigOP_mono_of_ge rate_nonneg rate_tendsto (bigOP_finset_sum rate_nonneg rate_tendsto _ hterm) 1
    fun n hn ω => ?_
  refine (opEnorm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_)
  rw [scov_sub_apply (by omega) _ (meanVec μ), ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)), ← abs_mul]
  exact ENNReal.ofReal_le_ofReal (abs_sub _ _)

end Rates

end Euclid

end StatFormal.MatrixSqrtPerturb
