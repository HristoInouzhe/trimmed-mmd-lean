import TauCeti.Probability.Distributions.Gaussian.ChiSquared
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Laurent–Massart tail bounds for the chi-squared law

Untrusted library code: no `Statements.lean` is involved.

For `X ∼ χ²_k` (`k > 0` real degrees of freedom, Tau Ceti's `chiSquaredMeasure k`) and every `t ≥ 0`,
* upper tail: `P(X ≥ k + 2√(kt) + 2t) ≤ e^{−t}` (also for `k = 0`);
* lower tail: `P(X ≤ k − 2√(kt)) ≤ e^{−t}`

(B. Laurent and P. Massart, *Adaptive estimation of a quadratic functional by model selection*, Ann. Statist. 28
(2000), Lemma 1, with all weights `a_i = 1`). The route is Chernoff's bound with the chi-squared moment generating
function `E e^{λX} = (1 − 2λ)^{−k/2}` (`λ < 1/2`, Tau Ceti `mgf_id_chiSquaredMeasure`) and the elementary inequalities
* `−log(1 − 2λ)/2 − λ ≤ λ²/(1 − 2λ)` on `[0, 1/2)`, in the form `log y ≥ (y − 1/y)/2` on `(0, 1]` (that is `u ≤ sinh u`
  for `u = −log y`), at `λ = √t/(√k + 2√t)`, where the Chernoff exponent equals `−t` exactly;
* `−log(1 + 2λ)/2 + λ ≤ λ²` on `[0, ∞)`, from `log(1 + x) ≥ 2x/(x + 2)`, at `λ = √(t/k)`.

## Main results

* `log_ge_half_sub_inv`, `log_one_add_ge_sub_sq`: the elementary inequalities;
* `chiSquared_upper_tail`, `chiSquared_lower_tail`: the bounds for `chiSquaredMeasure k` (`measureReal`);
* `chiSquared_upper_tail'`, `chiSquared_lower_tail'`: the same in `ℝ≥0∞`;
* `sum_sq_upper_tail`, `sum_sq_lower_tail`: for independent standard Gaussian `Z_1, …, Z_K` and `S = Σ Z_i²`,
  `P(S − K ≥ 2√(Kt) + 2t) ≤ e^{−t}` and `P(K − S ≥ 2√(Kt)) ≤ e^{−t}` (`K ≥ 1` for the lower tail);
* `stdGaussian_map_normSq`: `‖G‖² ∼ χ²_K` for `G ∼ N(0, I_K)`;
* `normSq_upper_tail`, `normSq_lower_tail`: the bounds for `‖G‖²`, `G ∼ N(0, I_K)` (law `stdGaussian`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace StatFormal.ChiSquare

open TauCeti.Probability

/-! ### Elementary inequalities -/

/-- `log y ≥ (y − y⁻¹)/2` for `0 < y ≤ 1` (with `y = e^{−u}`, this is `u ≤ sinh u`, `u ≥ 0`). -/
theorem log_ge_half_sub_inv {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) : (y - y⁻¹) / 2 ≤ Real.log y := by
  set u := -Real.log y with hu
  have hu0 : 0 ≤ u := by rw [hu, neg_nonneg]; exact Real.log_nonpos hy0.le hy1
  have hy : y = Real.exp (-u) := by rw [hu, neg_neg, Real.exp_log hy0]
  have hyinv : y⁻¹ = Real.exp u := by rw [hy, Real.exp_neg, inv_inv]
  have hs := Real.self_le_sinh_iff.2 hu0
  rw [Real.sinh_eq] at hs
  rw [hyinv, show Real.log y = -u by rw [hu, neg_neg]]
  rw [hy]
  linarith

/-- `−log(1 − 2λ)/2 − λ ≤ λ²/(1 − 2λ)` for `0 ≤ λ < 1/2`. -/
theorem neg_log_one_sub_two_mul_le {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    -Real.log (1 - 2 * l) / 2 - l ≤ l ^ 2 / (1 - 2 * l) := by
  have hy0 : 0 < 1 - 2 * l := by linarith
  have h := log_ge_half_sub_inv hy0 (by linarith)
  have key : ((1 - 2 * l) - (1 - 2 * l)⁻¹) / 2 = -2 * l - 2 * (l ^ 2 / (1 - 2 * l)) := by
    field_simp; ring
  rw [key] at h
  have : 0 ≤ l ^ 2 / (1 - 2 * l) := by positivity
  linarith

/-- `log(1 + x) ≥ x − x²/2` for `x ≥ 0`. -/
theorem log_one_add_ge_sub_sq {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  refine le_trans ?_ (Real.le_log_one_add_of_nonneg hx)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [pow_nonneg hx 3]

/-- `−log(1 + 2λ)/2 + λ ≤ λ²` for `λ ≥ 0`. -/
theorem neg_log_one_add_two_mul_le {l : ℝ} (hl0 : 0 ≤ l) : -Real.log (1 + 2 * l) / 2 + l ≤ l ^ 2 := by
  have h := log_one_add_ge_sub_sq (show 0 ≤ 2 * l by linarith)
  nlinarith

/-! ### The chi-squared law -/

lemma isProb (k : ℝ) (hk : 0 ≤ k) : IsProbabilityMeasure (chiSquaredMeasure k) :=
  isProbabilityMeasure_chiSquaredMeasure hk

lemma integrable_exp_chiSquared {k l : ℝ} (hk : 0 < k) (hl : l < 1 / 2) :
    Integrable (fun x => Real.exp (l * x)) (chiSquaredMeasure k) := by
  have : l ∈ integrableExpSet id (chiSquaredMeasure k) := by
    rw [integrableExpSet_id_chiSquaredMeasure hk]; exact hl
  exact this

/-- **Laurent–Massart, upper tail.** For `X ∼ χ²_k`, `k ≥ 0`, and `t ≥ 0`: `P(X ≥ k + 2√(kt) + 2t) ≤ e^{−t}`. -/
theorem chiSquared_upper_tail {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) :
    (chiSquaredMeasure k).real {x | k + 2 * √(k * t) + 2 * t ≤ x} ≤ Real.exp (-t) := by
  have := isProb k hk
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rcases hk.eq_or_lt with rfl | hk
  · -- `χ²_0 = δ_0`
    rw [chiSquaredMeasure_zero]
    have : {x : ℝ | (0 : ℝ) + 2 * √(0 * t) + 2 * t ≤ x} = Ici (2 * t) := by ext x; simp
    have h0 : (0 : ℝ) ∉ Ici (2 * t) := by simp; linarith
    rw [this, Measure.real, Measure.dirac_apply' _ measurableSet_Ici, Set.indicator_of_notMem h0]
    simp only [ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  set a := √k with ha
  set s := √t with hs
  have ha0 : 0 < a := Real.sqrt_pos.2 hk
  have hs0 : 0 < s := Real.sqrt_pos.2 ht
  have hka : k = a ^ 2 := (Real.sq_sqrt hk.le).symm
  have hts : t = s ^ 2 := (Real.sq_sqrt ht.le).symm
  have hkt : √(k * t) = a * s := by rw [Real.sqrt_mul hk.le]
  set l := s / (a + 2 * s) with hl
  have hden : 0 < a + 2 * s := by linarith
  have hl0 : 0 ≤ l := by positivity
  have hl12 : l < 1 / 2 := by rw [hl, div_lt_iff₀ hden]; linarith
  have h1 := measure_ge_le_exp_mul_mgf (μ := chiSquaredMeasure k) (X := id) (t := l)
    (k + 2 * √(k * t) + 2 * t) hl0 (by simpa using integrable_exp_chiSquared hk hl12)
  rw [mgf_id_chiSquaredMeasure hk.le (by linarith)] at h1
  have hy : 1 - 2 * l = a / (a + 2 * s) := by rw [hl]; field_simp; ring
  have hy0 : 0 < 1 - 2 * l := by rw [hy]; positivity
  refine h1.trans (le_of_eq_of_le (b := Real.exp (-l * (k + 2 * √(k * t) + 2 * t) - k / 2 * Real.log (1 - 2 * l)))
    ?_ ?_)
  · rw [Real.rpow_def_of_pos hy0, ← Real.exp_add]; congr 1; ring
  refine Real.exp_le_exp.2 ?_
  have hlog := log_ge_half_sub_inv hy0 (by linarith)
  have hinv : (1 - 2 * l)⁻¹ = (a + 2 * s) / a := by rw [hy, inv_div]
  rw [hinv, hy] at hlog
  -- the exponent with `log` replaced by its lower bound equals `−t`
  have hexact : -l * (k + 2 * (a * s) + 2 * t) - k / 2 * ((a / (a + 2 * s) - (a + 2 * s) / a) / 2) = -t := by
    rw [hl, hka, hts]; field_simp; ring
  rw [hkt, hy]
  have : -(k / 2) * Real.log (a / (a + 2 * s)) ≤ -(k / 2) * ((a / (a + 2 * s) - (a + 2 * s) / a) / 2) :=
    mul_le_mul_of_nonpos_left hlog (by linarith)
  linarith

/-- **Laurent–Massart, lower tail.** For `X ∼ χ²_k`, `k > 0`, and `t ≥ 0`: `P(X ≤ k − 2√(kt)) ≤ e^{−t}`. -/
theorem chiSquared_lower_tail {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) :
    (chiSquaredMeasure k).real {x | x ≤ k - 2 * √(k * t)} ≤ Real.exp (-t) := by
  have := isProb k hk.le
  set l := √(t / k) with hl
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have h1 := measure_le_le_exp_mul_mgf (μ := chiSquaredMeasure k) (X := id) (t := -l)
    (k - 2 * √(k * t)) (by linarith) (by simpa using integrable_exp_chiSquared hk (l := -l) (by linarith))
  rw [mgf_id_chiSquaredMeasure hk.le (by linarith)] at h1
  have hy0 : 0 < 1 - 2 * -l := by linarith
  refine h1.trans (le_of_eq_of_le (b := Real.exp (l * (k - 2 * √(k * t)) - k / 2 * Real.log (1 + 2 * l)))
    ?_ ?_)
  · rw [Real.rpow_def_of_pos hy0, ← Real.exp_add]; congr 1; ring_nf
  refine Real.exp_le_exp.2 ?_
  have hlog := neg_log_one_add_two_mul_le hl0
  have hl2 : l ^ 2 = t / k := Real.sq_sqrt (div_nonneg ht hk.le)
  have hlkt : l * √(k * t) = t := by
    rw [hl, ← Real.sqrt_mul (div_nonneg ht hk.le), show t / k * (k * t) = t ^ 2 by field_simp]
    exact Real.sqrt_sq ht
  have : k * (-Real.log (1 + 2 * l) / 2 + l) ≤ k * l ^ 2 := mul_le_mul_of_nonneg_left hlog hk.le
  rw [hl2, show k * (t / k) = t by field_simp] at this
  nlinarith

/-- The upper tail in `ℝ≥0∞`. -/
theorem chiSquared_upper_tail' {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) :
    chiSquaredMeasure k {x | k + 2 * √(k * t) + 2 * t ≤ x} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have := isProb k hk
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (chiSquared_upper_tail hk ht)

/-- The lower tail in `ℝ≥0∞`. -/
theorem chiSquared_lower_tail' {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) :
    chiSquaredMeasure k {x | x ≤ k - 2 * √(k * t)} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have := isProb k hk.le
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (chiSquared_lower_tail hk ht)

/-- `χ²_k` has no mass on `(−∞, 0]` for `k > 0`. -/
theorem chiSquared_Iic_zero {k : ℝ} (hk : 0 < k) : chiSquaredMeasure k (Iic 0) = 0 := by
  rw [chiSquaredMeasure_eq_withDensity hk, withDensity_apply _ measurableSet_Iic]
  have hae : (Iic (0 : ℝ) : Set ℝ) =ᵐ[volume] Iio 0 := Iio_ae_eq_Iic.symm
  rw [setLIntegral_congr hae, setLIntegral_congr_fun measurableSet_Iio (fun x hx => chiSquaredPDF_of_neg hx)]
  simp

/-! ### Sums of squares of independent standard Gaussians -/

section RV

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : ℕ} {Z : Fin K → Ω → ℝ}

lemma sum_sq_hasLaw (hind : iIndepFun Z P) (hlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) :
    HasLaw (fun ω => ∑ i, Z i ω ^ 2) (chiSquaredMeasure K) P := by
  simpa using iIndepFun.hasLaw_sum_sq_gaussian hind hlaw

/-- **Laurent–Massart, upper tail, for `S = Σ_{i ≤ K} Z_i²`, `Z_i` i.i.d. `N(0,1)`**:
`P(S − K ≥ 2√(Kt) + 2t) ≤ e^{−t}`. -/
theorem sum_sq_upper_tail (hind : iIndepFun Z P) (hlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) {t : ℝ}
    (ht : 0 ≤ t) :
    P {ω | 2 * √(K * t) + 2 * t ≤ ∑ i, Z i ω ^ 2 - K} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have h := sum_sq_hasLaw hind hlaw
  have hset : {ω | 2 * √(K * t) + 2 * t ≤ ∑ i, Z i ω ^ 2 - K} =
      (fun ω => ∑ i, Z i ω ^ 2) ⁻¹' Ici ((K : ℝ) + 2 * √(K * t) + 2 * t) := by
    ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Ici]; constructor <;> intro h <;> linarith
  rw [hset, ← Measure.map_apply_of_aemeasurable h.aemeasurable measurableSet_Ici,
    h.map_eq]
  exact chiSquared_upper_tail' (Nat.cast_nonneg K) ht

/-- **Laurent–Massart, lower tail, for `S = Σ_{i ≤ K} Z_i²`, `K ≥ 1`**: `P(K − S ≥ 2√(Kt)) ≤ e^{−t}`. -/
theorem sum_sq_lower_tail (hind : iIndepFun Z P) (hlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) (hK : 1 ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    P {ω | 2 * √(K * t) ≤ K - ∑ i, Z i ω ^ 2} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have h := sum_sq_hasLaw hind hlaw
  have hset : {ω | 2 * √(K * t) ≤ K - ∑ i, Z i ω ^ 2} =
      (fun ω => ∑ i, Z i ω ^ 2) ⁻¹' Iic ((K : ℝ) - 2 * √(K * t)) := by
    ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Iic]; constructor <;> intro h <;> linarith
  rw [hset, ← Measure.map_apply_of_aemeasurable h.aemeasurable measurableSet_Iic,
    h.map_eq]
  exact chiSquared_lower_tail' (by exact_mod_cast hK) ht

end RV

/-! ### The standard Gaussian vector -/

/-- `‖G‖² ∼ χ²_K` for `G ∼ N(0, I_K)` on `ℝ^K`. -/
theorem stdGaussian_map_normSq (K : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin K))).map (fun x => ‖x‖ ^ 2) = chiSquaredMeasure K := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : ((fun x : EuclideanSpace ℝ (Fin K) => ‖x‖ ^ 2) ∘ (WithLp.toLp 2)) =
      fun y : Fin K → ℝ => ∑ i, y i ^ 2 := by
    ext y; simp [EuclideanSpace.real_norm_sq_eq]
  rw [hf]
  have hindep : iIndepFun (fun (i : Fin K) (y : Fin K → ℝ) ↦ y i)
      (Measure.pi fun _ : Fin K ↦ gaussianReal (0 : ℝ) 1) :=
    iIndepFun_pi (X := fun _ ↦ (id : ℝ → ℝ)) fun _ ↦ aemeasurable_id
  have := sum_sq_hasLaw (Z := fun (i : Fin K) (y : Fin K → ℝ) ↦ y i) hindep fun i ↦
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  exact this.map_eq

section Vec

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : ℕ} {G : Ω → EuclideanSpace ℝ (Fin K)}

lemma normSq_hasLaw (hG : HasLaw G (stdGaussian (EuclideanSpace ℝ (Fin K))) P) :
    HasLaw (fun ω => ‖G ω‖ ^ 2) (chiSquaredMeasure K) P := by
  have h : HasLaw (fun x : EuclideanSpace ℝ (Fin K) => ‖x‖ ^ 2) (chiSquaredMeasure K)
      (stdGaussian (EuclideanSpace ℝ (Fin K))) := ⟨by fun_prop, stdGaussian_map_normSq K⟩
  exact h.comp hG

/-- **Laurent–Massart, upper tail, for `G ∼ N(0, I_K)`**: `P(‖G‖² − K ≥ 2√(Kt) + 2t) ≤ e^{−t}`. -/
theorem normSq_upper_tail (hG : HasLaw G (stdGaussian (EuclideanSpace ℝ (Fin K))) P) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | 2 * √(K * t) + 2 * t ≤ ‖G ω‖ ^ 2 - K} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have h := normSq_hasLaw hG
  have hset : {ω | 2 * √(K * t) + 2 * t ≤ ‖G ω‖ ^ 2 - K} =
      (fun ω => ‖G ω‖ ^ 2) ⁻¹' Ici ((K : ℝ) + 2 * √(K * t) + 2 * t) := by
    ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Ici]; constructor <;> intro h <;> linarith
  rw [hset, ← Measure.map_apply_of_aemeasurable h.aemeasurable measurableSet_Ici,
    h.map_eq]
  exact chiSquared_upper_tail' (Nat.cast_nonneg K) ht

/-- **Laurent–Massart, lower tail, for `G ∼ N(0, I_K)`, `K ≥ 1`**: `P(K − ‖G‖² ≥ 2√(Kt)) ≤ e^{−t}`. -/
theorem normSq_lower_tail (hG : HasLaw G (stdGaussian (EuclideanSpace ℝ (Fin K))) P) (hK : 1 ≤ K) {t : ℝ}
    (ht : 0 ≤ t) :
    P {ω | 2 * √(K * t) ≤ K - ‖G ω‖ ^ 2} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have h := normSq_hasLaw hG
  have hset : {ω | 2 * √(K * t) ≤ K - ‖G ω‖ ^ 2} =
      (fun ω => ‖G ω‖ ^ 2) ⁻¹' Iic ((K : ℝ) - 2 * √(K * t)) := by
    ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Iic]; constructor <;> intro h <;> linarith
  rw [hset, ← Measure.map_apply_of_aemeasurable h.aemeasurable measurableSet_Iic,
    h.map_eq]
  exact chiSquared_lower_tail' (by exact_mod_cast hK) ht

end Vec

end StatFormal.ChiSquare
