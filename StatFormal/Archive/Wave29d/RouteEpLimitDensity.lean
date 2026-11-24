import StatFormal.Archive.Wave29d.Statements
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral

/-!
# Route — robust equality JASA `thm:ep-limit0` (i), density bounds (untrusted)

At each anchor `x ∈ K`, `I(x) = ∫_K e^{−|x−z|²/ε} q(z) dz` satisfies
`q_min κ e^{−1} ε^{d/2} ≤ I(x)` (restrict to `B̄(x, √ε) ∩ K`, where the exponent is `≥ −1`) and
`I(x) ≤ q_max (πε)^{d/2}` (extend to `ℝ^d`, Gaussian integral); then average `−ε log I` with weights `a`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Real
open scoped ENNReal

namespace StatFormal.Wave29d

open StatFormal.Wave19b (floorW)

namespace EpDensity

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma gauss_integral {ε : ℝ} (hε : 0 < ε) (x : E) :
    ∫ z : E, Real.exp (-‖x - z‖ ^ 2 / ε) = (π * ε) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (show 0 < 1 / ε by positivity)
  rw [finrank_euclideanSpace, Fintype.card_fin, show π / (1 / ε) = π * ε by field_simp] at h
  rw [← h, ← integral_sub_left_eq_self (fun z : E => Real.exp (-(1 / ε) * ‖z‖ ^ 2)) volume x]
  congr 1; ext z; congr 1; ring

lemma gauss_integrable {ε : ℝ} (hε : 0 < ε) (x : E) :
    Integrable (fun z : E => Real.exp (-‖x - z‖ ^ 2 / ε)) := by
  by_contra h
  have h0 := integral_undef h
  rw [gauss_integral hε x] at h0
  exact (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < π * ε) ((d : ℝ) / 2)).ne' h0

lemma integral_density {K : Set E} (hK : MeasurableSet K) {q : E → ℝ} (hq : Measurable q) {qmin : ℝ}
    (hqmin : 0 < qmin) (hqK : ∀ z ∈ K, qmin ≤ q z) (g : E → ℝ) :
    ∫ z, g z ∂((volume.restrict K).withDensity fun z => ENNReal.ofReal (q z)) = ∫ z in K, q z * g z := by
  rw [integral_withDensity_eq_integral_toReal_smul (hq.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hK fun z hz => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [hqK z hz])]

end EpDensity

open EpDensity in
theorem eplimit_density : Claims.eplimit_density := by
  intro d k K a x q qmin qmax κ s₀ ε hK ha ha1 hxK hq hqmin hqK hκ hs₀ hvol hε hεs
  set ν := (volume.restrict K).withDensity fun z => ENNReal.ofReal (q z)
  set e : Fin k → EuclideanSpace ℝ (Fin d) → ℝ := fun i z => Real.exp (-‖x i - z‖ ^ 2 / ε)
  have he_int : ∀ i, Integrable (e i) := fun i => gauss_integrable hε (x i)
  have he_pos : ∀ i z, 0 < e i z := fun i z => Real.exp_pos _
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at ha1
    · exact h
  have hqmax : 0 < qmax := lt_of_lt_of_le hqmin ((hqK (x ⟨0, hk⟩) (hxK _)).1.trans (hqK _ (hxK _)).2)
  -- integrability of `q · e_i` on `K`
  have hqe_int : ∀ i, IntegrableOn (fun z => q z * e i z) K := by
    intro i
    refine Integrable.mono' ((he_int i).restrict.const_mul qmax) ((hq.mul (by fun_prop)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' hK).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [(hqK z hz).1]) (he_pos i z).le)]
    exact mul_le_mul_of_nonneg_right (hqK z hz).2 (he_pos i z).le
  have hI : ∀ i, ∫ z, Real.exp (-‖x i - z‖ ^ 2 / ε) ∂ν = ∫ z in K, q z * e i z := fun i =>
    integral_density hK hq hqmin (fun z hz => (hqK z hz).1) _
  -- the two bounds at each anchor
  set LB := qmin * κ * Real.exp (-1) * (√ε) ^ d
  set UB := qmax * (π * ε) ^ ((d : ℝ) / 2)
  have hLB : 0 < LB := by positivity
  have hUpper : ∀ i, ∫ z in K, q z * e i z ≤ UB := by
    intro i
    calc ∫ z in K, q z * e i z ≤ ∫ z in K, qmax * e i z :=
          setIntegral_mono_on (hqe_int i) ((he_int i).integrableOn.const_mul qmax) hK
            fun z hz => mul_le_mul_of_nonneg_right (hqK z hz).2 (he_pos i z).le
      _ = qmax * ∫ z in K, e i z := integral_const_mul _ _
      _ ≤ qmax * ∫ z, e i z := mul_le_mul_of_nonneg_left
          (setIntegral_le_integral (he_int i) (Eventually.of_forall fun z => (he_pos i z).le)) hqmax.le
      _ = UB := by rw [gauss_integral hε (x i)]
  have hLower : ∀ i, LB ≤ ∫ z in K, q z * e i z := by
    intro i
    set B := Metric.closedBall (x i) (√ε) ∩ K
    have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet.inter hK
    have hBfin : volume B ≠ ∞ :=
      ne_top_of_le_ne_top (measure_closedBall_lt_top (x := x i) (r := √ε)).ne (measure_mono inter_subset_left)
    have hsq : √ε ≤ s₀ := by
      rw [show s₀ = √(s₀ ^ 2) from (Real.sqrt_sq hs₀.le).symm]; exact Real.sqrt_le_sqrt hεs
    have hvolB : κ * (√ε) ^ d ≤ (volume B).toReal := by
      have := hvol (x i) (hxK i) (√ε) (Real.sqrt_pos.2 hε) hsq
      have h2 := ENNReal.toReal_mono hBfin this
      rwa [ENNReal.toReal_ofReal (by positivity)] at h2
    have hpt : ∀ z ∈ B, qmin * Real.exp (-1) ≤ q z * e i z := by
      intro z hz
      have hd : ‖x i - z‖ ≤ √ε := by
        have := hz.1; rw [Metric.mem_closedBall, dist_eq_norm] at this
        rwa [norm_sub_rev] at this
      have hexp : Real.exp (-1) ≤ e i z := by
        apply Real.exp_le_exp.2
        rw [le_div_iff₀ hε]
        have : ‖x i - z‖ ^ 2 ≤ ε := by
          have := pow_le_pow_left₀ (norm_nonneg _) hd 2
          rwa [Real.sq_sqrt hε.le] at this
        linarith
      exact mul_le_mul (hqK z hz.2).1 hexp (Real.exp_pos _).le (by linarith [(hqK z hz.2).1])
    calc LB ≤ (volume B).toReal * (qmin * Real.exp (-1)) := by
          simp only [LB]
          have hc : 0 ≤ qmin * Real.exp (-1) := by positivity
          have := mul_le_mul_of_nonneg_right hvolB hc
          linarith
      _ = ∫ z in B, qmin * Real.exp (-1) := by rw [setIntegral_const, smul_eq_mul, measureReal_def]
      _ ≤ ∫ z in B, q z * e i z :=
          setIntegral_mono_on (integrableOn_const hBfin) ((hqe_int i).mono_set inter_subset_right) hBm hpt
      _ ≤ ∫ z in K, q z * e i z := setIntegral_mono_set (hqe_int i)
          ((ae_restrict_iff' hK).2 (Eventually.of_forall fun z hz =>
            mul_nonneg (by linarith [(hqK z hz).1]) (he_pos i z).le))
          (Eventually.of_forall inter_subset_right)
  -- logarithms and the weighted average
  have hlogs : ∀ i, Real.log LB ≤ Real.log (∫ z, Real.exp (-‖x i - z‖ ^ 2 / ε) ∂ν) ∧
      Real.log (∫ z, Real.exp (-‖x i - z‖ ^ 2 / ε) ∂ν) ≤ Real.log UB := by
    intro i
    rw [hI]
    exact ⟨Real.log_le_log hLB (hLower i), Real.log_le_log (hLB.trans_le (hLower i)) (hUpper i)⟩
  have hsum_lo : Real.log LB ≤ ∑ i, a i * Real.log (∫ z, Real.exp (-‖x i - z‖ ^ 2 / ε) ∂ν) := by
    calc Real.log LB = ∑ i, a i * Real.log LB := by rw [← Finset.sum_mul, ha1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlogs i).1 (ha i).le
  have hsum_hi : ∑ i, a i * Real.log (∫ z, Real.exp (-‖x i - z‖ ^ 2 / ε) ∂ν) ≤ Real.log UB := by
    calc _ ≤ ∑ i, a i * Real.log UB :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlogs i).2 (ha i).le
      _ = Real.log UB := by rw [← Finset.sum_mul, ha1, one_mul]
  have hfl : floorW ε a (fun i z => ‖x i - z‖ ^ 2) ν =
      -ε * ∑ i, a i * Real.log (∫ z, Real.exp (-‖x i - z‖ ^ 2 / ε) ∂ν) := by
    unfold floorW; simp only [neg_div]
  rw [hfl]
  -- closed forms of `log LB`, `log UB`
  have hLBlog : Real.log LB = Real.log qmin + Real.log κ - 1 + d / 2 * Real.log ε := by
    simp only [LB]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow, Real.log_sqrt hε.le]
    ring
  have hUBlog : Real.log UB = Real.log qmax + d / 2 * Real.log (π * ε) := by
    simp only [UB]
    rw [Real.log_mul hqmax.ne' (by positivity), Real.log_rpow (by positivity)]
  have hinvε : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  have hinvπε : Real.log (1 / (π * ε)) = -Real.log (π * ε) := by rw [one_div, Real.log_inv]
  have hinvqκ : Real.log (1 / (qmin * κ)) = -(Real.log qmin + Real.log κ) := by
    rw [one_div, Real.log_inv, Real.log_mul hqmin.ne' hκ.ne']
  constructor
  · rw [hinvπε]
    have := mul_le_mul_of_nonneg_left hsum_hi hε.le
    rw [hUBlog] at this
    nlinarith
  · rw [hinvε, hinvqκ]
    have := mul_le_mul_of_nonneg_left hsum_lo hε.le
    rw [hLBlog] at this
    nlinarith

end StatFormal.Wave29d
