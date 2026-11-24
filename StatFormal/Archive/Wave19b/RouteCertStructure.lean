import StatFormal.Archive.Wave19b.Statements
import StatFormal.Archive.RobustEquality.SemidualStrong.Proofs
import StatFormal.Lib.SemiDiscrete.Convex
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Route — JASA `lem:cert-structure` (untrusted)

* `π_f(i|y) = a_i e^{(f_i − c_i(y))/ε} / S_f(y)`, `S_f = Σ_j a_j e^{(f_j − c_j)/ε}`, so `Σ_i π_f(i|y) = 1`.
* (iii) is the certified first-order condition (`foc_Jdual`).
* (i): `log(π_i/π_{f,i}) = (u_i + g̃ − g_f)/ε`, `u = f* − f`; integrate and use (iii) and strong duality `Θ = J(f*)`.
* (ii) gap: the supporting-hyperplane inequality of log-sum-exp (`lse_ge`) gives `g_{f*} − g_f ≤ −Σ_i π_f(i|·) u_i`.
* (ii) gradient: differentiation under the integral (`hasFDerivAt_integral_of_dominated_of_fderiv_le`), the
  derivative `−Σ_i π_f(i|y) e_i^*` of `g_f(y)` being bounded by `k`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave19b

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong
open StatFormal.Foundations.SemiDiscrete (SDHyp sum_exp_pos lse_ge)

section Cert
variable {K : Type} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}

/-- `S_f(y) = Σ_j a_j e^{(f_j − c_j(y))/ε}`. -/
def Ssum (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ) (y : K) : ℝ :=
  ∑ j, a j * Real.exp ((f j - c j y) / ε)

lemma Ssum_pos (h : SDHyp ε a c B) (f : Fin k → ℝ) (y : K) : 0 < Ssum ε a f c y :=
  sum_exp_pos h.hk h.ha _

lemma postW_eq (h : SDHyp ε a c B) (f : Fin k → ℝ) (i : Fin k) (y : K) :
    postW ε a f c i y = a i * Real.exp ((f i - c i y) / ε) / Ssum ε a f c y := by
  have hS := Ssum_pos h f y
  have he : (f i + gsoft ε a f c y - c i y) / ε = (f i - c i y) / ε - Real.log (Ssum ε a f c y) := by
    simp only [gsoft, Ssum]; field_simp [h.hε.ne']; ring
  rw [postW, he, Real.exp_sub, Real.exp_log hS, mul_div_assoc]

lemma postW_pos (h : SDHyp ε a c B) (f : Fin k → ℝ) (i : Fin k) (y : K) : 0 < postW ε a f c i y :=
  mul_pos (h.ha i) (Real.exp_pos _)

lemma sum_postW (h : SDHyp ε a c B) (f : Fin k → ℝ) (y : K) : ∑ i, postW ε a f c i y = 1 := by
  simp_rw [postW_eq h]
  rw [← Finset.sum_div]
  exact div_self (Ssum_pos h f y).ne'

lemma postW_le_one (h : SDHyp ε a c B) (f : Fin k → ℝ) (i : Fin k) (y : K) : postW ε a f c i y ≤ 1 := by
  rw [← sum_postW h f y]
  exact Finset.single_le_sum (fun j _ => (postW_pos h f j y).le) (Finset.mem_univ i)

lemma measurable_postW (h : SDHyp ε a c B) (f : Fin k → ℝ) (i : Fin k) : Measurable (postW ε a f c i) := by
  unfold postW
  have hg := h.measurable_gsoft f
  have hc := h.hc i
  fun_prop

lemma integrable_postW (h : SDHyp ε a c B) (f : Fin k → ℝ) (i : Fin k) (P : Measure K) [IsFiniteMeasure P] :
    Integrable (postW ε a f c i) P :=
  StatFormal.Foundations.SemiDiscrete.integrable_of_abs_le (measurable_postW h f i) 1 fun y => by
    rw [abs_of_pos (postW_pos h f i y)]; exact postW_le_one h f i y

lemma log_postW_div (h : SDHyp ε a c B) (fs f : Fin k → ℝ) (i : Fin k) (y : K) :
    Real.log (postW ε a fs c i y / postW ε a f c i y) =
      (fs i - f i + gsoft ε a fs c y - gsoft ε a f c y) / ε := by
  unfold postW
  rw [mul_div_mul_left _ _ (h.ha i).ne', ← Real.exp_sub, Real.log_exp]
  field_simp [h.hε.ne']; ring

lemma klFin_eq (h : SDHyp ε a c B) (fs f : Fin k → ℝ) (y : K) :
    klFin (fun i => postW ε a fs c i y) (fun i => postW ε a f c i y) =
      (∑ i, postW ε a fs c i y * (fs i - f i) + gsoft ε a fs c y - gsoft ε a f c y) / ε := by
  unfold klFin
  simp_rw [log_postW_div h]
  have hs := sum_postW h fs y
  have : ∑ i, postW ε a fs c i y * ((fs i - f i + gsoft ε a fs c y - gsoft ε a f c y) / ε) =
      (∑ i, postW ε a fs c i y * (fs i - f i) + (∑ i, postW ε a fs c i y) * (gsoft ε a fs c y - gsoft ε a f c y)) / ε := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, hs]; ring

/-- `g_{f'} − g_f ≤ −Σ_i π_f(i|y) (f'_i − f_i)`. -/
lemma gsoft_sub_le_lin (h : SDHyp ε a c B) (f f' : Fin k → ℝ) (y : K) :
    gsoft ε a f' c y - gsoft ε a f c y ≤ -∑ i, postW ε a f c i y * (f' i - f i) := by
  have hl := lse_ge h.hk h.ha (fun i => (f i - c i y) / ε) (fun i => (f' i - c i y) / ε)
  have hrw : ∀ i, (a i * Real.exp ((f i - c i y) / ε) / ∑ j, a j * Real.exp ((f j - c j y) / ε)) *
      ((f' i - c i y) / ε - (f i - c i y) / ε) = postW ε a f c i y * (f' i - f i) / ε := by
    intro i
    rw [postW_eq h]; simp only [Ssum]; field_simp [h.hε.ne']; ring
  simp_rw [hrw] at hl
  rw [← Finset.sum_div] at hl
  have hε := h.hε
  set L := ∑ i, postW ε a f c i y * (f' i - f i)
  have h2 := mul_le_mul_of_nonneg_left hl hε.le
  rw [mul_add, mul_div_cancel₀ _ hε.ne'] at h2
  simp only [gsoft]
  linarith

end Cert

lemma sdhyp_of {K : Type} [MeasurableSpace K] {k : ℕ} {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}
    (hs : Setting ε a c) : ∃ B, SDHyp ε a c B := setting_hyp hs

theorem cert_structure_iii : Claims.cert_structure_iii := by
  intro K _ k ε a c P _ fs hs hmax i
  obtain ⟨B, h⟩ := sdhyp_of hs
  have := StatFormal.Foundations.SemiDiscrete.foc_Jdual h hmax i
  unfold postW
  rw [integral_const_mul, this, mul_one]

lemma OTdisc_eq {K : Type} [MeasurableSpace K] {k : ℕ} {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}
    {B : ℝ} (h : SDHyp ε a c B) (P : Measure K) [IsProbabilityMeasure P] {fs : Fin k → ℝ}
    (hmax : ∀ g, Jdual ε a c P g ≤ Jdual ε a c P fs) (f : Fin k → ℝ) :
    OTdisc ε a c P - (Jdual ε a c P f : EReal) = ((Jdual ε a c P fs - Jdual ε a c P f : ℝ) : EReal) := by
  have hΘ := StatFormal.Foundations.SemiDiscrete.Theta_eq_Jdual' h P hmax
  change StatFormal.Foundations.SemiDiscrete.Theta ε a c P - _ = _
  rw [hΘ]
  rfl

theorem cert_structure_i : Claims.cert_structure_i := by
  intro K _ k ε a c P _ fs f hs hmax
  obtain ⟨B, h⟩ := sdhyp_of hs
  rw [OTdisc_eq h P hmax f]
  congr 1
  simp_rw [klFin_eq h fs f]
  have hint : ∀ i, Integrable (fun y => postW ε a fs c i y * (fs i - f i)) P :=
    fun i => (integrable_postW h fs i P).mul_const _
  have hsum : Integrable (fun y => ∑ i, postW ε a fs c i y * (fs i - f i)) P :=
    integrable_finset_sum _ fun i _ => hint i
  rw [integral_div, mul_div_cancel₀ _ h.hε.ne', integral_sub, integral_add, integral_finsetSum _ fun i _ => hint i]
  rotate_left
  · exact hsum
  · exact h.integrable_gsoft fs
  · exact hsum.add (h.integrable_gsoft fs)
  · exact h.integrable_gsoft f
  simp_rw [integral_mul_const]
  have hiii := cert_structure_iii K k ε a c P fs hs hmax
  simp_rw [hiii]
  unfold Jdual
  rw [show ∑ i, a i * (fs i - f i) = ∑ i, a i * fs i - ∑ i, a i * f i by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring]
  ring

theorem cert_structure_ii_gap : Claims.cert_structure_ii_gap := by
  intro K _ k ε a c P _ fs f hs hmax
  obtain ⟨B, h⟩ := sdhyp_of hs
  rw [OTdisc_eq h P hmax f]
  refine ⟨EReal.coe_nonneg.mpr (sub_nonneg.mpr (hmax f)), EReal.coe_le_coe_iff.mpr ?_⟩
  have hint : ∀ i, Integrable (fun y => postW ε a f c i y * (fs i - f i)) P :=
    fun i => (integrable_postW h f i P).mul_const _
  have hpt := integral_mono ((h.integrable_gsoft fs).sub (h.integrable_gsoft f))
    (integrable_finset_sum _ fun i _ => hint i).neg (gsoft_sub_le_lin h f fs)
  simp only [Pi.sub_apply, Pi.neg_apply] at hpt
  rw [integral_sub (h.integrable_gsoft fs) (h.integrable_gsoft f), integral_neg,
    integral_finsetSum _ fun i _ => hint i] at hpt
  simp_rw [integral_mul_const] at hpt
  unfold Jdual gradJ
  have e : ∑ i, (a i - ∫ y, postW ε a f c i y ∂P) * (fs i - f i) =
      (∑ i, a i * fs i - ∑ i, a i * f i) - ∑ i, (∫ y, postW ε a f c i y ∂P) * (fs i - f i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  linarith

/-! ### The gradient -/

section Grad
variable {K : Type} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}

/-- The derivative of `f ↦ g_f(y)`: `−Σ_i π_f(i|y) e_i^*`. -/
def dG (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (f : Fin k → ℝ) (y : K) : (Fin k → ℝ) →L[ℝ] ℝ :=
  -∑ i, postW ε a f c i y • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i

lemma hasFDerivAt_gsoft (h : SDHyp ε a c B) (y : K) (f : Fin k → ℝ) :
    HasFDerivAt (fun f => gsoft ε a f c y) (dG ε a c f y) f := by
  have hS : ∀ j, HasFDerivAt (fun f : Fin k → ℝ => a j * Real.exp ((f j - c j y) / ε))
      ((a j * Real.exp ((f j - c j y) / ε) / ε) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j) f := by
    intro j
    have h1 : HasFDerivAt (fun f : Fin k → ℝ => (f j - c j y) / ε)
        ((1 / ε) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j) f := by
      have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j).hasFDerivAt (x := f)).sub_const (c j y)
      convert this.const_mul (1 / ε) using 1
      · funext g; simp; ring
    have h2 := (h1.exp).const_mul (a j)
    convert h2 using 1
    rw [smul_smul, smul_smul]; congr 1; ring
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hS j
  have hpos := Ssum_pos h f y
  have hlog := (hsum.log hpos.ne').const_mul (-ε)
  change HasFDerivAt (fun f : Fin k → ℝ => -ε * Real.log (∑ j, a j * Real.exp ((f j - c j y) / ε))) _ f
  refine hlog.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun g => ?_
  simp only [dG, neg_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp_rw [postW_eq h]
  simp only [Ssum]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := h.hε.ne'
  field_simp

lemma norm_dG_le (h : SDHyp ε a c B) (f : Fin k → ℝ) (y : K) : ‖dG ε a c f y‖ ≤ k := by
  unfold dG
  rw [norm_neg]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i, ‖postW ε a f c i y • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i‖ ≤ 1 := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (postW_pos h f i y)]
    have hp : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
        simp only [ContinuousLinearMap.proj_apply, one_mul]; exact norm_le_pi_norm g i
    calc postW ε a f c i y * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i‖ ≤ 1 * 1 :=
          mul_le_mul (postW_le_one h f i y) hp (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc ∑ i, ‖postW ε a f c i y • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i‖
      ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = k := by simp

end Grad

theorem cert_structure_ii_grad : Claims.cert_structure_ii_grad := by
  intro K _ k ε a c P _ f hs
  obtain ⟨B, h⟩ := sdhyp_of hs
  refine ⟨?_, ?_⟩
  · have hint : HasFDerivAt (fun f => ∫ y, gsoft ε a f c y ∂P) (∫ y, dG ε a c f y ∂P) f := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => (k : ℝ)) Filter.univ_mem
        (Eventually.of_forall fun g => (h.measurable_gsoft g).aestronglyMeasurable)
        (h.integrable_gsoft f) ?_ (Eventually.of_forall fun y g _ => norm_dG_le h g y)
        (integrable_const _) (Eventually.of_forall fun y g _ => hasFDerivAt_gsoft h y g)
      unfold dG
      refine (Finset.measurable_sum _ fun i _ => ?_).neg.aestronglyMeasurable
      exact (measurable_postW h f i).smul_const _
    have hlin : HasFDerivAt (fun f : Fin k → ℝ => ∑ i, a i * f i)
        (∑ i, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) f := by
      refine HasFDerivAt.fun_sum fun i _ => ?_
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).hasFDerivAt).const_mul (a i)
    have htot := hlin.add hint
    have hval : ∫ y, dG ε a c f y ∂P = -∑ i, (∫ y, postW ε a f c i y ∂P) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i := by
      unfold dG
      rw [integral_neg, integral_finsetSum _ fun i _ => (integrable_postW h f i P).smul_const _]
      simp_rw [integral_smul_const]
    rw [hval] at htot
    change HasFDerivAt ((fun f : Fin k → ℝ => ∑ i, a i * f i) + fun f => ∫ y, gsoft ε a f c y ∂P) _ f
    refine htot.congr_fderiv ?_
    unfold gradJ
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, sub_eq_add_neg]
  · unfold gradJ
    rw [Finset.sum_sub_distrib, h.hsum, ← integral_finsetSum _ fun i _ => integrable_postW h f i P]
    simp_rw [sum_postW h f]
    simp

end StatFormal.Wave19b
