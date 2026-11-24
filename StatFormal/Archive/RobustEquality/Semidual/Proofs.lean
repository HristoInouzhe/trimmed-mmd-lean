import StatFormal.Archive.RobustEquality.Semidual.Statements
import StatFormal.Archive.RobustEquality.Gibbs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Proofs: `lem:semidual` (i) weak duality and (ii) increments (untrusted proof file)

Route (the paper's): (ii) is monotonicity of log-sum-exp under a uniform shift of the exponents;
(i) is the Gibbs variational principle (`lem_gibbs`) with reference `μ ⊗ Q` and potential
`φ(i,y) = (f_i + g_f(y) − c_i(y))/ε`, for which `∫ e^φ d(μ⊗Q) = 1`.
-/

noncomputable section
open Finset MeasureTheory

namespace StatFormal.RobustEquality.Semidual

/-- Log-sum-exp is monotone under a uniform shift: if `u_i ≤ u'_i + D` then
`log Σ a_i e^{u_i} ≤ log Σ a_i e^{u'_i} + D`. -/
lemma log_sum_exp_le {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (u u' : Fin k → ℝ)
    (D : ℝ) (h : ∀ i, u i ≤ u' i + D) :
    Real.log (∑ i, a i * Real.exp (u i)) ≤ Real.log (∑ i, a i * Real.exp (u' i)) + D := by
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  have hpos : 0 < ∑ i, a i * Real.exp (u i) :=
    Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) hne
  have hpos' : 0 < ∑ i, a i * Real.exp (u' i) :=
    Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) hne
  have hle : ∑ i, a i * Real.exp (u i) ≤ Real.exp D * ∑ i, a i * Real.exp (u' i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have : Real.exp (u i) ≤ Real.exp D * Real.exp (u' i) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [h i])
    nlinarith [ha i]
  calc Real.log (∑ i, a i * Real.exp (u i)) ≤ Real.log (Real.exp D * ∑ i, a i * Real.exp (u' i)) :=
        Real.log_le_log hpos hle
    _ = _ := by rw [Real.log_mul (Real.exp_pos _).ne' hpos'.ne', Real.log_exp]; ring

theorem semidual_incr : Claims.semidual_incr := by
  intro K k a f c ε B y y' hk hε ha hB
  unfold gsoft
  have h := log_sum_exp_le hk a ha (fun i => (f i - c i y') / ε) (fun i => (f i - c i y) / ε)
    (B / ε) (fun i => by
      rw [← add_div, div_le_div_iff_of_pos_right hε]; linarith [hB i])
  have : Real.log (∑ i, a i * Real.exp ((f i - c i y') / ε)) * ε ≤
      (Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε)) + B / ε) * ε :=
    mul_le_mul_of_nonneg_right h hε.le
  rw [add_mul, div_mul_cancel₀ _ hε.ne'] at this
  linarith

theorem semidual_lip : Claims.semidual_lip := by
  intro K k a f f' c ε D y hk hε ha hD
  unfold gsoft
  have h1 := log_sum_exp_le hk a ha (fun i => (f i - c i y) / ε) (fun i => (f' i - c i y) / ε)
    (D / ε) (fun i => by
      rw [← add_div, div_le_div_iff_of_pos_right hε]; linarith [(abs_le.mp (hD i)).2])
  have h2 := log_sum_exp_le hk a ha (fun i => (f' i - c i y) / ε) (fun i => (f i - c i y) / ε)
    (D / ε) (fun i => by
      rw [← add_div, div_le_div_iff_of_pos_right hε]; linarith [(abs_le.mp (hD i)).1])
  have e1 := mul_le_mul_of_nonneg_right h1 hε.le
  have e2 := mul_le_mul_of_nonneg_right h2 hε.le
  rw [add_mul, div_mul_cancel₀ _ hε.ne'] at e1 e2
  rw [abs_le]
  constructor <;> linarith

/-! ### Weak duality -/

variable {K : Type} [MeasurableSpace K] {k : ℕ}

lemma muDisc_univ (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) :
    IsProbabilityMeasure (muDisc a) := by
  constructor
  simp only [muDisc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (ha i).le), hsum, ENNReal.ofReal_one]

lemma integral_muDisc (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (φ : Fin k → ℝ) :
    ∫ i, φ i ∂(muDisc a) = ∑ i, a i * φ i := by
  unfold muDisc
  rw [integral_finsetSum_measure (fun i _ => Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (ha i).le, smul_eq_mul]

lemma measurable_gsoft (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ) (hc : ∀ i, Measurable (c i)) :
    Measurable (gsoft ε a f c) := by
  unfold gsoft
  refine Measurable.const_mul (Measurable.log ?_) _
  exact Finset.measurable_sum _ fun i _ =>
    ((((hc i).const_sub (f i)).div_const ε).exp).const_mul (a i)

lemma abs_log_S_le (hk : 0 < k) (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1)
    (u : Fin k → ℝ) (C : ℝ) (hu : ∀ i, |u i| ≤ C) :
    |Real.log (∑ i, a i * Real.exp (u i))| ≤ C := by
  have h0 : Real.log (∑ i, a i * Real.exp ((fun _ => (0 : ℝ)) i)) = 0 := by
    simp [hsum]
  have h1 := log_sum_exp_le hk a ha u (fun _ => 0) C (fun i => by linarith [(abs_le.mp (hu i)).2])
  have h2 := log_sum_exp_le hk a ha (fun _ => 0) u C (fun i => by linarith [(abs_le.mp (hu i)).1])
  rw [h0] at h1 h2
  rw [abs_le]; constructor <;> linarith

theorem semidual_weak : Claims.semidual_weak := by
  intro K _ k a f c Q _ γ _ ε hε ha hsum hc ⟨B0, hB0⟩ hfst hsnd
  -- `k ≥ 1` since `Σ a = 1`
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hsum
    · exact h
  have hμ := muDisc_univ a ha hsum
  set μ := muDisc a with hμdef
  set ν : Measure (Fin k × K) := μ.prod Q with hνdef
  have hνprob : IsProbabilityMeasure ν := by rw [hνdef]; infer_instance
  set g := gsoft ε a f c with hgdef
  have hgm : Measurable g := measurable_gsoft ε a f c hc
  set Fb : ℝ := ∑ i, |f i| with hFb
  have hfi : ∀ i, |f i| ≤ Fb := fun i =>
    Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) (mem_univ i)
  set C : ℝ := (Fb + B0) / ε with hC
  have hu : ∀ y i, |(f i - c i y) / ε| ≤ C := by
    intro y i
    rw [abs_div, abs_of_pos hε, hC]
    gcongr
    calc |f i - c i y| ≤ |f i| + |c i y| := abs_sub _ _
      _ ≤ Fb + B0 := add_le_add (hfi i) (hB0 i y)
  have hlogS : ∀ y, |Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε))| ≤ C := fun y =>
    abs_log_S_le hk a ha hsum _ C (hu y)
  have hgb : ∀ y, |g y| ≤ ε * C := by
    intro y
    rw [hgdef, gsoft, abs_mul, abs_neg, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left (hlogS y) hε.le
  -- the potential
  set φ : Fin k × K → ℝ := fun z => (f z.1 + g z.2 - c z.1 z.2) / ε with hφdef
  have hφm : Measurable φ := by
    refine measurable_from_prod_countable_right fun i => ?_
    have := hc i
    simp only [hφdef]
    fun_prop
  have hφb : ∀ z, |φ z| ≤ (Fb + ε * C + B0) / ε := by
    intro z
    simp only [hφdef]
    rw [abs_div, abs_of_pos hε]
    gcongr
    calc |f z.1 + g z.2 - c z.1 z.2| ≤ |f z.1 + g z.2| + |c z.1 z.2| := abs_sub _ _
      _ ≤ |f z.1| + |g z.2| + |c z.1 z.2| := by gcongr; exact abs_add_le _ _
      _ ≤ Fb + ε * C + B0 := by gcongr; exacts [hfi _, hgb _, hB0 _ _]
  have hν0 : ν Set.univ ≠ 0 := by simp
  have hgibbs := (StatFormal.RobustEquality.lem_gibbs (Fin k × K) ν hν0 φ hφm
    ⟨_, hφb⟩).1.2 ⟨γ, inferInstance, rfl⟩
  -- the partition function equals one
  have hexpφ : ∀ i y, Real.exp (φ (i, y)) =
      Real.exp ((f i - c i y) / ε) / ∑ j, a j * Real.exp ((f j - c j y) / ε) := by
    intro i y
    have : φ (i, y) = (f i - c i y) / ε - Real.log (∑ j, a j * Real.exp ((f j - c j y) / ε)) := by
      simp only [hφdef, hgdef, gsoft]
      field_simp
      ring
    rw [this, Real.exp_sub, Real.exp_log]
    exact Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.exp_pos _)) ⟨⟨0, hk⟩, mem_univ _⟩
  have hexpint : Integrable (fun z => Real.exp (φ z)) ν := by
    refine Integrable.of_bound hφm.exp.aestronglyMeasurable
      (Real.exp ((Fb + ε * C + B0) / ε)) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hφb z))
  have hZ : ∫ z, Real.exp (φ z) ∂ν = 1 := by
    rw [hνdef, integral_prod_symm _ hexpint]
    have : ∀ y, ∫ i, Real.exp (φ (i, y)) ∂μ = 1 := by
      intro y
      rw [hμdef, integral_muDisc a ha]
      simp_rw [hexpφ]
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div, div_self]
      exact (Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.exp_pos _))
        ⟨⟨0, hk⟩, mem_univ _⟩).ne'
    simp_rw [this]
    simp
  rw [hZ, Real.log_one] at hgibbs
  -- `∫ φ dγ` via the marginals
  have hint_b : ∀ (h : Fin k × K → ℝ) (M : ℝ), Measurable h → (∀ z, |h z| ≤ M) →
      Integrable h γ := fun h M hm hb =>
    Integrable.of_bound hm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)
  have hcm : Measurable (fun z : Fin k × K => c z.1 z.2) :=
    measurable_from_prod_countable_right fun i => hc i
  have i1 : Integrable (fun z : Fin k × K => f z.1) γ :=
    hint_b _ Fb (Measurable.of_discrete.comp measurable_fst) (fun z => hfi _)
  have i2 : Integrable (fun z : Fin k × K => g z.2) γ :=
    hint_b _ (ε * C) (hgm.comp measurable_snd) (fun z => hgb _)
  have i3 : Integrable (fun z : Fin k × K => c z.1 z.2) γ :=
    hint_b _ B0 hcm (fun z => hB0 _ _)
  have e1 : ∫ z, f z.1 ∂γ = ∑ i, a i * f i := by
    rw [← integral_map measurable_fst.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
      hfst, hμdef, integral_muDisc a ha]
  have e2 : ∫ z, g z.2 ∂γ = ∫ y, g y ∂Q := by
    rw [← integral_map measurable_snd.aemeasurable hgm.aestronglyMeasurable, hsnd]
  have hIφ : ∫ z, φ z ∂γ = ((∑ i, a i * f i) + (∫ y, g y ∂Q) - ∫ z, c z.1 z.2 ∂γ) / ε := by
    simp only [hφdef]
    rw [integral_div, integral_sub (show Integrable (fun z : Fin k × K => f z.1 + g z.2) γ from i1.add i2) i3, integral_add i1 i2, e1, e2]
  rw [hIφ] at hgibbs
  -- conclude in `EReal`
  unfold StatFormal.RobustEquality.klRef at hgibbs ⊢
  split_ifs at hgibbs ⊢ with hkl
  · rw [← EReal.coe_sub] at hgibbs
    have h := EReal.coe_le_coe_iff.mp hgibbs
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [sub_nonpos, div_le_iff₀ hε] at h
    linarith
  · rw [EReal.coe_mul_top_of_pos hε, EReal.coe_add_top]
    exact le_top

end StatFormal.RobustEquality.Semidual

namespace StatFormal.RobustEquality.Semidual
example : Claims.semidual_weak := semidual_weak
example : Claims.semidual_incr := semidual_incr
example : Claims.semidual_lip := semidual_lip
end StatFormal.RobustEquality.Semidual
