import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.Wave29d.Proofs
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Proofs
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Route — paper 2 `thm:npmle` for a general Feller kernel

* Weak duality: Jensen for `log` (`log_avg_le`) at `r_i = v_i ∫ψ_i dm`, and `n⁻¹Σ v_i ∫ψ_i dm ≤ 1`.
* Existence of a maximiser: `𝒫(L)` is compact (Prokhorov, `L` compact metric) and `m ↦ ∫ψ_i dm` is continuous
  (`ψ_i` bounded continuous by the Feller condition), `∫ψ_i dm > 0`.
* At a maximiser: the certified `lindsay_gen_maximiser` (sup over `𝒩` = `L(m*)`, `sup_m ∫D dm = 1`) and
  `lindsay_gen_dirac` (`sup_m ∫ D dm = max_y D(y)`) give `D ≤ 1`, i.e. dual feasibility of `v_i = 1/∫ψ_i dm*`.
* Refutation of the maximiser clause: the certified Wave 29d witness (`ψ(y) = e^{φ(y)}`, `φ(0) = 0`, `φ(y) = 1 − |y|`):
  a maximiser would give `ψ ≤ ∫ψ dm*` everywhere, hence `ψ = ∫ψ dm*` somewhere, but `ψ` has no maximum.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave30az

open StatFormal.Wave29d (psiK npmleK lambdaK MixSettingK phiRule lindsayDK lindsaySupK MeasConvex)
open StatFormal.Wave29d.LindsayGen

/-! ### Weak duality -/

theorem npmle_weak : Claims.npmle_weak := by
  intro K L _ _ n κ φ m v hS hm hv hfeas
  have hn : (0 : ℝ) < n := by exact_mod_cast hS.1
  have hA : ∀ i, 0 < ∫ y, psiK κ φ i y ∂m := fun i => A_pos hS i
  have hS1 : (1 / n : ℝ) * ∑ i, v i * ∫ y, psiK κ φ i y ∂m ≤ 1 := by
    have e : (1 / n : ℝ) * ∑ i, v i * ∫ y, psiK κ φ i y ∂m =
        ∫ y, (1 / n : ℝ) * ∑ i, v i * psiK κ φ i y ∂m := by
      rw [integral_const_mul, integral_finset_sum _ fun i _ => (psi_integrable hS i).const_mul _]
      simp_rw [integral_const_mul]
    rw [e]
    calc ∫ y, (1 / n : ℝ) * ∑ i, v i * psiK κ φ i y ∂m ≤ ∫ _y, (1 : ℝ) ∂m :=
          integral_mono ((integrable_finset_sum _ fun i _ => (psi_integrable hS i).const_mul _).const_mul _)
            (integrable_const _) hfeas
      _ = 1 := by simp
  have hJ := StatFormal.Foundations.Lindsay.log_avg_le hS.1 (fun i => v i * ∫ y, psiK κ φ i y ∂m)
    (fun i => mul_pos (hv i) (hA i))
  have hlog : Real.log ((1 / n : ℝ) * ∑ i, v i * ∫ y, psiK κ φ i y ∂m) ≤ 0 := by
    have hpos : 0 < ∑ i, v i * ∫ y, psiK κ φ i y ∂m :=
      Finset.sum_pos (fun i _ => mul_pos (hv i) (hA i)) ⟨⟨0, hS.1⟩, Finset.mem_univ _⟩
    apply Real.log_nonpos
    · positivity
    · exact hS1
  simp_rw [Real.log_mul (hv _).ne' (hA _).ne'] at hJ
  rw [Finset.sum_add_distrib, mul_add] at hJ
  unfold npmleK
  linarith

/-! ### Existence of a maximiser and strong duality -/

lemma measConvex_prob {L : Type*} [MeasurableSpace L] : MeasConvex {m : Measure L | IsProbabilityMeasure m} := by
  intro m hm m' hm' θ h0 h1
  haveI : IsProbabilityMeasure m := hm
  haveI : IsProbabilityMeasure m' := hm'
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem npmle_gen_duality : Claims.npmle_gen_duality := by
  intro K L _ _ _ _ _ _ _ _ _ n κ φ hS hφc hF
  have hpsic : ∀ i, Continuous (psiK κ φ i) := fun i => hF _ (Real.continuous_exp.comp (hφc i))
  have hmaxprop : ∀ ms : Measure L, IsProbabilityMeasure ms →
      (∀ m : Measure L, IsProbabilityMeasure m → npmleK κ φ m ≤ npmleK κ φ ms) →
        lambdaK κ φ {m | IsProbabilityMeasure m} = npmleK κ φ ms ∧
        (∀ y, (1 / n : ℝ) * ∑ i, (1 / ∫ y', psiK κ φ i y' ∂ms) * psiK κ φ i y ≤ 1) ∧
        -((1 / n : ℝ) * ∑ i, Real.log (1 / ∫ y', psiK κ φ i y' ∂ms)) = npmleK κ φ ms ∧
        IsLeast {D | ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧
            (∀ y, (1 / n : ℝ) * ∑ i, v i * psiK κ φ i y ≤ 1) ∧ D = -((1 / n : ℝ) * ∑ i, Real.log (v i))}
          (npmleK κ φ ms) := by
    intro ms hms hmax
    obtain ⟨hlam, hsup⟩ := StatFormal.Wave29d.lindsay_gen_maximiser K L n κ φ {m | IsProbabilityMeasure m} ms hS
      (fun m hm => hm) measConvex_prob hms hmax
    obtain ⟨y0, hy0, hy0max⟩ := StatFormal.Wave29d.lindsay_gen_dirac K L n κ φ ms hS hφc hF hms
    have hD : ∀ y, lindsayDK κ φ ms y ≤ 1 := fun y => by
      rw [← hsup, hy0]; exact hy0max y
    have hA : ∀ i, 0 < ∫ y', psiK κ φ i y' ∂ms := fun i => A_pos hS i
    have hfeas : ∀ y, (1 / n : ℝ) * ∑ i, (1 / ∫ y', psiK κ φ i y' ∂ms) * psiK κ φ i y ≤ 1 := by
      intro y
      calc _ = lindsayDK κ φ ms y := by
            unfold lindsayDK
            congr 1
            exact Finset.sum_congr rfl fun i _ => one_div_mul_eq_div _ _
        _ ≤ 1 := hD y
    have hval : -((1 / n : ℝ) * ∑ i, Real.log (1 / ∫ y', psiK κ φ i y' ∂ms)) = npmleK κ φ ms := by
      unfold npmleK
      simp_rw [one_div, Real.log_inv, Finset.sum_neg_distrib]
      ring
    refine ⟨hlam, hfeas, hval, ⟨⟨fun i => 1 / ∫ y', psiK κ φ i y' ∂ms, fun i => one_div_pos.2 (hA i), hfeas,
      hval.symm⟩, ?_⟩⟩
    rintro D ⟨v, hv, hvf, rfl⟩
    exact npmle_weak K L n κ φ ms v hS hms hv hvf
  refine ⟨?_, hmaxprop⟩
  -- existence through compactness of `𝒫(L)`
  have hcontA : ∀ i, Continuous fun μ : ProbabilityMeasure L => ∫ y, psiK κ φ i y ∂(μ : Measure L) := by
    intro i
    have := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact ⟨psiK κ φ i, hpsic i⟩)
    simpa using this
  have hcont : Continuous fun μ : ProbabilityMeasure L => npmleK κ φ (μ : Measure L) := by
    unfold npmleK
    refine continuous_const.mul (continuous_finsetSum _ fun i _ => (hcontA i).log fun μ => ?_)
    exact (A_pos hS i (m := (μ : Measure L))).ne'
  obtain ⟨y⟩ := (inferInstance : Nonempty L)
  haveI : Nonempty (ProbabilityMeasure L) := ⟨⟨Measure.dirac y, inferInstance⟩⟩
  obtain ⟨μs, -, hμs⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont.continuousOn
  refine ⟨μs, inferInstance, fun m hm => ?_⟩
  exact isMaxOn_iff.1 hμs ⟨m, hm⟩ (mem_univ _)

/-! ### Refutation of the maximiser clause for bounded measurable rules -/

open StatFormal.Wave29d.LindsayRefute in
theorem npmle_attain_refuted : Claims.npmle_attain_refuted := by
  intro H
  obtain ⟨ms, hms, hmax0⟩ := H hBad 1 1 hBad_meas hBad_bdd one_pos one_pos
  set φ := phiRule hBad 1 1 (fun _ : Fin 1 => x0) with hφ
  have hmax : ∀ m : Measure I, IsProbabilityMeasure m →
      npmleK ProbabilityTheory.Kernel.id φ m ≤ npmleK ProbabilityTheory.Kernel.id φ ms := hmax0
  have hpsi : ∀ z, psiK ProbabilityTheory.Kernel.id φ 0 z =
      Real.exp (if (z : ℝ) = 0 then 0 else 1 - |(z : ℝ)|) := by
    intro z
    simp only [psiK, ProbabilityTheory.Kernel.id_apply, integral_dirac]
    rw [hφ, phi_eq]
  have hS : MixSettingK ProbabilityTheory.Kernel.id φ := by
    refine ⟨one_pos, fun y => by simp, fun i => ?_, ⟨4, fun i y => ?_⟩⟩
    · rw [hφ]; unfold phiRule
      exact (((hBad_meas.sub measurable_const).pow_const 2).sub
        (measurable_const.mul ((measurable_const.sub measurable_subtype_coe).pow_const 2))).div_const _
    · rw [hφ, show i = 0 from Subsingleton.elim _ _, phi_eq]
      have hy : |(y : ℝ)| ≤ 1 := abs_le.2 ⟨y.2.1, y.2.2⟩
      split_ifs
      · norm_num
      · rw [abs_le]; constructor <;> linarith [abs_nonneg (y : ℝ)]
  have hnp : ∀ m : Measure I, npmleK ProbabilityTheory.Kernel.id φ m =
      Real.log (∫ z, psiK ProbabilityTheory.Kernel.id φ 0 z ∂m) := by
    intro m
    simp [npmleK]
  set A := ∫ z, psiK ProbabilityTheory.Kernel.id φ 0 z ∂ms with hAdef
  have hApos : 0 < A := A_pos hS 0
  have hle : ∀ y : I, psiK ProbabilityTheory.Kernel.id φ 0 y ≤ A := by
    intro y
    have h := hmax (Measure.dirac y) inferInstance
    rw [hnp, hnp, integral_dirac] at h
    exact (Real.log_le_log_iff (by rw [hpsi]; exact Real.exp_pos _) hApos).1 h
  -- `ψ = A` somewhere: `∫ (A − ψ) dms = 0` with `A − ψ ≥ 0`
  have hint : Integrable (psiK ProbabilityTheory.Kernel.id φ 0) ms := psi_integrable hS 0
  have h0 : ∫ z, (A - psiK ProbabilityTheory.Kernel.id φ 0 z) ∂ms = 0 := by
    rw [integral_sub (integrable_const _) hint, integral_const, probReal_univ, one_smul, sub_self]
  have hae : ∀ᵐ z ∂ms, A - psiK ProbabilityTheory.Kernel.id φ 0 z = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sub_nonneg.2 (hle z)) ((integrable_const _).sub hint)).1 h0
  haveI : NeZero ms := ⟨IsProbabilityMeasure.ne_zero ms⟩
  obtain ⟨y, hy⟩ := hae.exists
  -- a strictly better point
  obtain ⟨y', hlt⟩ : ∃ y' : I, psiK ProbabilityTheory.Kernel.id φ 0 y < psiK ProbabilityTheory.Kernel.id φ 0 y' := by
    rw [hpsi]
    by_cases h0 : (y : ℝ) = 0
    · refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ?_⟩
      rw [hpsi]
      simp only [h0, if_true]
      norm_num
    · have hy1 := y.2.1
      have hy2 := y.2.2
      refine ⟨⟨(y : ℝ) / 2, by linarith, by linarith⟩, ?_⟩
      rw [hpsi]
      have h2 : (y : ℝ) / 2 ≠ 0 := by simpa using h0
      simp only [h0, h2, if_false]
      apply Real.exp_lt_exp.2
      rw [abs_div, abs_two]
      have : 0 < |(y : ℝ)| := abs_pos.2 h0
      linarith
  have := hle y'
  linarith

end StatFormal.Wave30az
