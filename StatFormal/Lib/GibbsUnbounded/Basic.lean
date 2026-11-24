import StatFormal.Archive.RobustEquality.Paper2.Alternating.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.BigOperators

/-!
# The Gibbs (Donsker–Varadhan) inequality with an unbounded exponent, anchor by anchor (library)

* `gibbs_le_log`: for a probability `Γ ≪ ν` (`ν` finite) with integrable log-likelihood ratio and a `Γ`-integrable
  `g` with `e^g ∈ L¹(ν)`, `E_Γ g − ∫ log(dΓ/dν) dΓ ≤ log E_ν e^g` (no boundedness of `g`; the tilting argument of
  `RobustEquality/Gibbs`, with Mathlib's `integral_llr_tilted_right`).
* `coupling_gibbs`: for a coupling `γ` of a weighted discrete centre `P̂ = Σ_i a_i δ_{x_i}` and any `Q`, with
  `∫ c dγ < ∞` and `KL(γ ‖ P̂ ⊗ ν) < ∞` (`ν` a probability measure), nonnegative measurable `f`, `c` and `λ, τ > 0`,
  `∫ f dγ ≤ λ ∫ c dγ + τ KL(γ ‖ P̂ ⊗ ν) + τ Σ_i a_i log ∫ exp{(f(x_i,·) − λ c(x_i,·))/τ} dν`
  in `EReal` (`log ⊤ = ⊤`). The exponent `(f − λc)/τ` may be unbounded above and below. Proof: truncate `f` at `M`,
  normalise anchor by anchor (`g = (f_M − λc)/τ − log Z_M(x₀)`, so `∫ e^g d(P̂ ⊗ ν) = 1` for every `x₀` — no
  disintegration of `γ` is needed), apply `gibbs_le_log` on `E × E`, and let `M → ∞` (monotone convergence).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Finset
open scoped ENNReal

namespace StatFormal.Foundations.GibbsUnbounded

section Gibbs

variable {α : Type*} [MeasurableSpace α]

/-- **Gibbs inequality, integrable form** (no boundedness of the exponent). -/
lemma gibbs_le_log (ν Γ : Measure α) [IsFiniteMeasure ν] [IsProbabilityMeasure Γ] (g : α → ℝ)
    (hgΓ : Integrable g Γ) (hexp : Integrable (fun x => exp (g x)) ν) (hac : Γ ≪ ν)
    (hint : Integrable (llr Γ ν) Γ) :
    (∫ x, g x ∂Γ) - ∫ x, llr Γ ν x ∂Γ ≤ Real.log (∫ x, exp (g x) ∂ν) := by
  have hν : ν ≠ 0 := by
    rintro rfl
    have h := hac (show (0 : Measure α) Set.univ = 0 from rfl)
    simp at h
  have : NeZero ν := ⟨hν⟩
  have : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted hexp
  have hacτ : Γ ≪ ν.tilted g := hac.trans (absolutelyContinuous_tilted hexp)
  have hintτ : Integrable (llr Γ (ν.tilted g)) Γ := integrable_llr_tilted_right hac hgΓ hint hexp
  have heq := integral_llr_tilted_right hac hgΓ hexp hint
  have hnn := integral_llr_add_sub_measure_univ_nonneg hacτ hintτ
  simp only [probReal_univ, add_sub_cancel_right] at hnn
  linarith

end Gibbs

section Coupling

open StatFormal.RobustEquality.Paper2.Alternating (centre)

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

lemma centre_univ' {n : ℕ} {a : Fin n → ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (x : Fin n → E) :
    centre a x Set.univ = 1 := by
  unfold centre
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => ha0 i, ha1, ENNReal.ofReal_one]

lemma centre_isProb' {n : ℕ} {a : Fin n → ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (x : Fin n → E) :
    IsProbabilityMeasure (centre a x) := ⟨centre_univ' ha0 ha1 x⟩

lemma integrable_centre {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) (L : E → ℝ) : Integrable L (centre a x) := by
  unfold centre
  refine (integrable_finset_sum_measure).2 fun i _ => ?_
  exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

lemma integral_centre {n : ℕ} {a : Fin n → ℝ} (ha0 : ∀ i, 0 ≤ a i) (x : Fin n → E) (L : E → ℝ) :
    ∫ y, L y ∂(centre a x) = ∑ i, a i * L (x i) := by
  unfold centre
  rw [integral_finset_sum_measure fun i _ => (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (ha0 i), smul_eq_mul]

lemma lintegral_centre {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) (F : E → ℝ≥0∞) :
    ∫⁻ y, F y ∂(centre a x) = ∑ i, ENNReal.ofReal (a i) * F (x i) := by
  unfold centre
  rw [lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- From `∀ M, (I M : EReal) ≤ R` to `((⨆ M, I M : ℝ≥0∞) : EReal) ≤ R`. -/
lemma coe_iSup_le {ι : Sort*} [Nonempty ι] {I : ι → ℝ≥0∞} {R : EReal} (h : ∀ M, ((I M : ℝ≥0∞) : EReal) ≤ R) :
    (((⨆ M, I M : ℝ≥0∞)) : EReal) ≤ R := by
  obtain ⟨M₀⟩ := ‹Nonempty ι›
  have hR : 0 ≤ R := (EReal.coe_ennreal_nonneg _).trans (h M₀)
  rw [← EReal.coe_toENNReal hR, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine iSup_le fun M => ?_
  have := h M
  rwa [← EReal.coe_toENNReal hR, EReal.coe_ennreal_le_coe_ennreal_iff] at this

/-- **Anchor-wise Gibbs bound for a coupling of a discrete centre**, unbounded exponent. -/
theorem coupling_gibbs {n : ℕ} {a : Fin n → ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (x : Fin n → E)
    (ν : Measure E) [IsProbabilityMeasure ν]
    {f c : E × E → ℝ} (hf : Measurable f) (hc : Measurable c) (hf0 : ∀ z, 0 ≤ f z) (hc0 : ∀ z, 0 ≤ c z)
    {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ)
    (γ : Measure (E × E)) [IsProbabilityMeasure γ] (hfst : γ.map Prod.fst = centre a x)
    (hC : ∫⁻ z, ENNReal.ofReal (c z) ∂γ ≠ ⊤) (hK : klDiv γ ((centre a x).prod ν) ≠ ⊤) :
    ((∫⁻ z, ENNReal.ofReal (f z) ∂γ : ℝ≥0∞) : EReal) ≤
      ((l * (∫⁻ z, ENNReal.ofReal (c z) ∂γ).toReal + τ * (klDiv γ ((centre a x).prod ν)).toReal : ℝ) : EReal) +
        (τ : EReal) * ∑ i, ((a i : ℝ) : EReal) *
          ENNReal.log (∫⁻ y, ENNReal.ofReal (exp ((f (x i, y) - l * c (x i, y)) / τ)) ∂ν) := by
  have : IsProbabilityMeasure (centre a x) := centre_isProb' ha0 ha1 x
  set ρ := (centre a x).prod ν with hρ
  set Cr := (∫⁻ z, ENNReal.ofReal (c z) ∂γ).toReal with hCr
  set Kr := (klDiv γ ρ).toReal with hKr
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.1 hK
  have hcInt : Integrable c γ :=
    ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hc0)).2 hC.lt_top⟩
  have hCint : ∫ z, c z ∂γ = Cr := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hc0) hc.aestronglyMeasurable]
  have hKint : ∫ z, llr γ ρ z ∂γ = Kr := by
    rw [hKr, toReal_klDiv hac hllr]
    simp
  have hνne : ν ≠ 0 := IsProbabilityMeasure.ne_zero ν
  -- the truncated bound, for each level `M`
  have key : ∀ M : ℕ, ((∫⁻ z, ENNReal.ofReal (min (f z) M) ∂γ : ℝ≥0∞) : EReal) ≤
      ((l * Cr + τ * Kr : ℝ) : EReal) + (τ : EReal) * ∑ i, ((a i : ℝ) : EReal) *
          ENNReal.log (∫⁻ y, ENNReal.ofReal (exp ((f (x i, y) - l * c (x i, y)) / τ)) ∂ν) := by
    intro M
    set gM : E × E → ℝ := fun z => (min (f z) M - l * c z) / τ with hgM
    have hgMm : Measurable gM := ((hf.min measurable_const).sub (hc.const_mul l)).div_const τ
    have hgMle : ∀ z, gM z ≤ M / τ := fun z => by
      have : min (f z) M - l * c z ≤ M := by
        have := min_le_right (f z) (M : ℝ); have := mul_nonneg hl.le (hc0 z); linarith
      exact div_le_div_of_nonneg_right this hτ.le
    set ZM : E → ℝ≥0∞ := fun x0 => ∫⁻ y, ENNReal.ofReal (exp (gM (x0, y))) ∂ν with hZM
    have hFm : Measurable fun z : E × E => ENNReal.ofReal (exp (gM z)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hgMm)
    have hZMm : Measurable ZM := hFm.lintegral_prod_right'
    have hZMtop : ∀ x0, ZM x0 ≠ ⊤ := fun x0 => by
      refine ne_top_of_le_ne_top (b := ∫⁻ _y, ENNReal.ofReal (exp (M / τ)) ∂ν) ?_ (lintegral_mono fun y =>
        ENNReal.ofReal_le_ofReal (exp_le_exp.2 (hgMle _)))
      rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
    have hZM0 : ∀ x0, ZM x0 ≠ 0 := fun x0 h0 => by
      have hmeas : Measurable fun y => ENNReal.ofReal (exp (gM (x0, y))) := hFm.comp measurable_prodMk_left
      have hae := (lintegral_eq_zero_iff hmeas).1 h0
      have : ∀ᵐ y ∂ν, False := hae.mono fun y hy => by
        have : (0 : ℝ≥0∞) < ENNReal.ofReal (exp (gM (x0, y))) := ENNReal.ofReal_pos.2 (exp_pos _)
        exact this.ne' hy
      exact hνne (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 this))
    have hZMpos : ∀ x0, 0 < (ZM x0).toReal := fun x0 => ENNReal.toReal_pos (hZM0 x0) (hZMtop x0)
    set LM : E → ℝ := fun x0 => Real.log (ZM x0).toReal with hLM
    have hLMm : Measurable LM := Real.measurable_log.comp hZMm.ennreal_toReal
    set g : E × E → ℝ := fun z => gM z - LM z.1 with hg
    have hgm : Measurable g := hgMm.sub (hLMm.comp measurable_fst)
    -- the normalisation `∫ e^g dρ = 1`
    have hexpg : ∫⁻ z, ENNReal.ofReal (exp (g z)) ∂ρ = 1 := by
      have hFg : Measurable fun z : E × E => ENNReal.ofReal (exp (g z)) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hgm)
      rw [hρ, lintegral_prod _ hFg.aemeasurable]
      have hin : ∀ x0, ∫⁻ y, ENNReal.ofReal (exp (g (x0, y))) ∂ν = 1 := fun x0 => by
        have e : ∀ y, ENNReal.ofReal (exp (g (x0, y))) =
            ENNReal.ofReal (exp (gM (x0, y))) * ENNReal.ofReal ((ZM x0).toReal⁻¹) := fun y => by
          rw [← ENNReal.ofReal_mul (exp_pos _).le, hg]
          simp only
          rw [Real.exp_sub, hLM, Real.exp_log (hZMpos x0), div_eq_mul_inv]
        simp_rw [e]
        have hFm' : Measurable fun y => ENNReal.ofReal (exp (gM (x0, y))) := hFm.comp measurable_prodMk_left
        rw [lintegral_mul_const _ hFm']
        change ZM x0 * _ = 1
        have hZ : ZM x0 = ENNReal.ofReal (ZM x0).toReal := (ENNReal.ofReal_toReal (hZMtop x0)).symm
        conv_lhs => arg 1; rw [hZ]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_inv_cancel₀ (hZMpos x0).ne', ENNReal.ofReal_one]
      simp_rw [hin]
      rw [lintegral_const, one_mul]
      exact centre_univ' ha0 ha1 x
    have hexpInt : Integrable (fun z => exp (g z)) ρ :=
      ⟨(Real.measurable_exp.comp hgm).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => (exp_pos _).le)).2 (by rw [hexpg]; exact ENNReal.one_lt_top)⟩
    have hexp1 : ∫ z, exp (g z) ∂ρ = 1 := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => (exp_pos _).le)
        (Real.measurable_exp.comp hgm).aestronglyMeasurable, hexpg, ENNReal.toReal_one]
    -- integrability of `g` under `γ`
    have hminInt : Integrable (fun z => min (f z) M) γ := by
      refine Integrable.of_bound (hf.min measurable_const).aestronglyMeasurable M (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf0 z) (Nat.cast_nonneg M))]
      exact min_le_right _ _
    have hgMInt : Integrable gM γ := (hminInt.sub (hcInt.const_mul l)).div_const τ
    have hLMInt : Integrable (fun z : E × E => LM z.1) γ := by
      have h := integrable_centre a x LM
      rw [← hfst] at h
      exact (integrable_map_measure hLMm.aestronglyMeasurable measurable_fst.aemeasurable).1 h
    have hgInt : Integrable g γ := hgMInt.sub hLMInt
    have hG := gibbs_le_log ρ γ g hgInt hexpInt hac hllr
    rw [hexp1, Real.log_one, hKint] at hG
    -- evaluate `∫ g dγ`
    have hLMval : ∫ z, LM z.1 ∂γ = ∑ i, a i * LM (x i) := by
      rw [← integral_map measurable_fst.aemeasurable hLMm.aestronglyMeasurable, hfst, integral_centre ha0]
    have hgval : ∫ z, g z ∂γ = (∫ z, min (f z) M ∂γ - l * Cr) / τ - ∑ i, a i * LM (x i) := by
      rw [integral_sub hgMInt hLMInt, hLMval, hgM, integral_div, integral_sub hminInt (hcInt.const_mul l),
        integral_const_mul, hCint]
    rw [hgval] at hG
    have hreal : ∫ z, min (f z) M ∂γ ≤ l * Cr + τ * Kr + τ * ∑ i, a i * LM (x i) := by
      have h2 : (∫ z, min (f z) M ∂γ - l * Cr) / τ ≤ Kr + ∑ i, a i * LM (x i) := by linarith
      rw [div_le_iff₀ hτ] at h2
      linarith
    -- back to `EReal`
    have hI : ((∫⁻ z, ENNReal.ofReal (min (f z) M) ∂γ : ℝ≥0∞) : EReal) = ((∫ z, min (f z) M ∂γ : ℝ) : EReal) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hminInt (ae_of_all _ fun z => le_min (hf0 z) (Nat.cast_nonneg M)),
        EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg fun z => le_min (hf0 z) (Nat.cast_nonneg M))]
    rw [hI]
    have hLMlog : ∀ i, ((LM (x i) : ℝ) : EReal) ≤
        ENNReal.log (∫⁻ y, ENNReal.ofReal (exp ((f (x i, y) - l * c (x i, y)) / τ)) ∂ν) := fun i => by
      have e : ((LM (x i) : ℝ) : EReal) = ENNReal.log (ZM (x i)) := by
        rw [ENNReal.log_pos_real (hZM0 _) (hZMtop _)]
      rw [e]
      refine ENNReal.log_monotone (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_))
      exact div_le_div_of_nonneg_right (by linarith [min_le_left (f (x i, y)) (M : ℝ)]) hτ.le
    have hsum : ((∑ i, a i * LM (x i) : ℝ) : EReal) ≤ ∑ i, ((a i : ℝ) : EReal) *
        ENNReal.log (∫⁻ y, ENNReal.ofReal (exp ((f (x i, y) - l * c (x i, y)) / τ)) ∂ν) := by
      rw [EReal.coe_finsetSum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left (hLMlog i) (EReal.coe_nonneg.2 (ha0 i))
    calc ((∫ z, min (f z) M ∂γ : ℝ) : EReal)
        ≤ ((l * Cr + τ * Kr + τ * ∑ i, a i * LM (x i) : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hreal
      _ = ((l * Cr + τ * Kr : ℝ) : EReal) + (τ : EReal) * ((∑ i, a i * LM (x i) : ℝ) : EReal) := by
          rw [EReal.coe_add, EReal.coe_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (EReal.coe_nonneg.2 hτ.le))
  -- monotone convergence in the truncation level
  have hsup : ∫⁻ z, ENNReal.ofReal (f z) ∂γ = ⨆ M : ℕ, ∫⁻ z, ENNReal.ofReal (min (f z) M) ∂γ := by
    have hmeasM : ∀ M : ℕ, Measurable fun z => ENNReal.ofReal (min (f z) (M : ℝ)) := fun M =>
      ENNReal.measurable_ofReal.comp (hf.min measurable_const)
    have hmono : Monotone fun (M : ℕ) (z : E × E) => ENNReal.ofReal (min (f z) (M : ℝ)) := fun M N hMN z =>
      ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hMN))
    rw [← lintegral_iSup hmeasM hmono]
    refine lintegral_congr fun z => le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    obtain ⟨M, hM⟩ := exists_nat_ge (f z)
    exact le_iSup_of_le M (by rw [min_eq_left hM])
  rw [hsup]
  exact coe_iSup_le key

end Coupling

end StatFormal.Foundations.GibbsUnbounded
