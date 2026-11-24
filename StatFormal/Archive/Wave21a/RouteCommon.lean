import StatFormal.Archive.Wave21a.Statements
import StatFormal.Lib.SemiDiscrete.HeldOut

/-!
# Route — wave 21a shared lemmas (untrusted)

* `klRef_withDensity`: for densities `p, q` with respect to a σ-finite base `λ` (`q > 0` where `p > 0`),
  `KL(p·λ ‖ q·λ) = ∫ p log(p/q) dλ` (the paper's `klRef`), when the integrand is integrable.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave21a

open StatFormal.RobustEquality

section KLDensity

variable {K : Type*} [MeasurableSpace K]

lemma withDensity_ofReal_eq_mul (lam : Measure K) {p q : K → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hpq : ∀ x, p x ≠ 0 → 0 < q x) (hq0 : ∀ x, 0 ≤ q x) :
    lam.withDensity (fun x => ENNReal.ofReal (p x)) =
      (lam.withDensity fun x => ENNReal.ofReal (q x)).withDensity fun x => ENNReal.ofReal (p x / q x) := by
  rw [← withDensity_mul lam (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hq0 x)]
  congr 1
  by_cases h : p x = 0
  · simp [h]
  · field_simp [(hpq x h).ne']

/-- `KL(p·λ ‖ q·λ) = ∫ p log(p/q) dλ`. -/
theorem klRef_withDensity (lam : Measure K) [SigmaFinite lam] {p q : K → ℝ} (hp : Measurable p)
    (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hpq : ∀ x, p x ≠ 0 → 0 < q x)
    (hint : Integrable (fun x => p x * Real.log (p x / q x)) lam) :
    klRef (lam.withDensity fun x => ENNReal.ofReal (p x)) (lam.withDensity fun x => ENNReal.ofReal (q x)) =
      ((∫ x, p x * Real.log (p x / q x) ∂lam : ℝ) : EReal) := by
  set μ := lam.withDensity fun x => ENNReal.ofReal (p x)
  set ν := lam.withDensity fun x => ENNReal.ofReal (q x)
  haveI : SigmaFinite ν := SigmaFinite.withDensity_ofReal _
  have hμ : μ = ν.withDensity fun x => ENNReal.ofReal (p x / q x) :=
    withDensity_ofReal_eq_mul lam hp hq hp0 hpq hq0
  have hac : μ ≪ ν := by rw [hμ]; exact withDensity_absolutelyContinuous _ _
  have hrn : μ.rnDeriv ν =ᵐ[ν] fun x => ENNReal.ofReal (p x / q x) := by
    rw [hμ]; exact Measure.rnDeriv_withDensity ν (by fun_prop)
  have hllr : llr μ ν =ᵐ[μ] fun x => Real.log (p x / q x) := by
    filter_upwards [hac.ae_le hrn] with x hx
    rw [llr, hx, ENNReal.toReal_ofReal]
    by_cases h : p x = 0
    · simp [h]
    · exact div_nonneg (hp0 x) (hq0 x)
  have hmeas : Measurable fun x => ENNReal.ofReal (p x) := by fun_prop
  have hint' : Integrable (fun x => Real.log (p x / q x)) μ := by
    rw [integrable_withDensity_iff_integrable_smul' hmeas (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hint.congr (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul]
  have hI : Integrable (llr μ ν) μ := hint'.congr hllr.symm
  unfold klRef
  rw [if_pos ⟨hac, hI⟩, integral_congr_ae hllr]
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul]

end KLDensity

section Hoeffding

variable {K Ω ι : Type*} [MeasurableSpace K] [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

/-- One-sided Hoeffding event: with probability `≥ 1 − α`, `E_P g ≤ avg g(Y) + b √(log(1/α)/(2|ι|))`. -/
theorem hoeff_event {P : Measure K} [IsProbabilityMeasure P] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : K → ℝ} (hg : Measurable g) {lo b : ℝ} (hb : 0 ≤ b) (hgI : ∀ y, g y ∈ Set.Icc lo (lo + b))
    {Y : ι → Ω → K} (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y μ) (hlaw : ∀ j, μ.map (Y j) = P)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MeasurableSet {ω | ∫ x, g x ∂P ≤ (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) +
        b * √(Real.log (1 / α) / (2 * Fintype.card ι))} ∧
      ENNReal.ofReal (1 - α) ≤ μ {ω | ∫ x, g x ∂P ≤ (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) +
        b * √(Real.log (1 / α) / (2 * Fintype.card ι))} := by
  have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmeasS : MeasurableSet {ω | ∫ x, g x ∂P ≤ (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) +
        b * √(Real.log (1 / α) / (2 * Fintype.card ι))} :=
    measurableSet_le measurable_const
      (((Finset.measurable_sum _ fun j _ => hg.comp (hY j)).const_mul _).add_const _)
  refine ⟨hmeasS, ?_⟩
  rcases hb.lt_or_eq with hb | hb
  · set s : ℝ := √(Real.log (1 / α) / (2 * Fintype.card ι))
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    set t : ℝ := b * s
    have ht0 : 0 ≤ t := mul_nonneg hb.le hs0
    set bad : Set Ω := {ω | (Fintype.card ι : ℝ) * t ≤ ∑ j, ((∫ x, g x ∂P) - g (Y j ω))}
    have hbad_meas : MeasurableSet bad :=
      measurableSet_le measurable_const
        (Finset.measurable_sum _ fun j _ => measurable_const.sub (hg.comp (hY j)))
    have hbad : μ bad ≤ ENNReal.ofReal α := by
      have hH := StatFormal.Foundations.SemiDiscrete.hoeffding_lower_fintype hg hb hgI hY hind hlaw ht0
      have hexp : Real.exp (-(2 * Fintype.card ι * t ^ 2 / b ^ 2)) = α := by
        have : 2 * (Fintype.card ι : ℝ) * t ^ 2 / b ^ 2 = Real.log (1 / α) := by
          simp only [t, s]
          rw [mul_pow, Real.sq_sqrt (by
            have : 0 ≤ Real.log (1 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα0]; linarith)
            positivity)]
          field_simp
        rw [this, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
      rw [hexp] at hH
      rw [← ofReal_measureReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal hH
    have hgood : badᶜ ⊆ {ω | ∫ x, g x ∂P ≤ (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) + t} := by
      intro ω hω
      simp only [bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hω
      show ∫ x, g x ∂P ≤ (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) + t
      have : (Fintype.card ι : ℝ) * (∫ x, g x ∂P) ≤ (Fintype.card ι : ℝ) * ((1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) + t) := by
        rw [mul_add, ← mul_assoc, mul_one_div_cancel hm'.ne', one_mul]; linarith
      exact le_of_mul_le_mul_left this hm'
    calc ENNReal.ofReal (1 - α) = 1 - ENNReal.ofReal α := by
          rw [ENNReal.ofReal_sub _ hα0.le, ENNReal.ofReal_one]
      _ ≤ 1 - μ bad := tsub_le_tsub_left hbad _
      _ = μ badᶜ := (prob_compl_eq_one_sub hbad_meas).symm
      _ ≤ _ := measure_mono hgood
  · -- `b = 0`: `g` is constant
    subst hb
    have hconst : ∀ y, g y = lo := fun y => le_antisymm (by simpa using (hgI y).2) (hgI y).1
    have hEg : ∫ x, g x ∂P = lo := by simp [hconst]
    have huniv : {ω | ∫ x, g x ∂P ≤ (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) +
        0 * √(Real.log (1 / α) / (2 * Fintype.card ι))} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rw [hEg]
      simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, zero_mul, add_zero]
      rw [← mul_assoc, one_div_mul_cancel hm'.ne', one_mul]
    rw [huniv, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)

end Hoeffding

section UnionBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma nonneg_of_prob_ge {A : Set Ω} {a : ℝ} (h : ENNReal.ofReal (1 - a) ≤ μ A) : 0 ≤ a := by
  by_contra ha
  push_neg at ha
  have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 - a) := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  exact absurd (h1.trans_le (h.trans prob_le_one)) (lt_irrefl _)

lemma compl_le_of_prob_ge {A : Set Ω} (hA : MeasurableSet A) {a : ℝ} (h : ENNReal.ofReal (1 - a) ≤ μ A) :
    μ Aᶜ ≤ ENNReal.ofReal a := by
  have ha := nonneg_of_prob_ge h
  rw [prob_compl_eq_one_sub hA]
  calc 1 - μ A ≤ 1 - ENNReal.ofReal (1 - a) := tsub_le_tsub_left h _
    _ ≤ ENNReal.ofReal a := by
      rw [tsub_le_iff_right]
      rcases le_or_gt a 1 with h1 | h1
      · rw [← ENNReal.ofReal_add ha (by linarith), add_sub_cancel, ENNReal.ofReal_one]
      · calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal h1.le
          _ ≤ _ := le_self_add

/-- Union bound over a finite family, inner form. -/
lemma prob_iInter_ge {ι : Type*} [Fintype ι] {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) {a : ι → ℝ}
    (h : ∀ i, ENNReal.ofReal (1 - a i) ≤ μ (A i)) :
    MeasurableSet (⋂ i, A i) ∧ ENNReal.ofReal (1 - ∑ i, a i) ≤ μ (⋂ i, A i) := by
  have hm : MeasurableSet (⋂ i, A i) := MeasurableSet.iInter hA
  refine ⟨hm, ?_⟩
  have ha : ∀ i, 0 ≤ a i := fun i => nonneg_of_prob_ge (h i)
  have hc : μ (⋂ i, A i)ᶜ ≤ ENNReal.ofReal (∑ i, a i) := by
    rw [compl_iInter, ENNReal.ofReal_sum_of_nonneg fun i _ => ha i]
    exact (measure_iUnion_fintype_le μ _).trans (Finset.sum_le_sum fun i _ => compl_le_of_prob_ge (hA i) (h i))
  calc ENNReal.ofReal (1 - ∑ i, a i) = 1 - ENNReal.ofReal (∑ i, a i) := by
        rw [ENNReal.ofReal_sub _ (Finset.sum_nonneg fun i _ => ha i), ENNReal.ofReal_one]
    _ ≤ 1 - μ (⋂ i, A i)ᶜ := tsub_le_tsub_left hc _
    _ = μ (⋂ i, A i) := by rw [← prob_compl_eq_one_sub hm.compl, compl_compl]

/-- Union bound for two events. -/
lemma prob_inter_ge {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) {a b : ℝ}
    (hPA : ENNReal.ofReal (1 - a) ≤ μ A) (hPB : ENNReal.ofReal (1 - b) ≤ μ B) :
    ENNReal.ofReal (1 - (a + b)) ≤ μ (A ∩ B) := by
  have := (prob_iInter_ge (μ := μ) (A := fun i : Bool => if i then A else B) (a := fun i => if i then a else b)
    (fun i => by cases i <;> simpa) (fun i => by cases i <;> simpa)).2
  simp only [Fintype.sum_bool, if_true, if_false] at this
  have hset : (⋂ i : Bool, if i then A else B) = A ∩ B := by
    ext x; simp [Bool.forall_bool, and_comm]
  rwa [hset] at this

end UnionBound

end StatFormal.Wave21a
