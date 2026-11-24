import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

set_option linter.style.longLine false

/-!
# Entropic optimal plans for unbounded costs: existence, uniqueness, positive density (library)

Library component (Wave 30r, SB `lem:sharp`). Untrusted library code.

Setting: arbitrary measurable spaces `X`, `Y`, probability laws `μ`, `ν`, a cost `c : X × Y → ℝ≥0∞` with
`∫ c d(μ ⊗ ν) < ∞` (no boundedness, no topology), temperature `ε > 0`, the regularised problem
`inf_{π ∈ Π(μ,ν)} ∫ c dπ + ε KL(π ‖ μ ⊗ ν)` (Tau Ceti `entropicTransportCost`).

* `exists_entropicPlan`: an optimal coupling exists (Csiszár I-projection onto the couplings for the Gibbs reference
  `Z⁻¹ e^{-c/ε} μ ⊗ ν`, Tau Ceti `exists_isCoupling_klDiv_eq_schroedingerValue`, and the Gibbs reformulation
  `lintegral_add_mul_klDiv_eq_entropicTransportCost_iff`).
* `entropicPlan_unique`: it is unique (strict convexity, Tau Ceti `IsCoupling.eq_of_klDiv_eq_schroedingerValue`).
* `rnDeriv_pos_of_isMin`: the perturbation lemma. If `π` minimises `∫ c dπ + ε KL(π‖P)` along the segment
  `(1 − t) π + t P`, both values finite, then `dπ/dP > 0` `P`-a.e. Proof: on `A = {dπ/dP = 0}` the mixture has
  density `t`, and `klFun(t) + t(−log t) = (1 − t) klFun(0)`; off `A`, convexity of `klFun`. Hence
  `KL(π_t) + t(−log t) P(A) ≤ (1 − t) KL(π)`, the cost is affine in `t`, and minimality forces
  `ε (−log t) P(A) ≤ ∫ c dP` for every `t ∈ (0,1]`, i.e. `P(A) = 0`. No potentials are needed.
* `entropicPlan_rnDeriv_pos`, `entropicPlan_eq_withDensity`, `prod_ac_entropicPlan`: every optimal coupling has a
  density against `μ ⊗ ν` that is positive `μ ⊗ ν`-a.e.; in particular `π` and `μ ⊗ ν` are equivalent.
-/

noncomputable section
open MeasureTheory InformationTheory TauCeti Set Filter
open scoped ENNReal NNReal

namespace StatFormal.Foundations.EntropicPlan

/-! ### Pointwise inequalities for `klFun` along a mixture with the reference -/

lemma klFun_mix_le {p t : ℝ} (hp : 0 ≤ p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    klFun ((1 - t) * p + t) ≤ (1 - t) * klFun p := by
  have h := convexOn_klFun.2 (show p ∈ Ici (0 : ℝ) from hp) (show (1 : ℝ) ∈ Ici (0 : ℝ) by simp)
    (sub_nonneg.2 ht1) ht0 (by ring)
  simpa [klFun_one, smul_eq_mul] using h

lemma klFun_mix_zero {t n : ℝ} (ht : Real.log t = -n) :
    klFun ((1 - t) * 0 + t) + t * n = (1 - t) * klFun 0 := by
  rw [klFun_zero]
  simp only [mul_zero, zero_add, klFun, ht]
  ring

variable {α : Type*} [MeasurableSpace α]

/-- The density of the mixture `a π + b P` against `P`. -/
lemma rnDeriv_mix (P π : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure π] (a b : ℝ≥0) :
    (a • π + b • P).rnDeriv P =ᵐ[P] fun z => (a : ℝ≥0∞) * π.rnDeriv P z + b := by
  filter_upwards [Measure.rnDeriv_add' (a • π) (b • P) P, Measure.rnDeriv_smul_left' π P a,
    Measure.rnDeriv_smul_left' P P b, Measure.rnDeriv_self P] with z h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4]
  simp [ENNReal.smul_def]

/-- **Perturbation lemma.** If `π` minimises `∫ c dπ + ε KL(π‖P)` along the segment `(1 − t) π + t P`, with finite
value and `∫ c dP < ∞`, then its density against `P` is positive `P`-a.e. -/
theorem rnDeriv_pos_of_isMin {P π : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure π]
    {c : α → ℝ≥0∞} {ε : ℝ≥0} (hε : ε ≠ 0) (hcP : ∫⁻ z, c z ∂P ≠ ∞)
    (hfin : ∫⁻ z, c z ∂π + ε * klDiv π P ≠ ∞)
    (hmin : ∀ t : ℝ≥0, t ≤ 1 → ∫⁻ z, c z ∂π + ε * klDiv π P ≤
      ∫⁻ z, c z ∂((1 - t) • π + t • P) + ε * klDiv ((1 - t) • π + t • P) P) :
    ∀ᵐ z ∂P, 0 < π.rnDeriv P z := by
  have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε
  have hKfin : klDiv π P ≠ ∞ := by
    intro h
    apply hfin
    rw [h, ENNReal.mul_top hε', add_top]
  have hCfin : ∫⁻ z, c z ∂π ≠ ∞ := fun h => hfin (by rw [h, top_add])
  have hac : π ≪ P := (klDiv_ne_top_iff.1 hKfin).1
  set A : Set α := {z | π.rnDeriv P z = 0} with hA
  have hAm : MeasurableSet A := Measure.measurable_rnDeriv π P (measurableSet_singleton 0)
  suffices hPA : P A = 0 by
    rw [ae_iff]
    convert hPA using 2
    ext z
    simp [A, pos_iff_ne_zero]
  by_contra hPA
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (mul_ne_zero hε' hPA) hcP
  -- the mixing weight `t = e^{-n}`
  set tr : ℝ := Real.exp (-(n : ℝ)) with htr
  have htr0 : 0 ≤ tr := (Real.exp_pos _).le
  have htr1 : tr ≤ 1 := Real.exp_le_one_iff.2 (by simp)
  have hlog : Real.log tr = -(n : ℝ) := Real.log_exp _
  set t : ℝ≥0 := ⟨tr, htr0⟩ with ht
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe]; exact htr1
  have htpos : t ≠ 0 := by
    intro h
    have : tr = 0 := congrArg NNReal.toReal h
    exact (Real.exp_pos _).ne' this
  set a : ℝ≥0 := 1 - t with ha
  have hat : a + t = 1 := tsub_add_cancel_of_le ht1
  have ha_real : (a : ℝ) = 1 - tr := by rw [ha, NNReal.coe_sub ht1]; rfl
  set πt : Measure α := a • π + t • P with hπt
  have hπtac : πt ≪ P :=
    (hac.smul_left a).add_left (Measure.AbsolutelyContinuous.rfl.smul_left t)
  have hKt := klDiv_eq_lintegral_klFun_of_ac hπtac
  have hK := klDiv_eq_lintegral_klFun_of_ac hac
  -- pointwise inequality
  have hpt : ∀ᵐ z ∂P, ENNReal.ofReal (klFun (πt.rnDeriv P z).toReal) +
      A.indicator (fun _ => (t : ℝ≥0∞) * n) z ≤
      (a : ℝ≥0∞) * ENNReal.ofReal (klFun (π.rnDeriv P z).toReal) := by
    filter_upwards [rnDeriv_mix P π a t, Measure.rnDeriv_lt_top π P] with z hz hlt
    have hr : (πt.rnDeriv P z).toReal = (1 - tr) * (π.rnDeriv P z).toReal + tr := by
      rw [hz, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hlt.ne) ENNReal.coe_ne_top,
        ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, ha_real]
      rfl
    have hca : (a : ℝ≥0∞) = ENNReal.ofReal (1 - tr) := by rw [← ha_real, ENNReal.ofReal_coe_nnreal]
    have hct : (t : ℝ≥0∞) = ENNReal.ofReal tr := by rw [← ENNReal.ofReal_coe_nnreal]; rfl
    rw [hr, hca, ← ENNReal.ofReal_mul (by linarith)]
    by_cases hzA : z ∈ A
    · have h0 : π.rnDeriv P z = 0 := hzA
      rw [Set.indicator_of_mem hzA, h0, ENNReal.toReal_zero, ← klFun_mix_zero hlog, hct,
        ENNReal.ofReal_add (klFun_nonneg (by positivity)) (by positivity),
        ENNReal.ofReal_mul htr0, ENNReal.ofReal_natCast]
    · rw [Set.indicator_of_notMem hzA, add_zero]
      exact ENNReal.ofReal_le_ofReal (klFun_mix_le ENNReal.toReal_nonneg htr0 htr1)
  have hKineq : klDiv πt P + (t : ℝ≥0∞) * n * P A ≤ (a : ℝ≥0∞) * klDiv π P := by
    rw [hKt, hK, ← lintegral_indicator_const hAm, ← lintegral_add_right _ (measurable_const.indicator hAm),
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact lintegral_mono_ae hpt
  have hcost : ∫⁻ z, c z ∂πt = a * ∫⁻ z, c z ∂π + t * ∫⁻ z, c z ∂P := by
    rw [hπt, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    rfl
  have hmin' := hmin t ht1
  rw [← ha, ← hπt, hcost] at hmin'
  set F := ∫⁻ z, c z ∂π + ε * klDiv π P with hF
  set CP := ∫⁻ z, c z ∂P
  -- `F + t ε n P(A) ≤ a F + t CP`
  have h1 : F + t * (ε * n * P A) ≤ a * F + t * CP := by
    calc F + t * (ε * n * P A)
        ≤ (a * ∫⁻ z, c z ∂π + t * CP + ε * klDiv πt P) + t * (ε * n * P A) := by gcongr
      _ = a * ∫⁻ z, c z ∂π + t * CP + ε * (klDiv πt P + t * n * P A) := by ring
      _ ≤ a * ∫⁻ z, c z ∂π + t * CP + ε * (a * klDiv π P) := by gcongr
      _ = a * F + t * CP := by rw [hF]; ring
  have h2 : a * F + t * (F + ε * n * P A) ≤ a * F + t * CP := by
    calc a * F + t * (F + ε * n * P A) = (↑(a + t) : ℝ≥0∞) * F + t * (ε * n * P A) := by
          push_cast; ring
      _ = F + t * (ε * n * P A) := by rw [hat]; simp
      _ ≤ a * F + t * CP := h1
  have haF : (a : ℝ≥0∞) * F ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have h3 := (ENNReal.add_le_add_iff_left haF).1 h2
  have h4 : F + ε * n * P A ≤ CP :=
    (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.2 htpos) ENNReal.coe_ne_top).1 h3
  have h5 : (n : ℝ≥0∞) * (ε * P A) ≤ CP := by
    calc (n : ℝ≥0∞) * (ε * P A) = ε * n * P A := by ring
      _ ≤ F + ε * n * P A := le_add_self
      _ ≤ CP := h4
  exact absurd hn (not_lt.2 h5)

/-! ### Entropic optimal plans -/

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {c : X × Y → ℝ≥0∞} {ε : ℝ≥0}

/-- The value of the regularised problem is at most `∫ c d(μ ⊗ ν)` (the product coupling). -/
lemma entropicTransportCost_le_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    entropicTransportCost c ε μ ν ≤ ∫⁻ z, c z ∂(μ.prod ν) := by
  refine (entropicTransportCost_le (isCoupling_prod μ ν) c ε).trans_eq ?_
  simp [klDiv_self]

/-- **Every entropic optimal plan has a positive density against `μ ⊗ ν`** (cost with `∫ c d(μ⊗ν) < ∞`). -/
theorem entropicPlan_rnDeriv_pos [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hε : ε ≠ 0)
    (hcP : ∫⁻ z, c z ∂(μ.prod ν) ≠ ∞) {π : Measure (X × Y)} (hπ : IsCoupling π μ ν)
    (hopt : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν) :
    π ≪ μ.prod ν ∧ ∀ᵐ z ∂(μ.prod ν), 0 < π.rnDeriv (μ.prod ν) z := by
  have := hπ.isProbabilityMeasure
  have hfin : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) ≠ ∞ :=
    hopt ▸ (entropicTransportCost_le_prod.trans_lt hcP.lt_top).ne
  have hKfin : klDiv π (μ.prod ν) ≠ ∞ := by
    intro h
    apply hfin
    rw [h, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hε), add_top]
  refine ⟨(klDiv_ne_top_iff.1 hKfin).1, rnDeriv_pos_of_isMin hε hcP hfin fun t ht => ?_⟩
  have hmix : IsCoupling ((1 - t) • π + t • μ.prod ν) μ ν :=
    hπ.smul_add_smul (isCoupling_prod μ ν) (tsub_add_cancel_of_le ht)
  rw [hopt]
  exact entropicTransportCost_le hmix c ε

/-- Every entropic optimal plan is `(μ ⊗ ν).withDensity f` for a measurable `f > 0` (`μ ⊗ ν`-a.e.). -/
theorem entropicPlan_eq_withDensity [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hε : ε ≠ 0)
    (hcP : ∫⁻ z, c z ∂(μ.prod ν) ≠ ∞) {π : Measure (X × Y)} (hπ : IsCoupling π μ ν)
    (hopt : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν) :
    ∃ f : X × Y → ℝ≥0∞, Measurable f ∧ (∀ᵐ z ∂(μ.prod ν), 0 < f z) ∧ π = (μ.prod ν).withDensity f := by
  obtain ⟨hac, hpos⟩ := entropicPlan_rnDeriv_pos hε hcP hπ hopt
  have := hπ.isProbabilityMeasure
  exact ⟨_, Measure.measurable_rnDeriv _ _, hpos, (Measure.withDensity_rnDeriv_eq π _ hac).symm⟩

/-- An entropic optimal plan and `μ ⊗ ν` are equivalent measures. -/
theorem prod_ac_entropicPlan [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hε : ε ≠ 0)
    (hcP : ∫⁻ z, c z ∂(μ.prod ν) ≠ ∞) {π : Measure (X × Y)} (hπ : IsCoupling π μ ν)
    (hopt : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν) :
    μ.prod ν ≪ π := by
  obtain ⟨f, hf, hpos, rfl⟩ := entropicPlan_eq_withDensity hε hcP hπ hopt
  exact withDensity_absolutelyContinuous' hf.aemeasurable (hpos.mono fun z hz => hz.ne')

/-- The Gibbs reference measure `Z⁻¹ e^{-c/ε} μ ⊗ ν`. -/
abbrev gibbsRef (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) (ν : Measure Y) : Measure (X × Y) :=
  (μ.prod ν).tilted fun z => -((c z).toReal / ε)

lemma schroedingerValue_gibbsRef_ne_top [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : AEMeasurable c (μ.prod ν)) (hε : ε ≠ 0) (hcP : ∫⁻ z, c z ∂(μ.prod ν) ≠ ∞) :
    schroedingerValue (gibbsRef c ε μ ν) μ ν ≠ ∞ := by
  have hctop : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞ := ae_lt_top' hc hcP |>.mono fun z hz => hz.ne
  have h := entropicTransportCost_eq_mul_schroedingerValue_add hc hctop hε
  have hle : entropicTransportCost c ε μ ν ≠ ∞ := (entropicTransportCost_le_prod.trans_lt hcP.lt_top).ne
  intro hS
  apply hle
  rw [h, hS, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hε), top_add]

/-- **Existence of the entropic optimal plan** for any cost with `∫ c d(μ ⊗ ν) < ∞` (no boundedness). -/
theorem exists_entropicPlan [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : AEMeasurable c (μ.prod ν)) (hε : ε ≠ 0) (hcP : ∫⁻ z, c z ∂(μ.prod ν) ≠ ∞) :
    ∃ π, IsCoupling π μ ν ∧ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν := by
  have hctop : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞ := ae_lt_top' hc hcP |>.mono fun z hz => hz.ne
  obtain ⟨π, hπ, hval⟩ :=
    exists_isCoupling_klDiv_eq_schroedingerValue (schroedingerValue_gibbsRef_ne_top hc hε hcP)
  exact ⟨π, hπ, (lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hπ hc hctop hε).2 hval⟩

/-- **Uniqueness of the entropic optimal plan** for any cost with `∫ c d(μ ⊗ ν) < ∞`. -/
theorem entropicPlan_unique [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : AEMeasurable c (μ.prod ν)) (hε : ε ≠ 0) (hcP : ∫⁻ z, c z ∂(μ.prod ν) ≠ ∞)
    {π σ : Measure (X × Y)} (hπ : IsCoupling π μ ν)
    (hπo : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν)
    (hσ : IsCoupling σ μ ν)
    (hσo : ∫⁻ z, c z ∂σ + ε * klDiv σ (μ.prod ν) = entropicTransportCost c ε μ ν) : π = σ := by
  have hctop : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞ := ae_lt_top' hc hcP |>.mono fun z hz => hz.ne
  exact hπ.eq_of_klDiv_eq_schroedingerValue hσ
    ((lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hπ hc hctop hε).1 hπo)
    ((lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hσ hc hctop hε).1 hσo)
    (schroedingerValue_gibbsRef_ne_top hc hε hcP)

end StatFormal.Foundations.EntropicPlan
