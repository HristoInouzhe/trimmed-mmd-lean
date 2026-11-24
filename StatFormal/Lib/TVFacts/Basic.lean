import StatFormal.Lib.KernelFacts.OneSidedKS
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Total variation: Hahn sets, Scheffé sets of densities, maps, the Bayes risk, common parts (library, untrusted)

`tvDist` is `StatFormal.Distances.tvDist`, `sup_A |P(A) − Q(A)|` over measurable `A`.

## Main results

* `measureReal_sub_le_tvDist`: the one-sided event bound `P(A) − Q(A) ≤ TV(P,Q)`;
* `exists_measurableSet_sub_eq_tvDist`: the supremum is attained, at a Hahn set of `P − Q`;
* `tvDist_eq_iSup_sub`: `TV(P,Q) = sup_A (P(A) − Q(A))` (one-sided supremum);
* `tvDist_eq_sub_of_withDensity` (**Scheffé set**): for `P = ρ.withDensity (ofReal ∘ p)`, `Q = ρ.withDensity (ofReal ∘ q)`,
  `TV(P,Q) = P(q < p) − Q(q < p)`;
* `integral_sub_le_tvDist_of_mem_Icc`: `E_P ψ − E_Q ψ ≤ TV(P,Q)` for measurable `ψ` with values in `[0,1]`;
* `tvDist_map_eq_of_preimage`: total variation is preserved by a map `f` when some `P − Q` gap set of size `TV` is a preimage
  `f⁻¹(B)` (a sufficient statistic for the pair);
* `iInf_bayes_eq` (**Bayes risk**): `inf_A ½{P(Aᶜ) + Q(A)} = (1 − TV(P,Q))/2`;
* `tvDist_le_of_smul_le` (**common part**): `(1 − a)R ≤ P` and `(1 − a)R ≤ Q` for a probability measure `R` give `TV(P,Q) ≤ a`;
* `exists_contam_of_smul_le` (**contamination decomposition**): `(1 − a)R ≤ P`, `0 < a` give a probability measure `P₀` with
  `P = (1 − a)R + aP₀`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.TVFacts

open StatFormal.Distances

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- One-sided event bound: `P(A) − Q(A) ≤ TV(P,Q)` for finite measures and measurable `A`. -/
theorem measureReal_sub_le_tvDist (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] {A : Set α}
    (hA : MeasurableSet A) : P.real A - Q.real A ≤ tvDist P Q :=
  (le_abs_self _).trans (abs_measureReal_sub_le_tvDist hA)

/-- **Total variation is attained at a Hahn set**: for probability measures there is a measurable `s` with
`P(s) − Q(s) = TV(P,Q)`. -/
theorem exists_measurableSet_sub_eq_tvDist (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ∃ s, MeasurableSet s ∧ P.real s - Q.real s = tvDist P Q := by
  obtain ⟨s, hs, h1, h2⟩ := hahn_decomposition P Q
  exact ⟨s, hs, (KernelFacts.tvDist_eq_of_hahn_set P Q hs h1 h2).symm⟩

/-- **One-sided form of total variation**: `TV(P,Q) = sup_A (P(A) − Q(A))` over measurable `A`, for probability measures. -/
theorem tvDist_eq_iSup_sub (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    tvDist P Q = ⨆ A : {A : Set α // MeasurableSet A}, (P.real A.1 - Q.real A.1) := by
  obtain ⟨s, hs, hseq⟩ := exists_measurableSet_sub_eq_tvDist P Q
  exact (KernelFacts.ciSup_eq_of_le_of_eq (fun A : {A : Set α // MeasurableSet A} => measureReal_sub_le_tvDist P Q A.2) ⟨s, hs⟩ hseq).symm

/-- **Scheffé set of two densities.** If `P = ρ.withDensity (ofReal ∘ p)` and `Q = ρ.withDensity (ofReal ∘ q)` for measurable
real `p, q` (of any sign, `ENNReal.ofReal` clips at `0`) and probability measures `P, Q`, then `{q < p}` is a Hahn set of `P − Q`,
so `TV(P,Q) = P(q < p) − Q(q < p)`. -/
theorem tvDist_eq_sub_of_withDensity (ρ P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hP : P = ρ.withDensity fun x => ENNReal.ofReal (p x)) (hQ : Q = ρ.withDensity fun x => ENNReal.ofReal (q x)) :
    tvDist P Q = P.real {x | q x < p x} - Q.real {x | q x < p x} := by
  have hR : MeasurableSet {x | q x < p x} := measurableSet_lt hq hp
  refine KernelFacts.tvDist_eq_of_hahn_set P Q hR ?_ ?_
  · intro A hA hAR
    rw [hP, hQ]
    exact KernelFacts.withDensity_le_withDensity_on ρ
      (ae_of_all _ fun x (hx : q x < p x) => ENNReal.ofReal_le_ofReal hx.le) hA hAR
  · intro A hA hAR
    rw [hP, hQ]
    exact KernelFacts.withDensity_le_withDensity_on ρ
      (ae_of_all _ fun x (hx : x ∈ {x | q x < p x}ᶜ) => ENNReal.ofReal_le_ofReal (not_lt.1 hx)) hA hAR

/-- For measurable `ψ` with values in `[0,1]` and probability measures: `E_P ψ − E_Q ψ ≤ TV(P,Q)`. -/
theorem integral_sub_le_tvDist_of_mem_Icc (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ψ : α → ℝ} (hψ : Measurable ψ) (h01 : ∀ x, ψ x ∈ Icc (0 : ℝ) 1) :
    ∫ x, ψ x ∂P - ∫ x, ψ x ∂Q ≤ tvDist P Q := by
  have h := integral_sub_le_mul_tvDist_of_nonneg (μ := P) (ν := Q) hψ zero_le_one (fun x => (h01 x).1)
    (fun x => (h01 x).2)
  rwa [one_mul] at h

/-- **Total variation under a sufficient map.** If `f` is measurable and some measurable `B` has `P(f⁻¹B) − Q(f⁻¹B) = TV(P,Q)`,
then `TV(f#P, f#Q) = TV(P,Q)` (`≥` from the event `B`, `≤` by data processing). -/
theorem tvDist_map_eq_of_preimage (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {f : α → β}
    (hf : Measurable f) {B : Set β} (hB : MeasurableSet B)
    (hBeq : P.real (f ⁻¹' B) - Q.real (f ⁻¹' B) = tvDist P Q) :
    tvDist (P.map f) (Q.map f) = tvDist P Q := by
  refine le_antisymm (tvDist_map_le hf) ?_
  have h := measureReal_sub_le_tvDist (P.map f) (Q.map f) hB
  rw [map_measureReal_apply hf hB, map_measureReal_apply hf hB, hBeq] at h
  exact h

/-- **Bayes risk with equal priors.** For probability measures, the infimum over measurable `A` of `½{P(Aᶜ) + Q(A)}` (the risk
of the test that says `P` on `A`) equals `(1 − TV(P,Q))/2`; it is attained at a Hahn set. -/
theorem iInf_bayes_eq (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (⨅ A : {A : Set α // MeasurableSet A}, ((P (A.1)ᶜ).toReal + (Q A.1).toReal) / 2) = (1 - tvDist P Q) / 2 := by
  have key : ∀ A : {A : Set α // MeasurableSet A},
      ((P (A.1)ᶜ).toReal + (Q A.1).toReal) / 2 = (1 - (P.real A.1 - Q.real A.1)) / 2 := by
    intro A
    change (P.real (A.1)ᶜ + Q.real A.1) / 2 = _
    rw [probReal_compl_eq_one_sub A.2]
    ring
  have hlow : ∀ A : {A : Set α // MeasurableSet A}, (1 - tvDist P Q) / 2 ≤ ((P (A.1)ᶜ).toReal + (Q A.1).toReal) / 2 := by
    intro A
    rw [key A]
    have := measureReal_sub_le_tvDist P Q A.2
    linarith
  obtain ⟨s, hs, hseq⟩ := exists_measurableSet_sub_eq_tvDist P Q
  refine le_antisymm ?_ (le_ciInf hlow)
  refine (ciInf_le ⟨(1 - tvDist P Q) / 2, ?_⟩ ⟨s, hs⟩).trans_eq ?_
  · rintro _ ⟨A, rfl⟩
    exact hlow A
  · rw [key ⟨s, hs⟩, hseq]

/-- Real form of `c • R ≤ P`: `c R(A) ≤ P(A)` for `c ≥ 0` and finite `P`. -/
theorem mul_measureReal_le_of_smul_le {R P : Measure α} [IsFiniteMeasure P] {c : ℝ} (hc : 0 ≤ c)
    (h : ENNReal.ofReal c • R ≤ P) (A : Set α) : c * R.real A ≤ P.real A := by
  have h1 : (ENNReal.ofReal c • R) A ≤ P A := Measure.le_iff'.1 h A
  have h2 := ENNReal.toReal_mono (measure_ne_top P A) h1
  rwa [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h2

/-- **A common part bounds total variation.** If `ofReal (1 − a) • R ≤ P` and `ofReal (1 − a) • R ≤ Q` for probability measures
`P, Q, R` and `a ≤ 1`, then `TV(P,Q) ≤ a`: `P(A) − Q(A) = 1 − P(Aᶜ) − Q(A) ≤ 1 − (1 − a)R(Aᶜ) − (1 − a)R(A) = a`. -/
theorem tvDist_le_of_smul_le (P Q R : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {a : ℝ} (ha : a ≤ 1) (hP : ENNReal.ofReal (1 - a) • R ≤ P) (hQ : ENNReal.ofReal (1 - a) • R ≤ Q) :
    tvDist P Q ≤ a := by
  have hc : 0 ≤ 1 - a := by linarith
  have one_side : ∀ (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
      ENNReal.ofReal (1 - a) • R ≤ P → ENNReal.ofReal (1 - a) • R ≤ Q →
      ∀ A, MeasurableSet A → P.real A - Q.real A ≤ a := by
    intro P Q _ _ hP hQ A hA
    have h1 := mul_measureReal_le_of_smul_le hc hP Aᶜ
    have h2 := mul_measureReal_le_of_smul_le hc hQ A
    rw [probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hA] at h1
    nlinarith
  refine tvDist_le_of_forall fun A hA => ?_
  rw [abs_le]
  constructor
  · linarith [one_side Q P hQ hP A hA]
  · exact one_side P Q hP hQ A hA

/-- **Contamination decomposition.** If `ofReal (1 − a) • R ≤ P` for probability measures `R, P` and `0 < a ≤ 1`, then
`P₀ = (ofReal a)⁻¹ • (P − ofReal (1 − a) • R)` is a probability measure and `P = ofReal (1 − a) • R + ofReal a • P₀`. -/
theorem exists_contam_of_smul_le (P R : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure R] {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (h : ENNReal.ofReal (1 - a) • R ≤ P) :
    ∃ P₀ : Measure α, IsProbabilityMeasure P₀ ∧ P = ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀ := by
  have : IsFiniteMeasure (ENNReal.ofReal (1 - a) • R) := isFiniteMeasure_of_le P h
  set X := P - ENNReal.ofReal (1 - a) • R with hXdef
  have hX : X + ENNReal.ofReal (1 - a) • R = P := Measure.sub_add_cancel_of_le h
  have hda : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha0).ne'
  have hdt : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hXu : X univ = ENNReal.ofReal a := by
    have hsum := congrArg (fun μ : Measure α => μ univ) hX
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at hsum
    have h1 : X univ = 1 - ENNReal.ofReal (1 - a) := ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsum
    rw [h1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - a)]
    congr 1
    ring
  refine ⟨(ENNReal.ofReal a)⁻¹ • X, ⟨?_⟩, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, hXu, ENNReal.inv_mul_cancel hda hdt]
  · rw [smul_smul, ENNReal.mul_inv_cancel hda hdt, one_smul, add_comm, hX]

/-- **Mixtures with a common component.** If `P = (1 − a)R + aP₀` and `Q = (1 − a)R + aQ₀` (as `ofReal` weights) for probability
measures and `a ≤ 1`, then `TV(P,Q) ≤ a`. -/
theorem tvDist_le_of_mixture (P Q R P₀ Q₀ : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] {a : ℝ} (ha : a ≤ 1)
    (hP : P = ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀)
    (hQ : Q = ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • Q₀) : tvDist P Q ≤ a := by
  refine tvDist_le_of_smul_le P Q R ha ?_ ?_
  · rw [hP]; exact Measure.le_add_right le_rfl
  · rw [hQ]; exact Measure.le_add_right le_rfl

end StatFormal.TVFacts
