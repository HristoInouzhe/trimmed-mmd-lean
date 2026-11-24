import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Laws of distinct contexts: basic facts

* Atomless laws do not charge the diagonal: `(μ ⊗ ν)(diag) = 0` for atomless `ν`; for independent `X, Y` with
  atomless law of `Y`, `P(X = Y) = 0`; the non-injective tuples are `μ^{⊗M}`-null for atomless `μ`; an i.i.d.
  sequence from an atomless law is injective almost surely.
* Finite Dirac sums: integrals, values, the conditional law `cond` and the product `Measure.pi` of a finite Dirac
  sum are finite Dirac sums with explicit weights.
* `∫ f d(ν(· | D)) = ν(D)⁻¹ ∫_D f dν`.
* The set `D_M` of injective tuples is open (Hausdorff `Z`) and measurable; for a finite law `Π` carried by an open
  `D` and `L` bounded and continuous on `X × D`, `x ↦ ∫ L(x, y) dΠ(y)` is continuous.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Foundations.SworLaw

/-! ### Atomless laws and the diagonal -/

section Diag
variable {α : Type*} [MeasurableSpace α] [MeasurableEq α]

lemma prod_diagonal_eq_zero (μ ν : Measure α) [SFinite ν] (hν : ∀ x, ν {x} = 0) :
    (μ.prod ν) (diagonal α) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  have h : ∀ x, Prod.mk x ⁻¹' diagonal α = {x} := by
    intro x; ext y; simp [diagonal, eq_comm]
  simp [h, hν]

lemma measure_eq_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → α} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hat : ∀ x, P.map Y {x} = 0) : P {ω | X ω = Y ω} = 0 := by
  have hpair : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have h : {ω | X ω = Y ω} = (fun ω => (X ω, Y ω)) ⁻¹' diagonal α := rfl
  rw [h, ← Measure.map_apply hpair measurableSet_diagonal,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY]
  exact prod_diagonal_eq_zero _ _ hat

lemma measurableSet_injective (M : ℕ) : MeasurableSet {t : Fin M → α | Function.Injective t} := by
  have h : {t : Fin M → α | Function.Injective t} = ⋂ k : Fin M, ⋂ l : Fin M, {t | t k = t l → k = l} := by
    ext t; simp only [mem_setOf_eq, mem_iInter]; rfl
  rw [h]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun l => ?_
  have h1 : MeasurableSet {t : Fin M → α | t k = t l} :=
    measurableSet_eq_fun (measurable_pi_apply k) (measurable_pi_apply l)
  by_cases hkl : k = l
  · simp [hkl]
  · have h2 : {t : Fin M → α | t k = t l → k = l} = {t | t k = t l}ᶜ := by ext t; simp [hkl]
    rw [h2]; exact h1.compl

/-- For an atomless probability law, the non-injective `M`-tuples are null. -/
lemma pi_not_injective_eq_zero {M : ℕ} (μ : Measure α) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    Measure.pi (fun _ : Fin M => μ) {t | ¬ Function.Injective t} = 0 := by
  have hsub : {t : Fin M → α | ¬ Function.Injective t} ⊆
      ⋃ k : Fin M, ⋃ l : Fin M, ⋃ (_ : k ≠ l), {t | t k = t l} := by
    intro t ht
    simp only [Function.Injective, not_forall] at ht
    obtain ⟨k, l, hkl, hne⟩ := ht
    simp only [mem_iUnion, mem_setOf_eq]
    exact ⟨k, l, hne, hkl⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun k => measure_iUnion_null fun l => measure_iUnion_null fun hkl => ?_
  have hind : iIndepFun (fun i (t : Fin M → α) => t i) (Measure.pi fun _ : Fin M => μ) :=
    iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
  refine measure_eq_eq_zero (measurable_pi_apply k) (measurable_pi_apply l) (hind.indepFun hkl) ?_
  intro x
  rw [(measurePreserving_eval (fun _ : Fin M => μ) l).map_eq]
  exact hμ x

lemma pi_injective_eq_one {M : ℕ} (μ : Measure α) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    Measure.pi (fun _ : Fin M => μ) {t | Function.Injective t} = 1 := by
  rw [← prob_compl_eq_zero_iff (measurableSet_injective M)]
  exact pi_not_injective_eq_zero μ hμ

/-- An i.i.d. sequence from an atomless law is injective almost surely. -/
lemma ae_injective_of_iIndep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Zs : ℕ → Ω → α} (hm : ∀ i, Measurable (Zs i)) (hind : iIndepFun Zs P)
    (hat : ∀ i x, P.map (Zs i) {x} = 0) : ∀ᵐ ω ∂P, Function.Injective fun i => Zs i ω := by
  have h1 : ∀ i j, i ≠ j → ∀ᵐ ω ∂P, Zs i ω ≠ Zs j ω := by
    intro i j hij
    rw [ae_iff]; simp only [ne_eq, not_not]
    exact measure_eq_eq_zero (hm i) (hm j) (hind.indepFun hij) (hat j)
  have h2 : ∀ᵐ ω ∂P, ∀ i j, i ≠ j → Zs i ω ≠ Zs j ω := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [h1 i j hij] with ω hω _ using hω
  filter_upwards [h2] with ω hω i j hij
  by_contra h; exact hω i j h hij

end Diag

/-! ### Finite Dirac sums -/

section Dirac
variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {ι : Type*} [Fintype ι]

lemma sum_dirac_apply (a : ι → ℝ≥0∞) (x : ι → α) {s : Set α} (hs : MeasurableSet s) :
    (∑ i, a i • Measure.dirac (x i)) s = ∑ i, a i * s.indicator 1 (x i) := by
  simp [Measure.coe_finsetSum, Measure.dirac_apply' _ hs]

lemma isFiniteMeasure_sum_dirac (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) (x : ι → α) :
    IsFiniteMeasure (∑ i, a i • Measure.dirac (x i)) := by
  refine ⟨?_⟩
  rw [sum_dirac_apply _ _ MeasurableSet.univ]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  simp only [indicator_univ, Pi.one_apply, mul_one]
  exact (ha i).lt_top

lemma integral_sum_dirac (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) (x : ι → α) (f : α → ℝ) :
    ∫ y, f y ∂(∑ i, a i • Measure.dirac (x i)) = ∑ i, (a i).toReal * f (x i) := by
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (ha i)

lemma cond_sum_dirac (a : ι → ℝ≥0∞) (x : ι → α) {D : Set α} (hD : MeasurableSet D) :
    ProbabilityTheory.cond (∑ i, a i • Measure.dirac (x i)) D =
      ∑ i, ((∑ j, a j * D.indicator 1 (x j))⁻¹ * (a i * D.indicator 1 (x i))) • Measure.dirac (x i) := by
  ext s hs
  rw [cond_apply hD, sum_dirac_apply _ _ hD, sum_dirac_apply _ _ (hD.inter hs), sum_dirac_apply _ _ hs,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : x i ∈ D <;> by_cases h2 : x i ∈ s <;> simp [h1, h2, indicator_of_mem, indicator_of_notMem]

lemma indicator_univ_pi_one {M : ℕ} (A : Fin M → Set α) (y : Fin M → α) :
    (univ.pi A).indicator (1 : (Fin M → α) → ℝ≥0∞) y = ∏ s, (A s).indicator 1 (y s) := by
  classical
  by_cases h : y ∈ univ.pi A
  · rw [indicator_of_mem h]
    simp only [Pi.one_apply]
    rw [Finset.prod_eq_one]; intro s _
    rw [indicator_of_mem (h s (mem_univ s))]; rfl
  · rw [indicator_of_notMem h]
    simp only [mem_univ_pi, not_forall] at h
    obtain ⟨s, hs⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (indicator_of_notMem hs _)).symm

/-- The product of a finite Dirac sum is the Dirac sum over index tuples. -/
lemma pi_sum_dirac {n M : ℕ} (c : Fin n → ℝ≥0∞) (hc : ∀ j, c j ≠ ⊤) (x : Fin n → α) :
    Measure.pi (fun _ : Fin M => ∑ j, c j • Measure.dirac (x j)) =
      ∑ t : Fin M → Fin n, (∏ s, c (t s)) • Measure.dirac (x ∘ t) := by
  haveI := isFiniteMeasure_sum_dirac c hc x
  refine Measure.pi_eq fun A hA => ?_
  rw [sum_dirac_apply _ _ (MeasurableSet.univ_pi hA)]
  simp_rw [sum_dirac_apply _ _ (hA _)]
  rw [Fintype.prod_sum (fun (s : Fin M) (j : Fin n) => c j * (A s).indicator 1 (x j))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib, indicator_univ_pi_one]
  rfl

end Dirac

/-! ### Integrals under a conditional law -/

lemma integral_cond_eq {β : Type*} [MeasurableSpace β] (ν : Measure β) {D : Set β} (hD : MeasurableSet D)
    (f : β → ℝ) : ∫ y, f y ∂(ProbabilityTheory.cond ν D) = (ν.real D)⁻¹ * ∫ y, D.indicator f y ∂ν := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, integral_indicator hD, smul_eq_mul, ENNReal.toReal_inv]
  rfl

lemma cond_compl_eq_zero {β : Type*} [MeasurableSpace β] (ν : Measure β) {D : Set β} (hD : MeasurableSet D) :
    ProbabilityTheory.cond ν D Dᶜ = 0 := by
  rw [cond_apply hD, inter_compl_self, measure_empty, mul_zero]

/-! ### Distinct tuples and continuity in the query -/

section Cont

lemma isOpen_injective {Z : Type*} [TopologicalSpace Z] [T2Space Z] (M : ℕ) :
    IsOpen {t : Fin M → Z | Function.Injective t} := by
  have h : {t : Fin M → Z | Function.Injective t} = ⋂ k : Fin M, ⋂ l : Fin M, {t | t k = t l → k = l} := by
    ext t; simp only [mem_setOf_eq, mem_iInter]; rfl
  rw [h]
  refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l => ?_
  by_cases hkl : k = l
  · simp [hkl]
  · have h2 : {t : Fin M → Z | t k = t l → k = l} = {t | t k = t l}ᶜ := by ext t; simp [hkl]
    rw [h2]; exact (isClosed_eq (continuous_apply k) (continuous_apply l)).isOpen_compl

lemma measurable_indicator_of_continuousOn {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {D : Set Y} (hD : MeasurableSet D) {f : Y → ℝ} (hf : ContinuousOn f D) :
    Measurable (D.indicator f) := by
  classical
  rw [← piecewise_eq_indicator]
  exact hf.measurable_piecewise continuousOn_const hD

/-- For a finite law `Q` carried by an open `D` and `L` bounded and continuous on `X × D`, the map
`x ↦ ∫ L(x, y) dQ(y)` is continuous. -/
lemma continuous_integral_carried {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {D : Set Y} (hDo : IsOpen D)
    {L : X → Y → ℝ} {B : ℝ} (hL : ContinuousOn (fun p : X × Y => L p.1 p.2) (univ ×ˢ D))
    (hLb : ∀ x y, |L x y| ≤ B) (Q : Measure Y) [IsFiniteMeasure Q] (hQ : Q Dᶜ = 0) :
    Continuous fun x => ∫ y, L x y ∂Q := by
  have hae : ∀ᵐ y ∂Q, y ∈ D := by rw [ae_iff]; exact hQ
  have hLx : ∀ x, ContinuousOn (L x) D := fun x =>
    hL.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy => ⟨mem_univ _, hy⟩
  refine continuous_of_dominated (bound := fun _ => B) (fun x => ?_) (fun x => ?_) (integrable_const _) ?_
  · refine (measurable_indicator_of_continuousOn hDo.measurableSet (hLx x)).aestronglyMeasurable.congr ?_
    filter_upwards [hae] with y hy
    exact indicator_of_mem hy _
  · exact Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hLb x y
  · filter_upwards [hae] with y hy
    exact hL.comp_continuous (continuous_id.prodMk continuous_const) fun x => ⟨mem_univ _, hy⟩

end Cont

end StatFormal.Foundations.SworLaw
