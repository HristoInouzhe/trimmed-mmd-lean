import StatFormal.Lib.Donsker.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Donsker library — finite-dimensional laws and Prokhorov (untrusted library code)

Route.
* `continuous_linEval`: `f ↦ Σ_i u_i f(x_i)` is continuous on `C(X, ℝ)`.
* Uniqueness (`measure_ext_of_linEval`). Under `[SecondCountableTopology X] [LocallyCompactSpace X]`
  the Borel σ-algebra of `C(X, ℝ)` is the comap of the product σ-algebra under the coercion
  `C(X, ℝ) → (X → ℝ)` (`ContinuousMap.measurableSpace_eq_iSup_comap_eval`), so a law on `C(X, ℝ)` is
  determined by its push-forward to `X → ℝ` (`measure_ext_of_map_coe`). That push-forward is the
  projective limit of its finite-dimensional marginals on `I → ℝ`, `I : Finset X`
  (`IsProjectiveLimit.unique`), and each marginal is determined by its characteristic function
  (`Measure.ext_of_charFunDual` on the Banach space `I → ℝ`), i.e. by the laws of the linear
  functionals `v ↦ Σ_i u_i v_i` (`measure_pi_ext_of_sum`); enumerating `I` by `Fin I.card` these are
  the laws of `linEval`.
* Prokhorov (`tendstoInDistribution_of_tight`). For compact metric `X`, `C(X, ℝ)` is separable and
  metrizable, so `ProbabilityMeasure C(X, ℝ)` is metrizable (Lévy–Prokhorov) and the closure of the
  tight family of laws is compact (`isCompact_closure_of_isTightMeasureSet`), hence sequentially
  compact. Any subsequential limit has one-dimensional laws `γ p x u` (continuous mapping theorem
  and uniqueness of limits in distribution), so all subsequential limits coincide by
  `measure_ext_of_linEval`, and `tendsto_of_subseq_tendsto` concludes.
-/

noncomputable section

namespace StatFormal.Foundations.Donsker

open MeasureTheory ProbabilityTheory Filter Topology

lemma continuous_linEval {X : Type*} [TopologicalSpace X] {p : ℕ} (x : Fin p → X) (u : Fin p → ℝ) :
    Continuous (linEval x u) := by
  unfold linEval
  fun_prop

/-- Finite-dimensional laws on `ι → ℝ` are determined by the laws of linear functionals. -/
lemma measure_pi_ext_of_sum {ι : Type*} [Fintype ι] (ν₁ ν₂ : Measure (ι → ℝ))
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ∀ u : ι → ℝ, ν₁.map (fun v => ∑ i, u i * v i) = ν₂.map (fun v => ∑ i, u i * v i)) :
    ν₁ = ν₂ := by
  classical
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  have hL : (L : (ι → ℝ) → ℝ) = fun v => ∑ i, L (Pi.single i 1) * v i := by
    funext v
    conv_lhs => rw [show v = ∑ i, v i • (Pi.single i (1 : ℝ) : ι → ℝ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, map_smul, mul_comm]
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, hL, h]

lemma coe_measurable (X : Type*) [TopologicalSpace X] :
    Measurable (fun f : C(X, ℝ) => (f : X → ℝ)) :=
  measurable_pi_iff.2 fun x => ContinuousMap.measurable_eval x

lemma measure_ext_of_map_coe {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] (ν₁ ν₂ : Measure C(X, ℝ))
    (h : ν₁.map (fun f : C(X, ℝ) => (f : X → ℝ)) = ν₂.map (fun f : C(X, ℝ) => (f : X → ℝ))) :
    ν₁ = ν₂ := by
  have hm : (ContinuousMap.measurableSpace : MeasurableSpace C(X, ℝ)) =
      MeasurableSpace.comap (fun f : C(X, ℝ) => (f : X → ℝ)) MeasurableSpace.pi := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
      MeasurableSpace.comap_iSup]
    simp_rw [MeasurableSpace.comap_comp]
    rfl
  ext S hS
  rw [hm] at hS
  obtain ⟨T, hT, rfl⟩ := hS
  rw [← Measure.map_apply (coe_measurable X) hT, h, Measure.map_apply (coe_measurable X) hT]

theorem measure_ext_of_linEval {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    (ν₁ ν₂ : Measure C(X, ℝ)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ (p : ℕ) (x : Fin p → X) (u : Fin p → ℝ), ν₁.map (linEval x u) = ν₂.map (linEval x u)) :
    ν₁ = ν₂ := by
  apply measure_ext_of_map_coe
  set μ₁ := ν₁.map (fun f : C(X, ℝ) => (f : X → ℝ))
  set μ₂ := ν₂.map (fun f : C(X, ℝ) => (f : X → ℝ))
  have hfin : ∀ I : Finset X, μ₁.map I.restrict = μ₂.map I.restrict := by
    intro I
    apply measure_pi_ext_of_sum
    intro u
    let e := I.equivFin
    have key : ∀ ν : Measure C(X, ℝ), ((ν.map (fun f : C(X, ℝ) => (f : X → ℝ))).map I.restrict).map
        (fun v => ∑ i, u i * v i) =
          ν.map (linEval (fun j => (e.symm j : X)) (fun j => u (e.symm j))) := by
      intro ν
      have hs : Measurable (fun v : I → ℝ => ∑ i, u i * v i) := by fun_prop
      rw [Measure.map_map (Finset.measurable_restrict I) (coe_measurable X),
        Measure.map_map hs ((Finset.measurable_restrict I).comp (coe_measurable X))]
      congr 1
      funext f
      simp only [Function.comp_apply, linEval, Finset.restrict]
      exact (Equiv.sum_comp e.symm (fun i : I => u i * f i)).symm
    rw [key, key, h]
  have hP : IsProjectiveLimit μ₂ (fun I : Finset X => μ₁.map I.restrict) := fun I => (hfin I).symm
  exact IsProjectiveLimit.unique (fun I => rfl) hP

lemma probabilityMeasure_mk_map_id {E : Type*} [MeasurableSpace E] (ν : ProbabilityMeasure E)
    (h : IsProbabilityMeasure ((ν : Measure E).map id)) :
    (⟨(ν : Measure E).map id, h⟩ : ProbabilityMeasure E) = ν :=
  Subtype.ext Measure.map_id

/-- Prokhorov + identification of the limit by its finite-dimensional laws. -/
theorem tendstoInDistribution_of_tight {X : Type*} [MetricSpace X] [CompactSpace X]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (V : ℕ → Ω → C(X, ℝ))
    (hV : ∀ k, AEMeasurable (V k) μ) (htight : IsTightMeasureSet (Set.range fun k => μ.map (V k)))
    (γ : (p : ℕ) → (Fin p → X) → (Fin p → ℝ) → ProbabilityMeasure ℝ)
    (hfidi : ∀ (p : ℕ) (x : Fin p → X) (u : Fin p → ℝ),
      TendstoInDistribution (fun k ω => linEval x u (V k ω)) atTop id (fun _ => μ) (γ p x u : Measure ℝ)) :
    ∃ ν : ProbabilityMeasure C(X, ℝ), TendstoInDistribution V atTop id (fun _ => μ) (ν : Measure C(X, ℝ)) ∧
      ∀ p x u, (ν : Measure C(X, ℝ)).map (linEval x u) = (γ p x u : Measure ℝ) := by
  let P : ℕ → ProbabilityMeasure C(X, ℝ) := fun k => ⟨μ.map (V k), inferInstance⟩
  have hS : IsTightMeasureSet
      {((ν : ProbabilityMeasure C(X, ℝ)) : Measure C(X, ℝ)) | ν ∈ Set.range P} := by
    convert htight using 1
    ext m
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨P k, ⟨k, rfl⟩, rfl⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  have hmem : ∀ k, P k ∈ closure (Set.range P) := fun k => subset_closure ⟨k, rfl⟩
  -- every subsequential limit has the prescribed one-dimensional laws
  have hid : ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∀ ν' : ProbabilityMeasure C(X, ℝ),
      Tendsto (fun n => P (ψ n)) atTop (𝓝 ν') →
      ∀ p x u, (ν' : Measure C(X, ℝ)).map (linEval x u) = (γ p x u : Measure ℝ) := by
    intro ψ hψ ν' hν' p x u
    have h1 : TendstoInDistribution (fun n => V (ψ n)) atTop id (fun _ => μ)
        (ν' : Measure C(X, ℝ)) :=
      { forall_aemeasurable := fun n => hV (ψ n)
        aemeasurable_limit := aemeasurable_id
        tendsto := by
          rw [probabilityMeasure_mk_map_id]
          exact hν' }
    have h2 := h1.continuous_comp (continuous_linEval x u)
    have h3 : TendstoInDistribution (fun n ω => linEval x u (V (ψ n) ω)) atTop id (fun _ => μ)
        (γ p x u : Measure ℝ) :=
      { forall_aemeasurable := fun n => (hfidi p x u).forall_aemeasurable (ψ n)
        aemeasurable_limit := aemeasurable_id
        tendsto := (hfidi p x u).tendsto.comp hψ }
    have := tendstoInDistribution_unique _ h2 h3
    simpa [Function.comp_id, Measure.map_id] using this
  obtain ⟨ν, -, φ, hφ, hνlim⟩ := hK.tendsto_subseq hmem
  have hν := hid φ hφ.tendsto_atTop ν hνlim
  refine ⟨ν, ⟨hV, aemeasurable_id, ?_⟩, hν⟩
  rw [probabilityMeasure_mk_map_id]
  change Tendsto P atTop (𝓝 ν)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν', -, ψ, hψ, hlim⟩ := hK.tendsto_subseq (fun n => hmem (ns n))
  refine ⟨ψ, ?_⟩
  have hν' := hid (ns ∘ ψ) (hns.comp hψ.tendsto_atTop) ν' hlim
  have hEq : ν' = ν := ProbabilityMeasure.toMeasure_injective
    (measure_ext_of_linEval (ν' : Measure C(X, ℝ)) (ν : Measure C(X, ℝ))
      fun p x u => (hν' p x u).trans (hν p x u).symm)
  rw [← hEq]
  exact hlim

end StatFormal.Foundations.Donsker
