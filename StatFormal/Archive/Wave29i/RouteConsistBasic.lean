import StatFormal.Archive.Wave29i.Statements
import StatFormal.Lib.SworLaw.Quantise
import StatFormal.Archive.Wave26b.RouteICL

/-!
# Route — ICL `cor:consistency`, the population objective (untrusted)

* `Π_μ = μ^{⊗M}(· | D_M)` is finite and carried by `D_M`; a probability law when `μ^{⊗M}(D_M) > 0`, and then so is
  its one-slot marginal `Π̄_μ`; `∫ g dΠ̄_μ = M⁻¹ Σ_s ∫ g(t_s) dΠ_μ(t)`.
* `G_μ ∈ [0, B_L]` and `ρ_μ ∈ [K_min, K_max]` are continuous in the query; `R(μ) ≥ −λ_cov log K_max` on the
  admissible class.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave29i

open StatFormal.Wave11b (distinctSet ctxLaw Admissible jSwor collision)
open StatFormal.Wave26b (poolLaw riskIid)
open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.Foundations.SworLaw

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

namespace ConsistR

lemma distinctSet_eq (M : ℕ) : (distinctSet M : Set (Fin M → Z)) = {t | Function.Injective t} := rfl

lemma ctxLaw_eq (μ : Measure Z) (M : ℕ) :
    ctxLaw μ M = ProbabilityTheory.cond (Measure.pi fun _ : Fin M => μ) {t | Function.Injective t} := rfl

instance ctxLaw_isFinite (μ : Measure Z) [IsFiniteMeasure μ] (M : ℕ) : IsFiniteMeasure (ctxLaw μ M) := by
  rw [ctxLaw_eq]; infer_instance

lemma ctxLaw_isProb {μ : Measure Z} [IsFiniteMeasure μ] {M : ℕ}
    (h : 0 < Measure.pi (fun _ : Fin M => μ) (distinctSet M)) : IsProbabilityMeasure (ctxLaw μ M) :=
  cond_isProbabilityMeasure h.ne'

lemma ctxLaw_compl (μ : Measure Z) (M : ℕ) : ctxLaw μ M {t | Function.Injective t}ᶜ = 0 :=
  cond_compl_eq_zero _ (measurableSet_injective M)

instance consistMarg_isFinite (μ : Measure Z) [IsFiniteMeasure μ] (M : ℕ) : IsFiniteMeasure (consistMarg μ M) := by
  refine ⟨?_⟩
  unfold consistMarg
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · rw [Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top ?_ (measure_lt_top _ _)
    rw [ENNReal.inv_lt_top]
    exact_mod_cast hM

lemma consistMarg_univ (μ : Measure Z) [IsFiniteMeasure μ] {M : ℕ} (hM : 1 ≤ M) [IsProbabilityMeasure (ctxLaw μ M)] :
    IsProbabilityMeasure (consistMarg μ M) := by
  refine ⟨?_⟩
  unfold consistMarg
  rw [Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ, preimage_univ, measure_univ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (show M ≠ 0 by omega)) (ENNReal.natCast_ne_top M)

lemma integral_consistMarg (μ : Measure Z) [IsFiniteMeasure μ] (M : ℕ) {g : Z → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂(consistMarg μ M) = (M : ℝ)⁻¹ * ∑ s : Fin M, ∫ t, g (t s) ∂(ctxLaw μ M) := by
  unfold consistMarg
  rw [integral_smul_measure, integral_finsetSum_measure, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_map (measurable_pi_apply s).aemeasurable hg.aestronglyMeasurable]
  · intro s _
    exact StatFormal.Wave26b.integrable_of_continuous_bdd _ hg

/-! ### The per-query risk and the coverage -/

section Bounds
variable {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {BL : ℝ}

lemma continuousOn_query (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    {t : Fin M → Z} (ht : Function.Injective t) : Continuous fun x => L x t :=
  hL.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨mem_univ _, ht⟩

lemma continuousOn_slot (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    (x : Z) : ContinuousOn (L x) {t | Function.Injective t} :=
  hL.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht => ⟨mem_univ _, ht⟩

lemma continuous_consistG (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) (μ : Measure Z) [IsFiniteMeasure μ] : Continuous (consistG L μ) :=
  continuous_integral_carried (isOpen_injective M) hL
    (fun x t => by rw [abs_of_nonneg (hLb x t).1]; exact (hLb x t).2) (ctxLaw μ M) (ctxLaw_compl μ M)

lemma consistG_mem (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) (μ : Measure Z) [IsProbabilityMeasure (ctxLaw μ M)]
    (z : Z) : 0 ≤ consistG L μ z ∧ consistG L μ z ≤ BL := by
  unfold consistG
  refine ⟨integral_nonneg fun t => (hLb z t).1, ?_⟩
  calc ∫ t, L z t ∂(ctxLaw μ M) ≤ ∫ _, BL ∂(ctxLaw μ M) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => (hLb z t).1) (integrable_const _)
          (Eventually.of_forall fun t => (hLb z t).2)
    _ = BL := by simp

end Bounds

/-- The lower bound `R(μ) ≥ −λ_cov log K_max` for `μ^{⊗M}(D_M) > 0`. -/
lemma consistRisk_ge {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} {BL Kmin Kmax lcov : ℝ} (hM : 1 ≤ M)
    (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (hlcov : 0 ≤ lcov) (P₀ : Measure Z) [IsProbabilityMeasure P₀] (μ : Measure Z) [IsFiniteMeasure μ]
    (hpos : 0 < Measure.pi (fun _ : Fin M => μ) (distinctSet M)) :
    -(lcov * Real.log Kmax) ≤ consistRisk L Kk lcov P₀ μ := by
  haveI := ctxLaw_isProb hpos
  haveI := consistMarg_univ μ hM
  unfold consistRisk PhiC
  have h1 : 0 ≤ ∫ z, consistG L μ z ∂P₀ := integral_nonneg fun z => (consistG_mem hLb μ z).1
  have hρc := StatFormal.Wave26b.continuous_rhoC hK hKb hKmin (consistMarg μ M)
  have hmem := StatFormal.Wave26b.rhoC_mem hK hKb (consistMarg μ M)
  have h2 : ∫ z, Real.log (rhoC Kk (consistMarg μ M) z) ∂P₀ ≤ Real.log Kmax := by
    have hcont : Continuous fun z => Real.log (rhoC Kk (consistMarg μ M) z) :=
      hρc.log fun z => (hKmin.trans_le (hmem z).1).ne'
    calc ∫ z, Real.log (rhoC Kk (consistMarg μ M) z) ∂P₀ ≤ ∫ _, Real.log Kmax ∂P₀ :=
          integral_mono (StatFormal.Wave26b.integrable_of_continuous_bdd P₀ hcont) (integrable_const _) fun z =>
            Real.log_le_log (hKmin.trans_le (hmem z).1) (hmem z).2
      _ = Real.log Kmax := by simp
  nlinarith

end ConsistR

end StatFormal.Wave29i
