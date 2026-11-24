import StatFormal.Archive.RobustEquality.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Data.EReal.Operations

/-!
# Proof: `lem:gibbs` (Gibbs variational principle)

Route (the paper's): with `Γ* = ν.tilted g`, `llr Γ ν = llr Γ Γ* + g - log Z` `Γ`-a.e., so
`E_Γ g - KL(Γ‖ν) = log Z - KL(Γ‖Γ*) ≤ log Z`, with equality iff `Γ = Γ*` (converse Gibbs).
-/

noncomputable section
open Real MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatFormal.RobustEquality

variable {K : Type} [MeasurableSpace K]

/-- Core computation in the finite-KL case. -/
lemma gibbs_finite_case (ν : Measure K) [IsFiniteMeasure ν] [NeZero ν]
    (g : K → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B)
    (Γ : Measure K) [IsProbabilityMeasure Γ] (hac : Γ ≪ ν) (hint : Integrable (llr Γ ν) Γ) :
    (∫ x, g x ∂Γ) - ∫ x, llr Γ ν x ∂Γ ≤ Real.log (∫ x, Real.exp (g x) ∂ν) ∧
    ((∫ x, g x ∂Γ) - ∫ x, llr Γ ν x ∂Γ = Real.log (∫ x, Real.exp (g x) ∂ν) →
      Γ = ν.tilted g) := by
  have hexp : Integrable (fun x => Real.exp (g x)) ν := by
    refine Integrable.of_bound (hg.exp.aestronglyMeasurable) (Real.exp B) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hB x))
  have hgΓ : Integrable g Γ := by
    refine Integrable.of_bound hg.aestronglyMeasurable B ?_
    exact Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x
  have : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted hexp
  have hacτ : Γ ≪ ν.tilted g := hac.trans (absolutelyContinuous_tilted hexp)
  have hintτ : Integrable (llr Γ (ν.tilted g)) Γ :=
    integrable_llr_tilted_right hac hgΓ hint hexp
  have heq := integral_llr_tilted_right hac hgΓ hexp hint
  have hnn := integral_llr_add_sub_measure_univ_nonneg hacτ hintτ
  simp only [probReal_univ, add_sub_cancel_right] at hnn
  refine ⟨by linarith, fun h => ?_⟩
  have h0 : ∫ x, llr Γ (ν.tilted g) x ∂Γ = 0 := by linarith
  have hkl : klDiv Γ (ν.tilted g) = 0 := by
    rw [klDiv_of_ac_of_integrable hacτ hintτ, h0]
    simp
  exact klDiv_eq_zero_iff.mp hkl

theorem lem_gibbs : Claims.lem_gibbs := by
  intro K _ ν _ hν g hg ⟨B, hB⟩
  have : NeZero ν := ⟨fun h => hν (by simp [h])⟩
  have hexp : Integrable (fun x => Real.exp (g x)) ν := by
    refine Integrable.of_bound (hg.exp.aestronglyMeasurable) (Real.exp B) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hB x))
  have hτ : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted hexp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- membership: the tilted measure attains `log Z`
    refine ⟨ν.tilted g, hτ, ?_⟩
    have hac : ν.tilted g ≪ ν := tilted_absolutelyContinuous ν g
    have hll : llr (ν.tilted g) ν =ᵐ[ν.tilted g]
        fun x => g x - Real.log (∫ x, Real.exp (g x) ∂ν) :=
      hac.ae_le (log_rnDeriv_tilted_left_self hexp)
    have hgτ : Integrable g (ν.tilted g) := by
      refine Integrable.of_bound hg.aestronglyMeasurable B ?_
      exact Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x
    have hint : Integrable (llr (ν.tilted g) ν) (ν.tilted g) := by
      rw [integrable_congr hll]
      exact hgτ.sub (integrable_const _)
    have hval : ∫ x, llr (ν.tilted g) ν x ∂(ν.tilted g) =
        (∫ x, g x ∂(ν.tilted g)) - Real.log (∫ x, Real.exp (g x) ∂ν) := by
      rw [integral_congr_ae hll, integral_sub hgτ (integrable_const _)]
      simp
    rw [klRef, ite_eq_left ⟨hac, hint⟩, hval, ← EReal.coe_sub]
    congr 1
    ring
  · -- upper bound
    rintro v ⟨Γ, hΓ, rfl⟩
    rw [klRef]
    split_ifs with h
    · rw [← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (gibbs_finite_case ν g hg B hB Γ h.1 h.2).1
    · rw [EReal.sub_top]
      exact bot_le
  · -- equality case
    intro Γ hΓ heq
    rw [klRef] at heq
    split_ifs at heq with h
    · rw [← EReal.coe_sub] at heq
      exact (gibbs_finite_case ν g hg B hB Γ h.1 h.2).2 (EReal.coe_eq_coe_iff.mp heq)
    · rw [EReal.sub_top] at heq
      exact absurd heq.symm (EReal.coe_ne_bot _)

example : Claims.lem_gibbs := lem_gibbs

end StatFormal.RobustEquality
