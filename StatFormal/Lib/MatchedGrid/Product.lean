import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Squared Euclidean norms under product laws

For probability measures `ν j` and measurable coordinate maps `g j`,
`∫⁻ ‖(g j (w j))_j‖ₑ² ∂(⊗ ν) = Σ_j ∫⁻ ofReal ((g j x)²) ∂ν j`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Foundations.MatchedGrid

variable {K : ℕ}

lemma enorm_sq_toLp (v : Fin K → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin K))‖ₑ ^ 2 = ∑ j, ENNReal.ofReal (v j ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

lemma lintegral_enorm_sq_pi {X : Fin K → Type*} [∀ j, MeasurableSpace (X j)]
    (ν : (j : Fin K) → Measure (X j)) [∀ j, IsProbabilityMeasure (ν j)]
    (g : (j : Fin K) → X j → ℝ) (hg : ∀ j, Measurable (g j)) :
    ∫⁻ w, ‖(WithLp.toLp 2 (fun j => g j (w j)) : EuclideanSpace ℝ (Fin K))‖ₑ ^ 2 ∂(Measure.pi ν) =
      ∑ j, ∫⁻ x, ENNReal.ofReal (g j x ^ 2) ∂(ν j) := by
  simp_rw [enorm_sq_toLp]
  rw [lintegral_finsetSum _ (fun j _ => ?_)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hm : Measurable fun x : X j => ENNReal.ofReal (g j x ^ 2) :=
      ENNReal.measurable_ofReal.comp ((hg j).pow_const 2)
    rw [← (measurePreserving_eval ν j).lintegral_comp hm]
  · exact ENNReal.measurable_ofReal.comp (((hg j).comp (measurable_pi_apply j)).pow_const 2)

lemma lintegral_enorm_sq_pi_map (ν : Fin K → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] :
    ∫⁻ z, ‖z‖ₑ ^ 2 ∂((Measure.pi ν).map (WithLp.toLp 2 : (Fin K → ℝ) → EuclideanSpace ℝ (Fin K))) =
      ∑ j, ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(ν j) := by
  rw [lintegral_map (by fun_prop) (WithLp.measurable_toLp 2 _)]
  exact lintegral_enorm_sq_pi ν (fun _ x => x) (fun _ => measurable_id)

end StatFormal.Foundations.MatchedGrid
