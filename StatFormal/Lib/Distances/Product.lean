import StatFormal.Lib.Distances.TV
import TauCeti.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Total variation and relative entropy of product measures

Library component F.H (part 2). Untrusted library code.

Conventions: `tvDist` is the usual total-variation distance `sup_A |μ A − ν A|`
(`StatFormal/Foundations/Distances/TV.lean`); `μ^m` is `Measure.pi fun _ : Fin m => μ`.

## Main results

* `tvDist_prod_left_le`, `tvDist_prod_right_le`: a common factor does not increase TV;
* `tvDist_prod_prod_le`: `TV(μ ⊗ μ', ν ⊗ ν') ≤ TV(μ, ν) + TV(μ', ν')`;
* `tvDist_pi_le`: `TV(μ^m, ν^m) ≤ m · TV(μ, ν)` (hybrid argument via `piFinSuccAbove`);
* `klDiv_pi_eq`: `KL(μ^m ‖ ν^m) = m · KL(μ ‖ ν)` (from Tau Ceti's `klDiv_prod_prod`);
* `tvDist_pi_le_sqrt_klDiv`: `TV(μ^m, ν^m) ≤ √(m · KL(μ‖ν) / 2)` when `KL(μ‖ν) ≠ ⊤`.
-/

noncomputable section
open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace StatFormal.Distances

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem measureReal_mem_Icc {ρ : Measure α} [IsProbabilityMeasure ρ] (s : Set α) :
    ρ.real s ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, (measureReal_mono (subset_univ s)).trans_eq probReal_univ⟩

/-- A common right factor does not increase total variation. -/
theorem tvDist_prod_left_le {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure β) [IsProbabilityMeasure ρ] :
    tvDist (μ.prod ρ) (ν.prod ρ) ≤ tvDist μ ν := by
  refine tvDist_le_of_forall fun A hA => ?_
  have hm : Measurable fun x => ρ (Prod.mk x ⁻¹' A) := measurable_measure_prodMk_left hA
  have hreal : ∀ σ : Measure α, IsProbabilityMeasure σ →
      (σ.prod ρ).real A = ∫ x, ρ.real (Prod.mk x ⁻¹' A) ∂σ := fun σ _ => by
    rw [measureReal_def, Measure.prod_apply hA,
      ← integral_toReal hm.aemeasurable (ae_of_all _ fun x => measure_lt_top _ _)]
    rfl
  rw [hreal μ inferInstance, hreal ν inferInstance]
  have := abs_integral_sub_le_mul_tvDist (μ := μ) (ν := ν) hm.ennreal_toReal
    (fun x => measureReal_mem_Icc (ρ := ρ) (Prod.mk x ⁻¹' A))
  simpa [measureReal_def] using this

/-- A common left factor does not increase total variation. -/
theorem tvDist_prod_right_le {μ ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure α) [IsProbabilityMeasure ρ] :
    tvDist (ρ.prod μ) (ρ.prod ν) ≤ tvDist μ ν := by
  refine tvDist_le_of_forall fun A hA => ?_
  have hm : Measurable fun y => ρ ((fun x => (x, y)) ⁻¹' A) := measurable_measure_prodMk_right hA
  have hreal : ∀ σ : Measure β, IsProbabilityMeasure σ →
      (ρ.prod σ).real A = ∫ y, ρ.real ((fun x => (x, y)) ⁻¹' A) ∂σ := fun σ _ => by
    rw [measureReal_def, Measure.prod_apply_symm hA,
      ← integral_toReal hm.aemeasurable (ae_of_all _ fun x => measure_lt_top _ _)]
    rfl
  rw [hreal μ inferInstance, hreal ν inferInstance]
  have := abs_integral_sub_le_mul_tvDist (μ := μ) (ν := ν) hm.ennreal_toReal
    (fun y => measureReal_mem_Icc (ρ := ρ) ((fun x => (x, y)) ⁻¹' A))
  simpa [measureReal_def] using this

/-- Subadditivity of TV under products. -/
theorem tvDist_prod_prod_le {μ ν : Measure α} {μ' ν' : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
    tvDist (μ.prod μ') (ν.prod ν') ≤ tvDist μ ν + tvDist μ' ν' :=
  (tvDist_triangle (ν := ν.prod μ')).trans
    (add_le_add (tvDist_prod_left_le μ') (tvDist_prod_right_le ν))

/-- `μ^{m+1}` is the image of `μ ⊗ μ^m` under the measurable equivalence `piFinSuccAbove`. -/
theorem pi_succ_eq_map (μ : Measure α) [IsProbabilityMeasure μ] (m : ℕ) :
    Measure.pi (fun _ : Fin (m + 1) => μ) =
      (μ.prod (Measure.pi fun _ : Fin m => μ)).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) 0).symm :=
  ((MeasurePreserving.symm _ (measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => μ) 0)).map_eq).symm

/-- **TV tensorisation (hybrid argument)**: `TV(μ^m, ν^m) ≤ m · TV(μ, ν)`. -/
theorem tvDist_pi_le (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : ℕ) :
    tvDist (Measure.pi fun _ : Fin m => μ) (Measure.pi fun _ : Fin m => ν) ≤ m * tvDist μ ν := by
  induction m with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ), Measure.pi_of_empty (fun _ : Fin 0 => ν)]
    simp
  | succ m ih =>
    rw [pi_succ_eq_map μ m, pi_succ_eq_map ν m]
    calc _ ≤ tvDist (μ.prod (Measure.pi fun _ : Fin m => μ))
          (ν.prod (Measure.pi fun _ : Fin m => ν)) := tvDist_map_le (MeasurableEquiv.measurable _)
      _ ≤ tvDist μ ν + tvDist (Measure.pi fun _ : Fin m => μ) (Measure.pi fun _ : Fin m => ν) :=
          tvDist_prod_prod_le
      _ ≤ tvDist μ ν + m * tvDist μ ν := by gcongr
      _ = ((m + 1 : ℕ) : ℝ) * tvDist μ ν := by push_cast; ring

/-- **KL tensorisation**: `KL(μ^m ‖ ν^m) = m · KL(μ ‖ ν)`. -/
theorem klDiv_pi_eq (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : ℕ) :
    klDiv (Measure.pi fun _ : Fin m => μ) (Measure.pi fun _ : Fin m => ν) = m * klDiv μ ν := by
  induction m with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ), Measure.pi_of_empty (fun _ : Fin 0 => ν)]
    simp
  | succ m ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) 0
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) 0).map_eq
    have hprod : klDiv (Measure.pi fun _ : Fin (m + 1) => μ) (Measure.pi fun _ : Fin (m + 1) => ν)
        = klDiv (μ.prod (Measure.pi fun _ : Fin m => μ))
            (ν.prod (Measure.pi fun _ : Fin m => ν)) := by
      refine le_antisymm ?_ ?_
      · rw [pi_succ_eq_map μ m, pi_succ_eq_map ν m]
        exact klDiv_map_le _ _ (MeasurableEquiv.measurable _)
      · have h := klDiv_map_le (Measure.pi fun _ : Fin (m + 1) => μ)
          (Measure.pi fun _ : Fin (m + 1) => ν) e.measurable
        rw [hμ, hν] at h
        exact h
    rw [hprod, TauCeti.klDiv_prod_prod, ih]
    push_cast
    ring

/-- **Pinsker + tensorisation**: `TV(μ^m, ν^m) ≤ √(m · KL(μ‖ν) / 2)` when `KL(μ‖ν) ≠ ⊤`. -/
theorem tvDist_pi_le_sqrt_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (m : ℕ) (h : klDiv μ ν ≠ ∞) :
    tvDist (Measure.pi fun _ : Fin m => μ) (Measure.pi fun _ : Fin m => ν) ≤
      √(m * (klDiv μ ν).toReal / 2) := by
  have hpi := klDiv_pi_eq μ ν m
  have hne : klDiv (Measure.pi fun _ : Fin m => μ) (Measure.pi fun _ : Fin m => ν) ≠ ∞ := by
    rw [hpi]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) h
  have := tvDist_le_sqrt_klDiv hne
  rwa [hpi, ENNReal.toReal_mul, ENNReal.toReal_natCast] at this

end StatFormal.Distances
