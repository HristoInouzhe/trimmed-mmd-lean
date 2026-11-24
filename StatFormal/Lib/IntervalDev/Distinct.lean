import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option linter.style.longLine false

/-!
# Samples from atomless laws have pairwise distinct points almost surely

For probabilities `P, Q` on `ℝ` and two independent samples `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}`:

* `prod_diag_null`: `(P ⊗ Q){x = y} = 0` when `Q` is atomless (Fubini: `∫ Q{x} dP(x) = 0`);
* `pi_coord_eq_null`: `P^{⊗n}{X_i = X_j} = 0` for `i ≠ j`, `P` atomless (the coordinates are independent with law `P`);
* `prod_pi_cross_null`: `(P^{⊗n} ⊗ Q^{⊗m}){X_i = Y_j} = 0` when `Q` is atomless;
* `prod_pi_not_distinct_null`: the pooled sample has a repeated value with probability `0` when both are atomless
  (trimmed-mmd S4 :1088-1089, "with the pooled points pairwise distinct (almost surely, as `P` and `Q` have densities)").
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace StatFormal.IntervalDev

/-- The diagonal is `P ⊗ Q`-null when `Q` is atomless. -/
theorem prod_diag_null (P Q : Measure ℝ) [SFinite P] [SFinite Q] [NullSingletonClass Q] :
    (P.prod Q) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  simp

/-- Two distinct coordinates of an i.i.d. sample from an atomless law differ almost surely. -/
theorem pi_coord_eq_null (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) : (Measure.pi fun _ : Fin n => P) {ω | ω i = ω j} = 0 := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin n => P) (X := fun _ x => x)
    (fun _ => aemeasurable_id)).indepFun hij
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 hind
  rw [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => P) j).map_eq] at hmap
  have hm : Measurable (fun ω : Fin n → ℝ => (ω i, ω j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have : {ω : Fin n → ℝ | ω i = ω j} = (fun ω => (ω i, ω j)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := rfl
  rw [this, ← Measure.map_apply hm (measurableSet_eq_fun measurable_fst measurable_snd), hmap]
  exact prod_diag_null P P

/-- A point of the first sample equals a point of the second with probability `0` when `Q` is atomless. -/
theorem prod_pi_cross_null (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [NullSingletonClass Q] {n m : ℕ} (i : Fin n) (j : Fin m) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) {z | z.1 i = z.2 j} = 0 := by
  have hmap : ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).map
      (Prod.map (fun ω : Fin n → ℝ => ω i) (fun ω : Fin m → ℝ => ω j)) = P.prod Q := by
    rw [← Measure.map_prod_map _ _ (measurable_pi_apply i) (measurable_pi_apply j),
      (measurePreserving_eval (fun _ : Fin n => P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin m => Q) j).map_eq]
  have : {z : (Fin n → ℝ) × (Fin m → ℝ) | z.1 i = z.2 j} =
      Prod.map (fun ω : Fin n → ℝ => ω i) (fun ω : Fin m → ℝ => ω j) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := rfl
  rw [this, ← Measure.map_apply ((measurable_pi_apply i).prodMap (measurable_pi_apply j))
    (measurableSet_eq_fun measurable_fst measurable_snd), hmap]
  exact prod_diag_null P Q

/-- **The pooled points are pairwise distinct almost surely** when both laws are atomless. -/
theorem prod_pi_not_distinct_null (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [NullSingletonClass P] [NullSingletonClass Q] (n m : ℕ) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
      {z | ¬ (Function.Injective z.1 ∧ Function.Injective z.2 ∧ ∀ i j, z.1 i ≠ z.2 j)} = 0 := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  have h1 : ∀ i i' : Fin n, μ {z | i ≠ i' ∧ z.1 i = z.1 i'} = 0 := fun i i' => by
    by_cases hii : i = i'
    · simp [hii]
    · refine measure_mono_null (t := {ω : Fin n → ℝ | ω i = ω i'} ×ˢ univ) (fun z hz => ⟨hz.2, trivial⟩) ?_
      rw [hμ, Measure.prod_prod, pi_coord_eq_null P hii, zero_mul]
  have h2 : ∀ j j' : Fin m, μ {z | j ≠ j' ∧ z.2 j = z.2 j'} = 0 := fun j j' => by
    by_cases hjj : j = j'
    · simp [hjj]
    · refine measure_mono_null (t := univ ×ˢ {ω : Fin m → ℝ | ω j = ω j'}) (fun z hz => ⟨trivial, hz.2⟩) ?_
      rw [hμ, Measure.prod_prod, pi_coord_eq_null Q hjj, mul_zero]
  have h3 : ∀ (i : Fin n) (j : Fin m), μ {z | z.1 i = z.2 j} = 0 := fun i j => prod_pi_cross_null P Q i j
  refine measure_mono_null (t := (⋃ i, ⋃ i', {z | i ≠ i' ∧ z.1 i = z.1 i'}) ∪
    (⋃ j, ⋃ j', {z | j ≠ j' ∧ z.2 j = z.2 j'}) ∪ ⋃ i, ⋃ j, {z | z.1 i = z.2 j}) ?_ ?_
  · intro z hz
    simp only [mem_ofPred_eq, not_and_or, Function.Injective, not_forall, not_not] at hz
    rcases hz with ⟨a, b, hab, hne⟩ | ⟨a, b, hab, hne⟩ | ⟨a, b, hab⟩
    · exact Or.inl (Or.inl (mem_iUnion₂.2 ⟨a, b, hne, hab⟩))
    · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨a, b, hne, hab⟩))
    · exact Or.inr (mem_iUnion₂.2 ⟨a, b, hab⟩)
  · exact measure_union_null (measure_union_null (measure_iUnion_null fun i => measure_iUnion_null (h1 i))
      (measure_iUnion_null fun j => measure_iUnion_null (h2 j))) (measure_iUnion_null fun i => measure_iUnion_null (h3 i))

end StatFormal.IntervalDev
