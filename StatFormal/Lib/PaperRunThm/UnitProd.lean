import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Products with a one-point factor (library)

Library component (untrusted). The certified split-sample results of waves 30tv and 31ta are stated on
`U × sample` for an auxiliary randomisation `U` with law `ν`; the paper's run has none (`U = Unit`, `ν = dirac ()`).
These lemmas transport a statement about a set of `Unit × Ω` that does not depend on the `Unit` coordinate to its
section `S ⊆ Ω`:

* `unit_prod_set`: such a set is `univ ×ˢ S`;
* `dirac_prod_unit_set`: its measure under `dirac () ⊗ μ` is `μ S` (`Measure.prod_prod`);
* `measurableSet_of_unit_set`: it is measurable only if `S` is (preimage under the measurable `Prod.mk ()`).
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.PaperRunThm

/-- A set of `Unit × Ω` whose membership does not depend on the `Unit` coordinate is `univ ×ˢ S`, with `S` its
section at `()`. -/
theorem unit_prod_set {Ω : Type*} (S : Set Ω) (T : Set (Unit × Ω)) (h : ∀ ω, ((), ω) ∈ T ↔ ω ∈ S) :
    T = (univ : Set Unit) ×ˢ S := by
  ext ⟨u, ω⟩
  cases u
  simp only [Set.mem_prod, Set.mem_univ, true_and]
  exact h ω

/-- The measure under `dirac () ⊗ μ` of a set of `Unit × Ω` with section `S` is `μ S`. -/
theorem dirac_prod_unit_set {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (S : Set Ω)
    (T : Set (Unit × Ω)) (h : ∀ ω, ((), ω) ∈ T ↔ ω ∈ S) : ((Measure.dirac ()).prod μ) T = μ S := by
  rw [unit_prod_set S T h, Measure.prod_prod, measure_univ, one_mul]

/-- A measurable set of `Unit × Ω` has a measurable section `S` at `()`. -/
theorem measurableSet_of_unit_set {Ω : Type*} [MeasurableSpace Ω] (S : Set Ω) (T : Set (Unit × Ω))
    (h : ∀ ω, ((), ω) ∈ T ↔ ω ∈ S) (hT : MeasurableSet T) : MeasurableSet S := by
  have e : S = Prod.mk () ⁻¹' T := by
    ext ω; exact (h ω).symm
  rw [e]
  exact measurable_prodMk_left hT

end StatFormal.PaperRunThm
