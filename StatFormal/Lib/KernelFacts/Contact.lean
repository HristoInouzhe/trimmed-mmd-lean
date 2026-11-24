import StatFormal.Lib.Distances.TV
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Connected.Clopen

/-!
# Contact of the excess parts of two laws with continuous densities (library, untrusted)

For `P = p·μ`, `Q = q·μ` with `p, q ≥ 0` continuous on a topological space `X` and `μ` positive on nonempty open sets:
* `mem_support_sub_inf`: every point with `q x < p x` lies in the support of the excess `P₀ = P − P ⊓ Q`;
* `eq_of_le_of_prob`, `withDensity_le_of_le`: `p ≤ q` everywhere gives `P ≤ Q`, hence `P = Q` for probability measures;
* `support_sub_inf_inter_nonempty`: if moreover `X` is connected, `P ≠ Q` and `{p = q}` has empty interior, the supports of `P₀` and
  `Q₀ = Q − P ⊓ Q` meet (the closures of `{p > q}` and `{q > p}` are closed, cover `X`, and are both nonempty);
* `tvDist_pos_of_ne`: `TV(P, Q) > 0` for distinct finite measures;
* `tvDist_lt_one_of_common`: a nonzero measure below both probability measures forces `TV(P, Q) < 1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.KernelFacts

section TV

variable {α : Type*} [MeasurableSpace α]

/-- Distinct finite measures are at positive total-variation distance. -/
theorem tvDist_pos_of_ne {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≠ Q) :
    0 < StatFormal.Distances.tvDist P Q := by
  refine lt_of_le_of_ne (StatFormal.Distances.tvDist_nonneg P Q) (fun h0 => h ?_)
  ext A hA
  have h1 := StatFormal.Distances.abs_measureReal_sub_le_tvDist (μ := P) (ν := Q) hA
  rw [← h0, abs_nonpos_iff, sub_eq_zero] at h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P A) (measure_ne_top Q A)).1 h1

/-- **A common part bounds TV away from `1`.** If a measure `M` with `M(univ) ≠ 0` lies below both probability measures `P` and `Q`,
then `TV(P,Q) ≤ 1 − M(univ) < 1`. -/
theorem tvDist_lt_one_of_common {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (M : Measure α)
    (hMP : M ≤ P) (hMQ : M ≤ Q) (hM : M univ ≠ 0) : StatFormal.Distances.tvDist P Q < 1 := by
  haveI : IsFiniteMeasure M := isFiniteMeasure_of_le P hMP
  have hMpos : 0 < M.real univ := ENNReal.toReal_pos hM (measure_ne_top M univ)
  have rP : ∀ A, M.real A ≤ P.real A := fun A =>
    ENNReal.toReal_mono (measure_ne_top P A) (Measure.le_iff'.1 hMP A)
  have rQ : ∀ A, M.real A ≤ Q.real A := fun A =>
    ENNReal.toReal_mono (measure_ne_top Q A) (Measure.le_iff'.1 hMQ A)
  have key : ∀ A, MeasurableSet A → |P.real A - Q.real A| ≤ 1 - M.real univ := by
    intro A hA
    have eP := probReal_compl_eq_one_sub (μ := P) hA
    have eQ := probReal_compl_eq_one_sub (μ := Q) hA
    have eM := measureReal_compl (μ := M) hA
    have a1 := rP Aᶜ
    have a2 := rQ Aᶜ
    have a3 := rP A
    have a4 := rQ A
    rw [abs_le]; constructor <;> linarith
  exact (StatFormal.Distances.tvDist_le_of_forall key).trans_lt (by linarith)

end TV

section Contact

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Pointwise ordered densities give ordered measures. -/
theorem withDensity_le_of_le (μ : Measure X) {p q : X → ℝ} (hpq : ∀ x, p x ≤ q x) :
    μ.withDensity (fun x => ENNReal.ofReal (p x)) ≤ μ.withDensity (fun x => ENNReal.ofReal (q x)) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpq x)

/-- Ordered probability measures are equal. -/
theorem eq_of_le_of_prob {α : Type*} [MeasurableSpace α] {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : P ≤ Q) : P = Q := by
  ext s hs
  refine le_antisymm (Measure.le_iff'.1 h s) ?_
  have h1 : P sᶜ ≤ Q sᶜ := Measure.le_iff'.1 h sᶜ
  rw [prob_compl_eq_one_sub hs, prob_compl_eq_one_sub hs] at h1
  have hP : P s ≤ 1 := prob_le_one
  have hQ : Q s ≤ 1 := prob_le_one
  exact (ENNReal.sub_le_sub_iff_left hQ ENNReal.one_ne_top).1 h1

/-- **Points of excess are in the support of the excess.** If `q x < p x`, then `x ∈ supp(P − P ⊓ Q)`. -/
theorem mem_support_sub_inf (μ : Measure X) [μ.IsOpenPosMeasure] {p q : X → ℝ} (hp : Continuous p) (hq : Continuous q)
    (hq0 : ∀ x, 0 ≤ q x) (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : P = μ.withDensity fun x => ENNReal.ofReal (p x)) (hQ : Q = μ.withDensity fun x => ENNReal.ofReal (q x)) {x : X}
    (hx : q x < p x) : x ∈ (P - P ⊓ Q).support := by
  rw [Measure.mem_support_iff_forall]
  intro N hN
  set ε := (p x - q x) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hWo : IsOpen {y | q y + ε < p y} := isOpen_lt (hq.add continuous_const) hp
  have hxW : x ∈ {y | q y + ε < p y} := by simp only [mem_ofPred_eq]; rw [hε]; linarith
  obtain ⟨O, hOsub, hOo, hxO⟩ := mem_nhds_iff.1 (inter_mem hN (hWo.mem_nhds hxW))
  have hOm : MeasurableSet O := hOo.measurableSet
  have hμO : μ O ≠ 0 := (hOo.measure_pos μ ⟨x, hxO⟩).ne'
  have : IsFiniteMeasure (P ⊓ Q) := isFiniteMeasure_of_le P inf_le_left
  have hsub : P O - Q O ≤ (P - P ⊓ Q) O := by
    rw [Measure.sub_apply hOm inf_le_left]
    exact tsub_le_tsub_left (Measure.le_iff'.1 inf_le_right O) _
  have hlow : Q O + ENNReal.ofReal ε * μ O ≤ P O := by
    rw [hP, hQ, withDensity_apply _ hOm, withDensity_apply _ hOm, ← setLIntegral_const,
      ← lintegral_add_right _ measurable_const]
    refine setLIntegral_mono (ENNReal.measurable_ofReal.comp hp.measurable) fun y hy => ?_
    rw [← ENNReal.ofReal_add (hq0 y) hε0.le]
    exact ENNReal.ofReal_le_ofReal (hOsub hy).2.le
  have hQO : Q O ≠ ∞ := measure_ne_top Q O
  have hpos : 0 < P O - Q O := by
    rw [tsub_pos_iff_lt]
    refine lt_of_lt_of_le (ENNReal.lt_add_right hQO ?_) hlow
    exact mul_ne_zero (by simpa using hε0) hμO
  exact (hpos.trans_le hsub).trans_le (measure_mono fun y hy => (hOsub hy).1)

/-- **Contact on a connected space.** For probability measures `P = p·μ ≠ Q = q·μ` with continuous nonnegative densities on a
connected space, `μ` positive on nonempty open sets, and `{p = q}` with empty interior, the supports of `P − P ⊓ Q` and
`Q − P ⊓ Q` meet. -/
theorem support_sub_inf_inter_nonempty [ConnectedSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] {p q : X → ℝ}
    (hp : Continuous p) (hq : Continuous q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P = μ.withDensity fun x => ENNReal.ofReal (p x)) (hQ : Q = μ.withDensity fun x => ENNReal.ofReal (q x))
    (hPQ : P ≠ Q) (hint : interior {x | p x = q x} = ∅) :
    ((P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support).Nonempty := by
  set A := {x | q x < p x}
  set B := {x | p x < q x}
  have hA : A.Nonempty := by
    by_contra hA
    rw [not_nonempty_iff_eq_empty] at hA
    have hle : ∀ x, p x ≤ q x := fun x => not_lt.1 fun h => (hA ▸ (show x ∈ A from h) : x ∈ (∅ : Set X))
    exact hPQ (eq_of_le_of_prob (hP ▸ hQ ▸ withDensity_le_of_le μ hle))
  have hB : B.Nonempty := by
    by_contra hB
    rw [not_nonempty_iff_eq_empty] at hB
    have hle : ∀ x, q x ≤ p x := fun x => not_lt.1 fun h => (hB ▸ (show x ∈ B from h) : x ∈ (∅ : Set X))
    exact hPQ (eq_of_le_of_prob (hQ ▸ hP ▸ withDensity_le_of_le μ hle)).symm
  have hcover : closure A ∪ closure B = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_contra hx
    simp only [mem_union, not_or] at hx
    set O := (closure A)ᶜ ∩ (closure B)ᶜ
    have hOo : IsOpen O := isClosed_closure.isOpen_compl.inter isClosed_closure.isOpen_compl
    have hOsub : O ⊆ {x | p x = q x} := by
      intro y hy
      have h1 : ¬ q y < p y := fun h => hy.1 (subset_closure h)
      have h2 : ¬ p y < q y := fun h => hy.2 (subset_closure h)
      exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    have := interior_maximal hOsub hOo
    rw [hint] at this
    exact this ⟨hx.1, hx.2⟩
  have hmeet : (closure A ∩ closure B).Nonempty := by
    by_contra hd
    rw [not_nonempty_iff_eq_empty] at hd
    have hcl : IsClopen (closure A) := by
      refine ⟨isClosed_closure, ?_⟩
      have : closure A = (closure B)ᶜ := by
        ext x; constructor
        · intro hxA hxB; exact (hd ▸ (⟨hxA, hxB⟩ : x ∈ closure A ∩ closure B) : x ∈ (∅ : Set X))
        · intro hxB
          have : x ∈ closure A ∪ closure B := hcover ▸ mem_univ x
          exact this.resolve_right hxB
      rw [this]; exact isClosed_closure.isOpen_compl
    rcases isClopen_iff.1 hcl with h | h
    · exact (closure_empty_iff A).1 h ▸ hA |>.ne_empty rfl
    · obtain ⟨b, hb⟩ := hB
      have : b ∈ closure A ∩ closure B := ⟨h ▸ mem_univ b, subset_closure hb⟩
      rw [hd] at this; exact this
  obtain ⟨x, hxA, hxB⟩ := hmeet
  refine ⟨x, closure_minimal (fun y hy => mem_support_sub_inf μ hp hq hq0 P Q hP hQ hy) Measure.isClosed_support hxA, ?_⟩
  have hsupp : B ⊆ (Q - Q ⊓ P).support := fun y hy => mem_support_sub_inf μ hq hp hp0 Q P hQ hP hy
  rw [inf_comm] at hsupp
  exact closure_minimal hsupp Measure.isClosed_support hxB

end Contact

end StatFormal.KernelFacts
