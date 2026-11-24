import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Feature maps with the same Gram function (library, untrusted)

If `⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫` for all `x, y` (`φ : 𝒳 → H`, `φ' : 𝒳 → H'`, real inner-product spaces, `H'` complete), then
`Σ cᵢ φ xᵢ ↦ Σ cᵢ φ' xᵢ` is a well-defined linear isometry on the span of `φ(𝒳)`, which extends to its closure `K`
(`gramIso`). Consequences: representers transfer with no larger norm (projection onto `K`), and Bochner integrals of bounded
measurable multiples of `φ` and `φ'` have the same norms (so MMD, `D_α`, `D̂_α` depend only on the Gram function).
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

variable {𝒳 : Type*} {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] {φ : 𝒳 → H} {φ' : 𝒳 → H'}

section Iso

variable (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫)
include hG

lemma inner_lc_eq (c d : 𝒳 →₀ ℝ) :
    ⟪Finsupp.linearCombination ℝ φ c, Finsupp.linearCombination ℝ φ d⟫ =
      ⟪Finsupp.linearCombination ℝ φ' c, Finsupp.linearCombination ℝ φ' d⟫ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left,
    real_inner_smul_right, hG]

lemma norm_lc_eq (c : 𝒳 →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ φ c‖ = ‖Finsupp.linearCombination ℝ φ' c‖ := by
  have h := inner_lc_eq hG c c
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The coefficients-to-span map. -/
def lcSpan (φ : 𝒳 → H) : (𝒳 →₀ ℝ) →ₗ[ℝ] Submodule.span ℝ (Set.range φ) :=
  (Finsupp.linearCombination ℝ φ).codRestrict _ fun c => by
    rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ c

omit hG in
lemma lcSpan_surj (φ : 𝒳 → H) : Function.Surjective (lcSpan φ) := by
  rintro ⟨v, hv⟩
  rw [← Finsupp.range_linearCombination] at hv
  obtain ⟨c, rfl⟩ := hv
  exact ⟨c, rfl⟩

lemma ker_lcSpan_le : LinearMap.ker (lcSpan φ) ≤ LinearMap.ker (Finsupp.linearCombination ℝ φ') := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have h1 : Finsupp.linearCombination ℝ φ c = 0 := by
    have := congrArg Subtype.val hc; simpa [lcSpan] using this
  rw [← norm_eq_zero, ← norm_lc_eq hG, h1, norm_zero]

/-- The linear map `Σ cᵢ φ xᵢ ↦ Σ cᵢ φ' xᵢ` on the span. -/
def gramSpanMap : Submodule.span ℝ (Set.range φ) →ₗ[ℝ] H' :=
  ((LinearMap.ker (lcSpan φ)).liftQ (Finsupp.linearCombination ℝ φ') (ker_lcSpan_le hG)).comp
    ((lcSpan φ).quotKerEquivOfSurjective (lcSpan_surj φ)).symm.toLinearMap

lemma gramSpanMap_lc (c : 𝒳 →₀ ℝ) : gramSpanMap hG (lcSpan φ c) = Finsupp.linearCombination ℝ φ' c := by
  simp [gramSpanMap, LinearMap.quotKerEquivOfSurjective_symm_apply]

lemma gramSpanMap_norm (v : Submodule.span ℝ (Set.range φ)) : ‖gramSpanMap hG v‖ = ‖v‖ := by
  obtain ⟨c, rfl⟩ := lcSpan_surj φ v
  rw [gramSpanMap_lc, ← norm_lc_eq hG]
  rfl

end Iso

section Extend

variable [CompleteSpace H'] (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫)
include hG

/-- The closure of the span. -/
abbrev spanCl (φ : 𝒳 → H) : Submodule ℝ H := (Submodule.span ℝ (Set.range φ)).topologicalClosure

omit hG [CompleteSpace H'] in
lemma span_le_cl (φ : 𝒳 → H) : Submodule.span ℝ (Set.range φ) ≤ spanCl φ := Submodule.le_topologicalClosure _

/-- The inclusion of the span into its closure, as a continuous linear map. -/
def inclCl (φ : 𝒳 → H) : Submodule.span ℝ (Set.range φ) →L[ℝ] spanCl φ :=
  ⟨Submodule.inclusion (span_le_cl φ), continuous_inclusion (span_le_cl φ)⟩

omit hG [CompleteSpace H'] in
lemma inclCl_dense (φ : 𝒳 → H) : DenseRange (inclCl φ) := by
  have : DenseRange (Set.inclusion (span_le_cl φ : (Submodule.span ℝ (Set.range φ) : Set H) ⊆ spanCl φ)) :=
    (denseRange_inclusion_iff _).2 (Submodule.topologicalClosure_coe (Submodule.span ℝ (Set.range φ))).le
  exact this

omit hG [CompleteSpace H'] in
lemma inclCl_norm (φ : 𝒳 → H) (v : Submodule.span ℝ (Set.range φ)) : ‖inclCl φ v‖ = ‖v‖ := rfl

omit hG [CompleteSpace H'] in
lemma inclCl_unif (φ : 𝒳 → H) : IsUniformInducing (inclCl φ) := by
  exact Isometry.isUniformInducing fun _ _ => rfl

/-- The span map as a continuous linear map. -/
def gramSpanCLM : Submodule.span ℝ (Set.range φ) →L[ℝ] H' :=
  (gramSpanMap hG).mkContinuous 1 fun v => by rw [gramSpanMap_norm, one_mul]

/-- The extension to the closure. -/
def gramExt : spanCl φ →L[ℝ] H' := (gramSpanCLM hG).extend (inclCl φ)

lemma gramExt_incl (v : Submodule.span ℝ (Set.range φ)) : gramExt hG (inclCl φ v) = gramSpanMap hG v := by
  simp [gramExt, ContinuousLinearMap.extend_eq _ (inclCl_dense φ) (inclCl_unif φ), gramSpanCLM]

lemma gramExt_norm (w : spanCl φ) : ‖gramExt hG w‖ = ‖w‖ := by
  refine (inclCl_dense φ).induction_on w (isClosed_eq ((gramExt hG).continuous.norm) continuous_norm) ?_
  intro v
  rw [gramExt_incl, gramSpanMap_norm, inclCl_norm]

/-- **The Gram isometry** `U : closure(span φ(𝒳)) → H'`, `U (φ x) = φ' x`. -/
def gramIso : spanCl φ →ₗᵢ[ℝ] H' :=
  { toLinearMap := (gramExt hG).toLinearMap, norm_map' := gramExt_norm hG }

omit hG [CompleteSpace H'] in
lemma mem_spanCl (φ : 𝒳 → H) (x : 𝒳) : φ x ∈ spanCl φ := span_le_cl φ (Submodule.subset_span ⟨x, rfl⟩)

lemma gramIso_apply (x : 𝒳) (hx : φ x ∈ spanCl φ) : gramIso hG ⟨φ x, hx⟩ = φ' x := by
  have h1 : (⟨φ x, hx⟩ : spanCl φ) = inclCl φ ⟨φ x, Submodule.subset_span ⟨x, rfl⟩⟩ := rfl
  have h2 : (⟨φ x, Submodule.subset_span ⟨x, rfl⟩⟩ : Submodule.span ℝ (Set.range φ)) =
      lcSpan φ (Finsupp.single x 1) := by
    apply Subtype.ext; simp [lcSpan]
  change gramExt hG _ = _
  rw [h1, gramExt_incl, h2, gramSpanMap_lc]
  simp

lemma inner_gramIso_phi (w : spanCl φ) (x : 𝒳) : ⟪gramIso hG w, φ' x⟫ = ⟪(w : H), φ x⟫ := by
  rw [← gramIso_apply hG x (mem_spanCl φ x), LinearIsometry.inner_map_map]
  rfl

end Extend

section Transfer

variable [CompleteSpace H] [CompleteSpace H'] (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫)
include hG

instance spanCl_complete (φ : 𝒳 → H) : CompleteSpace (spanCl φ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Representers transfer with no larger norm. -/
lemma gram_rep_le (g : H) : ∃ g' : H', ‖g'‖ ≤ ‖g‖ ∧ ∀ x, ⟪g', φ' x⟫ = ⟪g, φ x⟫ := by
  set P := (spanCl φ).orthogonalProjectionOnto
  refine ⟨gramIso hG (P g), ?_, fun x => ?_⟩
  · rw [LinearIsometry.norm_map]
    exact (spanCl φ).norm_orthogonalProjectionOnto_apply_le g
  · rw [inner_gramIso_phi]
    have := (spanCl φ).inner_starProjection_left_eq_right g (φ x)
    rw [Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr (mem_spanCl φ x)] at this
    exact this

/-- Representers in the closure transfer isometrically. -/
lemma gram_rep_eq (g : spanCl φ) : ‖gramIso hG g‖ = ‖g‖ ∧ ∀ x, ⟪gramIso hG g, φ' x⟫ = ⟪(g : H), φ x⟫ :=
  ⟨LinearIsometry.norm_map _ _, inner_gramIso_phi hG g⟩

/-- `φ' = U ∘ P ∘ φ`. -/
lemma phi'_eq (x : 𝒳) : φ' x = gramIso hG ((spanCl φ).orthogonalProjectionOnto (φ x)) := by
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨φ x, mem_spanCl φ x⟩, gramIso_apply]

end Transfer

section Integrals

variable [CompleteSpace H] [CompleteSpace H'] (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫)
include hG

/-- `φ' = L ∘ φ` for the continuous linear map `L = U ∘ P`. -/
def gramCLM : H →L[ℝ] H' :=
  (gramIso hG).toContinuousLinearMap.comp (spanCl φ).orthogonalProjectionOnto

lemma phi'_eq_clm (x : 𝒳) : φ' x = gramCLM hG (φ x) := phi'_eq hG x

lemma norm_phi'_eq (x : 𝒳) : ‖φ' x‖ = ‖φ x‖ := by
  have h := hG x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h.symm

lemma norm_gramCLM_of_mem {w : H} (hw : w ∈ spanCl φ) : ‖gramCLM hG w‖ = ‖w‖ := by
  simp only [gramCLM, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨w, hw⟩]
  rfl

lemma integral_mem_spanCl [MeasurableSpace 𝒳] {μ : Measure 𝒳} {u : 𝒳 → ℝ}
    (hint : Integrable (fun x => u x • φ x) μ) : ∫ x, u x • φ x ∂μ ∈ spanCl φ := by
  have hQ : ∀ x, (spanCl φ).starProjection (u x • φ x) = u x • φ x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr ((spanCl φ).smul_mem _ (mem_spanCl φ x))
  have := ((spanCl φ).starProjection).integral_comp_comm hint
  simp_rw [hQ] at this
  rw [this]
  exact Submodule.starProjection_apply_mem _ _

/-- **Bochner norms depend only on the Gram function.** -/
theorem norm_integral_gram [MeasurableSpace 𝒳] {μ ν : Measure 𝒳} {u v : 𝒳 → ℝ}
    (hu : Integrable (fun x => u x • φ x) μ) (hv : Integrable (fun x => v x • φ x) ν) :
    ‖∫ x, u x • φ x ∂μ - ∫ x, v x • φ x ∂ν‖ = ‖∫ x, u x • φ' x ∂μ - ∫ x, v x • φ' x ∂ν‖ := by
  have e : ∀ (w : 𝒳 → ℝ) (ρ : Measure 𝒳), Integrable (fun x => w x • φ x) ρ →
      ∫ x, w x • φ' x ∂ρ = gramCLM hG (∫ x, w x • φ x ∂ρ) := by
    intro w ρ hw
    rw [← (gramCLM hG).integral_comp_comm hw]
    simp_rw [map_smul, ← phi'_eq_clm hG]
  rw [e u μ hu, e v ν hv, ← map_sub, norm_gramCLM_of_mem hG]
  exact (spanCl φ).sub_mem (integral_mem_spanCl hG hu) (integral_mem_spanCl hG hv)

end Integrals

end StatFormal.TIKernel
