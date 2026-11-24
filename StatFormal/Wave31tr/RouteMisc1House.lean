import StatFormal.Wave31tr.Statements
import StatFormal.Lib.KernelFacts.Pettis
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Wave 31tr, chunk M1: `house_encoding` (T32)

(A1) for the Gram function gives weak measurability (`KernelFacts.measurable_inner_of_gram`), hence Borel and strong measurability in
the separable Hilbert space (`KernelFacts.measurable_of_inner`, Pettis), `‖φ‖ ≤ κ` from `k(x,x) ≤ κ²`, and Bochner integrability of
`g • φ` (`KernelFacts.integrable_smul_of_bounded`). The RKHS case is the canonical feature map `x ↦ kerFun H x 1`, whose Gram function
is `kernel H x x′ 1` by the reproducing property (`RKHS.kerFun_inner`, `RKHS.kerFun_apply`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteMisc1

/-- The first part of `house_encoding`, for any feature map. -/
lemma house_general {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] (φ : 𝒳 → H) (κ : ℝ) (hκ : 0 ≤ κ)
    (hk : ∀ x', Measurable fun x => ⟪φ x, φ x'⟫_ℝ) (hd : ∀ x, ⟪φ x, φ x⟫_ℝ ≤ κ ^ 2) :
    Measurable φ ∧ StronglyMeasurable φ ∧ (∀ x, ‖φ x‖ ≤ κ) ∧
      ∀ (P : Measure 𝒳) [IsProbabilityMeasure P] (g : 𝒳 → ℝ) (C : ℝ), Measurable g → (∀ x, |g x| ≤ C) →
        Integrable (fun x => g x • φ x) P := by
  have hm := KernelFacts.measurable_of_gram hk
  have hs := hm.stronglyMeasurable
  have hb := KernelFacts.norm_le_of_gram hκ hd
  exact ⟨hm, hs, hb, fun P _ g C hg hgC => KernelFacts.integrable_smul_of_bounded P hs hb hg hgC⟩

/-- The Gram function of the canonical RKHS feature map. -/
lemma rkhs_gram {𝒳 H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H 𝒳 ℝ] (x x' : 𝒳) :
    ⟪RKHS.kerFun H x (1 : ℝ), RKHS.kerFun H x' (1 : ℝ)⟫_ℝ = RKHS.kernel H x x' (1 : ℝ) := by
  rw [RKHS.kerFun_inner, RKHS.kerFun_apply]
  simp

theorem house_encoding_route : Claims.house_encoding := by
  refine ⟨fun 𝒳 H _ _ _ _ _ _ _ φ κ hκ hk hd => house_general φ κ hκ hk hd, ?_⟩
  intro 𝒳 H _ _ _ _ _ _ _ _ κ hκ hk hd
  have hk' : ∀ x', Measurable fun x => ⟪RKHS.kerFun H x (1 : ℝ), RKHS.kerFun H x' (1 : ℝ)⟫_ℝ := fun x' => by
    simp_rw [rkhs_gram]; exact hk x'
  have hd' : ∀ x, ⟪RKHS.kerFun H x (1 : ℝ), RKHS.kerFun H x (1 : ℝ)⟫_ℝ ≤ κ ^ 2 := fun x => by
    rw [rkhs_gram]; exact hd x
  obtain ⟨-, hs, hb, -⟩ := house_general (fun x => RKHS.kerFun H x (1 : ℝ)) κ hκ hk' hd'
  exact ⟨hs, hb⟩

end StatFormal.Wave31tr.RouteMisc1
