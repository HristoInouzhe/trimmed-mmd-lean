import StatFormal.Wave31tq.RouteXCore
import StatFormal.Lib.SupportSeparation.Smooth
import StatFormal.Wave31tp.Proofs

/-!
# Wave 31tq, route X: Proposition S4.5 (`newgammaone`) and S4 :371-372 (`newgammaone_smooth`) (untrusted proof file)

Q8. Route (printed, S4 :374-397): when `supp P₀` (compact) and `supp Q₀` (closed) are disjoint, the smooth Urysohn function
`f = 1_E ⋆ b_{δ/2}` (`SupportSeparation.exists_smooth_one_zero`, built on 31tp L8 (a)) is `C^∞` with compact support, `0 ≤ f ≤ 1`,
`f = 1` on `supp P₀`, `f = 0` on `supp Q₀`; it is represented in `ℋ`:

* `newgammaone_smooth` (the general form, `ℝ^d = EuclideanSpace ℝ (Fin d)`): by the hypothesis `ContainsSmoothCompact φ`;
* `newgammaone` (Sobolev-type kernel on any `V`): `k̂₀(ξ) ≥ c(1 + ‖ξ‖²)^{−s}` is `𝓕 k₀(η) ≥ c(1 + 4π²‖η‖²)^{−s}` at `ξ = 2πη`,
  `‖f‖_{H^s} < ∞` (31tp L9 `sobolev_smooth_finite`) and 31tp L19 (a) `sobolev_incl` gives the representer; `φ` is continuous,
  strongly measurable and bounded by `√(k₀ 0)` (31tp L16 `mmd_fourier`).

Parts (b), (c) are `RouteX.core_b`, `RouteX.core_c`. No cross-chunk hypothesis is needed.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ContDiff

namespace StatFormal.Wave31tq.RouteX

open StatFormal.TrimmedMMD.Unconditional StatFormal.Distances StatFormal.Wave31tp

/-- The spectral lower bound in the angular convention gives it in Mathlib's convention:
`k̂₀(ξ) ≥ c(1 + ‖ξ‖²)^{−s}` for all `ξ` implies `𝓕 k₀(η) ≥ c(1 + 4π²‖η‖²)^{−s}` for all `η`. -/
theorem specDens_lower_of_kHat {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k₀ : V → ℝ} {c s : ℝ}
    (hspec : ∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ) :
    ∀ η, c * (1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ (-s) ≤ specDens k₀ η := by
  intro η
  have h := hspec ((2 * Real.pi) • η)
  have e1 : kHat k₀ ((2 * Real.pi) • η) = specDens k₀ η := by
    simp only [kHat, ftA, specDens, smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_smul]
  have e2 : ‖(2 * Real.pi) • η‖ ^ 2 = 4 * Real.pi ^ 2 * ‖η‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
  rwa [e1, e2] at h

/-- Q8 `newgammaone_smooth` (S4 :371-372): (a)–(c) for every continuous bounded feature map on `ℝ^d` whose RKHS contains the
smooth compactly supported functions. -/
theorem newgammaone_smooth_route : Claims.newgammaone_smooth := by
  intro d H _ _ _ _ φ κ P Q _ _ hφc hφm hκ hcs hα0 hα1 hK
  have hex : (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅ →
      ∃ g : H, (∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) ∧ (∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1) ∧
        ∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0 := fun hdis => by
    obtain ⟨f, hf, hfc, -, hf01, hf1, hf0⟩ := StatFormal.SupportSeparation.exists_smooth_one_zero hK
      Measure.isClosed_support (Set.disjoint_iff_inter_eq_empty.2 hdis)
    obtain ⟨g, hg⟩ := hcs f hf hfc
    exact ⟨g, fun x => by rw [hg]; exact hf01 x, fun x hx => by rw [hg]; exact hf1 x hx,
      fun x hx => by rw [hg]; exact hf0 x hx⟩
  exact ⟨hex, fun g hg hg1 hg0 => core_b φ κ P Q hφm hκ hα0 hα1 g hg hg1 hg0,
    fun sl hsl => core_c φ κ P Q hφc hφm hκ hα0 hα1 hex sl hsl⟩

/-- Q8 `newgammaone` (Proposition S4.5): a Sobolev-type kernel on any finite-dimensional `V`. -/
theorem newgammaone_route : Claims.newgammaone := by
  intro d V _ _ _ _ _ hd H _ _ _ _ φ k₀ c s P Q _ _ hk hki hgram hc hs hspec hα0 hα1 hK
  obtain ⟨hφc, hφm, hnorm, -⟩ := StatFormal.Wave31tp.mmd_fourier V H φ k₀ hk hki hgram
  have hκ : ∀ x, ‖φ x‖ ≤ √(k₀ 0) := fun x => (hnorm x).le
  have hspec' := specDens_lower_of_kHat hspec
  have hex : (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅ →
      ∃ g : H, (∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) ∧ (∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1) ∧
        ∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0 := fun hdis => by
    obtain ⟨f, hf, hfc, hf2, hf01, hf1, hf0⟩ := StatFormal.SupportSeparation.exists_smooth_one_zero hK
      Measure.isClosed_support (Set.disjoint_iff_inter_eq_empty.2 hdis)
    have hcf : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
    have hcs : HasCompactSupport (fun x => (f x : ℂ)) := hfc.comp_left Complex.ofReal_zero
    have hfin : sobolevS s (fun x => (f x : ℂ)) < ⊤ :=
      StatFormal.Wave31tp.sobolev_smooth_finite V (fun x => (f x : ℂ)) s hcf hcs
    obtain ⟨g, hg, -⟩ :=
      StatFormal.Wave31tp.sobolev_incl V H φ k₀ c s hk hki hgram hc hspec' f hf.continuous hf2 hfin
    exact ⟨g, fun x => by rw [hg]; exact hf01 x, fun x hx => by rw [hg]; exact hf1 x hx,
      fun x hx => by rw [hg]; exact hf0 x hx⟩
  exact ⟨hex, fun g hg hg1 hg0 => core_b φ (√(k₀ 0)) P Q hφm hκ hα0 hα1 g hg hg1 hg0,
    fun sl hsl => core_c φ (√(k₀ 0)) P Q hφc hφm hκ hα0 hα1 hex sl hsl⟩

end StatFormal.Wave31tq.RouteX
