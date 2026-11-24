import StatFormal.Archive.Wave30h.Statements
import StatFormal.Archive.Wave24g.RouteGap

/-!
# Route — the long-paper counterexample to `cor:field-local` (DEFECTS #82) under the journal form (untrusted)

Route-level sanity check, not a printed claim (moved out of `StatementsDraft.lean` by the critic, 2026-10-20: the
journal prints no counterexample, and the journal `cor:field-local` itself is the claim `fieldlocal_rate`).

`(F_b)_#μ_b = γ` (certified Wave 24g `muB_map_SbE`), so the journal misspecification of group `0` vanishes and that of
group `1` is `W₂((F_b)_#R₁, (F_b)_#R₀)`, the population parity gap, bounded below by the certified Wave 24g
`field_local_gap_lower`.
-/

noncomputable section
open MeasureTheory TauCeti

namespace StatFormal.Wave30h

open StatFormal.Wave24g (muB SbE shiftLaw gammaU muB_map_SbE field_local_gap_lower)

/-- The long-paper counterexample (DEFECTS #82, frozen Wave 24g: `γ = ν = Unif[0,1]`, `S_{μ_b} = F_b`, `R₀ = μ_b`,
`R₁ = μ_b(· − δ)`, both approximated by `μ_b`, `S_ν⁻¹ = id`) is avoided by the journal form: there the journal
misspecifications are `δ₀ = W₂((F_b)_#R₀, γ) = 0` and `δ₁ = W₂((F_b)_#R₁, γ)`, which EQUALS the population parity gap
`W₂((F_b)_#R₀, (F_b)_#R₁)` and is `≥ δ^{3/4}/100` — so the journal hypothesis does not hold with `δ_n = O(δ)` (the
old `W₂(R₁, μ_b) ≤ δ`), and the journal bound `O(δ_n)` is consistent with the gap. -/
theorem fieldlocal_counterexample_delta :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      wassersteinEDist 2 (muB.map SbE) gammaU = 0 ∧
      wassersteinEDist 2 ((shiftLaw δ muB).map SbE) gammaU =
        wassersteinEDist 2 (muB.map SbE) ((shiftLaw δ muB).map SbE) ∧
      ENNReal.ofReal (δ ^ (3 / 4 : ℝ) / 100) ≤ wassersteinEDist 2 ((shiftLaw δ muB).map SbE) gammaU := by
  intro δ hδ hδ1
  have hcomm : wassersteinEDist 2 ((shiftLaw δ muB).map SbE) gammaU =
      wassersteinEDist 2 (muB.map SbE) ((shiftLaw δ muB).map SbE) := by
    rw [muB_map_SbE, wassersteinEDist_comm measurable_edist]
  refine ⟨?_, hcomm, ?_⟩
  · rw [muB_map_SbE]; exact wassersteinEDist_self_of_measurable_edist measurable_edist 2 gammaU
  · rw [hcomm]; exact field_local_gap_lower δ hδ hδ1

end StatFormal.Wave30h
