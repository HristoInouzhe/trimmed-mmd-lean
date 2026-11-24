import StatFormal.Wave31tr.Statements
import StatFormal.Wave30tr.Proofs

/-!
# Wave 31tr, chunk M1: `any_threshold_converse` (T26)

The event `E⁺` of the certified `Wave30tr.thmA` at `δ′`: on it, for `α = α⋆ − ε ∈ [0, α⋆] ⊆ [0,1)`,
`D̂_α ≤ D_α + τ^A(α,δ′) ≤ τ(α)`, so `α` is in the crossing set and `α̂ = sInf ≤ α` (`csInf_le`, the set bounded below by `0`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteMisc1

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional

theorem any_threshold_converse_route : Claims.any_threshold_converse := by
  intro 𝒳 H _ _ _ _ _ φ κ D P Q _ _ δ' n m hφ hκ hD htv hδ0 hδ1 hn hm
  obtain ⟨Eplus, -, hEm, hEp, -, -, hE, -⟩ :=
    StatFormal.Wave30tr.thmA 𝒳 H φ κ D P Q δ' n m hφ hκ hD hδ0 hδ1 hn hm
  refine ⟨Eplus, hEm, hEp, fun τ z hz ε hε hτ => ?_⟩
  set a := StatFormal.Distances.tvDist P Q - ε
  have ha : a ∈ Ico (0 : ℝ) 1 := ⟨by simp only [a]; linarith [hε.2], by simp only [a]; linarith [hε.1]⟩
  have hcross : a ∈ crossSet (Demp φ z.1 z.2) τ := ⟨ha, ((hE z hz a ha).1).trans hτ⟩
  exact csInf_le ⟨0, fun b hb => hb.1.1⟩ hcross

end StatFormal.Wave31tr.RouteMisc1
