import StatFormal.Archive.Wave24a.Statements

/-!
# Route — B `cor:band-saturation-limit` (untrusted)

* Sandwich: `⟨v, Σ_j q_j(u) Z_j⟩ = Σ_j q_j(u) ⟨v, Z_j⟩` and `q(u) ∈ 𝒫_{κ∧κ^sat} ⊆ 𝒫_κ`. (The limit half is the frozen
  `Wave22b.cert_band_consistency` applied to `x̄^sat`; no separate target.)
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24a

theorem band_saturation_sandwich : Claims.band_saturation_sandwich := by
  intro E _ _ n Z q A κ κsat v hsimp hκ hsat
  have hsub : StatFormal.OTFD.Wave2.cappedSimplex (κ ⊓ κsat) ⊆ StatFormal.OTFD.Wave2.cappedSimplex κ :=
    fun p hp => ⟨hp.1, fun j => (hp.2 j).trans inf_le_left⟩
  refine ⟨iSup₂_le fun u hu => ?_, biSup_mono hsub⟩
  have hmem : q u ∈ StatFormal.OTFD.Wave2.cappedSimplex (κ ⊓ κsat) :=
    ⟨hsimp u hu, fun j => le_inf (hκ u hu j) (hsat u hu j)⟩
  have hin : ⟪v, ∑ j, q u j • Z j⟫ = ∑ j, q u j * ⟪v, Z j⟫ := by
    rw [inner_sum]; simp [inner_smul_right]
  rw [hin]
  exact le_iSup₂ (f := fun p (_ : p ∈ StatFormal.OTFD.Wave2.cappedSimplex (κ ⊓ κsat)) =>
    ((∑ j, p j * ⟪v, Z j⟫ : ℝ) : EReal)) (q u) hmem

example : Claims.band_saturation_sandwich := band_saturation_sandwich

end StatFormal.Wave24a
