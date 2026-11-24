import StatFormal.Archive.Wave24a.Statements
import StatFormal.Lib.Exchangeable.MonteCarloTest

/-!
# Route — G `lem:randomisation` (untrusted)

The library `Foundations/Exchangeable` proves both tests for any measurable left action `act` (`IsAct`); a `MulAction`
with measurable translations is one (`act g w = g • w`, `mul_smul`). The uniform law of the frozen
`OTFD.Conformal.unif` is the library's `unifG` (same definition).
-/

noncomputable section
open MeasureTheory Finset
open scoped ENNReal

namespace StatFormal.Wave24a

open StatFormal.Foundations.Exchangeable

lemma isAct_smul {G 𝒲 : Type*} [Group G] [MulAction G 𝒲] [MeasurableSpace 𝒲]
    (h : ∀ g : G, Measurable fun w : 𝒲 => g • w) : IsAct (fun (g : G) (w : 𝒲) => g • w) :=
  ⟨fun g h w => mul_smul g h w, h⟩

theorem randomisation_full : Claims.randomisation_full := by
  intro G 𝒲 _ _ _ _ μ _ T hmeas hinv hT α _ _
  have h := grp_test_valid (act := fun (g : G) (w : 𝒲) => g • w) μ (isAct_smul hmeas) hinv hT α
  simpa [grpPval, grpCount, grpPvalue] using h

theorem randomisation_mc : Claims.randomisation_mc := by
  intro G 𝒲 _ _ _ _ _ _ μ _ T B hmeas hinv hT α _ _
  have h := mc_test_valid (act := fun (g : G) (w : 𝒲) => g • w) μ (isAct_smul hmeas) hinv hT B α
  have hset : {z : 𝒲 × (Fin B → G) | mcPvalue T z.1 z.2 ≤ α} =
      {p : 𝒲 × (Fin B → G) | (mcCount (fun (g : G) (w : 𝒲) => g • w) T p.1 p.2 : ℝ) / (B + 1) ≤ α} := by
    ext z
    simp [mcPvalue, mcCount]
  rw [hset]
  exact h

example : Claims.randomisation_full := randomisation_full
example : Claims.randomisation_mc := randomisation_mc

end StatFormal.Wave24a
