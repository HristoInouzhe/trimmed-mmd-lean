import StatFormal.Wave31tr.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Lib.TVFacts.Removal

/-!
# Wave 31tr, chunk E2: contamination, trimmings as removals, different fractions (T34) (untrusted)

* `different_fractions_route` (T34(c)): `(1 − α₁∨α₂)R ≤ (1−α₁)R ≤ P` and likewise `≤ Q`, so `R` is a common part
  (`TVFacts.tvDist_le_of_smul_le`);
* `contam_equiv_route` (T34(a)): (⇐) a common component (`TVFacts.tvDist_le_of_mixture`); (⇒) at `α = 1` trivially, at `α = 0`
  `P = Q` (`TVFacts.eq_of_tvDist_eq_zero`), for `0 < α < 1` the certified `TrimmedMMD.ZeroSet.tvintersect` gives a common trimming
  `R = g_P·P = g_Q·Q` with `(1−α)R ≤ P, Q`, then `TVFacts.exists_contam_of_smul_le`; least element at `α = TV`;
* `trimming_removal_route` (T34(b)): `TVFacts.exists_removal_of_density`, `TVFacts.exists_density_of_removal`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RoutePop

open StatFormal.Distances StatFormal.TrimmedMMD.ZeroSet

/-! ### T34 (c) -/

theorem different_fractions_route : Claims.different_fractions := by
  intro 𝒳 _ P Q R _ _ _ α₁ α₂ h10 h11 h20 h21 hP hQ
  have hmax1 : max α₁ α₂ ≤ 1 := max_le h11.le h21.le
  refine TVFacts.tvDist_le_of_smul_le P Q R hmax1 ?_ ?_
  · exact (TVFacts.smul_le_smul_of_le R (ENNReal.ofReal_le_ofReal (by linarith [le_max_left α₁ α₂]))).trans hP
  · exact (TVFacts.smul_le_smul_of_le R (ENNReal.ofReal_le_ofReal (by linarith [le_max_right α₁ α₂]))).trans hQ

/-! ### T34 (a) -/

/-- The common trimming of `tvintersect` as a common part: for a trimming density `g` of `P` at level `α < 1`,
`R = g·P` is a probability measure with `(1−α)R ≤ P`. -/
theorem trim_common_part {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] {α : ℝ} (hα1 : α < 1)
    {g : 𝒳 → ℝ} (hg : IsTrimDensity P α g) :
    IsProbabilityMeasure (P.withDensity fun x => ENNReal.ofReal (g x)) ∧
      ENNReal.ofReal (1 - α) • P.withDensity (fun x => ENNReal.ofReal (g x)) ≤ P := by
  have hs : 0 < 1 - α := by linarith
  refine ⟨TVFacts.isProbabilityMeasure_withDensity_ofReal P hg.integrable (fun x => (hg.2.1 x).1) hg.2.2,
    TVFacts.smul_withDensity_ofReal_le P hg.1 hs.le fun x => ?_⟩
  have := mul_le_mul_of_nonneg_left (hg.2.1 x).2 hs.le
  rwa [mul_one_div_cancel hs.ne'] at this

theorem contam_equiv_route : Claims.contam_equiv := by
  intro 𝒳 _ P Q _ _
  have hiff : ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      (tvDist P Q ≤ α ↔
        ∃ R P₀ Q₀ : Measure 𝒳, IsProbabilityMeasure R ∧ IsProbabilityMeasure P₀ ∧ IsProbabilityMeasure Q₀ ∧
          P = ENNReal.ofReal (1 - α) • R + ENNReal.ofReal α • P₀ ∧
          Q = ENNReal.ofReal (1 - α) • R + ENNReal.ofReal α • Q₀) := by
    intro α hα0 hα1
    constructor
    · intro htv
      rcases eq_or_lt_of_le hα1 with h1 | h1
      · subst h1
        exact ⟨P, P, Q, inferInstance, inferInstance, inferInstance, by simp, by simp⟩
      · rcases eq_or_lt_of_le hα0 with h0 | h0
        · subst h0
          have hPQ : P = Q := TVFacts.eq_of_tvDist_eq_zero (le_antisymm htv (tvDist_nonneg P Q))
          exact ⟨P, P, Q, inferInstance, inferInstance, inferInstance, by simp, by simp [hPQ]⟩
        · obtain ⟨gP, gQ, hgP, hgQ, hR⟩ := (StatFormal.TrimmedMMD.ZeroSet.tvintersect 𝒳 P Q α hα0 h1).1 htv
          obtain ⟨hRprob, hRP⟩ := trim_common_part P h1 hgP
          obtain ⟨-, hRQ⟩ := trim_common_part Q h1 hgQ
          rw [← hR] at hRQ
          obtain ⟨P₀, hP₀, hPeq⟩ := TVFacts.exists_contam_of_smul_le P _ h0 hα1 hRP
          obtain ⟨Q₀, hQ₀, hQeq⟩ := TVFacts.exists_contam_of_smul_le Q _ h0 hα1 hRQ
          exact ⟨_, P₀, Q₀, hRprob, hP₀, hQ₀, hPeq, hQeq⟩
    · rintro ⟨R, P₀, Q₀, hR, hP₀, hQ₀, hP, hQ⟩
      exact TVFacts.tvDist_le_of_mixture P Q R P₀ Q₀ hα1 hP hQ
  refine ⟨hiff, ⟨⟨tvDist_nonneg P Q, tvDist_le_one, (hiff _ (tvDist_nonneg P Q) tvDist_le_one).1 le_rfl⟩, ?_⟩⟩
  rintro α ⟨hα0, hα1, hex⟩
  exact (hiff α hα0 hα1).2 hex

/-! ### T34 (b) -/

theorem trimming_removal_route : Claims.trimming_removal := by
  intro 𝒳 _ P _ α hα0 hα1 μ
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨ν, hνP, hνu, heq⟩ :=
      TVFacts.exists_removal_of_density P hα0 hα1 hg.1 (fun x => (hg.2.1 x).1) (fun x => (hg.2.1 x).2) hg.2.2
    exact ⟨ν, hνP, hνu.le, heq⟩
  · rintro ⟨ν, hνP, hνα, rfl⟩
    obtain ⟨g, hgm, hgb, hgi, heq⟩ := TVFacts.exists_density_of_removal P hα1 hνP hνα
    exact ⟨g, ⟨hgm, hgb, hgi⟩, heq⟩

end StatFormal.Wave31tr.RoutePop
