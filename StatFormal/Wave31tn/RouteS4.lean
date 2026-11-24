import StatFormal.Wave31tn.Statements
import StatFormal.Wave31tf.RouteSimple

/-!
# Wave 31tn route: S4 `prose:nouniformrate` (untrusted proof material)

`Û = α̃ + r` covers `TV` with probability `≥ 1 − δ′` on `𝒫₂` (from the uniform-rate bound), so the certified `thm:impossible`
(`Wave31ta.impossible_two`, same randomisation model) gives `P_{U,U}(Û ≥ 1) ≥ 1 − δ′` at the uniform pair (in `𝒫₂`, `TV = 0`,
`Wave31tf.density2_unif`); there `α̃ ≥ 1 − r > 0 = TV`, so `P_{U,U}(α̃ > TV) ≥ 1 − δ′ > δ`, against validity.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tn

namespace RouteS4

theorem nouniformrate_route : Claims.nouniformrate := by
  intro n m δ δ' r Ξ _ ρ _ T hn hm hδ0 hδ'0 hδδ' hr hT ⟨hval, hrate⟩
  have hPu2 := StatFormal.Wave31tf.density2_unif
  have himp := StatFormal.Wave31ta.impossible_two n m δ' Ξ ρ (fun z => T z + r) hn hm hδ'0 (by linarith)
    (hT.add_const r) (by
      intro P Q hP hQ
      haveI := StatFormal.Wave31tf.dataLaw_prob n m ρ hP hQ
      have h := hrate P Q hP hQ
      have hc : {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | StatFormal.Distances.tvDist P Q ≤ T z + r} =
          {z | r < StatFormal.Distances.tvDist P Q - T z}ᶜ := by
        ext z; simp only [mem_setOf_eq, mem_compl_iff, not_lt]; constructor <;> intro hz <;> linarith
      have hms : MeasurableSet {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | r < StatFormal.Distances.tvDist P Q - T z} :=
        measurableSet_lt measurable_const (by fun_prop)
      rw [hc, probReal_compl_eq_one_sub hms]
      linarith)
  have h2 := hval _ _ hPu2 hPu2
  rw [StatFormal.Distances.tvDist_self] at h2
  haveI := StatFormal.Wave31tf.dataLaw_prob n m ρ hPu2 hPu2
  have hsub : {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | 1 ≤ T z + r} ⊆ {z | 0 < T z} := by
    intro z hz; simp only [mem_setOf_eq] at hz ⊢; linarith
  have := himp.trans (measureReal_mono hsub)
  linarith

end RouteS4

end StatFormal.Wave31tn
