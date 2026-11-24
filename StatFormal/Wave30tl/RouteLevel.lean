import StatFormal.Wave30tl.RouteCrossing
import StatFormal.Archive.Wave15a.RouteTM

/-!
# Wave 30tl — the level of `eq:test` for every bounded kernel (untrusted proof route)

The paper's route, from the two certified claims that omit (A3): `thm:concentration` (`TrimmedMMD.Concentration.concentration`,
(A1)–(A2) only) for each sample at level `δ/2` gives measurable `A_P`, `A_Q`; on their cylinder intersection `E` (probability
`≥ 1 − δ` by the union bound), `lem:nullbound` (Wave 15a `nullbound`, under `H_{0,α}`, no (A3)) gives
`D̂_α ≤ d_H(P_n) + d_H(Q_m) ≤ r_n(α,δ/2) + r_m(α,δ/2)`. So the rejection region lies in `Eᶜ`, of probability `≤ δ`.
Measurability of the rejection region: `lem:crossing` (`measurable_Demp`).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

theorem test_level : Claims.test_level := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α δ n m hφ hκ hα0 hα1 hδ0 hδ1 hn hm hH0
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)
  set R := {z : (Fin n → 𝒳) × (Fin m → 𝒳) | rn κ α (δ / 2) n + rn κ α (δ / 2) m < Demp φ z.1 z.2 α}
  have hRm : MeasurableSet R := measurableSet_lt measurable_const (measurable_Demp hφ hn hm hα0 hα1)
  refine ⟨hRm, ?_⟩
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ21 : δ / 2 < 1 := by linarith
  obtain ⟨AP, hAPm, hAPp, hAP⟩ :=
    StatFormal.TrimmedMMD.Concentration.concentration 𝒳 H P φ κ α (δ / 2) n hφ hκ hα0 hα1 hn hδ2 hδ21
  obtain ⟨AQ, hAQm, hAQp, hAQ⟩ :=
    StatFormal.TrimmedMMD.Concentration.concentration 𝒳 H Q φ κ α (δ / 2) m hφ hκ hα0 hα1 hm hδ2 hδ21
  have hP : ENNReal.ofReal (1 - δ / 2) ≤ μ (Prod.fst ⁻¹' AP) := by
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one,
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hAPp
  have hQ : ENNReal.ofReal (1 - δ / 2) ≤ μ (Prod.snd ⁻¹' AQ) := by
    rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul,
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hAQp
  set E := Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ
  have hEm : MeasurableSet E := (measurable_fst hAPm).inter (measurable_snd hAQm)
  have hEp : ENNReal.ofReal (1 - δ) ≤ μ E := prob_inter_ge hδ0 hδ1 (measurable_snd hAQm) hP hQ
  have hRE : R ⊆ Eᶜ := by
    intro z hz hzE
    have hnb := StatFormal.Wave15a.nullbound 𝒳 H P Q φ κ α n m hφ hκ hα0 hα1 hn hm hH0 z.1 z.2
    have h1 := hAP hzE.1
    have h2 := hAQ hzE.2
    simp only [mem_setOf_eq] at h1 h2
    have : Demp φ z.1 z.2 α ≤ rn κ α (δ / 2) n + rn κ α (δ / 2) m := by linarith
    exact absurd hz (not_lt.2 this)
  calc μ R ≤ μ Eᶜ := measure_mono hRE
    _ = 1 - μ E := prob_compl_eq_one_sub hEm
    _ ≤ 1 - ENNReal.ofReal (1 - δ) := tsub_le_tsub_left hEp 1
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - δ)]
      congr 1; ring

theorem test_squared : Claims.test_squared := by
  intro 𝒳 H _ _ _ _ _ φ κ α δ n m hφ hκ hα0 hα1 hδ0 hδ1 hn hm x y
  have hκ0 : 0 ≤ κ := kappa_nonneg_of hκ (x ⟨0, hn⟩)
  have hr : 0 ≤ rn κ α (δ / 2) n + rn κ α (δ / 2) m := add_nonneg (rn_nonneg hκ0 hα1 _ n) (rn_nonneg hκ0 hα1 _ m)
  exact (sq_lt_sq₀ hr (Demp_nonneg φ x y α)).symm

end StatFormal.Wave30tl
