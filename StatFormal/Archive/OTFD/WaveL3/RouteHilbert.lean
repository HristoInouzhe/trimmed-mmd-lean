import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.OTFD.WaveL3.RouteUniq
import StatFormal.Archive.OTFD.WaveL1.RouteSieve

/-!
# Route (wave L3): Hilbert claims — Brenier uniqueness and the unconditional wave-L1 limits

Untrusted route file. Each unconditional claim is the certified wave-L1 theorem applied with its
`BrenierUniq` hypothesis discharged by `RouteBrenierH` (second moments: the quantile and R items) or
`RouteUniq` (bounded target / source with a first moment: the five A plan-stability and sieve items, `W₁`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL3

open StatFormal.OTFD.WaveL1

theorem cycmon_iff : Claims.cycmon_iff := fun _ _ _ _ => cycMon_iff_isCyclicallyMonotone

theorem brenier_uniq_H : Claims.brenier_uniq_H := by
  intro H _ _ _ _ _ _ P μ F hL hP2 hμ2 hF hmap hcm
  exact brenierUniq_of_lipNull hL hP2 hμ2 hF hmap hcm

theorem brenier_uniq_H_swap : Claims.brenier_uniq_H_swap := by
  intro H _ _ _ _ _ _ P μ Q hL hP2 hμ2 hQ hmap hcm
  exact brenierUniq_swap_of_lipNull hL hP2 hμ2 hQ hmap hcm

theorem brenier_exists_H : Claims.brenier_exists_H := by
  intro H _ _ _ _ _ _ P μ hL hP2 hμ2
  exact exists_brenierMap_of_lipNull hL hP2 hμ2

theorem brenier_uniq_H_bdd : Claims.brenier_uniq_H_bdd := by
  intro H _ _ _ _ _ _ P μ F M hL hP1 hμM hF hmap hcm
  exact brenierUniq_of_bdd_target hL hμM hP1 hF hmap hcm

theorem brenier_uniq_bdd_source : Claims.brenier_uniq_bdd_source := by
  intro H _ _ _ _ _ _ μ P Q M hL hμM hP1 hQ hmap hcm
  exact brenierUniq_of_bdd_source hL hμM hP1 hQ hmap hcm

/-! ### A `lem:plan-stability-H` -/

theorem plan_stab_a_uncond : Claims.plan_stab_a_uncond := by
  intro H _ _ _ _ _ _ P μ F M α ν π G hL hP1 hμM hF hmap hcm hα hν hfst hsnd hcmπ hG
  exact StatFormal.OTFD.WaveL1.plan_stab_a H P μ F M α ν π G hL hμM hF
    (brenierUniq_of_bdd_target hL hμM hP1 hF hmap hcm) hα hν hfst hsnd hcmπ hG

theorem plan_stab_b_uncond : Claims.plan_stab_b_uncond := by
  intro H _ _ _ _ _ _ P μ F M ν π hL hP1 hF hmap hcm hν hM hfst hsnd hcmπ
  obtain ⟨hμM, -⟩ := tendsto_mom2_of_bounded hν hM
  exact StatFormal.OTFD.WaveL1.plan_stab_b H P μ F M ν π hL hF
    (brenierUniq_of_bdd_target hL hμM hP1 hF hmap hcm) hν hM hfst hsnd hcmπ

theorem plan_stab_b_map_uncond : Claims.plan_stab_b_map_uncond := by
  intro H _ _ _ _ _ _ P μ F M ν T hL hP1 hF hmap hcm hν hM hT hTν hTcm
  obtain ⟨hμM, -⟩ := tendsto_mom2_of_bounded hν hM
  exact StatFormal.OTFD.WaveL1.plan_stab_b_map H P μ F M ν T hL hF
    (brenierUniq_of_bdd_target hL hμM hP1 hF hmap hcm) hν hM hT hTν hTcm

/-! ### A sieve limits -/

theorem sieve_strong_limit_uncond : Claims.sieve_strong_limit_uncond := by
  intro H _ _ _ _ _ _ e P μ F M FK he hsp hL hP1 hμM hF hmap hcm hFK hpush hcmK
  exact StatFormal.OTFD.WaveL1.sieve_strong_limit H e P μ F M FK he hsp hL hμM hF
    (brenierUniq_of_bdd_target hL hμM hP1 hF hmap hcm) hFK hpush hcmK

theorem sieve_strong_full_uncond : Claims.sieve_strong_full_uncond := by
  intro H _ _ _ _ _ _ e P μ F M FK c he hsp hL hP1 hμM hμ0 hF hmap hcm hFK hpush hcmK
  exact StatFormal.OTFD.WaveL1.sieve_strong_full H e P μ F M FK c he hsp hL hμM hμ0 hF
    (brenierUniq_of_bdd_target hL hμM hP1 hF hmap hcm) hFK hpush hcmK

theorem integrated_quantile_uncond : Claims.integrated_quantile_uncond := by
  intro H _ _ _ _ _ _ e P μ Q M QK he hsp hP hμM hQ hmap hcm hQK hpush hcmK
  exact StatFormal.OTFD.WaveL1.integrated_quantile H e P μ Q M QK he hsp hP hμM hQ
    (brenierUniq_swap_of_lipNull hP.2.2 hP.2.1.ne (mom2_ne_top_of_bounded hμM) hQ hmap hcm)
    hQK hpush hcmK

/-! ### R `lem:plan-w2`, `thm:moment-sieve` -/

theorem plan_w2_a_uncond : Claims.plan_w2_a_uncond := by
  intro H _ _ _ _ _ _ P μ F α ν π G hP hμ2 hF hmap hcm hα hν hfst hsnd hcmπ hG
  exact StatFormal.OTFD.WaveL1.plan_w2_a H P μ F α ν π G hP hμ2 hF
    (brenierUniq_of_lipNull hP.2.2 hP.2.1.ne hμ2 hF hmap hcm) hα hν hfst hsnd hcmπ hG

theorem plan_w2_b_uncond : Claims.plan_w2_b_uncond := by
  intro H _ _ _ _ _ _ P μ F ν π hP hμ2 hF hmap hcm hν hfst hsnd hcmπ
  exact StatFormal.OTFD.WaveL1.plan_w2_b H P μ F ν π hP hμ2 hF
    (brenierUniq_of_lipNull hP.2.2 hP.2.1.ne hμ2 hF hmap hcm) hν hfst hsnd hcmπ

theorem plan_w2_b_map_uncond : Claims.plan_w2_b_map_uncond := by
  intro H _ _ _ _ _ _ P μ F ν T hP hμ2 hF hmap hcm hν hT hTν hTcm
  exact StatFormal.OTFD.WaveL1.plan_w2_b_map H P μ F ν T hP hμ2 hF
    (brenierUniq_of_lipNull hP.2.2 hP.2.1.ne hμ2 hF hmap hcm) hν hT hTν hTcm

theorem moment_sieve_a_uncond : Claims.moment_sieve_a_uncond := by
  intro H _ _ _ _ _ _ e P μ F FK he hsp hP hμ2 hF hmap hcm hFK hpush hcmK
  exact StatFormal.OTFD.WaveL1.moment_sieve_a H e P μ F FK he hsp hP hμ2 hF
    (brenierUniq_of_lipNull hP.2.2 hP.2.1.ne hμ2 hF hmap hcm) hFK hpush hcmK

theorem moment_sieve_b_uncond : Claims.moment_sieve_b_uncond := by
  intro H _ _ _ _ _ _ e P μ Q QK he hsp hP hμ hQ hmap hcm hQK hpush hcmK
  exact StatFormal.OTFD.WaveL1.moment_sieve_b H e P μ Q QK he hsp hP hμ hQ
    (brenierUniq_swap_of_lipNull hP.2.2 hP.2.1.ne hμ.2.1.ne hQ hmap hcm) hQK hpush hcmK

/-! ### `W₁` targets -/

theorem lipnull_of_ac : Claims.lipnull_of_ac := fun _ _ hμ => StatFormal.OTFD.WaveL3.lipNull_of_ac hμ

theorem plan_stab_w1 : Claims.plan_stab_w1 := by
  intro H _ _ _ _ _ _ μ P Q M α ν π G hL hμM hP1 hQ hmap hcm hα hν hfst hsnd hcmπ hG
  exact tendsto_of_cmConc (brenierUniq_of_bdd_source hL hμM hP1 hQ hmap hcm) hα hν hfst hsnd hcmπ hG

end StatFormal.OTFD.WaveL3
