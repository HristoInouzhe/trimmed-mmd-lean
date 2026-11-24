import StatFormal.Archive.WaveP3c.RouteCond
import StatFormal.Archive.WaveP3c.RouteGS
import StatFormal.Archive.WaveP3c.RouteLip
import StatFormal.Archive.WaveP3c.RouteSieve

/-!
# Route (wave P3c), part 5: the new claims imply the frozen ones (mechanical check), and the claim–theorem check
-/

set_option linter.style.longLine false

namespace StatFormal.WaveP3c

/-! ### Each discharged claim implies the frozen claim of its stem -/

theorem implies_app_ghs_existence : Claims.ghs_existence_lipNull → StatFormal.Wave25b.Claims.app_ghs_existence :=
  fun h H _ _ _ _ _ _ P Q hP => h H P Q hP.2.2

theorem implies_cond_potentials_weighted :
    Claims.cond_potentials_weighted_mccann → StatFormal.OTFD.WaveL8.Claims.cond_potentials_weighted :=
  fun h K μ P U Q α ν χn g ζ hR hQm hmap hcm hF => (h K μ P U α ν χn g ζ hR hF).2 Q hQm hmap hcm

theorem implies_cond_maps_ae_weighted :
    Claims.cond_maps_ae_weighted_mccann → StatFormal.OTFD.WaveL8.Claims.cond_maps_ae_weighted :=
  fun h K μ P U χ Q Qn α ν χn g ζ hR hQm hmap hχ hQχ hF hg hQn =>
    (h K μ P U Qn α ν χn g ζ hR hF hg hQn).2 χ Q hQm hmap hχ hQχ

theorem implies_cond_band_one_sided_weighted :
    Claims.cond_band_one_sided_weighted_mccann → StatFormal.OTFD.WaveL8.Claims.cond_band_one_sided_weighted :=
  fun h K 𝒯 μ P U A χ Q Qn α ν χn g ζ e R EK hR hQm hmap hχ hQχ hF hg hQn hA hQR he =>
    (h K 𝒯 μ P U Qn α ν χn g ζ e EK hR hF hg hQn he).2 A χ Q R hQm hmap hχ hQχ hA hQR

theorem implies_cond_test_coverage_weighted :
    Claims.cond_test_coverage_weighted_mccann → StatFormal.OTFD.WaveL8.Claims.cond_test_coverage_weighted :=
  fun h K 𝒯 μ P U A χ Q Qn α ν χn g ζ m e Ue Le R EK p κ hR hQm hmap hχ hQχ hF hg hQn hA hQR he hp hκ hUL =>
    (h K 𝒯 μ P U Qn α ν χn g ζ m e Ue Le EK κ hR hF hg hQn he hκ).2 A χ Q R p hQm hmap hχ hQχ hA hQR hp hUL

theorem implies_cond_transfer_consistency_weighted :
    Claims.cond_transfer_consistency_weighted_mccann →
      StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_weighted :=
  fun h K Ω _ P μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ hR hZ hFm hmapP hDF hFh hχ' hQχ' hQm hmap hfit hQh =>
    (h K Ω P μ P' U DF Z F Fh Qh α ν χn g ζ hR hZ hFm hmapP hDF hFh hfit hQh).2 χ' Q' hχ' hQχ' hQm hmap

theorem implies_cond_transfer_consistency_prob_weighted :
    Claims.cond_transfer_consistency_prob_weighted_mccann →
      StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_prob_weighted :=
  fun h K Ω _ P _ μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ hR hZ hFm hmapP hDF hFh hχ' hQχ' hQm hmap hfit hQh hmeas =>
    (h K Ω P μ P' U DF Z F Fh Qh α ν χn g ζ hR hZ hFm hmapP hDF hFh hfit hQh hmeas).2 χ' Q' hχ' hQχ' hQm hmap

theorem implies_cond_rank_consistency :
    Claims.cond_rank_consistency_mccann → StatFormal.OTFD.WaveL8.Claims.cond_rank_consistency_uncond :=
  fun h K n M ε R z f u g μ P U Q α ν ζ ρ hR hQm hmap hcm hF hα hu hε hεlog hcol hz hρ =>
    (h K n M ε R z f u g μ P U α ν ζ ρ hR hF hα hu hε hεlog hcol hz hρ).2 Q hQm hmap hcm

theorem implies_sieve_conv_weak :
    Claims.sieve_conv_weak_mccann → StatFormal.OTFD.WaveL8.Claims.sieve_conv_weak :=
  fun h H _ _ _ _ _ _ e P μ ψ F M Lψ Lφ φ FK K₀ x he hspan hP hμ hψc hψL hFm hmap hsub hφL hFKm hFKmap hFKsub hK₀
    hK₀i hder => (h H e P μ M he hP hμ).2 ψ F Lψ Lφ φ FK K₀ x hspan hψc hψL hFm hmap hsub hφL hFKm hFKmap hFKsub hK₀
      hK₀i hder

theorem implies_sieve_conv_norm :
    Claims.sieve_conv_norm_mccann → StatFormal.OTFD.WaveL8.Claims.sieve_conv_norm :=
  fun h H _ _ _ _ _ _ e P μ ψ F M Lψ Lφ φ FK K₀ C he hspan hP hμ hψc hψL hFm hmap hsub hφL hFKm hFKmap hFKsub hK₀
    hK₀i hder hC hCK hFC => (h H e P μ M he hP hμ).2 ψ F Lψ Lφ φ FK K₀ C hspan hψc hψL hFm hmap hsub hφL hFKm hFKmap
      hFKsub hK₀ hK₀i hder hC hCK hFC

/-! ### The claim–theorem check (as the gate will do) -/

example : Claims.ghs_existence_lipNull := ghs_existence_lipNull
example : Claims.mccann_exists_H := mccann_exists_H
example : Claims.mccann_exists_fd := mccann_exists_fd
example : Claims.cond_potentials_weighted_mccann := cond_potentials_weighted_mccann
example : Claims.cond_maps_ae_weighted_mccann := cond_maps_ae_weighted_mccann
example : Claims.cond_band_one_sided_weighted_mccann := cond_band_one_sided_weighted_mccann
example : Claims.cond_test_coverage_weighted_mccann := cond_test_coverage_weighted_mccann
example : Claims.cond_transfer_consistency_weighted_mccann := cond_transfer_consistency_weighted_mccann
example : Claims.cond_transfer_consistency_prob_weighted_mccann := cond_transfer_consistency_prob_weighted_mccann
example : Claims.cond_rank_consistency_mccann := cond_rank_consistency_mccann
example : Claims.ghs_lipschitz_exists := ghs_lipschitz_exists
example : Claims.semidiscrete_exists := semidiscrete_exists
example : Claims.ghosal_sen_uniform := ghosal_sen_uniform
example : Claims.consistency_A_gs := consistency_A_gs
example : Claims.consistency_B_gs := consistency_B_gs
example : Claims.sieve_conv_weak_mccann := sieve_conv_weak_mccann
example : Claims.sieve_conv_norm_mccann := sieve_conv_norm_mccann

end StatFormal.WaveP3c
