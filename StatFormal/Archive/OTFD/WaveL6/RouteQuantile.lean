import StatFormal.Archive.OTFD.WaveL6.RouteForward

/-!
# Route (wave L6): A `thm:sieve-convergence`, exchanged (quantile) limits

Untrusted route file. The certified mean-square limit `WaveL3.integrated_quantile_uncond` (source `μ`, targets
`P_K`), turned by `sieve_core` (with `A = μ`) into convergence in `μ`-measure of `ι_K Q_{+,K} ∘ Π_K ∈ ∂χ_K`, then
`ConvexH.eventually_abs_inner_le` (resp. `eventually_norm_le`) on `𝒦₀' ⊆ int (supp μ)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL6

theorem sieve_quant_weak : Claims.sieve_quant_weak := by
  intro H _ _ _ _ _ _ e P μ χ Q M Lχ Lφ φ QK K₀ h he htot hPell hμM hχc hχL hQm hmap hQsub hlip hQK
    hpush hsub hK hKs hd ε hε
  have hL2 := WaveL3.integrated_quantile_uncond H e P μ Q M QK he htot hPell hμM hQm hmap
    (isCMMapAE_of_ae_subgrad hQsub) hQK hpush (fun K => isCMMapAE_of_ae_subgrad (hsub K))
  obtain ⟨hM, hG, hconv⟩ := sieve_core he (μ : Measure H) hlip hQK hQm hsub hL2
  exact ConvexH.eventually_abs_inner_le (μ : Measure H) hM hG hQsub (lip_max hχL) (le_max_right _ _)
    hχc hconv hK hKs hd h hε

theorem sieve_quant_norm : Claims.sieve_quant_norm := by
  intro H _ _ _ _ _ _ e P μ χ Q M Lχ Lφ φ QK K₀ C he htot hPell hμM hχc hχL hQm hmap hQsub hlip hQK
    hpush hsub hK hKs hd hC hrange hQC ε hε
  have hL2 := WaveL3.integrated_quantile_uncond H e P μ Q M QK he htot hPell hμM hQm hmap
    (isCMMapAE_of_ae_subgrad hQsub) hQK hpush (fun K => isCMMapAE_of_ae_subgrad (hsub K))
  obtain ⟨hM, hG, hconv⟩ := sieve_core he (μ : Measure H) hlip hQK hQm hsub hL2
  exact ConvexH.eventually_norm_le (μ : Measure H) hM hG hQsub (lip_max hχL) (le_max_right _ _)
    hχc hconv hK hKs hd hC (fun K u y hu hy => hrange K u hu y hy) hQC hε

end StatFormal.OTFD.WaveL6
