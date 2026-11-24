import StatFormal.Archive.OTFD.WaveL8.Statements
import StatFormal.Archive.OTFD.WaveL7.RouteClaims
import StatFormal.Archive.OTFD.WaveL6.RouteForward
import StatFormal.Archive.Wave23b.RouteConvRef
import StatFormal.Archive.Wave24f.RouteRate

/-!
# Route (wave L8): sieve limits and reference convergence without the first moment (bounded targets)

Untrusted route file. Each proof is the frozen route of the same claim (`OTFD/WaveL6/RouteForward`,
`Wave23b/RouteConvRef`, `Wave24f/RouteRate`) with the only moment use replaced: the wave-L3
`sieve_strong_limit_uncond` / `brenier_uniq_H_bdd` (first moment of `P`) by their moment-free wave-L7 forms
(`OTFD/WaveL7`, McCann's argument for bounded targets). No other change.
-/

set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.OTFD.WaveL8

section L6
open StatFormal.OTFD.WaveL6
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave22a (IsSubgrad supAff cubeH)

theorem sieve_conv_weak : StatFormal.OTFD.WaveL8.Claims.sieve_conv_weak := by
  intro H _ _ _ _ _ _ e P μ ψ F M Lψ Lφ φ FK K₀ h he htot hLN hμM hψc hψL hFm hmap hFsub hlip hFK
    hpush hsub hK hKs hd ε hε
  have hL2 := StatFormal.OTFD.WaveL7.sieve_strong_limit_uncond H e P μ F M FK he htot hLN hμM hFm hmap
    (isCMMapAE_of_ae_subgrad hFsub) hFK hpush (fun K => isCMMapAE_of_ae_subgrad (hsub K))
  obtain ⟨hM, hG, hconv⟩ := sieve_core he (P : Measure H) hlip hFK hFm hsub hL2
  exact ConvexH.eventually_abs_inner_le (P : Measure H) hM hG hFsub (lip_max hψL) (le_max_right _ _)
    hψc hconv hK hKs hd h hε

theorem sieve_conv_norm : StatFormal.OTFD.WaveL8.Claims.sieve_conv_norm := by
  intro H _ _ _ _ _ _ e P μ ψ F M Lψ Lφ φ FK K₀ C he htot hLN hμM hψc hψL hFm hmap hFsub hlip hFK
    hpush hsub hK hKs hd hC hrange hFC ε hε
  have hL2 := StatFormal.OTFD.WaveL7.sieve_strong_limit_uncond H e P μ F M FK he htot hLN hμM hFm hmap
    (isCMMapAE_of_ae_subgrad hFsub) hFK hpush (fun K => isCMMapAE_of_ae_subgrad (hsub K))
  obtain ⟨hM, hG, hconv⟩ := sieve_core he (P : Measure H) hlip hFK hFm hsub hL2
  exact ConvexH.eventually_norm_le (P : Measure H) hM hG hFsub (lip_max hψL) (le_max_right _ _)
    hψc hconv hK hKs hd hC (fun K x y hx hy => hrange K x hx y hy) hFC hε

theorem sieve_conv_norm_cube : StatFormal.OTFD.WaveL8.Claims.sieve_conv_norm_cube := by
  intro H _ _ _ _ _ _ e lam P μ S b x₀ F M SK bK zK FK K₀ he htot hlam0 hlam hLN hμM hS hScube hbdd
    hFm hmap hFsub hSK hbox hbddK hFK hpush hsub hK hKs hd ε hε
  set R := Real.sqrt (∑' k, lam k ^ 2)
  have hSR : ∀ y ∈ S, ‖y‖ ≤ R := fun y hy => norm_le_of_mem_cubeH he htot hlam (hScube hy)
  obtain ⟨hψc, hψL⟩ := Wave22a.ghs_lip H S b R x₀ hS hSR hbdd
  have hφL : ∀ K z z', |supAff (SK K) (bK K) z - supAff (SK K) (bK K) z'| ≤ R * ‖z - z'‖ :=
    fun K => (Wave22a.ghs_lip (Euc K) (SK K) (bK K) R (zK K) (hSK K)
      (fun z hz => norm_le_of_box hlam (hbox K z hz)) (hbddK K)).2
  have hcube : IsCompact (cubeH e lam) := ConvexH.isCompact_cube he htot hlam
  have hrange : ∀ K, ∀ x ∈ K₀, ∀ y, IsSubgrad (fun x' => supAff (SK K) (bK K) (truncK e K x')) x y →
      y ∈ cubeH e lam := fun K x _ y hy =>
    Wave22a.sieve_subgrad_cube H e lam K (SK K) (bK K) (zK K) he hlam0 (hSK K) (hbox K) (hbddK K) x y hy
  have hFC : ∀ x ∈ K₀, F x ∈ cubeH e lam := by
    intro x hx
    have hsg : IsSubgrad (supAff S b) x (F x) := ConvexH.subgrad_of_hasLineDerivAt hψc (hd x hx)
    have hcl := Wave22a.ghs_lip_subgrad H S b R x₀ hS hSR hbdd x (F x) hsg
    exact closure_minimal (convexHull_min hScube (convex_cubeH e lam)) hcube.isClosed hcl
  exact StatFormal.OTFD.WaveL8.sieve_conv_norm H e P μ (supAff S b) F M R R (fun K => supAff (SK K) (bK K)) FK K₀ (cubeH e lam)
    he htot hLN hμM hψc hψL hFm hmap hFsub hφL hFK hpush hsub hK hKs hd hcube hrange hFC ε hε

end L6

section W23b
open StatFormal.Wave23b
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave8b (embed proj embLaw)
open StatFormal.OTFD.WaveL1 (LipNull BrenierUniq IsCMMapAE CycMon CMConc)

theorem convref_a_uncond : StatFormal.OTFD.WaveL8.Claims.convref_a_uncond := by
  intro H _ _ _ _ _ _ P μ e M ν F νH Fμ he hLip hνM hFm hFlaw hCM hνH hconv hFμm hFμlaw hFμcm
  have hsupp := support_of_tendsto hconv (embLaw_ball he hνM hνH)
  exact convref_a H P μ e M ν F νH Fμ he hLip hνM hFm hFlaw hCM hνH hconv hFμm
    (StatFormal.OTFD.WaveL7.brenier_uniq_H_bdd H P μ Fμ M hLip hsupp hFμm hFμlaw hFμcm)

theorem convref_b_uncond : StatFormal.OTFD.WaveL8.Claims.convref_b_uncond := by
  intro H Ω _ _ _ _ _ _ _ Pr _ X Y e M ν F νH μY hX hY he hLip hνM hFm hFlaw hCM hνH hμY hconv
  obtain ⟨htend, hid⟩ := convref_b H Ω Pr X Y e M ν F νH μY hX hY he hLip hνM hFm hFlaw hCM hνH hμY hconv
  refine ⟨htend, fun Fμ hFμm hFμlaw hFμcm => hid Fμ hFμm ?_⟩
  have hsupp := support_of_tendsto htend (embLaw_ball he hνM hνH)
  exact StatFormal.OTFD.WaveL7.brenier_uniq_H_bdd H ⟨Pr.map X, inferInstance⟩ μY Fμ M hLip hsupp hFμm
    hFμlaw hFμcm

end W23b

section W24f
open Finset
open StatFormal.Wave24f
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave16b (rmsE)

theorem app_sample_rate : StatFormal.OTFD.WaveL8.Claims.app_sample_rate := by
  intro H _ _ _ _ _ _ e P μ F M FK Ω _ Pr _ Kn X Fhat Fm μgrid L α he hsp hL hμM hF hmap hcm hFK hpush
    hcmK hKn hX hlaw hm1 hm2 hα0 hα1 hgrid hgrid0
  -- the sieve error
  set s : (n : ℕ) → H → ℝ := fun n x => ‖embed e (Kn n) (FK (Kn n) (truncK e (Kn n) x)) - F x‖ with hs
  have hsm : ∀ n, Measurable (s n) := fun n =>
    ((((StatFormal.OTFD.WaveL1.continuous_embed e (Kn n)).measurable.comp
      ((hFK (Kn n)).comp (StatFormal.OTFD.WaveL1.continuous_truncK e (Kn n)).measurable)).sub hF)).norm
  -- three-term decomposition
  have hdec : ∀ n, rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖) ≤
      rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖) +
        (rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) +
          (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) := by
    intro n
    have h := StatFormal.OTFD.Wave16b.rate_decomp H (Kn n) n Ω Pr (embedLI he (Kn n)) (Fhat n) (Fm n)
      (fun ω i => FK (Kn n) (truncK e (Kn n) (X n ω i))) (fun ω i => F (X n ω i)) (hm1 n) (hm2 n)
      (fun i => (hsm n).comp (hX n i))
    simp only [embedLI_apply] at h
    refine h.trans ?_
    rw [add_assoc]
    gcongr
    exact rmsE_iid_le Pr (X n) (P : Measure H) (s n) (hsm n) (fun x => norm_nonneg _) (hX n) (hlaw n)
  -- the sieve term tends to zero
  have hsieve := StatFormal.OTFD.WaveL7.sieve_strong_limit_uncond H e P μ F M FK he hsp hL hμM hF hmap hcm
    hFK hpush hcmK
  have hs0 : Tendsto (fun n => (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) atTop (𝓝 0) := by
      have := hsieve.comp hKn
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, hs]
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have h2 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    exact h2.comp h1
  have hgs : Tendsto (fun n => rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) +
      (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgrid0 (fun _ => bot_le) hgrid
    simpa using hg.add hs0
  constructor
  · calc limsup (fun n => rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖)) atTop
        ≤ limsup ((fun n => rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖)) +
            fun n => rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) +
              (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) atTop :=
          limsup_le_limsup (Eventually.of_forall hdec)
      _ = _ := ENNReal.limsup_add_of_right_tendsto_zero hgs _
  · intro hemp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hdec
    simpa using hemp.add hgs

end W24f

end StatFormal.OTFD.WaveL8
