import StatFormal.Archive.WaveP3c.Statements
import StatFormal.Archive.Wave25b.RouteGHSMain
import StatFormal.Archive.Wave24a.RouteConsistency
import StatFormal.Archive.OTFD.WaveL3.RouteUniq
import StatFormal.Lib.Empirical.Varadarajan

/-!
# Route (wave P3c), part 3: Ghosal–Sen on compacts of the interior, and A/B `thm:consistency` (untrusted)

On the Varadarajan event (`P̂_n ⇀ P_K` almost surely, certified library `Foundations/Empirical`, no moment), the
certified wave-25b `app_ghs_stability_fd` (finite dimension, no `(⋆)`) applies with `P_n = P̂_n`, `Q_n = μ_K`,
`D_n = ℝ^K`, `ψ_n = ψ̂_n`: the subgradients of the `M`-Lipschitz `ψ̂_n` have norm `≤ M`, the gradient of `ψ` at the
points of `𝒦` is `F`, and `P_K ≪ Leb` is Lipschitz-null. Then the frozen Wave 24a `consistency_A`, `consistency_B`
apply.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP3c

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open TauCeti.Probability (empiricalMeasure)

section Lip
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A subgradient of an `M`-Lipschitz function has norm at most `M`. -/
theorem norm_le_of_isSubgrad_of_lipschitz {f : E → ℝ} {M : ℝ} (hf : ∀ x x', |f x - f x'| ≤ M * ‖x - x'‖)
    (hM : 0 ≤ M) {x y : E} (hy : IsSubgrad f x y) : ‖y‖ ≤ M := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using hM
  have h1 := hy (x + y)
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1
  have h2 := hf (x + y) x
  simp only [add_sub_cancel_left] at h2
  have h3 : ‖y‖ ^ 2 ≤ M * ‖y‖ := by linarith [le_abs_self (f (x + y) - f x)]
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  nlinarith

end Lip

theorem ghosal_sen_uniform : Claims.ghosal_sen_uniform := by
  intro K Ω _ Pr _ Z P μ ψ F M L ψh γ Fh 𝒦 hind hlaw hac hμM hψc hψL hFm hmap hsub h𝒦c h𝒦i hgrad hfst hsnd hsupp
    hψhL hFh
  have hM : 0 ≤ M := by
    by_contra hM
    push Not at hM
    have : (Metric.closedBall (0 : Euc K) M) = ∅ := Metric.closedBall_eq_empty.2 hM
    rw [this, compl_empty, measure_univ] at hμM
    exact one_ne_zero hμM
  have hLip : StatFormal.OTFD.WaveL1.LipNull (P : Measure (Euc K)) := StatFormal.OTFD.WaveL3.lipNull_of_ac hac
  filter_upwards [StatFormal.Empirical.tendsto_empiricalMeasure_ae_of_iIndepFun hind hlaw] with ω hω
  have hstab := StatFormal.Wave25b.app_ghs_stability_fd (Euc K) (fun n => empiricalMeasure (fun i => Z i ω) n)
    (fun _ => μ) P μ (fun n => γ n ω) (fun _ => univ) (fun n => ψh n ω) ψ F M L 0 𝒦 hω hLip tendsto_const_nhds
    (fun _ => hμM) hμM (fun n => hfst n ω) (fun n => hsnd n ω)
    (fun n p hp => ⟨mem_univ _, fun z _ => hsupp n ω hp z⟩) hψc hψL hFm hmap hsub h𝒦c h𝒦i
    (fun x hx v => by
      have := ((hgrad x hx).hasFDerivAt).hasLineDerivAt v
      simpa using this)
    (fun n _ x _ y hy => norm_le_of_isSubgrad_of_lipschitz (hψhL n ω) hM fun z => hy.2 z (mem_univ z))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hstab (ε / 2) (half_pos hε)] with n hn x hx
  have := hn x hx (Fh n ω x) ⟨mem_univ _, fun z _ => hFh n ω x hx z⟩
  rw [dist_eq_norm, norm_sub_rev]
  linarith

theorem consistency_A_gs : Claims.consistency_A_gs := by
  intro K Ω H _ Pr _ Z P μ ψ F M L ψh γ Fh 𝒦 PiK Lm hind hlaw hac hμM hψc hψL hFm hmap hsub h𝒦c h𝒦i hgrad hfst
    hsnd hsupp hψhL hFh
  exact StatFormal.Wave24a.consistency_A Ω (Euc K) H Pr PiK Lm F Fh 𝒦
    (ghosal_sen_uniform K Ω Pr Z P μ ψ F M L ψh γ Fh 𝒦 hind hlaw hac hμM hψc hψL hFm hmap hsub h𝒦c h𝒦i hgrad hfst
      hsnd hsupp hψhL hFh)

theorem consistency_B_gs : Claims.consistency_B_gs := by
  intro K Ω H _ Pr _ Z P μ ψ F M L ψh γ Fh 𝒦 PiK g cK c' hind hlaw hac hμM hψc hψL hFm hmap hsub h𝒦c h𝒦i hgrad hfst
    hsnd hsupp hψhL hFh hg1 hg2 hg3 hcK hgF
  have h := StatFormal.Wave24a.consistency_B Ω (Euc K) H Pr PiK g cK c' F Fh 𝒦 hg1 hg2 hg3 hcK hgF
  exact ⟨h.1, h.2 (ghosal_sen_uniform K Ω Pr Z P μ ψ F M L ψh γ Fh 𝒦 hind hlaw hac hμM hψc hψL hFm hmap hsub h𝒦c
    h𝒦i hgrad hfst hsnd hsupp hψhL hFh)⟩

end StatFormal.WaveP3c
