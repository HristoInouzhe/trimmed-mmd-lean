import StatFormal.Archive.OTFD.WaveL7.Statements
import StatFormal.Archive.OTFD.WaveL7.RouteMcCann

/-!
# Route (wave L7): the moment-free claims

Untrusted route file. `brenier_uniq_H_bdd` is `RouteMcCann.brenierUniq_of_bdd_target`; each of the five A limit
claims is the certified wave-L1 theorem with its `BrenierUniq` hypothesis discharged by it (for `plan_stab_b*` the
target bound comes from the certified `tendsto_mom2_of_bounded`). `ghs_grad_unique`: the graph plans of the two
gradient maps are couplings of `(A, B)` carried by the (closed) subdifferential graphs of the two finite Lipschitz
potentials, so they are equal by the library's moment-free McCann argument; `cm_unique_uncond` is the frozen
conditional `cm_unique_cond` with its premise discharged by `ghs_grad_unique`.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL7

open StatFormal.OTFD.WaveL1

theorem brenier_uniq_H_bdd : Claims.brenier_uniq_H_bdd := by
  intro H _ _ _ _ _ _ P μ F M hL hμM hF hmap hcm
  exact brenierUniq_of_bdd_target hL hμM hF hmap hcm

theorem plan_stab_a_uncond : Claims.plan_stab_a_uncond := by
  intro H _ _ _ _ _ _ P μ F M α ν π G hL hμM hF hmap hcm hα hν hfst hsnd hcmπ hG
  exact StatFormal.OTFD.WaveL1.plan_stab_a H P μ F M α ν π G hL hμM hF
    (brenierUniq_of_bdd_target hL hμM hF hmap hcm) hα hν hfst hsnd hcmπ hG

theorem plan_stab_b_uncond : Claims.plan_stab_b_uncond := by
  intro H _ _ _ _ _ _ P μ F M ν π hL hF hmap hcm hν hM hfst hsnd hcmπ
  obtain ⟨hμM, -⟩ := tendsto_mom2_of_bounded hν hM
  exact StatFormal.OTFD.WaveL1.plan_stab_b H P μ F M ν π hL hF
    (brenierUniq_of_bdd_target hL hμM hF hmap hcm) hν hM hfst hsnd hcmπ

theorem plan_stab_b_map_uncond : Claims.plan_stab_b_map_uncond := by
  intro H _ _ _ _ _ _ P μ F M ν T hL hF hmap hcm hν hM hT hTν hTcm
  obtain ⟨hμM, -⟩ := tendsto_mom2_of_bounded hν hM
  exact StatFormal.OTFD.WaveL1.plan_stab_b_map H P μ F M ν T hL hF
    (brenierUniq_of_bdd_target hL hμM hF hmap hcm) hν hM hT hTν hTcm

theorem sieve_strong_limit_uncond : Claims.sieve_strong_limit_uncond := by
  intro H _ _ _ _ _ _ e P μ F M FK he hsp hL hμM hF hmap hcm hFK hpush hcmK
  exact StatFormal.OTFD.WaveL1.sieve_strong_limit H e P μ F M FK he hsp hL hμM hF
    (brenierUniq_of_bdd_target hL hμM hF hmap hcm) hFK hpush hcmK

theorem sieve_strong_full_uncond : Claims.sieve_strong_full_uncond := by
  intro H _ _ _ _ _ _ e P μ F M FK c he hsp hL hμM hμ0 hF hmap hcm hFK hpush hcmK
  exact StatFormal.OTFD.WaveL1.sieve_strong_full H e P μ F M FK c he hsp hL hμM hμ0 hF
    (brenierUniq_of_bdd_target hL hμM hF hmap hcm) hFK hpush hcmK

theorem ghs_grad_unique : Claims.ghs_grad_unique := by
  intro H _ _ _ _ _ _ A B hA hLip f f' T T' L L' hf hf' hL hL' hT hT' hg hg' hmT hmT'
  have hc : IsCoupling (Graph A T) A B := StatFormal.OTFD.WaveL3.isCoupling_graph hT hmT
  have hc' : IsCoupling (Graph A T') A B := StatFormal.OTFD.WaveL3.isCoupling_graph hT' hmT'
  have hae : ∀ {g : H → ℝ} {S : H → H} {K : ℝ}, ConvexOn ℝ univ g → (∀ x z, |g x - g z| ≤ K * ‖x - z‖) →
      Measurable S → (∀ᵐ x ∂A, StatFormal.Wave23d.GatDiff g x (S x)) →
      ∀ᵐ z ∂(Graph A S), z ∈ StatFormal.McCannH.subgradGraph g := by
    intro g S K hgc hgL hS hgS
    have hgm : Measurable fun x : H => (x, S x) := measurable_id.prodMk hS
    have hm : MeasurableSet (StatFormal.McCannH.subgradGraph g) :=
      (StatFormal.McCannH.isClosed_subgradGraph (StatFormal.Wave23d.continuous_of_lip hgL)).measurableSet
    rw [ae_iff]
    change Graph A S (StatFormal.McCannH.subgradGraph g)ᶜ = 0
    unfold Graph
    rw [Measure.map_apply hgm hm.compl]
    refine measure_eq_zero_iff_ae_notMem.2 (hgS.mono fun x hx => ?_)
    simp only [mem_preimage, mem_compl_iff, not_not]
    exact fun z => StatFormal.Wave23d.subgrad_of_gatDiff hgc hgL hx z
  have heq : Graph A T = Graph A T' :=
    StatFormal.McCannH.eq_of_ae_mem_subgradGraph (StatFormal.OTFD.WaveL3.lipGraph_null hLip) hc hc'
      (StatFormal.Wave23d.continuous_of_lip hL) (StatFormal.Wave23d.continuous_of_lip hL')
      (hae hf hL hT hg) (hae hf' hL' hT' hg')
  exact StatFormal.Wave23d.ae_eq_of_graph_eq hT hT' heq

theorem cm_unique_uncond : Claims.cm_unique_uncond := by
  intro H _ _ _ _ _ _ γ γ' M hγ hγ' hfst hsnd hA hM hcm hcm'
  exact StatFormal.Wave23d.cm_unique_cond_thm H γ γ' M hγ hγ' hfst hsnd hA hM hcm hcm'
    (ghs_grad_unique H γ.fst γ.snd inferInstance hA)

end StatFormal.OTFD.WaveL7
