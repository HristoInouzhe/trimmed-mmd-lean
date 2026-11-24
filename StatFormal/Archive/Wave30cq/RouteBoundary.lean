import StatFormal.Archive.Wave30cq.Statements
import StatFormal.Archive.Wave30ah.RouteHprops
import StatFormal.Archive.Wave30z.RouteLimit

/-!
# Route (wave 30cq): trimmed-mmd `cor:boundary-linear` (a), existence of `G_P`, `G_Q` (untrusted)

With `K° = {cν : c ≥ 0}`, `‖ν‖ = 1`, every `g ∈ K°` with `‖g‖ ≤ 1` is `cν`, `c ∈ [0,1]`. Positive homogeneity
(frozen Wave 30ah `boundary_Hprops` (b), almost surely) gives `H_P(−g) = c H_P(−ν)` and `H_Q(g) = c H_Q(ν)`, so
`G_P = −H_P(−ν) ν` and `G_Q = H_Q(ν) ν` satisfy the corollary hypothesis; the limit is then the Wave 30z
`boundary_linear`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30cq

open StatFormal.Wave30v (Ball ballNeg polarSet coneHull)
open StatFormal.Wave30z

theorem boundary_ray_G : Claims.boundary_ray_G := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 ν hφ hφb hα0 hα1 hS hSc hGP hne hν hK
  have hH := (StatFormal.Wave30ah.boundary_Hprops 𝒳 E φ κ α P Q Ω' μ' 𝔾 hφ hφb hα0 hα1 hGP).1
  set GP : Ω' → E := fun ω' => (-Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg ν)) • (ν : E) with hGPdef
  set GQ : Ω' → E := fun ω' => Hfun φ α Q κ Sum.inr (𝔾 ω') ν • (ν : E) with hGQdef
  have hnorm : ⟪(ν : E), (ν : E)⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have hhyp : ∀ᵐ ω' ∂μ', ∀ g : Ball E,
      (g : E) ∈ polarSet (closure (coneHull (StatFormal.TrimmedMMD.Concentration.region φ α Q -
        StatFormal.TrimmedMMD.Concentration.region φ α P))) →
      Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), GP ω'⟫ ∧
        Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), GQ ω'⟫ := by
    filter_upwards [hH] with ω' hω'
    intro g hg
    rw [hK] at hg
    obtain ⟨c, hc0, hgc⟩ := hg
    have hc1 : c ≤ 1 := by
      have h := g.2
      rw [mem_closedBall_zero_iff, hgc, norm_smul, hν, mul_one, Real.norm_of_nonneg hc0] at h
      exact h
    have h1 := (hω'.2 (ballNeg ν) (ballNeg g) c hc0 hc1 (by simp [ballNeg, hgc])).1
    have h2 := (hω'.2 ν g c hc0 hc1 hgc).2
    refine ⟨?_, ?_⟩
    · rw [h1, hGPdef, hgc]
      simp only [inner_neg_left, inner_smul_left, inner_smul_right, hnorm, RCLike.conj_to_real]
      ring
    · rw [h2, hGQdef, hgc]
      simp only [inner_smul_left, inner_smul_right, hnorm, RCLike.conj_to_real]
      ring
  exact ⟨GP, GQ, hhyp, (StatFormal.Wave30z.boundary_linear 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 GP GQ
    hφ hφb hα0 hα1 hS hSc hGP hne hhyp).1⟩

end StatFormal.Wave30cq
