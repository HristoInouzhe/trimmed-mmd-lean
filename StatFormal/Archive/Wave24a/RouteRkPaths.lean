import StatFormal.Archive.Wave24a.Statements
import StatFormal.Archive.OTFD.Bands.Proofs
import StatFormal.Archive.OTFD.Wave19a.RouteSubgrad
import StatFormal.Archive.OTFD.Wave22b.RouteConvex
import StatFormal.Archive.Wave23a.RouteProbContent
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Route — B `prop:rk-paths` (untrusted)

(i) The certified `prop:band-boundary`(i) at `u = 0` with `M v` in place of `v` (`M⁻¹ M v = v`), composed with the
nondecreasing `p ↦ τ_p`. (ii) `F(Q(τv)) = τv`, `ρ(τv) = τ`, `c_K(c_K^{-1}(p)) = p` (Wave 23a `cdfK_inv_spec`) and
`τ > 0` because `c_K(0) = 0 < p`. (iii) The certified `lem:app-subgradient-convergence`(b) (`subgrad_conv_unif`) on
`A_{K,1−δ}`; for `v̂_n → v`, add uniform continuity of `∇χ` on the compact `A_{K,1−δ}` (continuous on `O` by the
Wave 22b `continuousAt_gradient`), with `‖τ v̂_n − τ v‖ ≤ B‖v̂_n − v‖`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Metric Matrix

namespace StatFormal.Wave24a

theorem rk_paths_mono : Claims.rk_paths_mono := by
  intro K M ψ T v τ Pv hM hψ hT hτ
  have h := StatFormal.OTFD.Bands.band_boundary_mono K M ψ T hM hψ hT 0 (M *ᵥ v)
  have hinv : M⁻¹ *ᵥ (M *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).1 (Matrix.PosDef.isUnit hM)), Matrix.one_mulVec]
  simp only [zero_add, hinv] at h
  exact fun a ha b hb hab => h (hτ ha hb hab)

theorem rk_paths_labels : Claims.rk_paths_labels := by
  intro K μ ρ Q F U v p hc h0 h1 hhom hv hFQ hp0 hp1 hmem
  obtain ⟨hτI, hτ⟩ := StatFormal.Wave23a.cdfK_inv_spec μ ρ hc h0 h1 ⟨hp0.le, hp1⟩
  set τ := StatFormal.Wave23a.cdfKInv μ ρ p with hτdef
  have hFQτ : F (Q (τ • v)) = τ • v := hFQ _ hmem
  have hρτ : ρ (τ • v) = τ := by rw [hhom τ hτI.1, hv, mul_one]
  have hτpos : τ ≠ 0 := by
    intro h; rw [h, h0] at hτ; linarith
  refine ⟨by rw [hFQτ, hρτ, hτ], ?_⟩
  rw [hFQτ, hρτ, smul_smul, inv_mul_cancel₀ hτpos, one_smul]

theorem rk_paths_consistency : Claims.rk_paths_consistency := by
  intro K C O A1 SK χ g T τ P v vh hC hCc hχ hg hgu hO hOC hdiff hA1 hA1O hT hSK
  have hunif := StatFormal.OTFD.Wave19a.subgrad_conv_unif K C g χ O A1 hC hCc hg hχ hgu hO hOC hdiff hA1O hA1
  refine ⟨fun ε hε => ?_, fun hv hvh ⟨B, hB⟩ hlim ε hε => ?_⟩
  · filter_upwards [hunif ε hε] with n hn w hw p hp
    exact hn _ (hSK w hw p hp) _ (hT n _ (hSK w hw p hp))
  · have hgc : ContinuousOn (gradient χ) A1 := fun u hu =>
      (StatFormal.OTFD.Wave22b.continuousAt_gradient hC hCc hχ hO hOC hdiff (hA1O hu)).continuousWithinAt
    have hU := hA1.uniformContinuousOn_of_continuous hgc
    rw [Metric.uniformContinuousOn_iff] at hU
    obtain ⟨δ, hδ, hδU⟩ := hU (ε / 2) (by positivity)
    have hB0 : 0 ≤ |B| := abs_nonneg B
    have hvev : ∀ᶠ n in atTop, ‖vh n - v‖ < δ / (|B| + 1) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (gt_mem_nhds (by positivity :
        (0 : ℝ) < δ / (|B| + 1)))
      exact this
    filter_upwards [hunif (ε / 2) (by positivity), hvev] with n hn hvn p hp
    have h1 := hn _ (hvh n p hp) _ (hT n _ (hvh n p hp))
    have h2 : dist (gradient χ (τ p • vh n)) (gradient χ (τ p • v)) < ε / 2 := by
      refine hδU _ (hvh n p hp) _ (hv p hp) ?_
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
      calc |τ p| * ‖vh n - v‖ ≤ (|B| + 1) * ‖vh n - v‖ := by
            gcongr; linarith [hB p hp, le_abs_self B]
        _ < (|B| + 1) * (δ / (|B| + 1)) := by gcongr
        _ = δ := by field_simp
    rw [dist_eq_norm] at h2
    calc ‖T n (τ p • vh n) - gradient χ (τ p • v)‖
        ≤ ‖T n (τ p • vh n) - gradient χ (τ p • vh n)‖ + ‖gradient χ (τ p • vh n) - gradient χ (τ p • v)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε / 2 + ε / 2 := by linarith
      _ = ε := by ring

example : Claims.rk_paths_mono := rk_paths_mono
example : Claims.rk_paths_labels := rk_paths_labels
example : Claims.rk_paths_consistency := rk_paths_consistency

end StatFormal.Wave24a
