import StatFormal.Wave31tq.RouteM25

/-!
# Wave 31tq, route M (Q27): the printed sentences about the Laplace kernel under Proposition 5.5 (untrusted)

`laplace_instances_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments)
(h5 : Claims.sobolev_angular) (hk : Claims.kernel_instances) : Claims.laplace_instances`. The Laplace profile `e^{−|x|/σ}` is
continuous, integrable and satisfies Proposition 5.5's two-sided bound with `s = 1`, `c = 2σ min(1, σ^{−2})`,
`C = 2σ max(1, σ^{−2})` (Q7(a), `Claims.kernel_instances`, chunk A); `‖φ x‖ = 1`. Then (a) is `newsobolev_E1_of`, (b)
`rate_sobolev_split_of`, (c) `excess_sobolev_of`, (d) `lower_sobolev_A_of` with `κ = 1`, at `s = 1`: `(2s+3)/4 = 5/4`,
`2/(2s+3) = 2/5`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteM

open StatFormal StatFormal.TrimmedMMD.Unconditional StatFormal.CrossLaws StatFormal.Distances

/-- Q27 `laplace_instances`, from Q1, Q12 case 2, Q20, Q5 and Q7. -/
theorem laplace_instances_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments)
    (h5 : Claims.sobolev_angular) (hk : Claims.kernel_instances) : Claims.laplace_instances := by
  intro H _ _ _ _ φ σ P Q _ _ p q x₀ ℓ₀ hσ hg hcross hpx hexp
  obtain ⟨hkc, hki, -, -, hkb, -⟩ := hk.1 σ hσ
  have hc : 0 < 2 * σ * min 1 (σ ^ 2)⁻¹ := mul_pos (by positivity) (lt_min one_pos (by positivity))
  have hs : (1 : ℝ) / 2 < 1 := by norm_num
  have e : (2 * (1 : ℝ) + 3) / 4 = 5 / 4 := by norm_num
  have e2 : (2 : ℝ) / (2 * 1 + 3) = 2 / 5 := by norm_num
  have hnorm : ∀ x, ‖φ x‖ ≤ 1 := fun x => by
    have h := hg x x
    rw [real_inner_self_eq_norm_sq, sub_self, abs_zero, neg_zero, zero_div, Real.exp_zero] at h
    nlinarith [norm_nonneg (φ x)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := newsobolev_E1_of h1 hcor hmom H φ (fun x => Real.exp (-|x| / σ)) (2 * σ * min 1 (σ ^ 2)⁻¹)
      (2 * σ * max 1 (σ ^ 2)⁻¹) 1 P Q p q x₀ ℓ₀ hkc hki hg hc hs hkb hcross hpx hexp
    rw [e] at h
    exact h
  · intro J δ s2 η hJ hδ hδ1 hs2 hs24 hη hη1
    have h := rate_sobolev_split_of h1 hcor H φ (fun x => Real.exp (-|x| / σ)) (2 * σ * min 1 (σ ^ 2)⁻¹)
      (2 * σ * max 1 (σ ^ 2)⁻¹) 1 1 P Q p q x₀ ℓ₀ J δ s2 η hkc hki hg hc hs hkb hcross hpx hexp hnorm hJ hδ hδ1 hs2
      hs24 hη hη1
    rw [e2] at h
    exact h
  · have h := excess_sobolev_of h1 hcor hmom h5 H φ (fun x => Real.exp (-|x| / σ)) (2 * σ * min 1 (σ ^ 2)⁻¹)
      (2 * σ * max 1 (σ ^ 2)⁻¹) 1 P Q p q x₀ ℓ₀ hkc hki hg hc hs hkb hcross hpx hexp
    rw [e] at h
    exact h
  · intro D δ δ' hD hδ hδδ' hδ'1
    have h := lower_sobolev_A_of h1 hcor hmom h5 H φ (fun x => Real.exp (-|x| / σ)) (2 * σ * min 1 (σ ^ 2)⁻¹)
      (2 * σ * max 1 (σ ^ 2)⁻¹) 1 1 D δ δ' P Q p q x₀ ℓ₀ hkc hki hg hc hs hkb hcross hpx hexp hnorm hD hδ hδδ' hδ'1
    rw [e2] at h
    exact h

end StatFormal.Wave31tq.RouteM
