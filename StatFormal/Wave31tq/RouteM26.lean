import StatFormal.Wave31tq.RouteM21
import StatFormal.Wave31tp.Proofs
import StatFormal.Wave31tr.RouteExcess

/-!
# Wave 31tq, route M (Q26): `prop:excess` (ii) "this holds under the hypotheses of Proposition 5.5" (untrusted)

`excess_sobolev_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments)
(h5 : Claims.sobolev_angular) : Claims.excess_sobolev`. Proposition 5.5 (`newsobolev_of`) gives the two-sided bound with
`γ = (2s+3)/4`; the certified 31tr theorem `excess_ii` (part (Pr), `Wave31tr.RouteExcess.excess_ii_route`) gives the excess at the
printed cuts, with (A1) from the certified 31tp L16 (`mmd_fourier`: `φ` strongly measurable, `‖φ x‖ = √k₀(0)`) and (A3) from Q5(b)
(`Claims.sobolev_angular`, chunk A: a kernel with `k̂₀ ≥ c(1 + ξ²)^{−s}` is characteristic).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteM

open StatFormal StatFormal.TrimmedMMD.Unconditional StatFormal.CrossLaws StatFormal.Distances

/-- The spectral lower bound on `ℝ` in the norm form of Q5. -/
theorem spec_norm {k₀ : ℝ → ℝ} {c s : ℝ} (hkb : ∀ ξ : ℝ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ) :
    ∀ ξ : ℝ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ := fun ξ => by
  rw [Real.norm_eq_abs, sq_abs]; exact hkb ξ

/-- (A3) under Prop 5.5's kernel hypotheses: the kernel is characteristic (Q5(b)). -/
theorem sobolev_char (h5 : Claims.sobolev_angular)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : ℝ → H} {k₀ : ℝ → ℝ} {c s : ℝ}
    (hk : Continuous k₀) (hki : Integrable k₀) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) (hc : 0 < c)
    (hkb : ∀ ξ : ℝ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ) :
    StatFormal.TrimmedMMD.ZeroSet.Characteristic φ ∧
      ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν], ∫ x, φ x ∂μ = ∫ x, φ x ∂ν → μ = ν := by
  have h := (h5.1 ℝ H φ k₀ c s hk hki hg hc (spec_norm hkb)).2.1
  exact ⟨h.2.1, h.1⟩

/-- Q26 `excess_sobolev` (Proposition 5.10(ii) under Proposition 5.5), from Q1, Q12 case 2, Q20 (through `newsobolev_of`) and
Q5 (`Claims.sobolev_angular`). -/
theorem excess_sobolev_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments)
    (h5 : Claims.sobolev_angular) : Claims.excess_sobolev := by
  intro H _ _ _ _ φ k₀ c C s P Q _ _ p q x₀ ℓ₀ hk hki hg hc hs hkb hcross hpx hexp
  obtain ⟨htv0, htv1, c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hε₀tv, hb⟩ :=
    newsobolev_of h1 hcor hmom H φ k₀ c C s P Q p q x₀ ℓ₀ hk hki hg hc hs hkb hcross hpx hexp
  have hchar := (sobolev_char h5 hk hki hg hc (fun ξ => (hkb ξ).1)).1
  obtain ⟨-, hsm, hnorm, -⟩ := StatFormal.Wave31tp.mmd_fourier ℝ H φ k₀ hk hki hg
  refine ⟨c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hε₀tv, hb, fun ε hε a b tS uS ha hb' hab ht hu => ?_⟩
  exact StatFormal.Wave31tr.RouteExcess.excess_ii_route.2 ℝ H P Q φ (√(k₀ 0)) ((2 * s + 3) / 4) c₁ c₂ ε₀ ε a b tS uS
    hsm (fun x => (hnorm x).le) hchar htv0 htv1 (by linarith) hc₁ (hc₁.trans_le hc₁₂) hε₀ hε₀tv
    (fun e he1 he2 => hb e ⟨he1, he2⟩) hε.1 hε.2 ha hb' hab ht hu

end StatFormal.Wave31tq.RouteM
