import StatFormal.Wave31tu.RouteTConst
import StatFormal.Wave31tq.Proofs
import StatFormal.Wave31tp.Proofs

/-!
# Wave 31tu route T: Theorem S4.19 under the printed hypotheses (Pr) (S4 :989-1018, :1061-1073; untrusted proof material)

* `laplace_twoSided`: under the hypotheses of Proposition 5.5, the two-sided bound of Proposition 5.5 at `s = 1` holds with constants
  `c₁, c₂, ε₀` chosen before the feature map: Q21 `newsobolev` with Q7 `kernel_instances` (the spectrum `2σ/(1+σ²ξ²)` between
  `2σ min{1,σ⁻²}(1+ξ²)⁻¹` and `2σ max{1,σ⁻²}(1+ξ²)⁻¹`) at the Fourier feature map of `e^{−|x|/σ}` (31tp L15 `feature_exists`,
  `fourier_feature` for completeness and separability), transferred to every feature map with the same Gram function by 31tp L12
  `gram_mmd` (`D_α` depends only on the kernel).
* `laplace_const_pr_i_of`: (Pr) (i) from (G) (i), with `r⋆` shrunk until `p + q` is bounded on `[x₀ − r⋆, x₀ + r⋆]` (Claim Y8 (c)).
* `laplace_const_pr_ii_of`: (Pr) (ii) from (G) (ii).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteT

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.Wave31tq
  StatFormal.TrimmedMMD.Unconditional

/-- **The constants of Proposition 5.5 at `s = 1` for the Laplace kernel, before the feature map.** -/
lemma laplace_twoSided {σ : ℝ} (hσ : 0 < σ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) (hexp : ExpTail P Q x₀) :
    0 < Distances.tvDist P Q ∧ Distances.tvDist P Q < 1 ∧
    ∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧ ε₀ ≤ Distances.tvDist P Q ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H),
        IsLaplaceFeature σ φ → TwoSided54 φ P Q c₁ c₂ ε₀ := by
  set k₀ : ℝ → ℝ := fun x => Real.exp (-|x| / σ) with hk₀
  obtain ⟨hcont, hint, hpd, -, hbounds, -⟩ := Wave31tq.kernel_instances.1 σ hσ
  obtain ⟨hψc, -, hψ0, hψi, -, hgram⟩ := Wave31tp.feature_exists ℝ k₀ hcont hint hpd
  obtain ⟨hcomp, hsep, hφc, -⟩ := Wave31tp.fourier_feature ℝ (Wave31tp.specDens k₀) hψc.measurable hψ0 hψi
  have := hcomp
  have := hsep
  set φ₀ := Wave31tp.fourierFeature (Wave31tp.specDens k₀) with hφ₀
  have hc : 0 < 2 * σ * min 1 (σ ^ 2)⁻¹ := by positivity
  obtain ⟨htv0, htv1, c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hε₀α, hD⟩ :=
    Wave31tq.newsobolev _ φ₀ k₀ (2 * σ * min 1 (σ ^ 2)⁻¹) (2 * σ * max 1 (σ ^ 2)⁻¹) 1 P Q p q x₀ ℓ₀ hcont hint hgram hc
      (by norm_num) hbounds hcross hpx hexp
  refine ⟨htv0, htv1, c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hε₀α, fun H _ _ _ φ hφ => ?_⟩
  have hgram' : ∀ x y, ⟪φ₀ x, φ₀ y⟫_ℝ = ⟪φ x, φ y⟫_ℝ := fun x y => by rw [hgram, hφ x y]
  have hsm : StronglyMeasurable φ₀ := hφc.stronglyMeasurable
  have hnorm : ∀ x, ‖φ₀ x‖ ≤ 1 := by
    intro x
    have h1 : ‖φ₀ x‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hgram]; simp [hk₀]
    nlinarith [norm_nonneg (φ₀ x)]
  have hDeq := (Wave31tp.gram_mmd ℝ _ H φ₀ φ 1 hgram' hsm hnorm).2.2.2.1 P Q
  refine ⟨hc₁, hc₁₂, hε₀, hε₀α, fun ε hε => ?_⟩
  have h := hD ε hε
  rw [(hDeq _).2.2, show (2 * (1 : ℝ) + 3) / 4 = 5 / 4 by norm_num] at h
  exact h

/-- **Theorem S4.19 (i)** under the printed hypotheses, from the uniform form. -/
theorem pr_i_of_G (hG : Claims.laplace_const_i) (h8 : Claims.condR_facts) : Claims.laplace_const_pr_i := by
  intro σ P Q _ _ p q x₀ ℓ₀ rs cs hσ hcross hpx hexp hcond
  obtain ⟨htv0, htv1, c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hε₀α, htwo⟩ := laplace_twoSided hσ P Q hcross hpx hexp
  obtain ⟨C', hC', htail⟩ := hexp
  obtain ⟨hshrink, ⟨rs', hrs', pbar, hpb⟩, -⟩ := (h8 P Q p q x₀ ℓ₀ hcross hpx).2 rs cs hcond
  have hcond' := hshrink rs' hrs'
  have hpbar0 : 0 ≤ pbar :=
    (add_nonneg (hcross.2.2.1 x₀) (hcross.2.2.2.1 x₀)).trans (hpb x₀ ⟨by linarith [hrs'.1], by linarith [hrs'.1]⟩)
  obtain ⟨C, hC, hall⟩ := hG σ (Distances.tvDist P Q) c₁ c₂ ε₀ C' cs rs' pbar hσ htv0 htv1 hc₁ hc₁₂ hε₀ hε₀α hC'
    hcond'.2.2.1 hcond'.1 hcond'.2.1 hpbar0
  exact ⟨C, hC, fun H _ _ _ _ φ hφ J n m α δ s2 η h R hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh =>
    hall H φ P Q p q x₀ ℓ₀ J n m α δ s2 η h R hφ hcross hpx ⟨hC', htail⟩ rfl (htwo H φ hφ) hcond' hpb hgrid hα0 hJ
      hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh⟩

/-- **Theorem S4.19 (ii)** under the printed hypotheses, from the uniform form. -/
theorem pr_ii_of_G (hG : Claims.laplace_const_ii) : Claims.laplace_const_pr_ii := by
  intro σ P Q _ _ p q x₀ ℓ₀ C' hσ hcross hpx hexp hsum
  obtain ⟨htv0, htv1, c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hε₀α, htwo⟩ := laplace_twoSided hσ P Q hcross hpx hexp
  obtain ⟨C, hC, hall⟩ := hG σ (Distances.tvDist P Q) c₁ c₂ ε₀ C' hσ htv0 htv1 hc₁ hc₁₂ hε₀ hε₀α hsum.1
  exact ⟨C, hC, fun H _ _ _ _ φ hφ J n m α δ s2 η h R hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh =>
    hall H φ P Q p q x₀ ℓ₀ J n m α δ s2 η h R hφ hcross hpx hsum rfl (htwo H φ hφ) hgrid hα0 hJ hδ0 hδ1 hs20 hs24
      hη0 hη1 hrun hdef hN10 hmesh⟩

/-- **Y18 (Pr) (i)**, `thm:laplaceconst` (i) under the printed hypotheses. -/
theorem laplace_const_pr_i_of (h4 : Claims.lap_intervals) (h8 : Claims.condR_facts) (h10 : Claims.lap_clip)
    (h15 : Claims.lap_fitted) (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale) : Claims.laplace_const_pr_i :=
  pr_i_of_G (laplace_const_i_of h4 h8 h10 h15 h16 h17) h8

/-- **Y18 (Pr) (ii)**, `thm:laplaceconst` (ii) under the printed hypotheses. -/
theorem laplace_const_pr_ii_of (h4 : Claims.lap_intervals) (h10 : Claims.lap_clip) (h15 : Claims.lap_fitted)
    (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale) : Claims.laplace_const_pr_ii :=
  pr_ii_of_G (laplace_const_ii_of h4 h10 h15 h16 h17)

end StatFormal.Wave31tu.RouteT
