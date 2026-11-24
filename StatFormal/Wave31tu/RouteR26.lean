import StatFormal.Wave31tu.RouteR25
import StatFormal.Wave31tq.Proofs
import StatFormal.Wave31tp.Proofs
import StatFormal.Wave31ti.Proofs
import StatFormal.Lib.MomentTrim.Region
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Wave 31tu route R: Proposition S4.8 (iii), the logarithmic rate for the Gaussian kernel (S4 :484-485, proof :736-745;
untrusted proof material)

The shorter route of `NEW_STATEMENTS_31tu.md` Y26 (decision D6): given `c > π²σ²ℓ₀/4`, take
`π²σ²ℓ₀/8 < c″ < c′ < c/2`. At one Gaussian feature map `φ₀` (the Fourier feature map of `e^{−z²/(2σ²)}`, 31tp L15
`feature_exists`, `fourier_feature`; positive definite by 31tq Q7 `kernel_instances`), 31tq Q22 `newgauss` gives `ε₀ ∈ (0, α⋆]` with
`D_{α⋆−ε} ≥ e^{−c″/ε}` on `(0, ε₀]`; by 31tp L12 `gram_mmd` the same holds for every feature map with the Gaussian Gram function.
With `ω(ε) = u(α⋆ − ε) = (1 − α⋆ + ε)D_{α⋆−ε}` (nondecreasing by 31ti `pathconvex`, `0 ≤ ω ≤ u(α⋆ − ·)`),
`ω(ε) ≥ (1 − α⋆)e^{−c″/ε} ≥ e^{−c′/ε}` for `ε ≤ ε₁ = min{ε₀, (c′ − c″)/log(1/(1−α⋆))}` (`α⋆ < 1` by 31tq `cross_tv`), and Y25
(`newrates_ii_exp_route`, `κ = 1`: `‖φx‖ = 1` and strong measurability by 31tp L16 `mmd_fourier`) gives the claim with `c > 2c′`.
`n₀` is chosen before the feature space and map.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteR

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.Wave31tq
  StatFormal.TrimmedMMD.Unconditional

/-- The Gaussian profile `e^{−z²/(2σ²)}` is continuous, integrable and positive definite. -/
lemma gauss_profile {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun z : ℝ => Real.exp (-z ^ 2 / (2 * σ ^ 2))) ∧ Integrable (fun z : ℝ => Real.exp (-z ^ 2 / (2 * σ ^ 2))) ∧
      Wave31tp.IsPosDefFun (fun z : ℝ => ((Real.exp (-z ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) := by
  refine ⟨by fun_prop, ?_, (Wave31tq.kernel_instances.2.2.2 σ hσ).1⟩
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  refine (integrable_exp_neg_mul_sq hb).congr (Eventually.of_forall fun z => ?_)
  change Real.exp (-(1 / (2 * σ ^ 2)) * z ^ 2) = Real.exp (-z ^ 2 / (2 * σ ^ 2))
  congr 1
  ring

/-- **The Gaussian margin before the feature map**: under the hypotheses of Proposition 5.6, for `c″ > π²σ²ℓ₀/8` there is
`ε₀ ∈ (0, α⋆]` with `D_{α⋆−ε} ≥ e^{−c″/ε}` on `(0, ε₀]` for every feature map with the Gaussian Gram function; and `0 < α⋆ < 1`. -/
lemma gauss_margin {σ : ℝ} (hσ : 0 < σ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) (hexp : ExpTail P Q x₀) {c'' : ℝ}
    (hc'' : Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 < c'') :
    0 < Distances.tvDist P Q ∧ Distances.tvDist P Q < 1 ∧
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ Distances.tvDist P Q ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H),
        (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
          ∀ ε ∈ Ioc (0 : ℝ) ε₀, Real.exp (-c'' / ε) ≤ Dpop φ P Q (Distances.tvDist P Q - ε) := by
  set k₀ : ℝ → ℝ := fun z => Real.exp (-z ^ 2 / (2 * σ ^ 2)) with hk₀
  obtain ⟨hcont, hint, hpd⟩ := gauss_profile hσ
  obtain ⟨hψc, -, hψ0, hψi, -, hgram⟩ := Wave31tp.feature_exists ℝ k₀ hcont hint hpd
  obtain ⟨hcomp, hsep, hφc, -⟩ := Wave31tp.fourier_feature ℝ (Wave31tp.specDens k₀) hψc.measurable hψ0 hψi
  have := hcomp
  have := hsep
  set φ₀ := Wave31tp.fourierFeature (Wave31tp.specDens k₀) with hφ₀
  have hgram₀ : ∀ x y, ⟪φ₀ x, φ₀ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2)) := fun x y => hgram x y
  obtain ⟨ε₀, CN, hε₀, hε₀α, hD⟩ := Wave31tq.newgauss _ φ₀ σ P Q p q x₀ ℓ₀ hσ hgram₀ hcross hpx hexp c'' hc'' 1 le_rfl
  have htv1 := (Wave31tq.RouteM.cross_tv Wave31tq.tv_density hcross hpx).2
  refine ⟨hε₀.trans_le hε₀α, htv1, ε₀, hε₀, hε₀α, fun H _ _ _ φ hφ ε hε => ?_⟩
  have hgram' : ∀ x y, ⟪φ₀ x, φ₀ y⟫_ℝ = ⟪φ x, φ y⟫_ℝ := fun x y => by rw [hgram₀, hφ x y]
  have hsm : StronglyMeasurable φ₀ := hφc.stronglyMeasurable
  have hnorm : ∀ x, ‖φ₀ x‖ ≤ 1 := by
    intro x
    have h1 : ‖φ₀ x‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hgram₀]; simp
    nlinarith [norm_nonneg (φ₀ x)]
  have hDeq := (Wave31tp.gram_mmd ℝ _ H φ₀ φ 1 hgram' hsm hnorm).2.2.2.1 P Q
  rw [← (hDeq _).2.2]
  exact (hD ε hε).1

/-- **Y26, Proposition S4.8 (iii)**: under the hypotheses of Proposition 5.6, on grids with at most `(n∧m)^b` levels, the rate
`c/log(n∧m)` for every `c > π²σ²ℓ₀/4`, with `n₀` chosen before the feature space and map. -/
theorem newrates_iii_gauss_route : Claims.newrates_iii_gauss := by
  intro σ P Q _ _ p q x₀ ℓ₀ b η δ s2 c hσ hcross hpx hexp hb hη0 hη1 hδ0 hδ1 hs20 hs24 hcc
  have hℓ : 0 < ℓ₀ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hℓ⟩ := hcross
    exact hℓ
  set a := Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 with ha
  have ha0 : 0 < a := by positivity
  have hca : 0 < c / 2 - a := by rw [ha]; linarith
  set c'' := a + (c / 2 - a) / 3 with hc''
  set c' := a + 2 * (c / 2 - a) / 3 with hc'
  have hc''a : a < c'' := by rw [hc'']; linarith
  have hc'c'' : c'' < c' := by rw [hc'', hc']; linarith
  have hc'pos : 0 < c' := by linarith
  have hcc' : 2 * c' < c := by rw [hc']; linarith
  obtain ⟨htv0, htv1, ε₀, hε₀, hε₀α, hmarg⟩ := gauss_margin hσ P Q hcross hpx hexp hc''a
  set αs := Distances.tvDist P Q with hαs
  set L := Real.log (1 / (1 - αs)) with hL
  have hL0 : 0 < L := Real.log_pos (one_lt_one_div (by linarith) (by linarith))
  set ε₁ := min ε₀ ((c' - c'') / L) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε₀ (div_pos (by linarith) hL0)
  have hε₁α : ε₁ ≤ αs := (min_le_left _ _).trans hε₀α
  obtain ⟨n₀, hn₀⟩ := newrates_ii_exp_route 1 αs c' ε₁ b η δ s2 c one_pos hc'pos hε₁0 hε₁α htv1 hb hη0 hη1 hδ0 hδ1 hs20
    hs24 hcc'
  refine ⟨n₀, fun H _ _ _ _ φ hφ J n m α h R hgrid hJ hJb hrun hdef hn hmesh => ?_⟩
  set k₀ : ℝ → ℝ := fun z => Real.exp (-z ^ 2 / (2 * σ ^ 2)) with hk₀
  obtain ⟨hcont, hint, -⟩ := gauss_profile hσ
  obtain ⟨-, hφsm, hφnorm, -⟩ := Wave31tp.mmd_fourier ℝ H φ k₀ hcont hint (fun x y => hφ x y)
  have hnorm : ∀ x, ‖φ x‖ ≤ 1 := fun x => by rw [hφnorm x]; simp [hk₀]
  have hanti := (Wave31ti.pathconvex ℝ H P Q φ 1 hφsm hnorm).2
  set ω : ℝ → ℝ := fun e => Wave31ti.uPath φ P Q (αs - e) with hω
  have hmono : MonotoneOn ω (Icc 0 αs) := by
    intro e₁ he₁ e₂ he₂ h12
    exact hanti ⟨by linarith [he₂.2], by linarith [he₂.1]⟩ ⟨by linarith [he₁.2], by linarith [he₁.1]⟩ (by linarith)
  have hω0 : ∀ e ∈ Icc (0 : ℝ) αs, 0 ≤ ω e := fun e he =>
    mul_nonneg (by linarith [he.1]) (StatFormal.MomentTrim.Dpop_nonneg φ P Q _)
  have hωexp : ∀ e ∈ Ioc (0 : ℝ) ε₁, Real.exp (-c' / e) ≤ ω e := by
    intro e he
    have hDe := hmarg H φ hφ e ⟨he.1, he.2.trans (min_le_left _ _)⟩
    have hDn := StatFormal.MomentTrim.Dpop_nonneg φ P Q (αs - e)
    have hexpL : Real.exp (-((c' - c'') / e)) ≤ 1 - αs := by
      have hLe : e * L ≤ c' - c'' := (le_div_iff₀ hL0).1 (he.2.trans (min_le_right _ _))
      have hlog : Real.log (1 - αs) = -L := by rw [hL, one_div, Real.log_inv, neg_neg]
      have h2 : -((c' - c'') / e) ≤ Real.log (1 - αs) := by
        rw [hlog, neg_le_neg_iff, le_div_iff₀ he.1]
        linarith
      calc Real.exp (-((c' - c'') / e)) ≤ Real.exp (Real.log (1 - αs)) := Real.exp_le_exp.2 h2
        _ = 1 - αs := Real.exp_log (by linarith)
    have hsplit : Real.exp (-c' / e) = Real.exp (-c'' / e) * Real.exp (-((c' - c'') / e)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (-c' / e) = Real.exp (-c'' / e) * Real.exp (-((c' - c'') / e)) := hsplit
      _ ≤ Dpop φ P Q (αs - e) * (1 - αs) := mul_le_mul hDe hexpL (Real.exp_pos _).le hDn
      _ ≤ Dpop φ P Q (αs - e) * (1 - (αs - e)) := mul_le_mul_of_nonneg_left (by linarith [he.1]) hDn
      _ = ω e := by simp only [hω, Wave31ti.uPath]; ring
  exact hn₀ ℝ H φ P Q ω J n m α h R hφsm hnorm rfl hmono hω0 (fun e _ => le_rfl) hωexp hgrid hJ hJb hrun hdef hn hmesh

end StatFormal.Wave31tu.RouteR
