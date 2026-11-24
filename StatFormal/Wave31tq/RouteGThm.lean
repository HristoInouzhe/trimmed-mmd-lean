import StatFormal.Wave31tq.RouteGStep
import StatFormal.Wave31to.Proofs
import StatFormal.Wave31ti.RoutePath

/-!
# Wave 31tq, chunk G: Theorem S4.13 and the bound on `ω_ℋ` (Q17 `newgauss_thm`)

Route (the printed proof, S4 :717-726, and S4 :739-741). With `Ω_ε² = ℓm₂/(2θε)` (`m₂ > 0` because `b` is a probability
density), Lemma S4.12 (`newgaussstep_of`) gives `f = 1_{(x₀,x₀+ρ)} ⋆ b_Ω` with a representer `g`,
`‖g‖² ≤ ρe^{σ²Ω²/2}/((2π)^{1/2}σ)` and `err(f) ≤ θε + (1−θ)ε/2`. The certified `Wave31to.newapproxgen_i` at `α = αs − ε ∈ [0,1)`
and `Wave31to.newapprox_err` (`E_P f − E_Q f = αs − err(f)`; no `αs < 1` needed) give, for every `f ∈ 𝓕`, `f ≠ 0`,
`(ε − err(f))/‖f‖ ≤ (1−α)D_α = D̄_{αs−ε}` (`osc f ≤ 1`). At the `f` above this is the printed bound; the same inequality for every
`f ∈ 𝓕` bounds the set whose supremum is `ω_ℋ(ε)` (`Wave31to.xiH`), so the bound is also a lower bound on `ω_ℋ(ε)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteG

open StatFormal StatFormal.Wave31tp StatFormal.TrimmedMMD.Unconditional

/-- The Gaussian feature map on the line is continuous, strongly measurable and has unit norms (31tp L16, L21). -/
theorem gauss_feature_facts {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {φ : ℝ → H}
    {σ : ℝ} (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) :
    Continuous φ ∧ StronglyMeasurable φ ∧ ∀ x, ‖φ x‖ = 1 := by
  have hgs := Wave31tp.gauss_spec ℝ σ hσ
  have hk : (fun x : ℝ => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) = fun z => Real.exp (-z ^ 2 / (2 * σ ^ 2)) := by
    funext z; rw [Real.norm_eq_abs, sq_abs]
  rw [hk] at hgs
  obtain ⟨hc, hm, hn, -⟩ := Wave31tp.mmd_fourier ℝ H φ (fun z => Real.exp (-z ^ 2 / (2 * σ ^ 2))) hgs.1 hgs.2.1 hφ
  refine ⟨hc, hm, fun x => ?_⟩
  rw [hn x]
  simp

/-- **The basic lower bound on the rescaled path** (from `newapproxgen_i` and `newapprox_err`, valid for `αs ≤ 1`): for
`f = ⟪g, φ ·⟫ ∈ 𝓕` measurable with `g ≠ 0` and `ε ∈ (0, αs]`, `(ε − err(f))/‖g‖ ≤ D̄_{αs−ε}`. -/
theorem sub_err_div_le_uPath {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ : ℝ} (hφm : StronglyMeasurable φ) (hφb : ∀ x, ‖φ x‖ ≤ κ) {g : H} (hgF : g ∈ Wave31to.Fset φ)
    (hgm : Measurable (Wave31to.wit φ g)) (hg0 : g ≠ 0) {ε : ℝ} (hε : 0 < ε) (hεα : ε ≤ StatFormal.Distances.tvDist P Q) :
    (ε - Wave31to.errFn P Q (Wave31to.wit φ g)) / ‖g‖ ≤
      StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) := by
  set αs := StatFormal.Distances.tvDist P Q with hαs
  have hα1 : αs ≤ 1 := StatFormal.Distances.tvDist_le_one
  have hgi := Wave31to.newapproxgen_i 𝒳 H P Q φ κ g (αs - ε) hφm hφb hg0 (by linarith) (by linarith)
  have hf01 : ∀ x, 0 ≤ Wave31to.wit φ g x ∧ Wave31to.wit φ g x ≤ 1 := hgF
  have herr := (Wave31to.newapprox_err 𝒳 P Q (Wave31to.wit φ g) hgm hf01).1
  have hosc : Wave31to.oscFn (Wave31to.wit φ g) ≤ 1 := by
    by_cases he : Nonempty 𝒳
    · have hs : (⨆ x, Wave31to.wit φ g x) ≤ 1 := ciSup_le fun x => (hf01 x).2
      have hi : 0 ≤ ⨅ x, Wave31to.wit φ g x := le_ciInf fun x => (hf01 x).1
      unfold Wave31to.oscFn; linarith
    · rw [not_nonempty_iff] at he
      simp [Wave31to.oscFn]
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg0
  rw [div_le_iff₀ hgpos, StatFormal.Wave31ti.uPath]
  have hD0 := StatFormal.Wave31ti.Dpop_nonneg0 φ P Q (αs - ε)
  nlinarith [mul_le_mul_of_nonneg_left hosc (show 0 ≤ αs - ε by linarith)]

/-- Q17 `newgauss_thm` (Theorem S4.13 and S4 :739-741), with Q1(b) (`Claims.tv_density`, chunk A) as a hypothesis. -/
theorem newgauss_thm_of (htv : Claims.tv_density) : Claims.newgauss_thm := by
  intro H _ _ _ _ φ σ P Q _ _ p q b x₀ ℓ r₀ hσ hφ hp hq hp0 hq0 hP hQ hsgn1 hsgn2 hℓ hr₀ hlip hb hb0 hb1 hbev hbft hm
    θ ε ρ hθ0 hθ1 hε0 hεα hρ m₂ Ω hcond
  set αs := StatFormal.Distances.tvDist P Q with hαs
  -- `m₂ > 0`
  have hne0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by rw [ae_iff]; simp
  have hm2pos : 0 < m₂ := by
    have hnn : 0 ≤ m₂ := integral_nonneg fun t => mul_nonneg (sq_nonneg t) (hb0 t)
    refine lt_of_le_of_ne hnn fun h0 => ?_
    have hz : (fun t => t ^ 2 * b t) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t => mul_nonneg (sq_nonneg t) (hb0 t)) hm).1 h0.symm
    have hbz : b =ᵐ[volume] 0 := by
      filter_upwards [hz, hne0] with t ht ht0
      have : t ^ 2 * b t = 0 := ht
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) ht0
      · exact h
    have := integral_congr_ae hbz
    rw [hb1] at this
    simp at this
  have hq0' : 0 < ℓ * m₂ / (2 * θ * ε) := by positivity
  have hΩ : 0 < Ω := Real.sqrt_pos.2 hq0'
  have hΩ2 : Ω ^ 2 = ℓ * m₂ / (2 * θ * ε) := Real.sq_sqrt hq0'.le
  -- Lemma S4.12
  obtain ⟨⟨g, hg, hgn⟩, hf01, herrf⟩ := newgaussstep_of htv H φ σ P Q p q b x₀ ℓ r₀ hσ hφ hp hq hp0 hq0 hP hQ hsgn1 hsgn2 hℓ
    hr₀ hlip hb hb0 hb1 hbev hbft hm Ω ρ hΩ hρ
  set f := mollify (Ioo x₀ (x₀ + ρ)) (dilateR Ω⁻¹ b) with hf
  have hθε : ℓ * m₂ / (2 * Ω ^ 2) = θ * ε := by
    rw [hΩ2]; field_simp
  have herr : StatFormal.Wave31to.errFn P Q f ≤ θ * ε + (1 - θ) * ε / 2 := by
    have : ℓ * m₂ / (2 * Ω ^ 2) = ℓ * (∫ t, t ^ 2 * b t) / (2 * Ω ^ 2) := rfl
    linarith
  -- the feature map
  obtain ⟨hφc, hφm, hφn⟩ := gauss_feature_facts hσ hφ
  have hφb : ∀ x, ‖φ x‖ ≤ 1 := fun x => (hφn x).le
  have hwit : ∀ g' : H, Measurable (StatFormal.Wave31to.wit φ g') := fun g' =>
    (continuous_const.inner hφc).measurable
  have hwf : StatFormal.Wave31to.wit φ g = f := funext hg
  have hgF : g ∈ StatFormal.Wave31to.Fset φ := fun x => by rw [hwf]; exact hf01 x
  -- `g ≠ 0`
  have hg0 : g ≠ 0 := by
    intro h0
    have hf0 : f = fun _ => (0 : ℝ) := by rw [← hwf, h0]; funext x; simp [StatFormal.Wave31to.wit]
    have he := (StatFormal.Wave31to.newapprox_err ℝ P Q f (hwf ▸ hwit g) hf01).1
    rw [hf0] at he herr
    simp at he
    rw [he] at herr
    nlinarith
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg0
  have hkey := sub_err_div_le_uPath P Q hφm hφb hgF (hwit g) hg0 hε0 hεα
  rw [hwf] at hkey
  -- the printed bound is at most `(ε − err(f))/‖g‖`
  set X := σ ^ 2 * ℓ * m₂ / (8 * θ * ε) with hX
  set c := (1 - θ) * ε / 2 with hc
  have hc0 : 0 < c := by rw [hc]; nlinarith
  set K := √(√(2 * Real.pi) * σ / ρ) * Real.exp (-X) with hK
  have hK0 : 0 ≤ K := by positivity
  have hKg : K * ‖g‖ ≤ 1 := by
    have hσΩ : σ ^ 2 * Ω ^ 2 / 2 = 2 * X := by rw [hΩ2, hX]; field_simp; ring
    have hs2 : (√(2 * Real.pi) * σ) > 0 := by positivity
    have hsq : (K * ‖g‖) ^ 2 ≤ 1 := by
      rw [mul_pow, hK, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul (-X)]
      have hgn' : ‖g‖ ^ 2 ≤ ρ * Real.exp (2 * X) / (√(2 * Real.pi) * σ) := by rw [← hσΩ]; exact hgn
      calc √(2 * Real.pi) * σ / ρ * Real.exp (↑2 * -X) * ‖g‖ ^ 2
          ≤ √(2 * Real.pi) * σ / ρ * Real.exp (↑2 * -X) * (ρ * Real.exp (2 * X) / (√(2 * Real.pi) * σ)) :=
            mul_le_mul_of_nonneg_left hgn' (by positivity)
        _ = Real.exp (2 * -X) * Real.exp (2 * X) := by field_simp
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_nonneg hK0 hgpos.le]
  have hbound : c * K ≤ (ε - StatFormal.Wave31to.errFn P Q f) / ‖g‖ := by
    rw [le_div_iff₀ hgpos]
    calc c * K * ‖g‖ = c * (K * ‖g‖) := by ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hKg hc0.le
      _ ≤ ε - StatFormal.Wave31to.errFn P Q f := by rw [hc]; linarith
  have hshape : (1 - θ) * ε / 2 * √(√(2 * Real.pi) * σ / ρ) * Real.exp (-(σ ^ 2 * ℓ * m₂ / (8 * θ * ε))) = c * K := by
    rw [hc, hK, hX]; ring
  have hD0 := StatFormal.Wave31ti.Dpop_nonneg0 φ P Q (αs - ε)
  refine ⟨?_, ?_, ?_⟩
  · -- `D̄ ≤ D`
    rw [StatFormal.Wave31ti.uPath]
    nlinarith
  · rw [hshape]; exact hbound.trans hkey
  · -- the bound on `ω_ℋ(ε)`
    rw [hshape]
    set S := {r | ∃ g' ∈ StatFormal.Wave31to.Fset φ, g' ≠ 0 ∧
      r = max (ε - StatFormal.Wave31to.errFn P Q (StatFormal.Wave31to.wit φ g')) 0 / ‖g'‖} with hS
    have hU0 : 0 ≤ StatFormal.Wave31ti.uPath φ P Q (αs - ε) := (mul_nonneg hc0.le hK0).trans (hbound.trans hkey)
    have hbdd : BddAbove S := by
      refine ⟨StatFormal.Wave31ti.uPath φ P Q (αs - ε), ?_⟩
      rintro r ⟨g', hg'F, hg'0, rfl⟩
      have hk' := sub_err_div_le_uPath P Q hφm hφb hg'F (hwit g') hg'0 hε0 hεα
      rcases le_total (ε - StatFormal.Wave31to.errFn P Q (StatFormal.Wave31to.wit φ g')) 0 with h | h
      · rw [max_eq_right h, zero_div]; exact hU0
      · rw [max_eq_left h]; exact hk'
    have hmem : max (ε - StatFormal.Wave31to.errFn P Q (StatFormal.Wave31to.wit φ g)) 0 / ‖g‖ ∈ S :=
      ⟨g, hgF, hg0, rfl⟩
    have hle : c * K ≤ max (ε - StatFormal.Wave31to.errFn P Q (StatFormal.Wave31to.wit φ g)) 0 / ‖g‖ := by
      rw [hwf]
      exact hbound.trans (div_le_div_of_nonneg_right (le_max_left _ _) hgpos.le)
    exact hle.trans (le_csSup hbdd hmem)

end StatFormal.Wave31tq.RouteG
