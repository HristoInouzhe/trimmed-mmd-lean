import StatFormal.Wave31tu.RouteFSetup
import StatFormal.Lib.FixedPoint.Basic

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: the common part of both cases of Proposition S4.27 (`prop:lapfitted`, S4 :1302-1305)

`fitted_common`: at a level `α = α⋆ − ε ∈ (0, α⋆)` and an exact minimizer of `eq:qp`, from the frozen claims Y7 `lap_const`, Y10
`lap_clip`, Y11 `lap_pop` and Y12 `lap_compare` (with the population objects of `exists_pop_objects`):
`κ₀ ∈ (0,1)`, `c_V > 0`, `ĝ > 0`, `N̂ = ‖φ̂‖ = 1/ĝ ≥ ½`, `osc(φ̂) ≤ 1`, plain genuine cuts are `(t̂, û)`, and there are `φ⋆` and `y`
with `osc(φ⋆) ≤ 1`, `max(‖φ⋆‖, ½) c_Vε^{1/4} ≤ 1` (`‖φ⋆‖ ≤ c_V^{−1}ε^{−1/4}` and `c_Vε^{1/4} ≤ g⋆ ≤ 2`), `err(φ⋆) ≤ ε`, and
Lemma S4.22 (i)–(iii).
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteF

open StatFormal StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration
  StatFormal.TrimmedMMD.Unconditional StatFormal.Wave31tq StatFormal.FixedPoint

/-- The common part of both cases of Proposition S4.27. -/
theorem fitted_common (h7 : Claims.lap_const) (h10 : Claims.lap_clip) (h11 : Claims.lap_pop) (h12 : Claims.lap_compare)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {c₁ c₂ ε₀ ε : ℝ} {n m : ℕ}
    {x : Fin n → ℝ} {y : Fin m → ℝ} {w : Fin n → ℝ} {v : Fin m → ℝ}
    (hφ : IsLaplaceFeature 1 φ) (h54 : TwoSided54 φ P Q c₁ c₂ ε₀) (htv : Distances.tvDist P Q < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hxy : ∀ i j, x i ≠ y j) (hε : 0 < ε) (hεα : ε < Distances.tvDist P Q)
    (hqp : IsQPMin φ (Distances.tvDist P Q - ε) x y w v) :
    let α := Distances.tvDist P Q - ε
    let κ := kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀
    let cv := cV (Distances.tvDist P Q) c₁ ε₀
    let gh := tHat φ x y w v α - uHat φ x y w v α
    let φh := gh⁻¹ • witness φ x y w v
    let Δ := fun g : H => linL (empirical x) (empirical y) (Wave31to.wit φ g) - linL P Q (Wave31to.wit φ g)
    let Dh := (1 - α) * qpVal φ x y w v
    let Th := errL P Q (Wave31to.wit φ φh)
    let e := (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂P) -
      (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂Q) - α
    0 < κ ∧ κ < 1 ∧ 0 < cv ∧ 0 < gh ∧ ‖φh‖ = 1 / gh ∧ 1 / 2 ≤ ‖φh‖ ∧ Wave31to.oscFn (Wave31to.wit φ φh) ≤ 1 ∧
    (∀ t' u', GenuineCuts φ x y w v α t' u' →
      (t' = tHat φ x y w v α ∧ u' = uHat φ x y w v α) ∨
        (IsEmpQuantile (ownX φ x y w v) (1 - α) t' ∧ IsEmpQuantile (ownY φ x y w v) α u')) ∧
    ∃ (φs : H) (yy : ℝ), Wave31to.oscFn (Wave31to.wit φ φs) ≤ 1 ∧
      max ‖φs‖ (1 / 2) * (cv * ε ^ (1 / 4 : ℝ)) ≤ 1 ∧ errL P Q (Wave31to.wit φ φs) ≤ ε ∧
      e = ε - Th ∧ yy ≤ Dh ∧ ‖φh‖ * yy + Th ≤ ε + Δ φh ∧
      (0 < κ * ε - |Δ φs| - Δ φh → κ * ε - |Δ φs| - Δ φh ≤ e) ∧
      (|Δ φs| ≤ κ * ε / 4 → cv * ε ^ (5 / 4 : ℝ) / 2 ≤ yy) := by
  intro α κ cv gh φh Δ Dh Th e
  obtain ⟨-, hsm, hκ1⟩ := laplace1_facts hφ
  obtain ⟨-, -, hκ0, hκlt, hcv, -, -, -, -⟩ := h7 H φ 1 P Q c₁ c₂ ε₀ hsm hκ1 htv h54
  have hα0 : 0 < α := by simp only [α]; linarith
  have hα1 : α < 1 := by simp only [α]; linarith
  obtain ⟨a, b, ts, us, ha, hb, hab, hts, hus⟩ := exists_pop_objects hφ P Q hα0.le hα1
  obtain ⟨-, -, hosc, hnorm, -, -, -, -, -, hTs, hgosc, hosc2, hpc⟩ :=
    h11 H 1 φ P Q ε a b ts us one_pos hφ hε hεα htv ha hb hab hts hus
  obtain ⟨hNs, hcvε, -⟩ := hpc c₁ c₂ ε₀ h54
  obtain ⟨-, -, -, -, hgh, -, -, hqx, hqy, -, hoscφh, hnormφh, hhalf, -, -, -, -, -, -, -⟩ :=
    h10 H 1 φ n m x y α w v one_pos hφ hn hm hxy hα0 hα1 hqp
  obtain ⟨⟨he, -, hyD, hi⟩, hii, hiii⟩ :=
    h12 H 1 φ P Q c₁ c₂ ε₀ ε a b ts us n m x y w v one_pos hφ htv h54 hε hεα ha hb hab hts hus hn hm hxy hqp
  refine ⟨hκ0, hκlt, hcv, hgh, hnormφh, hhalf, hoscφh.le, ?_, ?_⟩
  · intro t' u' hcut
    rcases hcut with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hqx t' h1, hqy u' h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · refine ⟨(ts - us)⁻¹ • (‖a - b‖⁻¹ • (a - b)), _, hosc, ?_, hTs, he, hyD, hi, hii, fun h => (hiii h).2.trans (hiii h).1⟩
    -- `max(‖φ⋆‖, ½) c_V ε^{1/4} ≤ 1`
    have he4 : 0 < ε ^ (1 / 4 : ℝ) := rpow_quarter_pos hε
    have hX : 0 < cv * ε ^ (1 / 4 : ℝ) := mul_pos hcv he4
    rw [max_mul_of_nonneg _ _ hX.le]
    refine max_le ?_ ?_
    · rw [rpow_neg_quarter hε.le] at hNs
      calc ‖(ts - us)⁻¹ • (‖a - b‖⁻¹ • (a - b))‖ * (cv * ε ^ (1 / 4 : ℝ))
          ≤ cv⁻¹ * (ε ^ (1 / 4 : ℝ))⁻¹ * (cv * ε ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_right hNs hX.le
        _ = (cv⁻¹ * cv) * ((ε ^ (1 / 4 : ℝ))⁻¹ * ε ^ (1 / 4 : ℝ)) := by ring
        _ = 1 := by
          have hcv' : 0 < cv := hcv
          rw [inv_mul_cancel₀ hcv'.ne', inv_mul_cancel₀ he4.ne', one_mul]
    · have : cv * ε ^ (1 / 4 : ℝ) ≤ 2 := hcvε.trans (hgosc.trans hosc2)
      linarith

end StatFormal.Wave31tu.RouteF
