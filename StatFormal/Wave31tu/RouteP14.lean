import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tq.Proofs

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y14 `own_ramp` (Lemma S4.26 `lem:lapown`, general part, S4 :1277-1291)

For a measurable `ψ : 𝒳 → [0,1]`, `a_o, b_o ≥ 0` with `a_o + b_o < 1` and `ϱ(s) = min{1, max{0, (s − a_o)/(1 − a_o − b_o)}}`:
`L(ψ) − max(a_o, b_o)·err(ψ)/(1 − a_o − b_o) ≤ L(ϱ ∘ ψ)`.

Route (printed: "the three pieces of `ϱ`"): with `ν = P ⊓ Q`, `μ₊ = P − ν`, `μ₋ = Q − ν` (so `P = μ₊ + ν`, `Q = μ₋ + ν`,
`μ₊(𝒳) = α⋆` by 31tq Q1 `tv_density`), `L(h) = ∫h dμ₊ − ∫h dμ₋` and `err(ψ) = ∫(1−ψ) dμ₊ + ∫ψ dμ₋`; pointwise on `[0,1]`,
`ϱ(s) − s ≥ −K(1 − s)` and `ϱ(s) − s ≤ Ks`, `K = max(a_o,b_o)/(1−a_o−b_o)` (`clamp_bounds`).
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances

/-- **The three pieces of `ϱ`.** For `s ∈ [0,1]`, `a_o, b_o ≥ 0`, `c = 1 − a_o − b_o > 0`, `K = max(a_o,b_o)/c` and
`ϱ(s) = min{1, max{0, (s − a_o)/c}}`: `ϱ(s) − s ≥ −K(1 − s)` and `ϱ(s) − s ≤ Ks`. -/
theorem clamp_bounds {s ao bo : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hao : 0 ≤ ao) (hbo : 0 ≤ bo) (hc : 0 < 1 - ao - bo) :
    0 ≤ min 1 (max 0 ((s - ao) / (1 - ao - bo))) - s + max ao bo / (1 - ao - bo) * (1 - s) ∧
      0 ≤ max ao bo / (1 - ao - bo) * s - (min 1 (max 0 ((s - ao) / (1 - ao - bo))) - s) := by
  set c := 1 - ao - bo with hcdef
  set K := max ao bo / c with hKdef
  have hKc : K * c = max ao bo := by rw [hKdef]; field_simp
  have hK0 : 0 ≤ K := div_nonneg (le_max_of_le_left hao) hc.le
  have hma : ao ≤ max ao bo := le_max_left _ _
  have hmb : bo ≤ max ao bo := le_max_right _ _
  set x := (s - ao) / c with hx
  have hxc : x * c = s - ao := by rw [hx]; field_simp
  rcases le_total x 0 with h0 | h0
  · -- `s ≤ a_o`: `ϱ = 0`
    have hr : min 1 (max 0 x) = 0 := by rw [max_eq_left h0, min_eq_right zero_le_one]
    rw [hr]
    have hsa : s ≤ ao := by nlinarith
    have h1 : c ≤ 1 - s := by rw [hcdef]; linarith
    have h2 : K * c ≤ K * (1 - s) := mul_le_mul_of_nonneg_left h1 hK0
    constructor <;> nlinarith
  · rcases le_total x 1 with h1 | h1
    · -- the linear piece
      have hr : min 1 (max 0 x) = x := by rw [max_eq_right h0, min_eq_right h1]
      rw [hr]
      constructor
      · have hkey : c * (x - s + K * (1 - s)) = (s - ao) - c * s + max ao bo * (1 - s) := by
          rw [← hKc]; nlinarith [hxc]
        have hnn : 0 ≤ (s - ao) - c * s + max ao bo * (1 - s) := by
          have : ao * (1 - s) ≤ max ao bo * (1 - s) := mul_le_mul_of_nonneg_right hma (by linarith)
          rw [hcdef]; nlinarith
        exact nonneg_of_mul_nonneg_right (by rw [hkey]; exact hnn) hc |> fun h => by
          by_contra hneg; push Not at hneg; nlinarith [mul_neg_of_pos_of_neg hc hneg]
      · have hkey : c * (K * s - (x - s)) = max ao bo * s - (s - ao) + c * s := by
          rw [← hKc]; nlinarith [hxc]
        have hnn : 0 ≤ max ao bo * s - (s - ao) + c * s := by
          have : bo * s ≤ max ao bo * s := mul_le_mul_of_nonneg_right hmb hs0
          rw [hcdef]; nlinarith
        by_contra hneg; push Not at hneg; nlinarith [mul_neg_of_pos_of_neg hc hneg]
    · -- `s ≥ 1 − b_o`: `ϱ = 1`
      have hr : min 1 (max 0 x) = 1 := by rw [max_eq_right h0, min_eq_left h1]
      rw [hr]
      have hs : c ≤ s := by nlinarith
      have h2 : K * c ≤ K * s := mul_le_mul_of_nonneg_left hs hK0
      have h3 : 1 - s ≤ bo := by nlinarith
      constructor <;> nlinarith

/-- Y14 `own_ramp`. -/
theorem own_ramp_route : Claims.own_ramp := by
  intro 𝒳 _ P Q _ _ ψ ao bo hψ hψ01 hao hbo hab
  have hc : 0 < 1 - ao - bo := by linarith
  set c := 1 - ao - bo with hcdef
  set K := max ao bo / c with hKdef
  set r : 𝒳 → ℝ := fun z => min 1 (max 0 ((ψ z - ao) / c)) with hrdef
  have hrm : Measurable r := measurable_const.min (measurable_const.max ((hψ.sub measurable_const).div_const _))
  have hr01 : ∀ z, 0 ≤ r z ∧ r z ≤ 1 := fun z => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  -- the decomposition `P = μ₊ + ν`, `Q = μ₋ + ν`
  set ν := P ⊓ Q with hν
  have hνP : ν ≤ P := inf_le_left
  have hνQ : ν ≤ Q := inf_le_right
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le P hνP
  set μp := P - ν with hμp
  set μm := Q - ν with hμm
  have hP : P = μp + ν := (Measure.sub_add_cancel_of_le hνP).symm
  have hQ : Q = μm + ν := (Measure.sub_add_cancel_of_le hνQ).symm
  have hmass : ν univ = ENNReal.ofReal (1 - tvDist P Q) := (StatFormal.Wave31tq.tv_density.1 𝒳 P Q).2.2.2.2
  have htv1 : tvDist P Q ≤ 1 := tvDist_le_one
  have hμpu : μp.real univ = tvDist P Q := by
    rw [measureReal_def, hμp, Measure.sub_apply MeasurableSet.univ hνP, hmass, measure_univ]
    rw [ENNReal.toReal_sub_of_le (by rw [← hmass, ← measure_univ (μ := P)]; exact hνP univ) ENNReal.one_ne_top]
    rw [ENNReal.toReal_ofReal (by linarith)]; simp
  -- integrals over the parts
  have hbint : ∀ (μ : Measure 𝒳) [IsFiniteMeasure μ] (h : 𝒳 → ℝ), Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → Integrable h μ :=
    fun μ _ h hm hb => Integrable.of_bound hm.aestronglyMeasurable 1
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hb z).1]; exact (hb z).2)
  have hsplitP : ∀ h : 𝒳 → ℝ, Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → ∫ z, h z ∂P = (∫ z, h z ∂μp) + ∫ z, h z ∂ν := by
    intro h hm hb; conv_lhs => rw [hP]
    exact integral_add_measure (hbint μp h hm hb) (hbint ν h hm hb)
  have hsplitQ : ∀ h : 𝒳 → ℝ, Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → ∫ z, h z ∂Q = (∫ z, h z ∂μm) + ∫ z, h z ∂ν := by
    intro h hm hb; conv_lhs => rw [hQ]
    exact integral_add_measure (hbint μm h hm hb) (hbint ν h hm hb)
  have hLψ : linL P Q ψ = (∫ z, ψ z ∂μp) - ∫ z, ψ z ∂μm := by
    unfold linL; rw [hsplitP ψ hψ hψ01, hsplitQ ψ hψ hψ01]; ring
  have hLr : linL P Q r = (∫ z, r z ∂μp) - ∫ z, r z ∂μm := by
    unfold linL; rw [hsplitP r hrm hr01, hsplitQ r hrm hr01]; ring
  have herr : errL P Q ψ = (μp.real univ - ∫ z, ψ z ∂μp) + ∫ z, ψ z ∂μm := by
    unfold errL; rw [hLψ, hμpu]; ring
  -- the two pointwise bounds, integrated
  have hψp := hbint μp ψ hψ hψ01
  have hψm := hbint μm ψ hψ hψ01
  have hrp := hbint μp r hrm hr01
  have hrm' := hbint μm r hrm hr01
  have hcb := fun z => clamp_bounds (hψ01 z).1 (hψ01 z).2 hao hbo hc
  have hI1 : 0 ≤ ∫ z, (r z - ψ z + K * (1 - ψ z)) ∂μp := integral_nonneg fun z => (hcb z).1
  have hI2 : 0 ≤ ∫ z, (K * ψ z - (r z - ψ z)) ∂μm := integral_nonneg fun z => (hcb z).2
  have e1 : ∫ z, (r z - ψ z + K * (1 - ψ z)) ∂μp = (∫ z, (r z - ψ z) ∂μp) + ∫ z, K * (1 - ψ z) ∂μp :=
    integral_add (f := fun z => r z - ψ z) (g := fun z => K * (1 - ψ z)) (hrp.sub hψp)
      (((integrable_const 1).sub hψp).const_mul K)
  have e2 : ∫ z, (r z - ψ z) ∂μp = (∫ z, r z ∂μp) - ∫ z, ψ z ∂μp := integral_sub hrp hψp
  have e3 : ∫ z, K * (1 - ψ z) ∂μp = K * ∫ z, (1 - ψ z) ∂μp := integral_const_mul K _
  have e4 : ∫ z, (1 - ψ z) ∂μp = (∫ _z, (1 : ℝ) ∂μp) - ∫ z, ψ z ∂μp := integral_sub (integrable_const 1) hψp
  have e5 : ∫ _z, (1 : ℝ) ∂μp = μp.real univ := by simp
  have f1 : ∫ z, (K * ψ z - (r z - ψ z)) ∂μm = (∫ z, K * ψ z ∂μm) - ∫ z, (r z - ψ z) ∂μm :=
    integral_sub (f := fun z => K * ψ z) (g := fun z => r z - ψ z) (hψm.const_mul K) (hrm'.sub hψm)
  have f2 : ∫ z, (r z - ψ z) ∂μm = (∫ z, r z ∂μm) - ∫ z, ψ z ∂μm := integral_sub hrm' hψm
  have f3 : ∫ z, K * ψ z ∂μm = K * ∫ z, ψ z ∂μm := integral_const_mul K _
  show linL P Q ψ - max ao bo * errL P Q ψ / c ≤ linL P Q r
  have hKe : max ao bo * errL P Q ψ / c = K * errL P Q ψ := by rw [hKdef]; ring
  rw [hKe, hLψ, hLr, herr]
  rw [e1, e2, e3, e4, e5] at hI1
  rw [f1, f2, f3] at hI2
  nlinarith [hI1, hI2]

end StatFormal.Wave31tu.RouteP
