import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Constants of a radial kernel (library, untrusted)

For a feature map `φ : E → ℋ` whose Gram function is radial, `⟪φ x, φ y⟫ = g ‖x − y‖`, with `g 0 = 1`, `g > 0` on `[0, ∞)` and
`g r → 0` as `r → ∞`, on a normed space `E` containing a unit vector: `‖φ x‖ = 1`, `‖φ x − φ y‖² = 2 − 2 g ‖x − y‖ < 2`, and the
diameter `sup ‖φ x − φ y‖` equals `√2` without being attained. The Gaussian `exp(−r²/(2σ²))` and the Laplace `exp(−r/σ)` profiles
satisfy the hypotheses (`gaussProfile_*`, `laplaceProfile_*`).
-/

noncomputable section
open Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.KernelFacts

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The squared feature distance of a radial Gram function: `‖φ x − φ y‖² = 2 − 2 g ‖x − y‖` when `g 0 = 1`. -/
theorem radial_norm_sub_sq (g : ℝ → ℝ) (φ : E → H) (hk : ∀ x y, ⟪φ x, φ y⟫_ℝ = g ‖x - y‖) (h0 : g 0 = 1) (x y : E) :
    ‖φ x - φ y‖ ^ 2 = 2 - 2 * g ‖x - y‖ := by
  rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hk, hk, hk]
  simp [h0]; ring

/-- A radial Gram function with `g 0 = 1` gives unit-norm features. -/
theorem radial_norm_eq_one (g : ℝ → ℝ) (φ : E → H) (hk : ∀ x y, ⟪φ x, φ y⟫_ℝ = g ‖x - y‖) (h0 : g 0 = 1) (x : E) :
    ‖φ x‖ = 1 := by
  have h := hk x x
  rw [real_inner_self_eq_norm_sq, sub_self, norm_zero, h0] at h
  have hn : 0 ≤ ‖φ x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖φ x‖ - 1), sq_nonneg (‖φ x‖ + 1)]

/-- The constants of a radial kernel: unit features, `‖φ x − φ y‖² = 2 − 2g < 2`, and diameter `√2` (least upper bound of the
pairwise distances), not attained. Hypotheses: `g 0 = 1`, `g > 0` on `[0,∞)`, `g → 0` at `+∞`, and a unit vector `e ∈ E`. -/
theorem radial_constants (g : ℝ → ℝ) (φ : E → H) (hk : ∀ x y, ⟪φ x, φ y⟫_ℝ = g ‖x - y‖) (h0 : g 0 = 1)
    (hpos : ∀ r, 0 ≤ r → 0 < g r) (hlim : Tendsto g atTop (𝓝 0)) (e : E) (he : ‖e‖ = 1) :
    (∀ x, ‖φ x‖ = 1) ∧
    (∀ x y, ‖φ x - φ y‖ ^ 2 = 2 - 2 * g ‖x - y‖ ∧ ‖φ x - φ y‖ ^ 2 < 2) ∧
    IsLUB (Set.range fun pr : E × E => ‖φ pr.1 - φ pr.2‖) (√2) ∧
    ∀ x y, ‖φ x - φ y‖ < √2 := by
  have hsq : ∀ x y, ‖φ x - φ y‖ ^ 2 = 2 - 2 * g ‖x - y‖ := radial_norm_sub_sq g φ hk h0
  have hlt2 : ∀ x y, ‖φ x - φ y‖ ^ 2 < 2 := fun x y => by
    rw [hsq]; linarith [hpos ‖x - y‖ (norm_nonneg _)]
  have hlt : ∀ x y, ‖φ x - φ y‖ < √2 := fun x y => by
    rw [← Real.sqrt_sq (norm_nonneg (φ x - φ y))]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (hlt2 x y)
  refine ⟨radial_norm_eq_one g φ hk h0, fun x y => ⟨hsq x y, hlt2 x y⟩, ⟨?_, ?_⟩, hlt⟩
  · rintro _ ⟨pr, rfl⟩
    exact (hlt pr.1 pr.2).le
  · intro b hb
    -- the distances along `t • e`, `t → ∞`, tend to `√2`
    have hnorm : ∀ t : ℝ, 0 ≤ t → ‖(0 : E) - t • e‖ = t := fun t ht => by
      rw [zero_sub, norm_neg, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]
    have hT : Tendsto (fun t : ℝ => ‖φ 0 - φ (t • e)‖) atTop (𝓝 (√2)) := by
      have h1 : Tendsto (fun t : ℝ => √(2 - 2 * g t)) atTop (𝓝 (√(2 - 2 * 0))) :=
        ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)).sqrt)
      simp only [mul_zero, sub_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      conv_lhs => rw [← hnorm t ht]
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    refine le_of_tendsto hT (Eventually.of_forall fun t => hb ⟨((0 : E), t • e), rfl⟩)

/-- The Gaussian profile `exp(−r²/(2σ²))` satisfies the hypotheses of `radial_constants`. -/
theorem gaussProfile_facts {σ : ℝ} (hσ : 0 < σ) :
    (fun r : ℝ => Real.exp (-r ^ 2 / (2 * σ ^ 2))) 0 = 1 ∧ (∀ r, 0 < Real.exp (-r ^ 2 / (2 * σ ^ 2))) ∧
    Tendsto (fun r : ℝ => Real.exp (-r ^ 2 / (2 * σ ^ 2))) atTop (𝓝 0) := by
  refine ⟨by simp, fun r => Real.exp_pos _, ?_⟩
  have hc : 0 < 2 * σ ^ 2 := by positivity
  refine Real.tendsto_exp_atBot.comp ?_
  have : Tendsto (fun r : ℝ => r ^ 2 / (2 * σ ^ 2)) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const hc
  simpa [neg_div] using this

/-- The Laplace profile `exp(−r/σ)` satisfies the hypotheses of `radial_constants`. -/
theorem laplaceProfile_facts {σ : ℝ} (hσ : 0 < σ) :
    (fun r : ℝ => Real.exp (-r / σ)) 0 = 1 ∧ (∀ r, 0 < Real.exp (-r / σ)) ∧
    Tendsto (fun r : ℝ => Real.exp (-r / σ)) atTop (𝓝 0) := by
  refine ⟨by simp, fun r => Real.exp_pos _, ?_⟩
  refine Real.tendsto_exp_atBot.comp ?_
  have : Tendsto (fun r : ℝ => r / σ) atTop atTop := tendsto_id.atTop_div_const hσ
  simpa [neg_div] using this

end StatFormal.KernelFacts
