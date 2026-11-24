import StatFormal.Lib.GaussianEOT.Optimal
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Gaussian identities for Brownian bridges on `ℝ`

* `ext_of_map_lin`: Cramér–Wold on `ℝ × ℝ` (two finite measures with the same laws of every `αz₁ + βz₂` coincide).
* `std2_map_lin_eq`: two linear images `(au₁ + bu₂, cu₁ + du₂)` of a standard Gaussian pair coincide when their
  covariance entries `a² + b²`, `ac + bd`, `c² + d²` agree.
* `gaussPair_bridge`: for `U ∼ N(0, εt)`, `W ∼ N(0, ε(1−t))` independent, `(U + W, U)` has the law of `(S, tS + V)`,
  `S ∼ N(0, ε)`, `V ∼ N(0, εt(1−t))` independent (the Brownian-bridge decomposition at time `t`).
* `brownian_three`: the law of `((x, x + U + W), x + U)`, `x ∼ μ`, is `R₀₁ = Law(x, x + S)` mixed with the bridge kernel
  `N((1−t)x + ty, εt(1−t))`.
* `refWitness`: a process on `ℝ³` with `(X₀, X_t − X₀, X₁ − X_t) ∼ μ ⊗ N(0, εt) ⊗ N(0, ε(1−t))` for every `t ∈ [0,1]`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.SchrodingerPath

open StatFormal.Foundations.GaussianEOT

/-- Cramér–Wold on `ℝ × ℝ`. -/
lemma ext_of_map_lin {ρ ρ' : Measure (ℝ × ℝ)} [IsFiniteMeasure ρ] [IsFiniteMeasure ρ']
    (h : ∀ α β : ℝ, ρ.map (fun z => α * z.1 + β * z.2) = ρ'.map (fun z => α * z.1 + β * z.2)) : ρ = ρ' := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  have hL : (⇑L) = fun z : ℝ × ℝ => L (1, 0) * z.1 + L (0, 1) * z.2 := by
    funext z
    have hz : z = z.1 • ((1 : ℝ), (0 : ℝ)) + z.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hL, h]

/-- The standard Gaussian pair. -/
abbrev std2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

lemma std2_map_lin_dual (a b c d α β : ℝ) :
    (std2.map (fun u : ℝ × ℝ => (a * u.1 + b * u.2, c * u.1 + d * u.2))).map (fun z => α * z.1 + β * z.2) =
      gaussianReal 0 (((α * a + β * c) ^ 2 + (α * b + β * d) ^ 2).toNNReal) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : ((fun z : ℝ × ℝ => α * z.1 + β * z.2) ∘ fun u : ℝ × ℝ => (a * u.1 + b * u.2, c * u.1 + d * u.2)) =
      fun u : ℝ × ℝ => 0 + (α * a + β * c) * u.1 + (α * b + β * d) * u.2 := by
    funext u; simp only [Function.comp]; ring
  rw [he, gauss_lin2]

/-- Linear images of the standard Gaussian pair with the same covariance coincide. -/
theorem std2_map_lin_eq {a b c d a' b' c' d' : ℝ} (h1 : a ^ 2 + b ^ 2 = a' ^ 2 + b' ^ 2)
    (h2 : a * c + b * d = a' * c' + b' * d') (h3 : c ^ 2 + d ^ 2 = c' ^ 2 + d' ^ 2) :
    std2.map (fun u : ℝ × ℝ => (a * u.1 + b * u.2, c * u.1 + d * u.2)) =
      std2.map (fun u : ℝ × ℝ => (a' * u.1 + b' * u.2, c' * u.1 + d' * u.2)) := by
  refine ext_of_map_lin fun α β => ?_
  rw [std2_map_lin_dual, std2_map_lin_dual]
  have e1 : (α * a + β * c) ^ 2 + (α * b + β * d) ^ 2 =
      α ^ 2 * (a ^ 2 + b ^ 2) + 2 * α * β * (a * c + b * d) + β ^ 2 * (c ^ 2 + d ^ 2) := by ring
  have e2 : (α * a' + β * c') ^ 2 + (α * b' + β * d') ^ 2 =
      α ^ 2 * (a' ^ 2 + b' ^ 2) + 2 * α * β * (a' * c' + b' * d') + β ^ 2 * (c' ^ 2 + d' ^ 2) := by ring
  rw [e1, e2, h1, h2, h3]

/-- `N(0, v) ⊗ N(0, w)` as a diagonal image of the standard pair. -/
lemma gaussProd_eq_std2 {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (gaussianReal 0 v.toNNReal).prod (gaussianReal 0 w.toNNReal) =
      std2.map (fun u : ℝ × ℝ => (√v * u.1 + 0 * u.2, 0 * u.1 + √w * u.2)) := by
  have hv' : (gaussianReal 0 1).map (fun u => 0 + √v * u) = gaussianReal 0 v.toNNReal := by
    rw [gauss_affine_std, Real.sq_sqrt hv]
  have hw' : (gaussianReal 0 1).map (fun u => 0 + √w * u) = gaussianReal 0 w.toNNReal := by
    rw [gauss_affine_std, Real.sq_sqrt hw]
  rw [← hv', ← hw', Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  simp [Prod.map]

/-- The Brownian-bridge decomposition at time `t ∈ [0,1]`: `(U + W, U) ∼ (S, tS + V)`. -/
theorem gaussPair_bridge {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((gaussianReal 0 (ε * t).toNNReal).prod (gaussianReal 0 (ε * (1 - t)).toNNReal)).map
        (fun p : ℝ × ℝ => (p.1 + p.2, p.1)) =
      ((gaussianReal 0 ε.toNNReal).prod (gaussianReal 0 (ε * t * (1 - t)).toNNReal)).map
        (fun q : ℝ × ℝ => (q.1, t * q.1 + q.2)) := by
  have h0 : 0 ≤ t := ht.1
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hA : 0 ≤ ε * t := mul_nonneg hε h0
  have hB : 0 ≤ ε * (1 - t) := mul_nonneg hε h1
  have hC : 0 ≤ ε * t * (1 - t) := mul_nonneg hA h1
  rw [gaussProd_eq_std2 hA hB, gaussProd_eq_std2 hε hC, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have eL : ((fun p : ℝ × ℝ => (p.1 + p.2, p.1)) ∘
      fun u : ℝ × ℝ => (√(ε * t) * u.1 + 0 * u.2, 0 * u.1 + √(ε * (1 - t)) * u.2)) =
      fun u : ℝ × ℝ => (√(ε * t) * u.1 + √(ε * (1 - t)) * u.2, √(ε * t) * u.1 + 0 * u.2) := by
    funext u; simp only [Function.comp]; ext <;> ring
  have eR : ((fun q : ℝ × ℝ => (q.1, t * q.1 + q.2)) ∘
      fun u : ℝ × ℝ => (√ε * u.1 + 0 * u.2, 0 * u.1 + √(ε * t * (1 - t)) * u.2)) =
      fun u : ℝ × ℝ => (√ε * u.1 + 0 * u.2, (t * √ε) * u.1 + √(ε * t * (1 - t)) * u.2) := by
    funext u; simp only [Function.comp]; ext <;> ring
  rw [eL, eR]
  have sA := Real.sq_sqrt hA
  have sB := Real.sq_sqrt hB
  have sC := Real.sq_sqrt hC
  have sε := Real.sq_sqrt hε
  have mA : √(ε * t) * √(ε * t) = ε * t := Real.mul_self_sqrt hA
  apply std2_map_lin_eq
  · linear_combination sA + sB - sε
  · linear_combination mA - t * sε
  · linear_combination sA - t ^ 2 * sε - sC

/-- The three-time law of `X₀ + √ε B`: `((x, x + U + W), x + U)` with `x ∼ μ`, `U ∼ N(0,εt)`, `W ∼ N(0,ε(1−t))`
independent is the reference endpoint law `Law(x, x + S)` mixed with the bridge kernel `N((1−t)x + ty, εt(1−t))`. -/
theorem brownian_three (μ : Measure ℝ) [SFinite μ] {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    (μ.prod ((gaussianReal 0 (ε * t).toNNReal).prod (gaussianReal 0 (ε * (1 - t)).toNNReal))).map
        (fun p : ℝ × ℝ × ℝ => ((p.1, p.1 + p.2.1 + p.2.2), p.1 + p.2.1)) =
      ((((μ.prod (gaussianReal 0 ε.toNNReal)).map (fun p : ℝ × ℝ => (p.1, p.1 + p.2))).prod
          (gaussianReal 0 (ε * t * (1 - t)).toNNReal)).map
        (fun q : (ℝ × ℝ) × ℝ => (q.1, (1 - t) * q.1.1 + t * q.1.2 + q.2))) := by
  set A := gaussianReal 0 (ε * t).toNNReal
  set B := gaussianReal 0 (ε * (1 - t)).toNNReal
  set N := gaussianReal 0 ε.toNNReal
  set V := gaussianReal 0 (ε * t * (1 - t)).toNNReal
  -- left side through the bridge decomposition
  have hL : (μ.prod (A.prod B)).map (fun p : ℝ × ℝ × ℝ => ((p.1, p.1 + p.2.1 + p.2.2), p.1 + p.2.1)) =
      ((μ.prod (A.prod B)).map (Prod.map id (fun p : ℝ × ℝ => (p.1 + p.2, p.1)))).map
        (fun r : ℝ × ℝ × ℝ => ((r.1, r.1 + r.2.1), r.1 + r.2.2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    simp only [Function.comp, Prod.map, id]
    ext <;> simp; ring
  have hM : (μ.prod (A.prod B)).map (Prod.map id (fun p : ℝ × ℝ => (p.1 + p.2, p.1))) =
      (μ.prod (N.prod V)).map (Prod.map id (fun q : ℝ × ℝ => (q.1, t * q.1 + q.2))) := by
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop),
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop), gaussPair_bridge hε ht]
  rw [hL, hM, Measure.map_map (by fun_prop) (by fun_prop)]
  -- right side through associativity
  have hassoc : (μ.prod N).prod V = (μ.prod (N.prod V)).map MeasurableEquiv.prodAssoc.symm := by
    rw [← Measure.prodAssoc_prod, Measure.map_map (by fun_prop) (by fun_prop)]
    simp
  have hk : ((μ.prod N).map (fun p : ℝ × ℝ => (p.1, p.1 + p.2))).prod V =
      ((μ.prod N).prod V).map (Prod.map (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) id) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
  rw [hk, hassoc,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext r
  simp only [Function.comp, Prod.map, id, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk,
    MeasurableEquiv.symm_mk, Equiv.prodAssoc_symm_apply]
  ext <;> simp; ring

/-! ### A process with the three-time laws of `X₀ + √ε B` -/

/-- `X_t = x + √ε (t z₁ + √(t(1−t)) z₂)` on `ℝ³ = {(x, z₁, z₂)}`. -/
def refWitness (ε : ℝ) (t : ℝ) (ω : ℝ × ℝ × ℝ) : ℝ := ω.1 + √ε * (t * ω.2.1 + √(t * (1 - t)) * ω.2.2)

lemma measurable_refWitness (ε t : ℝ) : Measurable (refWitness ε t) := by
  unfold refWitness; fun_prop

theorem refWitness_law (μ : Measure ℝ) [SFinite μ] {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    (μ.prod std2).map (fun ω => (refWitness ε 0 ω, refWitness ε t ω - refWitness ε 0 ω,
        refWitness ε 1 ω - refWitness ε t ω)) =
      μ.prod ((gaussianReal 0 (ε * t).toNNReal).prod (gaussianReal 0 (ε * (1 - t)).toNNReal)) := by
  have h0 : 0 ≤ t := ht.1
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hA : 0 ≤ ε * t := mul_nonneg hε h0
  have hB : 0 ≤ ε * (1 - t) := mul_nonneg hε h1
  have hT : 0 ≤ t * (1 - t) := mul_nonneg h0 h1
  set s := √(t * (1 - t))
  have hmap : (fun ω => (refWitness ε 0 ω, refWitness ε t ω - refWitness ε 0 ω,
      refWitness ε 1 ω - refWitness ε t ω)) =
      Prod.map id (fun u : ℝ × ℝ => ((√ε * t) * u.1 + (√ε * s) * u.2, (√ε * (1 - t)) * u.1 + (-(√ε * s)) * u.2)) := by
    funext ω
    simp only [refWitness, Prod.map, id, s]
    simp
    constructor <;> ring
  rw [hmap, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, gaussProd_eq_std2 hA hB]
  congr 1
  have sA := Real.sq_sqrt hA
  have sB := Real.sq_sqrt hB
  have sε := Real.sq_sqrt hε
  have sT : s ^ 2 = t * (1 - t) := Real.sq_sqrt hT
  apply std2_map_lin_eq
  · have : (√ε * t) ^ 2 + (√ε * s) ^ 2 = √ε ^ 2 * (t ^ 2 + s ^ 2) := by ring
    rw [this, sε, sT]; nlinarith
  · have : √ε * t * (√ε * (1 - t)) + √ε * s * -(√ε * s) = √ε ^ 2 * (t * (1 - t) - s ^ 2) := by ring
    rw [this, sT]; ring
  · have : (√ε * (1 - t)) ^ 2 + (-(√ε * s)) ^ 2 = √ε ^ 2 * ((1 - t) ^ 2 + s ^ 2) := by ring
    rw [this, sε, sT]; nlinarith

end StatFormal.SchrodingerPath
