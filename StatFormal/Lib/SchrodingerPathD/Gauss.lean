import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Gaussian identities for Brownian bridges on `ℝᵈ`

* `isoG d s = N(0, s I_d) = multivariateGaussian 0 (s₊ • 1)`; `isoG_eq_map`: it is the law of `√s Z`, `Z ∼ N(0, I_d)`;
  `charFunDual_isoG`: its characteristic function `exp(−s‖L‖²/2)`.
* `gaussPairD_bridge`: for `U ∼ N(0, εt I)`, `W ∼ N(0, ε(1−t) I)` independent, `(U + W, U)` has the law of
  `(S, tS + V)`, `S ∼ N(0, ε I)`, `V ∼ N(0, εt(1−t) I)` independent (Brownian-bridge decomposition at time `t`).
* `brownian_threeD`: the law of `((x, x + U + W), x + U)`, `x ∼ μ`, is `R₀₁ = Law(x, x + S)` mixed with the bridge
  kernel `N((1−t)x + ty, εt(1−t) I)`.
* `gaussPairD_witness`, `witnessD_law`: the process `x + t z₁ + √(t(1−t)) z₂` under `μ ⊗ N(0,εI) ⊗ N(0,εI)` has the
  three-time laws of `X₀ + √ε B` for every `t ∈ [0,1]`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal NNReal RealInnerProductSpace

set_option linter.style.longLine false

namespace StatFormal.SchrodingerPathD

local notation "E" d => EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- `N(0, s I_d)` (`s₊ = max s 0`). -/
def isoG (d : ℕ) (s : ℝ) : Measure (E d) :=
  multivariateGaussian 0 ((s.toNNReal : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))

instance (s : ℝ) : IsProbabilityMeasure (isoG d s) := by unfold isoG; infer_instance

lemma charFun_isoG (s : ℝ) (x : E d) : charFun (isoG d s) x = cexp (-((s.toNNReal : ℝ) * ‖x‖ ^ 2) / 2) := by
  have hS : ((s.toNNReal : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (NNReal.coe_nonneg _)
  rw [isoG, charFun_multivariateGaussian hS]
  congr 1
  simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub]
  have hx : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hx, smul_eq_mul]
  push_cast
  ring

lemma isoG_eq_map {s : ℝ} (hs : 0 ≤ s) : isoG d s = (stdGaussian (E d)).map (fun z => √s • z) := by
  apply Measure.ext_of_charFun
  funext x
  have hn : ‖√s • x‖ ^ 2 = s * ‖x‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hs]
  rw [charFun_isoG, charFun_map_smul, charFun_stdGaussian, Real.coe_toNNReal _ hs]
  congr 1
  rw [show ((‖√s • x‖ : ℝ) : ℂ) ^ 2 = ((s * ‖x‖ ^ 2 : ℝ) : ℂ) by rw [← hn]; push_cast; rfl]
  push_cast
  ring

lemma charFunDual_isoG (s : ℝ) (L : StrongDual ℝ (E d)) :
    charFunDual (isoG d s) L = cexp (-((s.toNNReal : ℝ) * ‖L‖ ^ 2) / 2) := by
  rw [← charFun_toDual_symm_eq_charFunDual, charFun_isoG, LinearIsometryEquiv.norm_map]

/-- The Brownian-bridge decomposition at time `t ∈ [0,1]` in `ℝᵈ`: `(U + W, U) ∼ (S, tS + V)`. -/
theorem gaussPairD_bridge {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((isoG d (ε * t)).prod (isoG d (ε * (1 - t)))).map (fun p : (E d) × (E d) => (p.1 + p.2, p.1)) =
      ((isoG d ε).prod (isoG d (ε * t * (1 - t)))).map (fun q : (E d) × (E d) => (q.1, t • q.1 + q.2)) := by
  have h0 : 0 ≤ t := ht.1
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hA : 0 ≤ ε * t := mul_nonneg hε h0
  have hB : 0 ≤ ε * (1 - t) := mul_nonneg hε h1
  have hC : 0 ≤ ε * t * (1 - t) := mul_nonneg hA h1
  set L₁ : ((E d) × (E d)) →L[ℝ] ((E d) × (E d)) :=
    ((ContinuousLinearMap.fst ℝ (E d) (E d)) + (ContinuousLinearMap.snd ℝ (E d) (E d))).prod
      (ContinuousLinearMap.fst ℝ (E d) (E d))
  set L₂ : ((E d) × (E d)) →L[ℝ] ((E d) × (E d)) :=
    (ContinuousLinearMap.fst ℝ (E d) (E d)).prod
      (t • (ContinuousLinearMap.fst ℝ (E d) (E d)) + (ContinuousLinearMap.snd ℝ (E d) (E d)))
  have e₁ : (fun p : (E d) × (E d) => (p.1 + p.2, p.1)) = ⇑L₁ := rfl
  have e₂ : (fun q : (E d) × (E d) => (q.1, t • q.1 + q.2)) = ⇑L₂ := rfl
  rw [e₁, e₂]
  apply Measure.ext_of_charFunDual
  funext M
  rw [charFunDual_map, charFunDual_map, charFunDual_prod, charFunDual_prod, charFunDual_isoG, charFunDual_isoG,
    charFunDual_isoG, charFunDual_isoG, Real.coe_toNNReal _ hA, Real.coe_toNNReal _ hB, Real.coe_toNNReal _ hε,
    Real.coe_toNNReal _ hC, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  set A := M.comp (ContinuousLinearMap.inl ℝ (E d) (E d))
  set B := M.comp (ContinuousLinearMap.inr ℝ (E d) (E d))
  have k1 : (M.comp L₁).comp (ContinuousLinearMap.inl ℝ (E d) (E d)) = A + B := by
    ext u; simp [L₁, A, B, ← map_add]
  have k2 : (M.comp L₁).comp (ContinuousLinearMap.inr ℝ (E d) (E d)) = A := by
    ext u; simp [L₁, A]
  have k3 : (M.comp L₂).comp (ContinuousLinearMap.inl ℝ (E d) (E d)) = A + t • B := by
    ext u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', L₂, A, B, ContinuousLinearMap.inr_apply, add_zero, smul_eq_mul]
    rw [show ((u, t • u) : (E d) × (E d)) = (u, 0) + t • ((0 : E d), u) by simp, map_add, map_smul, smul_eq_mul]
  have k4 : (M.comp L₂).comp (ContinuousLinearMap.inr ℝ (E d) (E d)) = B := by
    ext u; simp [L₂, B]
  rw [k1, k2, k3, k4]
  -- the dual norms through the Riesz isometry
  set a := (InnerProductSpace.toDual ℝ (E d)).symm A
  set b := (InnerProductSpace.toDual ℝ (E d)).symm B
  have nA : ‖A‖ = ‖a‖ := ((InnerProductSpace.toDual ℝ (E d)).symm.norm_map A).symm
  have nB : ‖B‖ = ‖b‖ := ((InnerProductSpace.toDual ℝ (E d)).symm.norm_map B).symm
  have nAB : ‖A + B‖ = ‖a + b‖ := by
    rw [← map_add]; exact ((InnerProductSpace.toDual ℝ (E d)).symm.norm_map _).symm
  have nAtB : ‖A + t • B‖ = ‖a + t • b‖ := by
    have : (InnerProductSpace.toDual ℝ (E d)).symm (A + t • B) = a + t • b := by
      rw [map_add, LinearIsometryEquiv.map_smulₛₗ]; simp [a, b]
    rw [← this]; exact ((InnerProductSpace.toDual ℝ (E d)).symm.norm_map _).symm
  rw [nA, nB, nAB, nAtB]
  have q1 : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := norm_add_sq_real a b
  have q2 : ‖a + t • b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (t * ⟪a, b⟫) + t ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  push_cast
  rw [← ofReal_pow, ← ofReal_pow, ← ofReal_pow, ← ofReal_pow, q1, q2]
  push_cast
  ring

/-- The three-time law of `X₀ + √ε B` in `ℝᵈ`. -/
theorem brownian_threeD (μ : Measure (E d)) [SFinite μ] {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    (μ.prod ((isoG d (ε * t)).prod (isoG d (ε * (1 - t))))).map
        (fun p : (E d) × (E d) × (E d) => ((p.1, p.1 + p.2.1 + p.2.2), p.1 + p.2.1)) =
      ((((μ.prod (isoG d ε)).map (fun p : (E d) × (E d) => (p.1, p.1 + p.2))).prod
          (isoG d (ε * t * (1 - t)))).map
        (fun q : ((E d) × (E d)) × (E d) => (q.1, (1 - t) • q.1.1 + t • q.1.2 + q.2))) := by
  set A := isoG d (ε * t)
  set B := isoG d (ε * (1 - t))
  set N := isoG d ε
  set V := isoG d (ε * t * (1 - t))
  have hL : (μ.prod (A.prod B)).map (fun p : (E d) × (E d) × (E d) => ((p.1, p.1 + p.2.1 + p.2.2), p.1 + p.2.1)) =
      ((μ.prod (A.prod B)).map (Prod.map id (fun p : (E d) × (E d) => (p.1 + p.2, p.1)))).map
        (fun r : (E d) × (E d) × (E d) => ((r.1, r.1 + r.2.1), r.1 + r.2.2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    simp only [Function.comp, Prod.map, id]
    ext <;> simp [add_assoc]
  have hM : (μ.prod (A.prod B)).map (Prod.map id (fun p : (E d) × (E d) => (p.1 + p.2, p.1))) =
      (μ.prod (N.prod V)).map (Prod.map id (fun q : (E d) × (E d) => (q.1, t • q.1 + q.2))) := by
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop),
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop), gaussPairD_bridge hε ht]
  rw [hL, hM, Measure.map_map (by fun_prop) (by fun_prop)]
  have hassoc : (μ.prod N).prod V = (μ.prod (N.prod V)).map MeasurableEquiv.prodAssoc.symm := by
    rw [← Measure.prodAssoc_prod, Measure.map_map (by fun_prop) (by fun_prop)]
    simp
  have hk : ((μ.prod N).map (fun p : (E d) × (E d) => (p.1, p.1 + p.2))).prod V =
      ((μ.prod N).prod V).map (Prod.map (fun p : (E d) × (E d) => (p.1, p.1 + p.2)) id) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
  rw [hk, hassoc,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext r
  simp only [Function.comp, Prod.map, id, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk,
    MeasurableEquiv.symm_mk, Equiv.prodAssoc_symm_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp
  · simp
  · simp only
    module

/-- Riesz-vector form of the dual norm. -/
lemma dual_norm_eq (A : StrongDual ℝ (E d)) : ‖A‖ = ‖(InnerProductSpace.toDual ℝ (E d)).symm A‖ :=
  ((InnerProductSpace.toDual ℝ (E d)).symm.norm_map A).symm

/-- The witness decomposition: for `z₁, z₂ ∼ N(0, εI)` independent and `s = √(t(1−t))`,
`(t z₁ + s z₂, (1−t) z₁ − s z₂) ∼ N(0, εt I) ⊗ N(0, ε(1−t) I)`. -/
theorem gaussPairD_witness {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((isoG d ε).prod (isoG d ε)).map
        (fun z : (E d) × (E d) => (t • z.1 + √(t * (1 - t)) • z.2, (1 - t) • z.1 - √(t * (1 - t)) • z.2)) =
      (isoG d (ε * t)).prod (isoG d (ε * (1 - t))) := by
  have h0 : 0 ≤ t := ht.1
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hA : 0 ≤ ε * t := mul_nonneg hε h0
  have hB : 0 ≤ ε * (1 - t) := mul_nonneg hε h1
  have hs : √(t * (1 - t)) ^ 2 = t * (1 - t) := Real.sq_sqrt (mul_nonneg h0 h1)
  set σ := √(t * (1 - t))
  set L₃ : ((E d) × (E d)) →L[ℝ] ((E d) × (E d)) :=
    (t • (ContinuousLinearMap.fst ℝ (E d) (E d)) + σ • (ContinuousLinearMap.snd ℝ (E d) (E d))).prod
      ((1 - t) • (ContinuousLinearMap.fst ℝ (E d) (E d)) - σ • (ContinuousLinearMap.snd ℝ (E d) (E d)))
  have e₃ : (fun z : (E d) × (E d) => (t • z.1 + σ • z.2, (1 - t) • z.1 - σ • z.2)) = ⇑L₃ := rfl
  rw [e₃]
  apply Measure.ext_of_charFunDual
  funext M
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod, charFunDual_isoG, charFunDual_isoG,
    charFunDual_isoG, charFunDual_isoG, Real.coe_toNNReal _ hA, Real.coe_toNNReal _ hB, Real.coe_toNNReal _ hε,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  set A := M.comp (ContinuousLinearMap.inl ℝ (E d) (E d))
  set B := M.comp (ContinuousLinearMap.inr ℝ (E d) (E d))
  have k1 : (M.comp L₃).comp (ContinuousLinearMap.inl ℝ (E d) (E d)) = t • A + (1 - t) • B := by
    ext u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.prod_apply,
      L₃, A, B, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply, smul_zero,
      add_zero, sub_zero, smul_eq_mul]
    rw [show ((t • u, (1 - t) • u) : (E d) × (E d)) = t • (u, (0 : E d)) + (1 - t) • ((0 : E d), u) by simp,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have k2 : (M.comp L₃).comp (ContinuousLinearMap.inr ℝ (E d) (E d)) = σ • A - σ • B := by
    ext u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.prod_apply,
      L₃, A, B, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply, smul_zero,
      zero_add, zero_sub, smul_eq_mul]
    rw [show ((σ • u, -(σ • u)) : (E d) × (E d)) = σ • (u, (0 : E d)) - σ • ((0 : E d), u) by simp,
      map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [k1, k2]
  set a := (InnerProductSpace.toDual ℝ (E d)).symm A
  set b := (InnerProductSpace.toDual ℝ (E d)).symm B
  have m1 : (InnerProductSpace.toDual ℝ (E d)).symm (t • A + (1 - t) • B) = t • a + (1 - t) • b := by
    rw [map_add, LinearIsometryEquiv.map_smulₛₗ, LinearIsometryEquiv.map_smulₛₗ]; simp [a, b]
  have m2 : (InnerProductSpace.toDual ℝ (E d)).symm (σ • A - σ • B) = σ • a - σ • b := by
    rw [map_sub, LinearIsometryEquiv.map_smulₛₗ, LinearIsometryEquiv.map_smulₛₗ]; simp [a, b]
  rw [dual_norm_eq (t • A + (1 - t) • B), dual_norm_eq (σ • A - σ • B), dual_norm_eq A, dual_norm_eq B, m1, m2]
  have q1 : ‖t • a + (1 - t) • b‖ ^ 2 = t ^ 2 * ‖a‖ ^ 2 + 2 * (t * (1 - t) * ⟪a, b⟫) + (1 - t) ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_left, inner_smul_right, norm_smul, norm_smul, mul_pow, mul_pow,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    simp only [conj_trivial]; ring
  have q2 : ‖σ • a - σ • b‖ ^ 2 = σ ^ 2 * (‖a‖ ^ 2 - 2 * ⟪a, b⟫ + ‖b‖ ^ 2) := by
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_sq_real]
  push_cast
  rw [← ofReal_pow, ← ofReal_pow, ← ofReal_pow, ← ofReal_pow, q1, q2, hs]
  push_cast
  ring

/-- The witness process `X_t(x, z₁, z₂) = x + t z₁ + √(t(1−t)) z₂` on `(ℝᵈ)³`. -/
def witnessD (t : ℝ) (ω : (E d) × (E d) × (E d)) : E d := ω.1 + t • ω.2.1 + √(t * (1 - t)) • ω.2.2

lemma measurable_witnessD (t : ℝ) : Measurable (witnessD (d := d) t) := by
  unfold witnessD; fun_prop

/-- Under `μ ⊗ N(0, εI) ⊗ N(0, εI)` the witness process has the three-time laws of `X₀ + √ε B` for every
`t ∈ [0,1]`. -/
theorem witnessD_law (μ : Measure (E d)) [SFinite μ] {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    (μ.prod ((isoG d ε).prod (isoG d ε))).map
        (fun ω => (witnessD 0 ω, witnessD t ω - witnessD 0 ω, witnessD 1 ω - witnessD t ω)) =
      μ.prod ((isoG d (ε * t)).prod (isoG d (ε * (1 - t)))) := by
  have e : (fun ω : (E d) × (E d) × (E d) => (witnessD 0 ω, witnessD t ω - witnessD 0 ω, witnessD 1 ω - witnessD t ω)) =
      Prod.map id (fun z : (E d) × (E d) => (t • z.1 + √(t * (1 - t)) • z.2, (1 - t) • z.1 - √(t * (1 - t)) • z.2)) := by
    funext ω
    simp only [witnessD, Prod.map, id, sub_self, mul_zero, Real.sqrt_zero, zero_smul, add_zero, one_smul, zero_mul]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only; abel
    · simp only; rw [sub_smul, one_smul]; abel
  rw [e, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, gaussPairD_witness hε ht]

end StatFormal.SchrodingerPathD
