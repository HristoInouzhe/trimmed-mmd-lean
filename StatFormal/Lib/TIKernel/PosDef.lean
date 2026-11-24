import StatFormal.Wave31tp.Statements
import Mathlib.Probability.Independence.Basic

/-!
# Positive definite functions: elementary facts and the integral form (library, untrusted)

For `k : V → ℂ` positive definite in the Bochner–Rudin sense (`Wave31tp.IsPosDefFun`): `k 0` is real and nonnegative,
`k (−z) = conj (k z)`, `‖k z‖ ≤ re (k 0)`; and for every bounded continuous positive definite `h` and every probability measure
`μ`, the double integral `∫∫ h (x − y) dμ dμ` is a nonnegative real (by averaging the finite quadratic form over `n` i.i.d.
points: `n h(0) + n(n−1) D ≥ 0` for every `n`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

open StatFormal.Wave31tp

variable {V : Type*} [AddCommGroup V]

lemma posdef_two (k : V → ℂ) (hk : IsPosDefFun k) (x₁ x₂ : V) (c₁ c₂ : ℂ) :
    (c₁ * conj c₁ * k 0 + c₁ * conj c₂ * k (x₁ - x₂) + (c₂ * conj c₁ * k (x₂ - x₁) + c₂ * conj c₂ * k 0)).im = 0 ∧
    0 ≤ (c₁ * conj c₁ * k 0 + c₁ * conj c₂ * k (x₁ - x₂) + (c₂ * conj c₁ * k (x₂ - x₁) + c₂ * conj c₂ * k 0)).re := by
  have h := hk 2 ![x₁, x₂] ![c₁, c₂]
  simpa [Fin.sum_univ_two, sub_self] using h

lemma posdef_zero (k : V → ℂ) (hk : IsPosDefFun k) : (k 0).im = 0 ∧ 0 ≤ (k 0).re := by
  have h := hk 1 ![0] ![1]
  simpa using h

lemma posdef_neg (k : V → ℂ) (hk : IsPosDefFun k) (z : V) : k (-z) = conj (k z) := by
  have h1 := (posdef_two k hk z 0 1 1).1
  have h2 := (posdef_two k hk z 0 1 Complex.I).1
  have h0 := (posdef_zero k hk).1
  simp only [sub_zero, zero_sub, map_one, mul_one, one_mul, Complex.conj_I] at h1 h2
  apply Complex.ext
  · simp [Complex.add_im, Complex.mul_im, h0] at h2
    simp
    linarith
  · simp [Complex.add_im, h0] at h1
    simp
    linarith

lemma posdef_norm_le (k : V → ℂ) (hk : IsPosDefFun k) (z : V) : ‖k z‖ ≤ (k 0).re := by
  by_cases hz : k z = 0
  · simp [hz, (posdef_zero k hk).2]
  have hn : 0 < ‖k z‖ := norm_pos_iff.mpr hz
  have hr : (‖k z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set c₂ : ℂ := -(k z) / (‖k z‖ : ℂ) with hc₂
  have h := (posdef_two k hk z 0 1 c₂).2
  have hneg := posdef_neg k hk z
  simp only [sub_zero, zero_sub, hneg, map_one, mul_one, one_mul] at h
  have hcc : conj c₂ = -(conj (k z)) / (‖k z‖ : ℂ) := by simp [hc₂]
  have hc : c₂ * conj c₂ = 1 := by
    rw [hcc, hc₂, div_mul_div_comm, neg_mul_neg, Complex.mul_conj']
    field_simp
  have e1 : conj c₂ * k z = -(‖k z‖ : ℂ) := by
    rw [hcc, neg_div, neg_mul, div_mul_eq_mul_div, Complex.conj_mul']
    field_simp
  have e2 : c₂ * conj (k z) = -(‖k z‖ : ℂ) := by
    rw [hc₂, neg_div, neg_mul, div_mul_eq_mul_div, Complex.mul_conj']
    field_simp
  rw [hc, e1, e2] at h
  have hre : (k 0).re + -‖k z‖ + (-‖k z‖ + (k 0).re) ≥ 0 := by
    simpa [Complex.add_re, Complex.mul_re] using h
  linarith

section Average

variable {W : Type*} [MeasurableSpace W]

/-- Two distinct coordinates of an i.i.d. sample have the product law. -/
lemma map_pair_pi {n : ℕ} (μ : Measure W) [IsProbabilityMeasure μ] {i j : Fin n} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin n => μ).map (fun x => (x i, x j)) = μ.prod μ := by
  have hind : iIndepFun (fun k (x : Fin n → W) => x k) (Measure.pi fun _ : Fin n => μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := hind.indepFun hij
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 h2]
  rw [(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq]

lemma integral_pair_pi {n : ℕ} (μ : Measure W) [IsProbabilityMeasure μ] {i j : Fin n} (hij : i ≠ j)
    {F : W × W → ℂ} (hF : AEStronglyMeasurable F (μ.prod μ)) :
    ∫ x, F (x i, x j) ∂(Measure.pi fun _ : Fin n => μ) = ∫ p, F p ∂(μ.prod μ) := by
  have hm : AEMeasurable (fun x : Fin n → W => (x i, x j)) (Measure.pi fun _ : Fin n => μ) :=
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
  rw [← integral_map hm (by rwa [map_pair_pi μ hij])]
  rw [map_pair_pi μ hij]

end Average

section IntegralForm

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma sum_ite_diag (n : ℕ) (a b : ℂ) :
    ∑ i : Fin n, ∑ j : Fin n, (if i = j then a else b) = n * a + ((n : ℂ) * n - n) * b := by
  have : ∀ i : Fin n, ∑ j : Fin n, (if i = j then a else b) = a + ((n : ℂ) - 1) * b := by
    intro i
    have : ∑ j : Fin n, (if i = j then a else b) = ∑ j : Fin n, (b + (if i = j then a - b else 0)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Integral positive definiteness**: for a bounded continuous positive definite `h` and a probability measure `μ`,
`∫∫ h (x − y) d(μ ⊗ μ)` is a nonnegative real. -/
theorem integral_posdef {h : V → ℂ} (hh : IsPosDefFun h) (hc : Continuous h) {C : ℝ} (hC : ∀ z, ‖h z‖ ≤ C)
    (μ : Measure V) [IsProbabilityMeasure μ] :
    (∫ p, h (p.1 - p.2) ∂(μ.prod μ)).im = 0 ∧ 0 ≤ (∫ p, h (p.1 - p.2) ∂(μ.prod μ)).re := by
  set D := ∫ p, h (p.1 - p.2) ∂(μ.prod μ)
  have hFc : Continuous fun p : V × V => h (p.1 - p.2) := hc.comp (continuous_fst.sub continuous_snd)
  have hF : AEStronglyMeasurable (fun p : V × V => h (p.1 - p.2)) (μ.prod μ) := hFc.aestronglyMeasurable
  have h0 := posdef_zero h hh
  -- the averaged quadratic form
  have key : ∀ n : ℕ, ((n : ℂ) * h 0 + ((n : ℂ) * n - n) * D).im = 0 ∧
      0 ≤ ((n : ℂ) * h 0 + ((n : ℂ) * n - n) * D).re := by
    intro n
    set P := Measure.pi fun _ : Fin n => μ
    have hint : ∀ i j : Fin n, Integrable (fun x : Fin n → V => h (x i - x j)) P := by
      intro i j
      refine Integrable.mono' (integrable_const C) ?_ (Eventually.of_forall fun x => hC _)
      exact (hc.comp ((continuous_apply i).sub (continuous_apply j))).aestronglyMeasurable
    have hS : ∫ x, ∑ i : Fin n, ∑ j : Fin n, h (x i - x j) ∂P = (n : ℂ) * h 0 + ((n : ℂ) * n - n) * D := by
      rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
      simp_rw [integral_finset_sum _ fun j _ => hint _ j]
      rw [← sum_ite_diag n (h 0) D]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hij
      · subst hij; simp [P]
      · exact integral_pair_pi (F := fun p : V × V => h (p.1 - p.2)) μ hij hF
    rw [← hS]
    have hpt : ∀ x : Fin n → V, (∑ i : Fin n, ∑ j : Fin n, h (x i - x j)).im = 0 ∧
        0 ≤ (∑ i : Fin n, ∑ j : Fin n, h (x i - x j)).re := by
      intro x
      simpa using hh n x (fun _ => 1)
    have hI : Integrable (fun x : Fin n → V => ∑ i : Fin n, ∑ j : Fin n, h (x i - x j)) P :=
      integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j
    have eim := (integral_im hI).symm
    have ere := (integral_re hI).symm
    simp only [RCLike.im_to_complex, RCLike.re_to_complex] at eim ere
    constructor
    · rw [eim]
      simp [fun x => (hpt x).1]
    · rw [ere]
      exact integral_nonneg fun x => (hpt x).2
  have him : D.im = 0 := by
    have := (key 2).1
    simp [Complex.add_im, Complex.mul_im, h0.1] at this
    norm_num at this
    linarith
  refine ⟨him, ?_⟩
  by_contra hneg
  push_neg at hneg
  obtain ⟨n, hn⟩ := exists_nat_gt ((h 0).re / (-D.re) + 2)
  have h2 := (key n).2
  have hre : ((n : ℂ) * h 0 + ((n : ℂ) * n - n) * D).re = n * (h 0).re + ((n : ℝ) * n - n) * D.re := by
    simp [Complex.add_re, Complex.mul_re, him]
  rw [hre] at h2
  have hpos : 0 < -D.re := by linarith
  have hn2 : (2 : ℝ) < n := by
    have := div_nonneg h0.2 hpos.le
    linarith
  have hlt : (h 0).re < ((n : ℝ) - 1) * (-D.re) := by
    have : (h 0).re / (-D.re) < (n : ℝ) - 1 := by linarith
    rwa [div_lt_iff₀ hpos] at this
  nlinarith

end IntegralForm

end StatFormal.TIKernel
