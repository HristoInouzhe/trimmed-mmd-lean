import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Hilbert-space sample means: second moment and expectation bound

Library component (concentration, part 1). Untrusted library code.

Setting: `H` a real complete inner-product space, `φ : X → H` strongly measurable with
`‖φ x‖ ≤ κ`, `P` a probability measure on `X`, and the i.i.d. sample realised as
`Measure.pi (fun _ : Fin n => P)` on `Fin n → X`. (Strong measurability is what Bochner
integration needs; for separable Borel `H` it follows from `Measurable φ`.)

`meanDev P φ n x := (n : ℝ)⁻¹ • ∑ i, φ (x i) - ∫ y, φ y ∂P` (empirical minus population mean
embedding).

## Main results

* `integral_norm_meanDev_sq`: `E‖meanDev‖² = (E_P‖φ‖² − ‖E_P φ‖²) / n` for `n ≠ 0`
  (cross terms vanish by independence of coordinates under `Measure.pi`);
* `integral_norm_meanDev_le`: `E‖meanDev‖ ≤ κ / √n` for `n ≠ 0` (Jensen via `variance_nonneg`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace StatFormal.Concentration

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Empirical mean embedding minus population mean embedding. -/
def meanDev (P : Measure X) (φ : X → H) (n : ℕ) (x : Fin n → X) : H :=
  (n : ℝ)⁻¹ • ∑ i, φ (x i) - ∫ y, φ y ∂P

variable {P : Measure X} [IsProbabilityMeasure P] {φ : X → H} {κ : ℝ}

theorem norm_integral_le_of_bound (hκ : ∀ x, ‖φ x‖ ≤ κ) : ‖∫ y, φ y ∂P‖ ≤ κ := by
  simpa using norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ hκ)

theorem integrable_of_bound (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    Integrable φ P :=
  Integrable.of_bound hφ.aestronglyMeasurable κ (ae_of_all _ hκ)

/-- `meanDev` as an average of centred terms (for `n ≠ 0`). -/
theorem meanDev_eq {n : ℕ} (hn : n ≠ 0) (x : Fin n → X) :
    meanDev P φ n x = (n : ℝ)⁻¹ • ∑ i, (φ (x i) - ∫ y, φ y ∂P) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [meanDev, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- Integrals of functions of one coordinate under the product measure. -/
theorem integral_comp_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (i : Fin n) {g : X → E} (hg : AEStronglyMeasurable g P) :
    ∫ x, g (x i) ∂(Measure.pi fun _ : Fin n => P) = ∫ y, g y ∂P := by
  have h := (measurePreserving_eval (fun _ : Fin n => P) i).map_eq
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : Fin n => P).map (Function.eval i)) := by
    rw [h]; exact hg
  calc ∫ x, g (x i) ∂(Measure.pi fun _ : Fin n => P)
      = ∫ y, g y ∂((Measure.pi fun _ : Fin n => P).map (Function.eval i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable hg').symm
    _ = ∫ y, g y ∂P := by rw [h]

/-- `E_P‖φ − Eφ‖² = E_P‖φ‖² − ‖Eφ‖²`. -/
theorem integral_norm_sub_integral_sq (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    ∫ y, ‖φ y - ∫ z, φ z ∂P‖ ^ 2 ∂P = ∫ y, ‖φ y‖ ^ 2 ∂P - ‖∫ z, φ z ∂P‖ ^ 2 := by
  set m := ∫ z, φ z ∂P with hm
  have hint := integrable_of_bound (P := P) hφ hκ
  have hsq : Integrable (fun y => ‖φ y‖ ^ 2) P :=
    Integrable.of_bound (hφ.norm.pow 2).aestronglyMeasurable (κ ^ 2) (ae_of_all _ fun y => by
      have h0 := norm_nonneg (φ y)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ h0 (hκ y) 2)
  have hin : Integrable (fun y => 2 * inner ℝ (φ y) m) P := by
    have h1 : Integrable (fun y => inner ℝ m (φ y)) P := hint.const_inner m
    simpa [real_inner_comm] using h1.const_mul 2
  simp_rw [norm_sub_sq_real]
  have hsub : Integrable (fun y => ‖φ y‖ ^ 2 - 2 * inner ℝ (φ y) m) P := hsq.sub hin
  rw [integral_add hsub (integrable_const _), integral_sub hsq hin, integral_const,
    integral_const_mul]
  have : ∫ y, inner ℝ (φ y) m ∂P = ‖m‖ ^ 2 := by
    simp_rw [real_inner_comm m]
    rw [integral_inner hint m, ← hm, real_inner_self_eq_norm_sq]
  rw [this, probReal_univ, one_smul]
  ring

/-- **Second moment of the Hilbert-space sample mean**:
`E‖(1/n) ∑ φ(Xᵢ) − Eφ‖² = (E‖φ‖² − ‖Eφ‖²) / n`. -/
theorem integral_norm_meanDev_sq {n : ℕ} (hn : n ≠ 0) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    ∫ x, ‖meanDev P φ n x‖ ^ 2 ∂(Measure.pi fun _ : Fin n => P) =
      (∫ y, ‖φ y‖ ^ 2 ∂P - ‖∫ y, φ y ∂P‖ ^ 2) / n := by
  set Pn := Measure.pi fun _ : Fin n => P with hPn
  set m := ∫ y, φ y ∂P with hm
  set Y : X → H := fun y => φ y - m with hYdef
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hYm : StronglyMeasurable Y := hφ.sub stronglyMeasurable_const
  have hYb : ∀ y, ‖Y y‖ ≤ 2 * κ := fun y =>
    (norm_sub_le _ _).trans (by linarith [hκ y, norm_integral_le_of_bound (P := P) hκ])
  have hYint : Integrable Y P := Integrable.of_bound hYm.aestronglyMeasurable _ (ae_of_all _ hYb)
  have hY0 : ∫ y, Y y ∂P = 0 := by
    rw [integral_sub (integrable_of_bound hφ hκ) (integrable_const m), integral_const,
      probReal_univ, one_smul, sub_self]
  have hcoord : ∀ i : Fin n, ∫ x, Y (x i) ∂Pn = 0 := fun i => by
    rw [integral_comp_eval i hYint.aestronglyMeasurable, hY0]
  have hterm_int : ∀ i j : Fin n,
      Integrable (fun x : Fin n → X => inner ℝ (Y (x i)) (Y (x j))) Pn :=
    fun i j => Integrable.of_bound
      ((hYm.comp_measurable (measurable_pi_apply i)).inner
        (hYm.comp_measurable (measurable_pi_apply j))).aestronglyMeasurable
      (2 * κ * (2 * κ)) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul (hYb _) (hYb _) (norm_nonneg _) ((norm_nonneg _).trans (hYb (x i))))
  have hterm : ∀ i j : Fin n, ∫ x, inner ℝ (Y (x i)) (Y (x j)) ∂Pn =
      if i = j then ∫ y, ‖Y y‖ ^ 2 ∂P else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      exact (integral_congr_ae (ae_of_all _ fun (x : Fin n → X) =>
        real_inner_self_eq_norm_sq (Y (x i)))).trans
        (integral_comp_eval (g := fun y => ‖Y y‖ ^ 2) i (hYm.norm.pow 2).aestronglyMeasurable)
    · have hind : IndepFun (fun x : Fin n → X => x i) (fun x => x j) Pn :=
        (iIndepFun_pi (μ := fun _ : Fin n => P) (X := fun _ : Fin n => (id : X → X))
          (fun _ => aemeasurable_id)).indepFun hij
      have hmap : ∀ k : Fin n, Integrable Y (Pn.map fun x => x k) := fun k => by
        have h := (measurePreserving_eval (fun _ : Fin n => P) k).map_eq
        change Integrable Y (Pn.map (Function.eval k))
        rw [h]; exact hYint
      have := hind.integral_bilin_comp_comp (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable (hmap i) (hmap j) (innerSL ℝ)
      have key : ∫ x, inner ℝ (Y (x i)) (Y (x j)) ∂Pn =
          inner ℝ (∫ x, Y (x i) ∂Pn) (∫ x, Y (x j) ∂Pn) := this
      rw [key, hcoord i, hcoord j, inner_zero_left]
  have hpt : ∀ x : Fin n → X, ‖meanDev P φ n x‖ ^ 2 =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, inner ℝ (Y (x i)) (Y (x j)) := by
    intro x
    rw [meanDev_eq hn, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
    rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _
    fun j _ => hterm_int i j]
  simp_rw [integral_finsetSum _ fun j _ => hterm_int _ j, hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [integral_norm_sub_integral_sq hφ hκ, ← hm]
  field_simp

/-- **Expectation bound**: `E‖(1/n) ∑ φ(Xᵢ) − Eφ‖ ≤ κ / √n` for `n ≠ 0`. -/
theorem integral_norm_meanDev_le {n : ℕ} (hn : n ≠ 0) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    ∫ x, ‖meanDev P φ n x‖ ∂(Measure.pi fun _ : Fin n => P) ≤ κ / √n := by
  set Pn := Measure.pi fun _ : Fin n => P
  set F : (Fin n → X) → ℝ := fun x => ‖meanDev P φ n x‖ with hF
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x)
  have hFm : StronglyMeasurable F := by
    refine StronglyMeasurable.norm ?_
    refine StronglyMeasurable.sub ?_ stronglyMeasurable_const
    refine StronglyMeasurable.const_smul ?_ _
    exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hφ.comp_measurable (measurable_pi_apply i)
  have hFb : ∀ x, ‖F x‖ ≤ 2 * κ := fun x => by
    rw [Real.norm_eq_abs, abs_norm]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(n : ℝ)⁻¹ • ∑ i, φ (x i)‖ ≤ κ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnpos]
      calc (n : ℝ)⁻¹ * ‖∑ i, φ (x i)‖ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, κ := by
            gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hκ _)
        _ = κ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    linarith [norm_integral_le_of_bound (P := P) hκ]
  have hmem : MemLp F 2 Pn := MemLp.of_bound hFm.aestronglyMeasurable (2 * κ) (ae_of_all _ hFb)
  have hvar := variance_eq_sub hmem
  have hv0 := variance_nonneg F Pn
  have h2 : ∫ x, F x ^ 2 ∂Pn ≤ κ ^ 2 / n := by
    have hsq := integral_norm_meanDev_sq (P := P) hn hφ hκ
    have hle : ∫ y, ‖φ y‖ ^ 2 ∂P ≤ κ ^ 2 := by
      calc ∫ y, ‖φ y‖ ^ 2 ∂P ≤ ∫ _y, κ ^ 2 ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun y => by positivity) (integrable_const _)
              (ae_of_all _ fun y => pow_le_pow_left₀ (norm_nonneg _) (hκ y) 2)
        _ = κ ^ 2 := by simp
    change ∫ x, ‖meanDev P φ n x‖ ^ 2 ∂Pn ≤ κ ^ 2 / n
    rw [hsq]
    gcongr
    linarith [sq_nonneg ‖∫ y, φ y ∂P‖]
  have hE2 : (∫ x, F x ∂Pn) ^ 2 ≤ κ ^ 2 / n := by
    have : Pn[F ^ 2] = ∫ x, F x ^ 2 ∂Pn := by simp [Pi.pow_apply]
    linarith
  have hrhs : κ / √n = √(κ ^ 2 / n) := by
    rw [Real.sqrt_div' _ hnpos.le, Real.sqrt_sq hκ0]
  rw [hrhs]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hE2)

end StatFormal.Concentration
