import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.BigOperators

/-!
# Rademacher averages and the Ledoux–Talagrand contraction principle

Library component (concentration, part 3). Untrusted library code.

## Conventions

* A Rademacher vector is `σ : Fin n → Bool` with sign `rsign b = if b then 1 else -1`; the
  expectation over i.i.d. uniform signs is the finite average
  `radE F = 2⁻ⁿ · ∑_σ F σ` (exactly `E_σ F(σ)` for σ uniform on `{±1}ⁿ`).
* Classes are indexed by an arbitrary nonempty type `T`; suprema are `⨆ t` in `ℝ`, and every
  result assumes a uniform bound `|a t i| ≤ B`, so all suprema are finite (no junk values).

## Main results

* `radE_iSup_contraction` (**Ledoux–Talagrand, signed form, constant 1**): for 1-Lipschitz
  `φ i`, `E_σ sup_t ∑ σᵢ φᵢ(a t i) ≤ E_σ sup_t ∑ σᵢ a t i` (fixed points; induction over
  coordinates, pairing `σ` with `σ` flipped at one coordinate);
* `radE_iSup_posPart_le`: the corollary for `u ↦ max u 0`;
* `radE_rsign_mul`: `E σᵢσⱼ = δᵢⱼ`; `sq_radE_le` (Jensen for `radE`);
* `radE_norm_sum_le`: `E_σ ‖∑ σᵢ vᵢ‖ ≤ √(∑ ‖vᵢ‖²)` in a real inner-product space;
* `radE_abs_sum_rsign_le`: `E_σ |∑ σᵢ| ≤ √n`.
-/

noncomputable section
open Finset Real

namespace StatFormal.Concentration

/-- Rademacher sign of a Boolean. -/
def rsign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem rsign_true : rsign true = 1 := rfl
@[simp] theorem rsign_false : rsign false = -1 := rfl

theorem rsign_not (b : Bool) : rsign (!b) = -rsign b := by cases b <;> simp

theorem abs_rsign (b : Bool) : |rsign b| = 1 := by cases b <;> simp

theorem rsign_mul_self (b : Bool) : rsign b * rsign b = 1 := by cases b <;> simp

/-- Expectation over a uniform sign vector `σ ∈ {±1}ⁿ`. -/
def radE {n : ℕ} (F : (Fin n → Bool) → ℝ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ σ, F σ

variable {n : ℕ}

theorem radE_mono {F G : (Fin n → Bool) → ℝ} (h : ∀ σ, F σ ≤ G σ) : radE F ≤ radE G := by
  unfold radE
  gcongr with σ
  exact h σ

theorem radE_add (F G : (Fin n → Bool) → ℝ) :
    radE (fun σ => F σ + G σ) = radE F + radE G := by
  simp [radE, sum_add_distrib, mul_add]

theorem radE_const_mul (c : ℝ) (F : (Fin n → Bool) → ℝ) :
    radE (fun σ => c * F σ) = c * radE F := by
  simp only [radE, ← mul_sum]; ring

theorem radE_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin n → Bool) → ℝ) :
    radE (fun σ => ∑ k ∈ s, F k σ) = ∑ k ∈ s, radE (F k) := by
  simp only [radE, mul_sum]
  rw [Finset.sum_comm]

theorem card_signs : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring

theorem radE_const (c : ℝ) : radE (fun _ : Fin n → Bool => c) = c := by
  simp only [radE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signs]
  field_simp

/-- Flip the sign at coordinate `i`. -/
def flipAt (i : Fin n) (σ : Fin n → Bool) : Fin n → Bool := fun j => if j = i then !σ j else σ j

theorem flipAt_flipAt (i : Fin n) (σ : Fin n → Bool) : flipAt i (flipAt i σ) = σ := by
  funext j; by_cases h : j = i <;> simp [flipAt, h]

theorem sum_flipAt (i : Fin n) (F : (Fin n → Bool) → ℝ) :
    ∑ σ, F (flipAt i σ) = ∑ σ, F σ :=
  Equiv.sum_comp (Function.Involutive.toPerm _ (flipAt_flipAt i)) F

/-- Flip all signs. -/
def negSigns (σ : Fin n → Bool) : Fin n → Bool := fun j => !σ j

theorem radE_negSigns (F : (Fin n → Bool) → ℝ) : radE (fun σ => F (negSigns σ)) = radE F := by
  have h : Function.Involutive (negSigns (n := n)) := fun σ => by funext j; simp [negSigns]
  simp only [radE]
  exact congrArg _ (Equiv.sum_comp (Function.Involutive.toPerm _ h) F)

theorem bddAbove_of_abs_le {T : Type*} {f : T → ℝ} {C : ℝ} (h : ∀ t, |f t| ≤ C) :
    BddAbove (Set.range f) :=
  ⟨C, by rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (h t)⟩

/-- The two-point comparison behind the contraction principle. -/
theorem iSup_add_iSup_sub_le {T : Type*} [Nonempty T] (u v w : T → ℝ)
    (hv : ∀ s t, |v s - v t| ≤ |w s - w t|) (h₁ : BddAbove (Set.range fun t => u t + w t))
    (h₂ : BddAbove (Set.range fun t => u t - w t)) :
    (⨆ t, (u t + v t)) + ⨆ t, (u t - v t) ≤ (⨆ t, (u t + w t)) + ⨆ t, (u t - w t) := by
  set R := (⨆ t, (u t + w t)) + ⨆ t, (u t - w t)
  have hst : ∀ s t, (u s + v s) + (u t - v t) ≤ R := by
    intro s t
    have hs1 : u s + w s ≤ ⨆ t, (u t + w t) := le_ciSup h₁ s
    have hs2 : u s - w s ≤ ⨆ t, (u t - w t) := le_ciSup h₂ s
    have ht1 : u t + w t ≤ ⨆ t, (u t + w t) := le_ciSup h₁ t
    have ht2 : u t - w t ≤ ⨆ t, (u t - w t) := le_ciSup h₂ t
    have hvst := (le_abs_self _).trans (hv s t)
    rcases le_total (w t) (w s) with hw | hw
    · rw [abs_of_nonneg (sub_nonneg.2 hw)] at hvst; linarith
    · rw [abs_of_nonpos (sub_nonpos.2 hw)] at hvst; linarith
  have h1 : ∀ t, (⨆ s, (u s + v s)) ≤ R - (u t - v t) := fun t =>
    ciSup_le fun s => by linarith [hst s t]
  have h2 : (⨆ t, (u t - v t)) ≤ R - ⨆ s, (u s + v s) :=
    ciSup_le fun t => by linarith [h1 t]
  linarith

/-- One step of the contraction principle: replace the identity at coordinate `i` by a
1-Lipschitz `φ`. -/
theorem radE_iSup_update_le {T : Type*} [Nonempty T] (a : T → Fin n → ℝ) {B : ℝ}
    (ha : ∀ t j, |a t j| ≤ B) (ψ : Fin n → ℝ → ℝ) (hψ : ∀ j x y, |ψ j x - ψ j y| ≤ |x - y|)
    (i : Fin n) (hψi : ψ i = id) (φ : ℝ → ℝ) (hφ : ∀ x y, |φ x - φ y| ≤ |x - y|) :
    radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j)) ≤
      radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * ψ j (a t j)) := by
  set u : (Fin n → Bool) → T → ℝ :=
    fun σ t => ∑ j ∈ univ.erase i, rsign (σ j) * ψ j (a t j) with hu
  have hsplitG : ∀ σ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j) =
      u σ t + rsign (σ i) * φ (a t i) := by
    intro σ t
    rw [← Finset.add_sum_erase _ _ (mem_univ i), Function.update_self, add_comm]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  have hsplitF : ∀ σ t, ∑ j, rsign (σ j) * ψ j (a t j) = u σ t + rsign (σ i) * a t i := by
    intro σ t
    rw [← Finset.add_sum_erase _ _ (mem_univ i), hψi, add_comm]
    rfl
  have hu_flip : ∀ σ t, u (flipAt i σ) t = u σ t := by
    intro σ t
    refine sum_congr rfl fun j hj => ?_
    simp [flipAt, ne_of_mem_erase hj]
  have hflip_i : ∀ σ, rsign (flipAt i σ i) = -rsign (σ i) := by
    intro σ; simp [flipAt, rsign_not]
  -- uniform bound on `u`
  set C := ∑ j, (|ψ j 0| + B) with hC
  have hψb : ∀ j y, |ψ j y| ≤ |ψ j 0| + |y| := by
    intro j y
    have := hψ j y 0
    rw [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (ψ j y) (ψ j 0)
    linarith
  have hCu : ∀ σ t, |u σ t| ≤ C := by
    intro σ t
    calc |u σ t| ≤ ∑ j ∈ univ.erase i, |rsign (σ j) * ψ j (a t j)| := abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ univ.erase i, |ψ j (a t j)| := by simp [abs_mul, abs_rsign]
      _ ≤ ∑ j ∈ univ.erase i, (|ψ j 0| + B) :=
          sum_le_sum fun j _ => (hψb j _).trans (by linarith [ha t j])
      _ ≤ C := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun j _ _ => by
          have := (abs_nonneg _).trans (ha t j); positivity
  have hbdd : ∀ σ (c : ℝ), |c| ≤ 1 → BddAbove (Set.range fun t => u σ t + c * a t i) := by
    intro σ c hc
    refine bddAbove_of_abs_le (C := C + B) fun t => ?_
    refine (abs_add_le _ _).trans ?_
    have h1 := hCu σ t
    have h2 : |c * a t i| ≤ B := by
      rw [abs_mul]
      calc |c| * |a t i| ≤ 1 * B := mul_le_mul hc (ha t i) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    linarith
  -- pointwise pairing
  have hpair : ∀ σ, (⨆ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j)) +
      (⨆ t, ∑ j, rsign (flipAt i σ j) * Function.update ψ i φ j (a t j)) ≤
      (⨆ t, ∑ j, rsign (σ j) * ψ j (a t j)) +
        ⨆ t, ∑ j, rsign (flipAt i σ j) * ψ j (a t j) := by
    intro σ
    simp_rw [hsplitG, hsplitF, hu_flip, hflip_i]
    have key := iSup_add_iSup_sub_le (u σ) (fun t => φ (a t i)) (fun t => a t i)
      (fun s t => hφ _ _)
    rcases Bool.eq_false_or_eq_true (σ i) with h | h
    · rw [h, rsign_true]
      have h1 := hbdd σ 1 (by simp)
      have h2 := hbdd σ (-1) (by simp)
      simp only [one_mul, neg_mul, ← sub_eq_add_neg] at h1 h2 ⊢
      exact key h1 h2
    · rw [h, rsign_false]
      have h1 := hbdd σ 1 (by simp)
      have h2 := hbdd σ (-1) (by simp)
      simp only [one_mul, neg_mul, neg_neg, ← sub_eq_add_neg] at h1 h2 ⊢
      linarith [key h1 h2]
  -- sum over σ using the flip involution
  unfold radE
  have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have hG := sum_flipAt i (fun σ => ⨆ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j))
  have hF := sum_flipAt i (fun σ => ⨆ t, ∑ j, rsign (σ j) * ψ j (a t j))
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ univ) => hpair σ
  rw [sum_add_distrib, sum_add_distrib] at hsum
  linarith

/-- Mixed family: `φ j` on `S`, identity off `S`. -/
def mixφ (φ : Fin n → ℝ → ℝ) (S : Finset (Fin n)) : Fin n → ℝ → ℝ :=
  fun j => if j ∈ S then φ j else id

/-- **Ledoux–Talagrand contraction principle** (signed form, constant 1), for fixed points:
if each `φ i` is 1-Lipschitz then `E_σ sup_t ∑ σᵢ φᵢ(a t i) ≤ E_σ sup_t ∑ σᵢ a t i`. -/
theorem radE_iSup_contraction {T : Type*} [Nonempty T] (a : T → Fin n → ℝ) {B : ℝ}
    (ha : ∀ t j, |a t j| ≤ B) (φ : Fin n → ℝ → ℝ) (hφ : ∀ j x y, |φ j x - φ j y| ≤ |x - y|) :
    radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * φ j (a t j)) ≤
      radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * a t j) := by
  classical
  have hS : ∀ S : Finset (Fin n),
      radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * mixφ φ S j (a t j)) ≤
        radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * a t j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [mixφ]
    | insert i S hi ih =>
      have hupd : mixφ φ (insert i S) = Function.update (mixφ φ S) i (φ i) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [mixφ]
        · simp [mixφ, hj]
      rw [hupd]
      refine le_trans (radE_iSup_update_le a ha _ ?_ i (by simp [mixφ, hi]) (φ i) (hφ i)) ih
      intro j x y
      simp only [mixφ]
      split_ifs
      · exact hφ j x y
      · exact le_rfl
  simpa [mixφ] using hS univ

/-- Contraction for the positive part `u ↦ max u 0`. -/
theorem radE_iSup_posPart_le {T : Type*} [Nonempty T] (a : T → Fin n → ℝ) {B : ℝ}
    (ha : ∀ t j, |a t j| ≤ B) :
    radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * max (a t j) 0) ≤
      radE (fun σ => ⨆ t, ∑ j, rsign (σ j) * a t j) :=
  radE_iSup_contraction a ha (fun _ u => max u 0) fun _ x y => abs_max_sub_max_le_abs x y 0

/-! ### Second-moment (Khintchine-type) bounds -/

theorem radE_rsign_mul (i j : Fin n) :
    radE (fun σ => rsign (σ i) * rsign (σ j)) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij; simp only [rsign_mul_self, radE_const]
  · have h := sum_flipAt i (fun σ : Fin n → Bool => rsign (σ i) * rsign (σ j))
    have hj : ∀ σ, flipAt i σ j = σ j := fun σ => by simp [flipAt, Ne.symm hij]
    have hi : ∀ σ, rsign (flipAt i σ i) = -rsign (σ i) := fun σ => by simp [flipAt, rsign_not]
    simp only [hj, hi, neg_mul, sum_neg_distrib] at h
    unfold radE
    have : ∑ σ : Fin n → Bool, rsign (σ i) * rsign (σ j) = 0 := by linarith
    rw [this, mul_zero]

/-- Jensen for the Rademacher average. -/
theorem sq_radE_le (F : (Fin n → Bool) → ℝ) : radE F ^ 2 ≤ radE (fun σ => F σ ^ 2) := by
  unfold radE
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n → Bool))) (f := F)
  rw [Finset.card_univ] at h
  have hc : ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) = (2 : ℝ) ^ n := card_signs
  rw [hc] at h
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [mul_pow]
  calc ((2 : ℝ) ^ n)⁻¹ ^ 2 * (∑ σ, F σ) ^ 2
      ≤ ((2 : ℝ) ^ n)⁻¹ ^ 2 * ((2 : ℝ) ^ n * ∑ σ, F σ ^ 2) := by gcongr
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ σ, F σ ^ 2 := by field_simp

theorem radE_nonneg {F : (Fin n → Bool) → ℝ} (h : ∀ σ, 0 ≤ F σ) : 0 ≤ radE F := by
  unfold radE; exact mul_nonneg (by positivity) (sum_nonneg fun σ _ => h σ)

/-- `E_σ ‖∑ σᵢ vᵢ‖ ≤ √(∑ ‖vᵢ‖²)`. -/
theorem radE_norm_sum_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : Fin n → H) :
    radE (fun σ => ‖∑ i, rsign (σ i) • v i‖) ≤ √(∑ i, ‖v i‖ ^ 2) := by
  have hsq : radE (fun σ => ‖∑ i, rsign (σ i) • v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
    have hpt : ∀ σ : Fin n → Bool, ‖∑ i, rsign (σ i) • v i‖ ^ 2 =
        ∑ i, ∑ j, inner ℝ (v i) (v j) * (rsign (σ i) * rsign (σ j)) := by
      intro σ
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      refine sum_congr rfl fun i _ => ?_
      rw [inner_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right]; ring
    simp_rw [hpt]
    rw [radE_sum]
    simp_rw [radE_sum, radE_const_mul, radE_rsign_mul]
    simp
  have hJ := sq_radE_le (fun σ => ‖∑ i, rsign (σ i) • v i‖)
  rw [hsq] at hJ
  exact (le_abs_self _).trans (Real.abs_le_sqrt hJ)

/-- `E_σ |∑ σᵢ| ≤ √n`. -/
theorem radE_abs_sum_rsign_le : radE (fun σ : Fin n → Bool => |∑ i, rsign (σ i)|) ≤ √n := by
  have h := radE_norm_sum_le (H := ℝ) (n := n) (fun _ => 1)
  simpa [smul_eq_mul, Real.norm_eq_abs] using h

end StatFormal.Concentration
