import StatFormal.Lib.Concentration.Rademacher

/-!
# Contraction principle, absolute-value form

Library component (concentration, part 3b). Untrusted library code. Conventions as in
`Rademacher.lean` (`radE` = exact average over `σ ∈ {±1}ⁿ`, nonempty index type, uniform bound).

* `radE_iSup_abs_contraction`: if each `φ i` is 1-Lipschitz with `φ i 0 = 0`, then
  `E_σ sup_t |∑ σᵢ φᵢ(a t i)| ≤ 2 E_σ sup_t |∑ σᵢ a t i|`.

Proof: `|z| = z₊ + (−z)₊`; `sup_t (Z_t)₊` is the signed supremum over `T` with the zero function
adjoined (`Option T`, using `φ i 0 = 0`); `σ ↦ −σ` turns the `(−Z)₊` term into the first; the
signed contraction (`radE_iSup_contraction`) on `Option T`; and `max(0, sup_t W_t) ≤ sup_t |W_t|`.
-/

noncomputable section
open Finset Real

namespace StatFormal.Concentration

variable {n : ℕ}

theorem radE_iSup_abs_contraction {T : Type*} [Nonempty T] (a : T → Fin n → ℝ) {B : ℝ}
    (ha : ∀ t j, |a t j| ≤ B) (φ : Fin n → ℝ → ℝ) (hφ : ∀ j x y, |φ j x - φ j y| ≤ |x - y|)
    (hφ0 : ∀ j, φ j 0 = 0) :
    radE (fun σ => ⨆ t, |∑ j, rsign (σ j) * φ j (a t j)|) ≤
      2 * radE (fun σ => ⨆ t, |∑ j, rsign (σ j) * a t j|) := by
  -- adjoin the zero function
  set a' : Option T → Fin n → ℝ := fun o j => o.elim 0 fun t => a t j with ha'
  have ha'b : ∀ o j, |a' o j| ≤ max B 0 := by
    intro o j
    cases o with
    | none => simp [ha']
    | some t => exact (ha t j).trans (le_max_left _ _)
  have hφb : ∀ j y, |φ j y| ≤ |y| := fun j y => by simpa [hφ0] using hφ j y 0
  -- uniform bounds
  set C := ∑ j : Fin n, max B 0 with hC
  have hZb : ∀ (σ : Fin n → Bool) t, |∑ j, rsign (σ j) * φ j (a t j)| ≤ C := by
    intro σ t
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_rsign, one_mul]
    exact (hφb j _).trans ((ha t j).trans (le_max_left _ _))
  have hWb : ∀ (σ : Fin n → Bool) t, |∑ j, rsign (σ j) * a t j| ≤ C := by
    intro σ t
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_rsign, one_mul]
    exact (ha t j).trans (le_max_left _ _)
  have hZ'b : ∀ (σ : Fin n → Bool) o, |∑ j, rsign (σ j) * φ j (a' o j)| ≤ C := by
    intro σ o
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_rsign, one_mul]
    exact (hφb j _).trans (ha'b o j)
  have hW'b : ∀ (σ : Fin n → Bool) o, |∑ j, rsign (σ j) * a' o j| ≤ C := by
    intro σ o
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_rsign, one_mul]
    exact ha'b o j
  -- Step 1: `sup |Z| ≤ sup Z' + sup Z'∘(−σ)` pointwise in `σ`
  set Z' : (Fin n → Bool) → ℝ := fun σ => ⨆ o, ∑ j, rsign (σ j) * φ j (a' o j) with hZ'
  have hpos : ∀ σ : Fin n → Bool, ∀ t,
      max (∑ j, rsign (σ j) * φ j (a t j)) 0 ≤ Z' σ := by
    intro σ t
    have hb := bddAbove_of_abs_le (hZ'b σ)
    refine max_le ?_ ?_
    · exact le_ciSup hb (some t)
    · have := le_ciSup hb none
      simpa [ha', hφ0] using this
  have hstep1 : ∀ σ : Fin n → Bool, (⨆ t, |∑ j, rsign (σ j) * φ j (a t j)|) ≤
      Z' σ + Z' (negSigns σ) := by
    intro σ
    refine ciSup_le fun t => ?_
    have h1 := hpos σ t
    have h2 := hpos (negSigns σ) t
    have hneg : ∑ j, rsign (negSigns σ j) * φ j (a t j) = -∑ j, rsign (σ j) * φ j (a t j) := by
      simp [negSigns, rsign_not, neg_mul, sum_neg_distrib]
    rw [hneg] at h2
    have key : ∀ z : ℝ, |z| ≤ max z 0 + max (-z) 0 := fun z => by
      rcases le_total 0 z with h | h
      · rw [abs_of_nonneg h]; linarith [le_max_left z 0, le_max_right (-z) 0]
      · rw [abs_of_nonpos h]; linarith [le_max_right z 0, le_max_left (-z) 0]
    linarith [key (∑ j, rsign (σ j) * φ j (a t j))]
  -- Step 2: average and contraction on `Option T`
  have hcon := radE_iSup_contraction a' ha'b φ hφ
  have hstep3 : ∀ σ : Fin n → Bool, (⨆ o, ∑ j, rsign (σ j) * a' o j) ≤
      ⨆ t, |∑ j, rsign (σ j) * a t j| := by
    intro σ
    have hb := bddAbove_of_abs_le (C := C) fun t => by rw [abs_abs]; exact hWb σ t
    refine ciSup_le fun o => ?_
    cases o with
    | none =>
      obtain ⟨t₀⟩ := ‹Nonempty T›
      simpa [ha'] using (abs_nonneg _).trans (le_ciSup hb t₀)
    | some t => exact (le_abs_self _).trans (le_ciSup hb t)
  calc radE (fun σ => ⨆ t, |∑ j, rsign (σ j) * φ j (a t j)|)
      ≤ radE (fun σ => Z' σ + Z' (negSigns σ)) := radE_mono hstep1
    _ = 2 * radE Z' := by rw [radE_add, radE_negSigns]; ring
    _ ≤ 2 * radE (fun σ => ⨆ o, ∑ j, rsign (σ j) * a' o j) := by
        exact mul_le_mul_of_nonneg_left hcon (by norm_num)
    _ ≤ 2 * radE (fun σ => ⨆ t, |∑ j, rsign (σ j) * a t j|) := by
        exact mul_le_mul_of_nonneg_left (radE_mono hstep3) (by norm_num)

end StatFormal.Concentration
