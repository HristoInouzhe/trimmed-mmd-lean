import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Hoeffding's permutation representation of a U-statistic of order two

Library component F.B (part 4). Untrusted library code: no `Statements.lean` is involved.

For `F : Fin n → Fin n → ℝ`, the off-diagonal sum `Σ_{a ≠ b} F a b` is recovered by averaging,
over all permutations `σ`, the value of `F` at a fixed off-diagonal pair moved by `σ`
(Hoeffding 1963, §5). This is the combinatorial half of the proof that a U-statistic is an average
of sums of independent blocks.

## Main results

* `permSum_comp`, `exists_perm_apply_apply`, `permSum_eq_of_ne`: `Σ_σ F (σ p) (σ q)` does not
  depend on the off-diagonal pair `(p, q)`;
* `natCast_mul_permSum`: `n (n − 1) · Σ_σ F (σ p) (σ q) = |Perm| · Σ_{a ≠ b} F a b` for `p ≠ q`;
* `offDiagSum_half_sq`: `Σ_{a ≠ b} (z a − z b)²/2 = Σ_{a < b} (z a − z b)²`.
-/

noncomputable section
open Finset

namespace StatFormal.Bernstein

variable {n : ℕ}

/-- The off-diagonal sum `Σ_{a ≠ b} F a b`. -/
def offDiagSum (F : Fin n → Fin n → ℝ) : ℝ := ∑ a, ∑ b, if a ≠ b then F a b else 0

/-- The permutation sum `Σ_σ F (σ p) (σ q)`. -/
def permSum (F : Fin n → Fin n → ℝ) (p q : Fin n) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), F (σ p) (σ q)

theorem permSum_comp (F : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (p q : Fin n) :
    permSum F (τ p) (τ q) = permSum F p q := by
  unfold permSum
  exact Fintype.sum_equiv (Equiv.mulRight τ) (fun σ => F (σ (τ p)) (σ (τ q)))
    (fun σ => F (σ p) (σ q)) fun σ => by simp [Equiv.Perm.mul_apply]

theorem exists_perm_apply_apply {p q p' q' : Fin n} (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ τ : Equiv.Perm (Fin n), τ p = p' ∧ τ q = q' := by
  set s := Equiv.swap p p' with hs
  have hsq : s q ≠ p' := by
    intro h
    have : s q = s p := by rw [h, hs, Equiv.swap_apply_left]
    exact hpq (s.injective this).symm
  refine ⟨Equiv.swap (s q) q' * s, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hs, Equiv.swap_apply_left, ← hs]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hsq) hpq'
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem permSum_eq_of_ne (F : Fin n → Fin n → ℝ) {p q a b : Fin n} (hpq : p ≠ q) (hab : a ≠ b) :
    permSum F a b = permSum F p q := by
  obtain ⟨τ, h1, h2⟩ := exists_perm_apply_apply hpq hab
  rw [← h1, ← h2, permSum_comp]

theorem sum_offDiag_permSum (F : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, if a ≠ b then permSum F a b else 0) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * offDiagSum F := by
  have h1 : ∀ a b : Fin n, (if a ≠ b then permSum F a b else 0) =
      ∑ σ : Equiv.Perm (Fin n), if a ≠ b then F (σ a) (σ b) else 0 := by
    intro a b
    split_ifs <;> simp [permSum]
  simp_rw [h1]
  have h2 : (∑ a : Fin n, ∑ b : Fin n, ∑ σ : Equiv.Perm (Fin n),
      if a ≠ b then F (σ a) (σ b) else 0) =
      ∑ σ : Equiv.Perm (Fin n), ∑ a, ∑ b, if a ≠ b then F (σ a) (σ b) else 0 := by
    calc _ = ∑ a : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ b : Fin n,
          (if a ≠ b then F (σ a) (σ b) else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [h2]
  have h3 : ∀ σ : Equiv.Perm (Fin n),
      (∑ a, ∑ b, if a ≠ b then F (σ a) (σ b) else 0) = offDiagSum F := by
    intro σ
    unfold offDiagSum
    have h4 : ∀ a b : Fin n, (if a ≠ b then F (σ a) (σ b) else 0) =
        if σ a ≠ σ b then F (σ a) (σ b) else 0 := fun a b => by
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
    simp_rw [h4]
    rw [Equiv.sum_comp σ (fun a => ∑ b, if a ≠ σ b then F a (σ b) else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Equiv.sum_comp σ (fun b => if a ≠ b then F a b else 0)
  simp_rw [h3]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_offDiag_one : (∑ a : Fin n, ∑ b : Fin n, if a ≠ b then (1 : ℝ) else 0) =
    n * (n - 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have : ∀ a : Fin n, (∑ b : Fin n, if a ≠ b then (1 : ℝ) else 0) = n - 1 := by
    intro a
    rw [Finset.sum_boole]
    have : (Finset.univ.filter fun b : Fin n => a ≠ b) = Finset.univ.erase a := by
      ext b; simp [eq_comm]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub h]
    simp
  simp_rw [this]
  simp
  ring

/-- **Hoeffding's identity**: for `p ≠ q`,
`n (n − 1) Σ_σ F (σ p) (σ q) = |Perm| Σ_{a ≠ b} F a b`. -/
theorem natCast_mul_permSum (F : Fin n → Fin n → ℝ) {p q : Fin n} (hpq : p ≠ q) :
    (n : ℝ) * (n - 1) * permSum F p q =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * offDiagSum F := by
  rw [← sum_offDiag_permSum, ← sum_offDiag_one, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hab
  · rw [one_mul, permSum_eq_of_ne F hpq hab]
  · rw [zero_mul]

/-- `Σ_{a ≠ b} (z a − z b)²/2 = Σ_{a < b} (z a − z b)²`. -/
theorem offDiagSum_half_sq (z : Fin n → ℝ) :
    offDiagSum (fun a b => (z a - z b) ^ 2 / 2) =
      ∑ a, ∑ b, if a < b then (z a - z b) ^ 2 else 0 := by
  unfold offDiagSum
  have h1 : ∀ a b : Fin n, (if a ≠ b then (z a - z b) ^ 2 / 2 else 0) =
      (if a < b then (z a - z b) ^ 2 else 0) / 2 +
        (if b < a then (z b - z a) ^ 2 else 0) / 2 := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
      ring
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => (if b < a then (z b - z a) ^ 2 else 0) / 2)]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  ring

end StatFormal.Bernstein
