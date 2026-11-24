import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Perm

/-!
# FROZEN STATEMENTS — otfd hard transfers (unique assignment ⇔ strict-margin potentials)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-B_bands.md`, `otfd-G_geodesic.md`):
* B `def:hard-transfer` / `prop:hard-transfer` and the paragraph after it
  (`papers/B_bands/supplement.tex:6643-6676`): "Dual potentials with a strict margin exist because
  the optimal assignment is unique ... with a tie some fitted head lies on a cell boundary."
* G `prop:hardtransfer` and the construction before it (`papers/G_geodesic/supp_moved.tex:562-575`):
  "An optimal assignment is `c_s`-cyclically monotone, so it has dual potentials `ψ_j` with a strict
  margin" — flagged by the 2026-10-09 review (M4) as needing uniqueness.

Generic cost `c k j` (data point `k`, grid point `j`): covers B (`‖z_k - u_j‖²`) and G (`c_s(v_j, x_k)`).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

namespace StatFormal.OTFD

open Finset

variable {N : ℕ}

/-- Total cost of the assignment `k ↦ σ k`. -/
def assignCost (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) : ℝ := ∑ k, c k (σ k)

/-- `σ` is an optimal assignment. -/
def IsOptimal (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) : Prop :=
  ∀ τ : Equiv.Perm (Fin N), assignCost c σ ≤ assignCost c τ

/-- `σ` is the unique optimal assignment. -/
def IsUniqueOptimal (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) : Prop :=
  IsOptimal c σ ∧ ∀ τ, IsOptimal c τ → τ = σ

/-- Dual potentials `ψ` with margin `δ`: in the score `c k j - ψ j`, data point `k` prefers its own
grid point `σ k` to every other grid point by at least `δ` (B: "every fitted head lies strictly inside
its own cell" when `δ > 0`). -/
def HasMarginPotentials (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (δ : ℝ) : Prop :=
  ∃ ψ : Fin N → ℝ, ∀ k j, j ≠ σ k → c k (σ k) - ψ (σ k) + δ ≤ c k j - ψ j

namespace Claims

/-- Finite Rockafellar / complementary slackness: every optimal assignment admits potentials with
margin `0` (the non-strict statement that cyclical monotonicity does give). -/
def potentials_of_optimal : Prop :=
  ∀ (N : ℕ) (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)),
    IsOptimal c σ → HasMarginPotentials c σ 0

/-- B's justification, and G's construction repaired (M4): a *unique* optimal assignment admits
potentials with a strict margin. -/
def strict_margin_of_unique : Prop :=
  ∀ (N : ℕ) (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)),
    IsUniqueOptimal c σ → ∃ δ > 0, HasMarginPotentials c σ δ

/-- Converse: potentials with a strict margin force `σ` to be the unique optimal assignment.
(So uniqueness is exactly what the strict margin needs.) -/
def unique_of_strict_margin : Prop :=
  ∀ (N : ℕ) (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (δ : ℝ),
    0 < δ → HasMarginPotentials c σ δ → IsUniqueOptimal c σ

/-- G's sentence as written ("optimal ⇒ strict margin") is false. -/
def optimal_not_imp_strict_margin : Prop :=
  ¬ ∀ (N : ℕ) (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)),
    IsOptimal c σ → ∃ δ > 0, HasMarginPotentials c σ δ

/-- `prop:hard-transfer` (i), cell part: with strict-margin potentials, the cell of fitted point `k`
(the set of minimisers of `j ↦ c k j - ψ j`) is exactly `{σ k}`, so the hard transfer sends every
fitted point to its assignment partner. -/
def cell_eq_partner : Prop :=
  ∀ (N : ℕ) (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (δ : ℝ) (ψ : Fin N → ℝ),
    0 < δ → (∀ k j, j ≠ σ k → c k (σ k) - ψ (σ k) + δ ≤ c k j - ψ j) →
      ∀ k j, (∀ j', c k j - ψ j ≤ c k j' - ψ j') ↔ j = σ k

/-- Sharper refutation of G's sentence, realisable for any data-to-grid cost `c k j = cost(x_k, v_j)`
(in particular G's `c_s`): if two data points coincide (`c k = c k'`, i.e. a tie), no assignment —
optimal or not — has strict-margin potentials. -/
def no_strict_margin_of_duplicate : Prop :=
  ∀ (N : ℕ) (c : Fin N → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (k k' : Fin N),
    k ≠ k' → c k = c k' → ∀ δ > 0, ¬ HasMarginPotentials c σ δ

end Claims
end StatFormal.OTFD
