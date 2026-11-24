import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Basic

/-!
# FROZEN STATEMENTS — trimmed MMD: extreme trimmed means and the bang-bang trimming

Sources: `trimmed-mmd/paper.tex:1100-1120` (`lem:trimmedmean`) and `:1380-1420` (`eq:trimset-emp`,
`prop:bangbang` (i)–(ii)). Verbatim in `inventory/extracted/trimmed-mmd.md`.

Encoding. Order statistics: `ord v j` is the `(j+1)`-th smallest value of `v : Fin n → ℝ`
(0-indexed, via Mathlib's `Tuple.sort`), so the paper's `v_{(i)}` is `ord v (i−1)`.
Capped simplex `Δ_α(n) = {w : 0 ≤ w_i ≤ c, Σ w_i = 1}`, `c = [n(1−α)]⁻¹`.
`prop:bangbang` is stated in an abstract real inner-product space `E` for feature vectors
`x_i = φ(X_i)`, `y_j = φ(Y_j)` (the RKHS is one such space).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset

namespace StatFormal.TrimmedMMD.BangBang

/-- `(j+1)`-th smallest value of `v` (junk `0` for `j ≥ n`). -/
def ord {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then v (Tuple.sort v ⟨j, h⟩) else 0

/-- The cap `c = [n(1−α)]⁻¹`. -/
def cap (n : ℕ) (α : ℝ) : ℝ := 1 / (n * (1 - α))

/-- `k = ⌊1/c⌋ = ⌊n(1−α)⌋`. -/
def kfloor (n : ℕ) (α : ℝ) : ℕ := ⌊(n : ℝ) * (1 - α)⌋₊

/-- The capped simplex `Δ_α(n)`. -/
def capped (n : ℕ) (α : ℝ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i ∧ w i ≤ cap n α) ∧ ∑ i, w i = 1}

/-- Objective of `eq:qp`: `‖Σ w_i x_i − Σ v_j y_j‖²`. -/
def qp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n m : ℕ}
    (x : Fin n → E) (y : Fin m → E) (p : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  ‖∑ i, p.1 i • x i - ∑ j, p.2 j • y j‖ ^ 2

namespace Claims

/-- `lem:trimmedmean`, value: `max_{w ∈ Δ_α(n)} Σ w_i v_i = Σ_{i>n−k} c v_{(i)} + (1−kc) v_{(n−k)}`,
the last term read as `0` when `k = n`. -/
def trimmedmean_value : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ) (α : ℝ), 0 < n → 0 ≤ α → α < 1 →
    IsGreatest ((fun w => ∑ i, w i * v i) '' capped n α)
      (cap n α * ∑ j ∈ Ico (n - kfloor n α) n, ord v j +
        (if kfloor n α < n then (1 - kfloor n α * cap n α) * ord v (n - kfloor n α - 1) else 0))

/-- `lem:trimmedmean`, maximisers: every maximiser has `w_i = c` when `v_i > v_{(n−k)}`, `w_i = 0`
when `v_i < v_{(n−k)}`, and the tied indices share the remaining mass `1 − c·#{i : v_i > v_{(n−k)}}`
(here `k < n`). -/
def trimmedmean_argmax : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ) (α : ℝ) (w : Fin n → ℝ), 0 < n → 0 ≤ α → α < 1 → kfloor n α < n →
    IsMaxOn (fun w => ∑ i, w i * v i) (capped n α) w → w ∈ capped n α →
      let θ := ord v (n - kfloor n α - 1)
      (∀ i, θ < v i → w i = cap n α) ∧ (∀ i, v i < θ → w i = 0) ∧
        ∑ i ∈ univ.filter (fun i => v i = θ), w i =
          1 - cap n α * (univ.filter (fun i => θ < v i)).card

/-- `prop:bangbang` (i): the set of minimisers is nonempty, and the witness
`d̂ = Σ w_i x_i − Σ v_j y_j` is the same at every minimiser, with `‖d̂‖² = D̂²` the minimum value. -/
def bangbang_i : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ), 0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
      (∃ p ∈ capped n α ×ˢ capped m β, IsMinOn (qp x y) (capped n α ×ˢ capped m β) p) ∧
      ∀ p ∈ capped n α ×ˢ capped m β, ∀ p' ∈ capped n α ×ˢ capped m β,
        IsMinOn (qp x y) (capped n α ×ˢ capped m β) p →
        IsMinOn (qp x y) (capped n α ×ˢ capped m β) p' →
          ∑ i, p.1 i • x i - ∑ j, p.2 j • y j = ∑ i, p'.1 i • x i - ∑ j, p'.2 j • y j

/-- `prop:bangbang` (ii): if `D̂ > 0`, every minimiser `(w,v)` keeps the `X`'s with the smallest witness
values at the cap and drops those above the `(k_n+1)`-th smallest, the ties sharing the residual
mass; symmetrically for `v` with the largest values. (`k_n = ⌊n(1−α)⌋ < n`, `k_m = ⌊m(1−β)⌋ < m`.) -/
def bangbang_ii : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)),
    0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 → kfloor n α < n → kfloor m β < m →
    p ∈ capped n α ×ˢ capped m β → IsMinOn (qp x y) (capped n α ×ˢ capped m β) p → 0 < qp x y p →
      let d := ∑ i, p.1 i • x i - ∑ j, p.2 j • y j
      let dx : Fin n → ℝ := fun i => inner ℝ d (x i)
      let dy : Fin m → ℝ := fun j => inner ℝ d (y j)
      let θx := ord dx (kfloor n α)
      let θy := ord dy (m - kfloor m β - 1)
      (∀ i, dx i < θx → p.1 i = cap n α) ∧ (∀ i, θx < dx i → p.1 i = 0) ∧
      ∑ i ∈ univ.filter (fun i => dx i = θx), p.1 i =
        1 - cap n α * (univ.filter (fun i => dx i < θx)).card ∧
      (∀ j, θy < dy j → p.2 j = cap m β) ∧ (∀ j, dy j < θy → p.2 j = 0) ∧
      ∑ j ∈ univ.filter (fun j => dy j = θy), p.2 j =
        1 - cap m β * (univ.filter (fun j => θy < dy j)).card

end Claims
end StatFormal.TrimmedMMD.BangBang
