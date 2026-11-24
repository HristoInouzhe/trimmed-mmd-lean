import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# FROZEN STATEMENTS — context distributions for ICL: oracle inequality and the rejected designs

Sources (verbatim in `inventory/extracted/context-distribution-icl.md`):
* `cor:oracle` (`paper/v3/sections/06_estimation.tex:96`), in its abstract form ("the same holds for
  any class of joint laws"): a uniform deviation `dev` between the empirical and pool objectives turns
  an `ε_opt`-minimiser of one into an `(ε_opt + 2 dev)`-minimiser of the other.
* `prop:diag-vertex` (`supp/alternatives.tex:18`) and `prop:diag-cap` (`supp/alternatives.tex:39`).

Encodings (see card):
* `KL(w | u_n) = Σ_i w_i log(n w_i)` with `0 log 0 = 0` (Mathlib: `Real.log 0 = 0`).
* `Δ = Δ^{n-1}` is `simplex n = {w : w_i ≥ 0, Σ w_i = 1}`; a vertex is `Pi.single i 1`.
* "`F_n` twice continuously differentiable on `Δ`" is encoded as `ContDiff ℝ 2 F` on `ℝ^n` (a `C²`
  function on the simplex extends), and the Hessian bound `vᵀ∇²F(w)v ≤ L_F‖v‖²` for tangent `v` as the
  second derivative of `t ↦ F(w + t v)` at `0`, which equals `vᵀ∇²F(w)v` for `C²` `F`.
* `‖v‖²` is the Euclidean `Σ v_i²`.
* `λ ≥ 0` in `diag_vertex` (the paper's `λ` weights a reward; for `λ < 0` the claim is false, e.g.
  `n = 2`, `F = −(w₀−w₁)²`, `L_F = −4`, `λ = −1`, found by the fidelity critic).
* `cor:oracle`: infima are `sInf` of the image; `BddBelow` of the pool objective makes them genuine
  infima (both objectives are bounded in the paper since `0 ≤ L ≤ B_L`).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset

namespace StatFormal.ICL.Diag

/-- The probability simplex `Δ^{n-1} = {w : w_i ≥ 0, Σ_i w_i = 1}`. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- `KL(w | u_n) = Σ_i w_i log(n w_i)`. -/
def klUnif (n : ℕ) (w : Fin n → ℝ) : ℝ := ∑ i, w i * Real.log (n * w i)

/-- The bounded-density class `C_c = {w ∈ Δ : w_i ≤ c/n}`. -/
def capSet (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {w | w ∈ simplex n ∧ ∀ i, w i ≤ c / n}

namespace Claims

/-- `cor:oracle` (abstract form): if `|J_m − J_pool| ≤ dev` on the class and `ŵ` is an
`ε_opt`-minimiser of `J_m`, then `J_pool(ŵ) ≤ inf J_pool + ε_opt + 2 dev`. -/
def oracle : Prop :=
  ∀ (ι : Type) (S : Set ι) (Jm Jp : ι → ℝ) (dev εopt : ℝ) (wh : ι),
    wh ∈ S → (∀ w ∈ S, |Jm w - Jp w| ≤ dev) → BddBelow (Jp '' S) →
    Jm wh ≤ sInf (Jm '' S) + εopt →
      Jp wh ≤ sInf (Jp '' S) + εopt + 2 * dev

/-- `prop:diag-vertex`: if `λ > L_F/2`, every minimiser of `F − λ KL(·|u_n)` over `Δ` is a vertex. -/
def diag_vertex : Prop :=
  ∀ (n : ℕ) (F : (Fin n → ℝ) → ℝ) (LF lam : ℝ), ContDiff ℝ 2 F →
    (∀ w ∈ simplex n, ∀ v : Fin n → ℝ, ∑ i, v i = 0 →
      deriv (deriv (fun t : ℝ => F (w + t • v))) 0 ≤ LF * ∑ i, v i ^ 2) →
    0 ≤ lam → LF / 2 < lam →
    ∀ w ∈ simplex n,
      (∀ w' ∈ simplex n, F w - lam * klUnif n w ≤ F w' - lam * klUnif n w') →
        ∃ i, w = Pi.single i 1

/-- `prop:diag-vertex`, linear case: for `F_n(w) = Σ_j c_j w_j` the conclusion holds for every `λ > 0`. -/
def diag_vertex_linear : Prop :=
  ∀ (n : ℕ) (cost : Fin n → ℝ) (lam : ℝ), 0 < lam →
    ∀ w ∈ simplex n,
      (∀ w' ∈ simplex n,
        ∑ i, cost i * w i - lam * klUnif n w ≤ ∑ i, cost i * w' i - lam * klUnif n w') →
        ∃ i, w = Pi.single i 1

/-- `prop:diag-cap`: with `k = n/c ∈ ℕ` and linear `F_n`, for every `λ ≥ 0` the uniform law on any
`k` examples with the smallest costs lies in `C_c` and minimises `F_n − λ KL(·|u_n)` over `C_c`. -/
def diag_cap : Prop :=
  ∀ (n k : ℕ) (c lam : ℝ) (cost : Fin n → ℝ) (S : Finset (Fin n)),
    0 < n → 0 < c → (k : ℝ) = n / c → 0 ≤ lam → S.card = k →
    (∀ i ∈ S, ∀ j ∉ S, cost i ≤ cost j) →
      (fun i => if i ∈ S then (1 / k : ℝ) else 0) ∈ capSet n c ∧
      ∀ w ∈ capSet n c,
        ∑ i, cost i * (if i ∈ S then (1 / k : ℝ) else 0) -
            lam * klUnif n (fun i => if i ∈ S then (1 / k : ℝ) else 0) ≤
          ∑ i, cost i * w i - lam * klUnif n w

end Claims
end StatFormal.ICL.Diag
