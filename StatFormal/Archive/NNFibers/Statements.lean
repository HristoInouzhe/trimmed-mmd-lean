import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# FROZEN STATEMENTS — embedded solution fibers: exact counts and the symmetry remark

Source: `proliferation-and-geometry-in-nns/paper_revised.tex` — `def:structures`, `def:pieces`
(l.455-500), `prop:disjoint` (l.531: pieces ↔ labelled partitions), `prop:count` (l.697),
`eq:moment` (l.710), `eq:blocksize-law` (l.935), `rmk:symmetry-factor` (l.410).

Combinatorial layer: by `prop:disjoint`, the pieces of `Λ^m_r` correspond to partitions of `[m]`
with `r` distinguished blocks labelled injectively by the original units; `T(r,m)` is defined here as
that count (the geometric bijection itself is not formalised). Convention `T(0,ℓ) = B_ℓ` holds by
definition. Stirling numbers are Mathlib's `Nat.stirlingSecond` (defined by recursion), so `prop:count`
includes the (new) fact that it counts set partitions.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset

namespace StatFormal.NNFibers

/-- `T(r,m)`: partitions of `Fin m` together with an injective labelling of `r` of their blocks. -/
def T (r m : ℕ) : ℕ :=
  ∑ P : Finpartition (univ : Finset (Fin m)), (P.parts.card).descFactorial r

/-- Bell number `B_m` = number of set partitions of `Fin m`. -/
def bell (m : ℕ) : ℕ := Fintype.card (Finpartition (univ : Finset (Fin m)))

/-- Number of labelled partitions of `Fin m` with `q + 1` labelled blocks whose block labelled `0`
has exactly `n` elements (the event `N₁ = n` of `eq:blocksize-law`, with `q + 1` original units). -/
def Tblock (q m n : ℕ) : ℕ :=
  ∑ P : Finpartition (univ : Finset (Fin m)),
    ((univ : Finset (Fin (q + 1) ↪ P.parts)).filter
      (fun e => ((e 0 : Finset (Fin m)).card = n))).card

namespace Claims

/-- Mathlib's `stirlingSecond m q` counts partitions of an `m`-set into `q` blocks. -/
def stirlingSecond_card : Prop :=
  ∀ m q : ℕ, ((univ : Finset (Finpartition (univ : Finset (Fin m)))).filter
    (fun P => P.parts.card = q)).card = Nat.stirlingSecond m q

/-- `prop:count`: `T(r,m) = Σ_{q=r}^{m} (q)_r S(m,q)` for `1 ≤ r ≤ m` (the sum may start at `0`:
`(q)_r = 0` for `q < r`). -/
def prop_count : Prop :=
  ∀ r m : ℕ, 1 ≤ r → r ≤ m →
    T r m = ∑ q ∈ range (m + 1), q.descFactorial r * Nat.stirlingSecond m q

/-- `eq:moment` in counting form: `T(r,m) = B_m · E[(K_m)_r]`, i.e.
`T(r,m) = Σ_q (q)_r · #{partitions with q blocks}` with `Σ_q #{…} = B_m`. -/
def eq_moment : Prop :=
  ∀ r m : ℕ, T r m = ∑ q ∈ range (m + 1), q.descFactorial r *
      ((univ : Finset (Finpartition (univ : Finset (Fin m)))).filter (fun P => P.parts.card = q)).card ∧
    ∑ q ∈ range (m + 1),
      ((univ : Finset (Finpartition (univ : Finset (Fin m)))).filter (fun P => P.parts.card = q)).card
      = bell m

/-- `eq:blocksize-law` in counting form, with `q + 1` original units:
`#{N₁ = n} = C(m,n) · T(q, m−n)` for `1 ≤ n ≤ m − q` (paper: `q` units, `1 ≤ n ≤ m − q + 1`). -/
def blocksize_law : Prop :=
  ∀ q m n : ℕ, 1 ≤ n → n + q ≤ m →
    Tblock q m n = m.choose n * T q (m - n)

/-- `rmk:symmetry-factor` is false for `tanh`. Case `d_in = d_out = 1`, `q = 1`, `m = 2`,
`θ* = (ω=1, a=1)`. A width-2 parameter is two units `(ω₁,a₁),(ω₂,a₂)`, realising
`x ↦ a₁ tanh(ω₁ x) + a₂ tanh(ω₂ x)`. `Λ²₁` (`def:pieces`, all structures and unit orders) is
{both `ω = 1`, `a₁ + a₂ = 1`} ∪ {one unit `(1,1)`, the other `(ω', 0)` with `ω' ≠ 1`}; its copy under
the symmetry `(ω,a) ↦ (−ω,−a)` applied to the distinguished group is
{both `ω = −1`, `a₁ + a₂ = −1`} ∪ {one unit `(−1,−1)`, the other `(ω', 0)`, `ω' ≠ 1`} (the zero-type
unit is not flipped).
The remark asserts that the functional fiber is the union of these `g^q = 2` copies. Refutation:
`((1,2),(−1,1))` is in the fiber and in neither copy. -/
def Lam (θ : (ℝ × ℝ) × (ℝ × ℝ)) : Prop :=
  (θ.1.1 = 1 ∧ θ.2.1 = 1 ∧ θ.1.2 + θ.2.2 = 1) ∨
  (θ.1 = (1, 1) ∧ θ.2.2 = 0 ∧ θ.2.1 ≠ 1) ∨ (θ.2 = (1, 1) ∧ θ.1.2 = 0 ∧ θ.1.1 ≠ 1)

def LamFlip (θ : (ℝ × ℝ) × (ℝ × ℝ)) : Prop :=
  (θ.1.1 = -1 ∧ θ.2.1 = -1 ∧ θ.1.2 + θ.2.2 = -1) ∨
  (θ.1 = (-1, -1) ∧ θ.2.2 = 0 ∧ θ.2.1 ≠ 1) ∨ (θ.2 = (-1, -1) ∧ θ.1.2 = 0 ∧ θ.1.1 ≠ 1)

def symmetry_factor_false : Prop :=
  ∃ θ : (ℝ × ℝ) × (ℝ × ℝ),
    (∀ x : ℝ, θ.1.2 * Real.tanh (θ.1.1 * x) + θ.2.2 * Real.tanh (θ.2.1 * x) = 1 * Real.tanh (1 * x)) ∧
      ¬ Lam θ ∧ ¬ LamFlip θ

end Claims
end StatFormal.NNFibers
