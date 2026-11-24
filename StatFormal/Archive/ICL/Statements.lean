import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Basic.Real.Basic

/-!
# FROZEN STATEMENTS — context distributions for ICL: the conditional Poisson (CPS) law

Sources: `context-distribution-ICL/paper/v3/sections/03_framework.tex:55-66` (definition of `Π_w`,
`e_M`, inclusion probabilities) and `sections/06_estimation.tex:6-31` (`prop:cps-gradient`).
Weights `w` live in `Δ^(M) = {w ∈ Δ^{n−1} : |supp w| ≥ M}`; a context is an `M`-subset `S` of the pool;
for a fixed validation query, `L S` is the loss of context `S` (`L(z̃_i; z_S)`).
`w_{−ℓ}` is `w` restricted to `[n] \ {ℓ}`; we keep `w` on `Fin n` and sum over `univ.erase ℓ`.
Not covered (declared): the logit derivative `∂G/∂η_ℓ = π_ℓ(V_ℓ − G)` and its continuous extension to
faces; the Frank–Wolfe gap at fixed prompts. "G is a rational function" is definitional here.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset

namespace StatFormal.ICL

variable {n : ℕ}

/-- Elementary symmetric polynomial of the weights on the index set `s`: `e_k(w|_s)`. -/
def esym (w : Fin n → ℝ) (s : Finset (Fin n)) (k : ℕ) : ℝ :=
  ∑ S ∈ s.powersetCard k, ∏ j ∈ S, w j

/-- `Δ^(M)`: probability weights with at least `M` positive coordinates. -/
def InDeltaM (w : Fin n → ℝ) (M : ℕ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ M ≤ (univ.filter fun j => w j ≠ 0).card

/-- CPS law on `M`-subsets of `s`: `Π(S) = ∏_{j∈S} w_j / e_M(w|_s)`. -/
def cps (w : Fin n → ℝ) (s : Finset (Fin n)) (M : ℕ) (S : Finset (Fin n)) : ℝ :=
  (∏ j ∈ S, w j) / esym w s M

/-- Inclusion probability `π_ℓ = Π_w(ℓ ∈ S)`. -/
def incl (w : Fin n → ℝ) (M : ℕ) (ℓ : Fin n) : ℝ :=
  ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∈ S), cps w univ M S

/-- Per-query risk `G(w) = Σ_S Π_w(S) L(S)`. -/
def Grisk (w : Fin n → ℝ) (M : ℕ) (L : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S ∈ univ.powersetCard M, cps w univ M S * L S

/-- `V_ℓ = E L(z_ℓ, z_T)`, `T ∼ Π_{w_{−ℓ}}` of size `M − 1` on `[n] \ {ℓ}`. -/
def Vrisk (w : Fin n → ℝ) (M : ℕ) (L : Finset (Fin n) → ℝ) (ℓ : Fin n) : ℝ :=
  ∑ T ∈ (univ.erase ℓ).powersetCard (M - 1), cps w (univ.erase ℓ) (M - 1) T * L (insert ℓ T)

namespace Claims

/-- Well-posedness of `Π_w` on `Δ^(M)` (`03_framework.tex:60-64`): `e_M(w) > 0`, so `Π_w` is a
probability law on `M`-subsets. -/
def cps_wellPosed : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ), InDeltaM w M →
    0 < esym w univ M ∧ (∀ S ∈ univ.powersetCard M, 0 ≤ cps w univ M S) ∧
      ∑ S ∈ univ.powersetCard M, cps w univ M S = 1

/-- `prop:cps-gradient` (i): `π_ℓ = w_ℓ e_{M−1}(w_{−ℓ}) / e_M(w)` and `Σ_ℓ π_ℓ = M`. -/
def cps_incl : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ), 1 ≤ M → InDeltaM w M →
    (∀ ℓ, incl w M ℓ = w ℓ * esym w (univ.erase ℓ) (M - 1) / esym w univ M) ∧
      ∑ ℓ, incl w M ℓ = M

/-- `prop:cps-gradient` (ii): given `ℓ ∈ S` (with `π_ℓ > 0`), `S \ {ℓ}` has law `Π_{w_{−ℓ}}`;
and `Σ_ℓ π_ℓ V_ℓ = M G`. -/
def cps_conditional : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ) (L : Finset (Fin n) → ℝ), 1 ≤ M → InDeltaM w M →
    (∀ ℓ, 0 < incl w M ℓ → ∀ T ∈ (univ.erase ℓ).powersetCard (M - 1),
        cps w univ M (insert ℓ T) / incl w M ℓ = cps w (univ.erase ℓ) (M - 1) T) ∧
      ∑ ℓ, incl w M ℓ * Vrisk w M L ℓ = M * Grisk w M L

/-- `prop:cps-gradient` (ii), "hence": `V_ℓ = E[L(S) | ℓ ∈ S]` when `π_ℓ > 0`. -/
def cps_condExp : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ) (L : Finset (Fin n) → ℝ), 1 ≤ M → InDeltaM w M →
    ∀ ℓ, 0 < incl w M ℓ → Vrisk w M L ℓ =
      (∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∈ S), cps w univ M S * L S) / incl w M ℓ

/-- `prop:cps-gradient` (iii), partial derivative and Euler identity: at `w ∈ Δ^(M)`,
`∂G/∂w_ℓ = e_{M−1}(w_{−ℓ})/e_M(w) · (V_ℓ − G)` (as a rational function of `w ∈ ℝⁿ`), and
`Σ_ℓ w_ℓ ∂G/∂w_ℓ = 0`. -/
def cps_gradient : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ) (L : Finset (Fin n) → ℝ), 1 ≤ M → InDeltaM w M →
    (∀ ℓ, HasDerivAt (fun t => Grisk (Function.update w ℓ t) M L)
        (esym w (univ.erase ℓ) (M - 1) / esym w univ M * (Vrisk w M L ℓ - Grisk w M L)) (w ℓ)) ∧
      ∑ ℓ, w ℓ * (esym w (univ.erase ℓ) (M - 1) / esym w univ M * (Vrisk w M L ℓ - Grisk w M L))
        = 0

end Claims
end StatFormal.ICL
