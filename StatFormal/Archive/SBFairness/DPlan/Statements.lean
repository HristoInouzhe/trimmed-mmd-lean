import StatFormal.Archive.SBFairness.Statements
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# FROZEN STATEMENTS — SB fairness repair: Gaussian entropic plans in `ℝᵈ` (`lem:dplan`) and the
# parity-defect algebra (`thm:paritydefect`)

Source: `schrodinger_bridge_fairness_repair.tex:665-690` (`lem:dplan`, `eq:dC`, `eq:dquad`, `eq:dCexp`),
`:712-730` (`thm:paritydefect`), proofs `:2903-2960`. Verbatim in `inventory/extracted/data-fairness-repair.md`.

Encoding. Matrix square roots enter as hypotheses: `S` positive definite with `S² = A` (this is `A^{1/2}`,
unique among PD roots), `N ε` positive definite with `(N ε)² = 4SBS + ε²I`. Then
`C_ε = ½(S N_ε S⁻¹ − εI)` is `eq:dC`. "`2C+εI` is the principal square root of `4AB+ε²I`" is encoded as
"`2C+εI = S N S⁻¹` with `N` positive definite" (a square root similar to a PD matrix, hence with positive
spectrum). The optimality of the Gaussian plan with this cross-covariance (`π^⋆_ε` is Gaussian with
cross-covariance `C`) is NOT formalised. `O(ε²)` is stated entrywise.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Matrix

namespace StatFormal.SBFairness.DPlan

variable {d : ℕ}

local notation "Mat" d => Matrix (Fin d) (Fin d) ℝ

/-- `eq:dC`: `C = ½(S N S⁻¹ − εI)`. -/
def Cmat (S N : Mat d) (ε : ℝ) : Mat d := (1 / 2 : ℝ) • (S * N * S⁻¹ - ε • (1 : Mat d))

namespace Claims

/-- `eq:dquad`: `C² + εC = AB`, and `(2C + εI)² = 4AB + ε²I` with `2C + εI = S N S⁻¹`, `N ≻ 0`. -/
def dplan_quad : Prop :=
  ∀ (d : ℕ) (A B S N : Mat d) (ε : ℝ), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Mat d) →
      Cmat S N ε * Cmat S N ε + ε • Cmat S N ε = A * B ∧
      (2 • Cmat S N ε + ε • (1 : Mat d)) * (2 • Cmat S N ε + ε • (1 : Mat d)) =
        4 • (A * B) + ε ^ 2 • (1 : Mat d) ∧
      2 • Cmat S N ε + ε • (1 : Mat d) = S * N * S⁻¹

/-- `lem:dplan`: `BC` is symmetric. -/
def dplan_BC_symm : Prop :=
  ∀ (d : ℕ) (A B S N : Mat d) (ε : ℝ), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Mat d) →
      (B * Cmat S N ε).transpose = B * Cmat S N ε

/-- `lem:dplan`: uniqueness — any solution `C'` of `C'² + εC' = AB` whose `2C' + εI` is a principal root
(`= S N' S⁻¹` with `N' ≻ 0`) equals `C_ε`. -/
def dplan_unique : Prop :=
  ∀ (d : ℕ) (A B S N N' C' : Mat d) (ε : ℝ), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Mat d) →
    N'.PosDef → C' * C' + ε • C' = A * B → 2 • C' + ε • (1 : Mat d) = S * N' * S⁻¹ →
      C' = Cmat S N ε

/-- `eq:dCexp`: `C_ε = C₀ − (ε/2) I + O(ε²)`, with `C₀ = S R S⁻¹`, `R ≻ 0`, `R² = SBS`
(`C₀ = A^{1/2}(A^{1/2}BA^{1/2})^{1/2}A^{-1/2}`). -/
def dplan_expansion : Prop :=
  ∀ (d : ℕ) (A B S R : Mat d) (N : ℝ → Mat d), A.PosDef → B.PosDef →
    S.PosDef → S * S = A → R.PosDef → R * R = S * B * S →
    (∀ ε, 0 < ε → (N ε).PosDef ∧ N ε * N ε = 4 • (S * B * S) + ε ^ 2 • (1 : Mat d)) →
      ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ i j,
        |(Cmat S (N ε) ε - (S * R * S⁻¹ - (ε / 2) • (1 : Mat d))) i j| ≤ K * ε ^ 2

/-- `lem:dplan`, commuting case (diagonal form): for diagonal `A = diag a`, `B = diag b`, the solution is
diagonal with entries `c_ε` of `lem:gaussplan` (scalar `c² + εc = a_i b_i`, `σ₀² = a_i`, `σ₁² = b_i`). -/
def dplan_diagonal : Prop :=
  ∀ (d : ℕ) (a b : Fin d → ℝ) (ε : ℝ), (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < ε →
    Cmat (diagonal fun i => Real.sqrt (a i)) (diagonal fun i => Real.sqrt (4 * a i * b i + ε ^ 2)) ε =
      diagonal fun i => cEps ε (Real.sqrt (a i)) (Real.sqrt (b i))

/-- `thm:paritydefect`, "non-zero at first order unless `A₀ = A₁`": with Brenier matrices
`T_s = S_s⁻¹ R_s S_s⁻¹` (`R_s ≻ 0`, `R_s² = S_s B S_s`, `S_s² = A_s`), `T₀ = T₁` forces `A₀ = A₁`. -/
def paritydefect_nonzero : Prop :=
  ∀ (d : ℕ) (A₀ A₁ B S₀ S₁ R₀ R₁ : Mat d), A₀.PosDef → A₁.PosDef → B.PosDef →
    S₀.PosDef → S₀ * S₀ = A₀ → S₁.PosDef → S₁ * S₁ = A₁ →
    R₀.PosDef → R₀ * R₀ = S₀ * B * S₀ → R₁.PosDef → R₁ * R₁ = S₁ * B * S₁ →
      S₀⁻¹ * R₀ * S₀⁻¹ = S₁⁻¹ * R₁ * S₁⁻¹ → A₀ = A₁

/-- `thm:paritydefect`, `eq:Ps`: the push-forward covariance of the barycentric map,
`P = Cᵀ A⁻¹ C = B − ε T^Br + O(ε²)` with `T^Br = S⁻¹ R S⁻¹` (entrywise `O(ε²)`). Together with
`paritydefect_nonzero` this gives the parity gap `P₀ − P₁ = −ε(T₀ − T₁) + O(ε²)`, non-zero at first order
unless `A₀ = A₁`. -/
def paritydefect_expansion : Prop :=
  ∀ (d : ℕ) (A B S R : Mat d) (N : ℝ → Mat d), A.PosDef → B.PosDef →
    S.PosDef → S * S = A → R.PosDef → R * R = S * B * S →
    (∀ ε, 0 < ε → (N ε).PosDef ∧ N ε * N ε = 4 • (S * B * S) + ε ^ 2 • (1 : Mat d)) →
      ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ i j,
        |((Cmat S (N ε) ε).transpose * A⁻¹ * Cmat S (N ε) ε - (B - ε • (S⁻¹ * R * S⁻¹))) i j|
          ≤ K * ε ^ 2

/-- Proof of `lem:dplan` (l.2930): `C B⁻¹ ≻ 0`, which gives `Σ = [[A, C], [Cᵀ, B]] ≻ 0`. -/
def dplan_CBinv_posDef : Prop :=
  ∀ (d : ℕ) (A B S N : Mat d) (ε : ℝ), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Mat d) →
      (Cmat S N ε * B⁻¹).PosDef

end Claims
end StatFormal.SBFairness.DPlan
