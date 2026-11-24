import StatFormal.Archive.OTFD.Statements
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# FROZEN STATEMENTS — otfd A: fixed-`K` distribution-freeness of hard OT ranks (`thm:fixedK-df`)

Sources: `otfd/papers/A_sieves/main.tex:496-512` (`thm:fixedK-df`), supplement `:579-632`
(`lem:app-invariant-perm` and the proof). Verbatim in `inventory/extracted/otfd-A_sieves.md`.

Setting: projected sample `Z = (Z₁,…,Z_n)` with values in a real inner-product space `E` (`ℝ^K` with the
`M_K` inner product), deterministic grid `u : Fin n → E`, assignment cost
`C(z,σ) = Σ_i ‖z_i − u_{σ(i)}‖²`. `σ̂` is any fixed selection of a minimiser that is Borel (the paper: "a
fixed Borel rule, e.g. the lexicographically first minimiser"), encoded as: every fibre `{z | σ̂ z = h}` is
measurable. Exchangeability: the law of `Z ∘ τ` equals the law of `Z` for every permutation `τ`.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.OTFD.Ranks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Assignment cost `C(z,σ) = Σ_i ‖z_i − u_{σ(i)}‖²`. -/
def cost {n : ℕ} (u : Fin n → E) (z : Fin n → E) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, ‖z i - u (σ i)‖ ^ 2

/-- `σ` is a minimiser of `C(z,·)`. -/
def IsMin {n : ℕ} (u : Fin n → E) (z : Fin n → E) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ, cost u z σ ≤ cost u z τ

/-- `C(z,·)` has a unique minimiser. -/
def UniqueMin {n : ℕ} (u : Fin n → E) (z : Fin n → E) : Prop := ∃! σ, IsMin u z σ

namespace Claims

/-- `lem:app-invariant-perm`: a random permutation whose law is invariant under right multiplication is
uniform: `P(σ = h) = 1/n!` for every `h`. -/
def invariant_perm_uniform : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (σ : Ω → Equiv.Perm (Fin n)),
    (∀ h, MeasurableSet {ω | σ ω = h}) →
    (∀ π h, P {ω | σ ω * π = h} = P {ω | σ ω = h}) →
      ∀ h, P {ω | σ ω = h} = (Nat.factorial n : ENNReal)⁻¹

/-- `thm:fixedK-df`: exchangeable sample + a.s. unique optimal assignment + Borel tie rule ⇒ the hard rank
permutation `σ̂(Z)` is uniform on `S_n`; hence the rank vector `(u_{σ̂(1)},…,u_{σ̂(n)})` has the law of
`(u_{π(1)},…,u_{π(n)})`, `π` uniform, whatever the law of `Z`. -/
def fixedK_df : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (u : Fin n → E) (Z : Ω → Fin n → E) (sel : (Fin n → E) → Equiv.Perm (Fin n)),
    Measurable Z → (∀ z, IsMin u z (sel z)) → (∀ h, MeasurableSet {z | sel z = h}) →
    (∀ τ : Equiv.Perm (Fin n), P.map (fun ω => Z ω ∘ τ) = P.map Z) →
    (∀ᵐ ω ∂P, UniqueMin u (Z ω)) →
      ∀ h, P {ω | sel (Z ω) = h} = (Nat.factorial n : ENNReal)⁻¹

/-- "Almost-sure uniqueness forces the grid points to be distinct" and "a sample with a repeated point is
not uniquely assigned": a unique minimiser exists only if `u` is injective and `z` is injective. -/
def unique_forces_distinct : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) (u z : Fin n → E),
    UniqueMin u z → Function.Injective u ∧ Function.Injective z

/-- "Non-atomicity alone does not imply almost-sure uniqueness": for `n = 2` grid points in `ℝ²` there
is a non-atomic law `ν` (on the perpendicular bisector) such that, for an i.i.d. pair from `ν`, the optimal
assignment is not unique with probability one. -/
def nonatomic_not_sufficient : Prop :=
  ∃ (u : Fin 2 → EuclideanSpace ℝ (Fin 2)) (ν : Measure (EuclideanSpace ℝ (Fin 2))),
    Function.Injective u ∧ IsProbabilityMeasure ν ∧ NoAtoms ν ∧
      ∀ᵐ z ∂(Measure.pi fun _ : Fin 2 => ν), ¬ UniqueMin u z

end Claims
end StatFormal.OTFD.Ranks
