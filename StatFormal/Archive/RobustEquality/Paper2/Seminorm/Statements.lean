import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.Bounds.Basic

/-!
# FROZEN STATEMENTS — robust equality, companion paper (`paper2/`): seminorm structure and the free end

**Draft** for critic review; on approval the human renames it `Statements.lean` and freezes it.

Sources (verbatim in `inventory/extracted/robust-equality-paper2.md`): `thm:seminorm`
(`paper2/main.tex:330`) and `thm:npmle` (`paper2/main.tex:498`), with the definitions of
`main.tex:212-282`: the sets `𝓑^𝒩(P̂; r)` (`eq:BN`, l.222), the groupwise term `T^𝒩_s(h, λ)` (`eq:T`,
l.247, and its `ε = 0` reading l.252), the certificate `F̄ = (Δ + √T₀ + √T₁)²` (`thm:certificate`, l.254),
the nominal disparity `Δ` (l.218) and its coupling form (`lem:delta-inf`, l.296); linear rules
`h_w = ⟪w, ·⟫` (l.327).

Covered:
* `seminorm_T` — (i) for a single finitely supported reference and `ε > 0`: `T_s` is jointly convex on
  `E × (0,∞)`, even in `w`, and `T_s(t w, t² λ) = t² T_s(w, λ)` for `t > 0`;
* `seminorm_N` — (ii) same setting, `r_s` above the floor: `T_s ≥ 0`, `N_s² = inf_{λ>0} T_s` is a genuine
  infimum (`IsGLB`) and `≥ 0`, `N_s` is a `Seminorm`, and `N_s(w) ≤ √r_s ‖w‖`;
* `seminorm_G` — (iii) with **one reference per group** (each with its own centre, atoms and budget):
  `inf_{λ₀,λ₁>0} F̄ = (Δ + N₀ + N₁)²` (`IsGLB`) and `G(t w) = t G(w)`, `t > 0`;
* `seminorm_wass` — (iv)(a),(c): `ε = 0`, full-support reference on `K = E`, cost `‖A(x − x₀)‖²` for a
  continuous linear automorphism `A`: `inf_{λ>0} T⁰_s = β_s ‖(A⁻¹)† w‖²`; for `A = id`, `= β_s ‖w‖²`;
* `npmle_duality` — `thm:npmle` duality for a finite mixing space `L`: `sup_m = min_v`, both attained,
  and at **every** maximiser `m*`, `v*_i = 1/∫ψ_i dm*` is dual feasible with dual value the primal value;
* `npmle_convex` — every `Φ_y` is jointly convex on `ℝⁿ × E × (0,∞)` (finitely supported `κ(y, ·)`);
* `npmle_correction` — the certified correction `z' = z − λε log max(1, V)` is feasible and bounds
  `T^𝒩_s(w, λ)` (against every reference of the mixture class);
* `npmle_programme` — the convex semi-infinite reformulation: for each `λ > 0` the maximum over `𝒩` in
  `T^𝒩_s(w, λ)` exists and equals `min{λ r − (1/n) Σ z_i : Φ_y(z, w, λ) ≤ 0 ∀ y}`; hence
  `N_s² = inf{λ r − (1/n) Σ z_i : λ > 0, Φ_y ≤ 0 ∀ y}` (same `IsGLB`).

Not covered (declared):
* (iv)(b) (entropic sets with the Lebesgue reference on `ℝ^d`: an infinite, non-finite reference);
* classes `𝒩` beyond a single reference in (i)–(iii) (in particular the free end and mixture classes for
  (i)–(iii); `thm:npmle` covers mixture classes only through a finite `L`), non-finitely supported
  references, and non-finitely supported kernels `κ(y, ·)` in `npmle_convex`/`npmle_correction`/
  `npmle_programme` (the paper: Feller kernel, compact `L`);
* `ε = 0` with a finite (or any non-full-support) reference, in (i)–(iii) and (iv);
* the paper's `ℝ^d`-specific forms: (iv)(c) is stated through `A` with `‖A u‖² = uᵀM⁻¹u`, not through a
  matrix square root (see Encodings);
* the identity `Δ(w) = W₂(h_#P̂₀, h_#P̂₁)` (`lem:delta-inf`, not this target): `Δ` is *defined* by its
  coupling form; `thm:certificate` itself (`F ≤ F̄`); the `ε ↓ 0` remark after `thm:npmle`.

Encodings (see card):
* covariates live in a real inner-product space `E` (Hilbert, `CompleteSpace`, for (iv)) — generalises `ℝ^d`;
  `|·|` is `‖·‖`; `h_w = ⟪w, ·⟫`, so `f_h(x₀, x) = ⟪w, x − x₀⟫²` and `c(x₀, x) = ‖x − x₀‖²` (`gexp`);
* centre `P̂_s = Σ_i a_i δ_{x_i}` with `a_i ≥ 0`, `Σ a_i = 1` (generalises the empirical law, `a_i = 1/n_s`);
  `thm:npmle` keeps the paper's uniform weights `1/n`;
* single reference `ν = Σ_j m_j δ_{y_j}`, `m_j > 0` (zero atoms dropped), `Σ m_j ≤ 1`, at least one atom;
  `E_{x∼ν}` is `∫ · dν` (unnormalised), as in `eq:T`; `FinSetting` collects these and `ε > 0`;
* "`r_s` at least the floor, so that the set is non-empty" is `Feasible`: some kernel `p_i` (rows of a
  coupling `γ = Σ a_i p_ij δ_{(x_i, y_j)}` with first marginal `P̂`) has
  `Σ_i a_i (Σ_j p_ij c(x_i, y_j) + ε Σ_j p_ij log(p_ij/m_j)) ≤ r` — `KL(γ ‖ P̂ ⊗ ν)` for a finite `ν`
  (`0 log 0 = 0` via `Real.log 0 = 0`); for finite supports the infimum over couplings is attained, so
  this is non-emptiness of `𝓑^ν(P̂; r)`;
* `λ` ranges over `Set.Ioi 0` throughout; `Nsq = ⨅_{λ>0} T` in `ℝ` is made non-junk by the `IsGLB` and
  `0 ≤` conjuncts of `seminorm_N`; `√T`, `√Nsq` are non-junk since `T ≥ 0` there; every `inf`/`sup` of a
  claim is an `IsGLB`/`IsLUB`/`IsLeast`/`IsGreatest` or a `⨅` in `EReal`;
* `Deltafin` is `√(⨅_γ Σ γ_ij ⟪w, x⁰_i − x¹_j⟫²)` over the transport polytope of the two centres: the
  polytope is non-empty (product coupling) and the summands are `≥ 0`, so the real `⨅` is genuine;
* (iv): `T⁰_s(w, λ) = λ β + Σ_i a_i sup_{x ∈ E} {⟪w, x − x_i⟫² − λ ‖A(x − x_i)‖²}` in `EReal` (`+∞` for
  small `λ`); (a) is `A = id` (Wasserstein balls, `N_s = √β‖w‖`, the paper's `r_s` is `β`), (c) is
  `A = M^{-1/2}` (cost `(x−x₀)ᵀM⁻¹(x−x₀)`), for which `(A⁻¹)† w = M^{1/2} w`; the claim is for every
  automorphism `A`, and `N_s = √β ‖(A⁻¹)† w‖`;
* `thm:npmle`: `L = Fin p` (finite, `p > 0`), `𝒩 = {ν_m = Σ_y m_y κ(y, ·) : m ∈ Δ_p}`; in
  `npmle_duality` the functions `ψ_i(y)` enter as **any** positive array (every `ψ_i(y)` of the theorem is
  positive and finite for a bounded rule on a compact `K`); elsewhere `κ(y, ·) = Σ_k κ_{yk} δ_{ξ_k}` with
  `κ_{yk} ≥ 0`, `0 < κ(y, K)` (the paper's `κ(y, K) ≤ 1` is not needed); the mixture reference
  is `nuMix κ m` and `T^𝒩_s(w, λ) = sup_m Tfin(…, nuMix κ m, …)` (`eq:T` with uniform weights);
  `n > 0` everywhere (no `λ/0`);
* "`V ≥ sup_y {Φ_y/λ + 1}` is certified" is the hypothesis `∀ y, Φ_y(z, w, λ)/λ + 1 ≤ V`.
On freezing: hashed in `certify/statements.lock`; AI agents must not edit the frozen file.
Critic notes: `Δ` is the coupling form `min_γ E_γ{h(X)−h(Y)}²`; that it equals `W₂(h#μ₀, h#μ₁)²` is `lem:delta-inf`, NOT
certified here (BACKLOG). `npmle_programme` is an "iff for every candidate value" (it does not assert the infimum exists).
One reference per group with `ε > 0` and finite `L` (paper: any class `𝒩`, `ε ≥ 0`, compact `L`, Feller kernel) — declared.
-/

noncomputable section
open Finset Real ContinuousLinearMap

namespace StatFormal.RobustEquality.Paper2.Seminorm

/-! ### Definitions (verbatim copies of the proof routes' definitions, so that bridging is
`rfl`; new here: `FinSetting`, `T0`, `nuMix`) -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n q p s : ℕ}

/-- `lse_m(u) = log Σ_j m_j e^{u_j}`. -/
def lse (m u : Fin q → ℝ) : ℝ := Real.log (∑ j, m j * Real.exp (u j))

/-- `f_{h_w}(x₀, x) − λ c(x₀, x)` at displacement `u = x − x₀`. -/
def gexp (w : E) (l : ℝ) (u : E) : ℝ := (inner ℝ w u) ^ 2 - l * ‖u‖ ^ 2

/-- `T(w, λ) = λ r + Σ_i a_i λε log Σ_j m_j exp{gexp(w, λ, y_j − x_i)/(λε)}`. -/
def Tfin (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E) (w : E)
    (l : ℝ) : ℝ :=
  l * r + ∑ i, a i * (l * ε * lse m (fun j => gexp w l (y j - x i) / (l * ε)))

/-- The budget has a feasible kernel: `Σ_i a_i (E_{p_i} c + ε KL(p_i ‖ ν)) ≤ r` (the set is non-empty). -/
def Feasible (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E) : Prop :=
  ∃ p : Fin n → Fin q → ℝ, (∀ i j, 0 ≤ p i j) ∧ (∀ i, ∑ j, p i j = 1) ∧
    ∑ i, a i * (∑ j, p i j * ‖y j - x i‖ ^ 2 + ε * ∑ j, p i j * Real.log (p i j / m j)) ≤ r

/-- Standing hypotheses: `ε > 0`, a probability centre, a finite sub-probability reference with
positive atoms. -/
def FinSetting (ε : ℝ) (a : Fin n → ℝ) (m : Fin q → ℝ) : Prop :=
  0 < ε ∧ (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧ 0 < q ∧ (∀ j, 0 < m j) ∧ ∑ j, m j ≤ 1

/-- `N_s(w)² = inf_{λ > 0} T(w, λ)`. -/
def Nsq (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E) (w : E) : ℝ :=
  ⨅ l : Set.Ioi (0 : ℝ), Tfin ε r a x m y w l

/-- The nominal disparity of two finite centres, `Δ(w) = (min_γ Σ γ_ij ⟪w, x⁰_i − x¹_j⟫²)^{1/2}`. -/
def Deltafin {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (w : E) : ℝ :=
  √(⨅ γ : {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = a₀ i) ∧
      ∀ j, ∑ i, γ i j = a₁ j},
    ∑ i, ∑ j, (γ : Fin n₀ → Fin n₁ → ℝ) i j * (inner ℝ w (x₀ i - x₁ j)) ^ 2)

/-- `ε = 0`, full-support reference on `E`, cost `‖A(x − x₀)‖²`:
`T⁰(w, λ) = λ β + Σ_i a_i sup_{x ∈ E} {⟪w, x − x_i⟫² − λ ‖A(x − x_i)‖²}` (in `EReal`). -/
def T0 (A : E ≃L[ℝ] E) (β : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (w : E) (l : ℝ) : EReal :=
  ((l * β : ℝ) : EReal) + ∑ i, ((a i : ℝ) : EReal) *
    ⨆ z : E, (((inner ℝ w (z - x i)) ^ 2 - l * ‖A (z - x i)‖ ^ 2 : ℝ) : EReal)

/-- The probability simplex on `Fin p`. -/
def simplex (p : ℕ) : Set (Fin p → ℝ) := {m | (∀ y, 0 ≤ m y) ∧ ∑ y, m y = 1}

/-- `Lval(m) = (1/n) Σ_i log Σ_y m_y ψ_i(y)`. -/
def Lval (ψ : Fin n → Fin p → ℝ) (m : Fin p → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, Real.log (∑ y, m y * ψ i y)

/-- Dual objective `D(v) = −(1/n) Σ log v_i`. -/
def Dval (v : Fin n → ℝ) : ℝ := -((1 / (n : ℝ)) * ∑ i, Real.log (v i))

/-- Dual feasibility. -/
def DualFeas (ψ : Fin n → Fin p → ℝ) (v : Fin n → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ ∀ y, (1 / (n : ℝ)) * ∑ i, v i * ψ i y ≤ 1

/-- `Φ_y(z, w, λ)` for a finite kernel `κ(y, ·) = Σ_k κ_k δ_{ξ_k}`. -/
def Phi (ε : ℝ) (x : Fin n → E) (κ : Fin s → ℝ) (ξ : Fin s → E) (z : Fin n → ℝ) (w : E)
    (l : ℝ) : ℝ :=
  l / n * ∑ i, ∑ k, κ k * Real.exp ((z i + gexp w l (ξ k - x i)) / (l * ε)) - l

/-- The mixture reference `ν_m = Σ_y m_y κ(y, ·)`, as weights on the atoms `ξ_k`. -/
def nuMix (κ : Fin p → Fin s → ℝ) (m : Fin p → ℝ) : Fin s → ℝ := fun k => ∑ y, m y * κ y k

end Defs

namespace Claims

/-- `thm:seminorm` (i), single finite reference, `ε > 0`. -/
def seminorm_T : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n q : ℕ) (ε r : ℝ)
    (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E),
    FinSetting ε a m →
      ConvexOn ℝ (Set.univ ×ˢ Set.Ioi 0) (fun p : E × ℝ => Tfin ε r a x m y p.1 p.2) ∧
      (∀ (w : E) (l : ℝ), 0 < l → Tfin ε r a x m y (-w) l = Tfin ε r a x m y w l) ∧
      ∀ (w : E) (l t : ℝ), 0 < l → 0 < t →
        Tfin ε r a x m y (t • w) (t ^ 2 * l) = t ^ 2 * Tfin ε r a x m y w l

/-- `thm:seminorm` (ii), single finite reference, `ε > 0`, budget above the floor. -/
def seminorm_N : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n q : ℕ) (ε r : ℝ)
    (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E),
    FinSetting ε a m → Feasible ε r a x m y →
      (∀ (w : E) (l : ℝ), 0 < l → 0 ≤ Tfin ε r a x m y w l) ∧
      (∀ w : E, IsGLB {v | ∃ l : ℝ, 0 < l ∧ v = Tfin ε r a x m y w l} (Nsq ε r a x m y w)) ∧
      (∀ w : E, 0 ≤ Nsq ε r a x m y w) ∧
      ∃ N : Seminorm ℝ E, (∀ w, N w = √(Nsq ε r a x m y w)) ∧ ∀ w, N w ≤ √r * ‖w‖

/-- `thm:seminorm` (iii), one finite reference per group, common `ε > 0`. -/
def seminorm_G : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ q₀ q₁ : ℕ) (ε r₀ r₁ : ℝ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (m₀ : Fin q₀ → ℝ) (y₀ : Fin q₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (m₁ : Fin q₁ → ℝ) (y₁ : Fin q₁ → E),
    FinSetting ε a₀ m₀ → FinSetting ε a₁ m₁ →
    Feasible ε r₀ a₀ x₀ m₀ y₀ → Feasible ε r₁ a₁ x₁ m₁ y₁ →
      (∀ w : E, IsGLB {v | ∃ l₀ l₁ : ℝ, 0 < l₀ ∧ 0 < l₁ ∧ v = (Deltafin a₀ x₀ a₁ x₁ w +
          √(Tfin ε r₀ a₀ x₀ m₀ y₀ w l₀) + √(Tfin ε r₁ a₁ x₁ m₁ y₁ w l₁)) ^ 2}
        ((Deltafin a₀ x₀ a₁ x₁ w + √(Nsq ε r₀ a₀ x₀ m₀ y₀ w) + √(Nsq ε r₁ a₁ x₁ m₁ y₁ w)) ^ 2)) ∧
      ∀ (w : E) (t : ℝ), 0 < t →
        Deltafin a₀ x₀ a₁ x₁ (t • w) + √(Nsq ε r₀ a₀ x₀ m₀ y₀ (t • w)) +
            √(Nsq ε r₁ a₁ x₁ m₁ y₁ (t • w)) =
          t * (Deltafin a₀ x₀ a₁ x₁ w + √(Nsq ε r₀ a₀ x₀ m₀ y₀ w) + √(Nsq ε r₁ a₁ x₁ m₁ y₁ w))

/-- `thm:seminorm` (iv)(a),(c): `ε = 0`, full-support reference on `K = E`, cost `‖A(x − x₀)‖²`. -/
def seminorm_wass : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (n : ℕ)
    (β : ℝ) (a : Fin n → ℝ) (x : Fin n → E),
    0 ≤ β → (∀ i, 0 ≤ a i) → ∑ i, a i = 1 →
      (∀ (A : E ≃L[ℝ] E) (w : E), (⨅ l : Set.Ioi (0 : ℝ), T0 A β a x w l) =
        ((β * ‖(adjoint (A.symm : E →L[ℝ] E)) w‖ ^ 2 : ℝ) : EReal)) ∧
      ∀ w : E, (⨅ l : Set.Ioi (0 : ℝ), T0 (ContinuousLinearEquiv.refl ℝ E) β a x w l) =
        ((β * ‖w‖ ^ 2 : ℝ) : EReal)

/-- `thm:npmle`, duality, finite `L = Fin p`, any positive `ψ`. -/
def npmle_duality : Prop :=
  ∀ (n p : ℕ) (ψ : Fin n → Fin p → ℝ), 0 < n → 0 < p → (∀ i y, 0 < ψ i y) →
    (∃ ms ∈ simplex p, IsGreatest (Lval ψ '' simplex p) (Lval ψ ms) ∧
      IsLeast (Dval '' {v | DualFeas ψ v}) (Lval ψ ms)) ∧
    ∀ ms ∈ simplex p, (∀ m ∈ simplex p, Lval ψ m ≤ Lval ψ ms) →
      DualFeas ψ (fun i => 1 / ∑ y, ms y * ψ i y) ∧
      Dval (fun i => 1 / ∑ y, ms y * ψ i y) = Lval ψ ms

/-- `thm:npmle`, joint convexity of `Φ_y` on `ℝⁿ × E × (0,∞)`, finitely supported `κ(y, ·)`. -/
def npmle_convex : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n s : ℕ) (ε : ℝ)
    (x : Fin n → E) (κ : Fin s → ℝ) (ξ : Fin s → E),
    0 < n → 0 < ε → (∀ k, 0 ≤ κ k) →
      ConvexOn ℝ (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioi 0))
        (fun q : (Fin n → ℝ) × E × ℝ => Phi ε x κ ξ q.1 q.2.1 q.2.2)

/-- `thm:npmle`, the certified correction, finite `L` and finitely supported `κ(y, ·)`. -/
def npmle_correction : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n p s : ℕ) (ε r l V : ℝ)
    (x : Fin n → E) (κ : Fin p → Fin s → ℝ) (ξ : Fin s → E) (z : Fin n → ℝ) (w : E),
    0 < n → 0 < p → 0 < ε → 0 < l → (∀ y k, 0 ≤ κ y k) → (∀ y, 0 < ∑ k, κ y k) →
    (∀ y, Phi ε x (κ y) ξ z w l / l + 1 ≤ V) →
      (∀ y, Phi ε x (κ y) ξ (fun i => z i - l * ε * Real.log (max 1 V)) w l ≤ 0) ∧
      ∀ m ∈ simplex p, Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l ≤
        l * r - (1 / (n : ℝ)) * ∑ i, (z i - l * ε * Real.log (max 1 V))

/-- `thm:npmle`, the convex semi-infinite programme: per `λ`, and for `N_s² = inf_λ T^𝒩_s`. -/
def npmle_programme : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n p s : ℕ) (ε r : ℝ)
    (x : Fin n → E) (κ : Fin p → Fin s → ℝ) (ξ : Fin s → E) (w : E),
    0 < n → 0 < p → 0 < ε → (∀ y k, 0 ≤ κ y k) → (∀ y, 0 < ∑ k, κ y k) →
      (∀ l : ℝ, 0 < l →
        (∃ t, IsGreatest
          {v | ∃ m ∈ simplex p, v = Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l} t) ∧
        ∀ t, IsGreatest
          {v | ∃ m ∈ simplex p, v = Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l} t →
          IsLeast {v | ∃ z : Fin n → ℝ, (∀ y, Phi ε x (κ y) ξ z w l ≤ 0) ∧
            v = l * r - (1 / (n : ℝ)) * ∑ i, z i} t) ∧
      ∀ N2 : ℝ,
        IsGLB {t | ∃ l : ℝ, 0 < l ∧ IsGreatest
          {v | ∃ m ∈ simplex p, v = Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l} t} N2 ↔
        IsGLB {v | ∃ (l : ℝ) (z : Fin n → ℝ), 0 < l ∧ (∀ y, Phi ε x (κ y) ξ z w l ≤ 0) ∧
          v = l * r - (1 / (n : ℝ)) * ∑ i, z i} N2

end Claims
end StatFormal.RobustEquality.Paper2.Seminorm
