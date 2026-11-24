import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# FROZEN STATEMENTS — otfd paper B: sampling-free quantile bands and their certificates

Sources (verbatim in `inventory/extracted/otfd-B_bands.md`):
* `prop:band-boundary` (`papers/B_bands/main.tex:692`);
* `prop:band-certificate` (`main.tex:720`) (i) zero-gap criterion, (ii) dual certificate,
  (iii) uniform weight caps (entropic and quadratic);
* `lem:ext-solver-error` (`papers/B_bands/supplement.tex:4801`), the `tanh(Δ/4ε)` bound and its
  sharpness for `n = 2`.
The maps are those of `subsec:oos-menu` (`main.tex:597-606`):
`Q̂_f(u) = Σ_i softmax_i((f_i − ‖u − Z_i‖²_M)/ε) Z_i`; quadratic regularisation replaces the softmax by
the Euclidean projection onto the simplex. Scores `s_j(u) = a_j + ⟨b_j, u⟩` as in `lem:oos-potential`.

Encodings (see card):
* `ℝ^K = Fin K → ℝ`, `⟨·,·⟩` = `dotProduct`, `‖x‖²_M = xᵀMx`; `M` is `Matrix.PosDef`.
* "`T(u) ∈ ½M⁻¹∂ψ(u)`" is `2 M T(u) ∈ ∂ψ(u)`, the subgradient inequality written out.
* `prop:band-boundary`(ii) is stated pointwise ("every value on `A` is dominated by a value on
  `∂A = frontier A`"), which, `A` being closed, gives `sup_A = sup_{∂A}`; `K ≥ 1` (for `K = 0` the
  frontier of the one-point space is empty).
* `max_k`, `min_k`, `osc` over `Fin n` are `⨆`/`⨅` (finite, `n ≥ 1`).
* `δ_j(p)` is `sInf` over the (nonempty) region of `max_k s_k − s_j`; the support function enters as
  any upper bound `σ_A ≥ sup_{u∈A} ⟨v, u⟩` (the paper uses the exact value or an upper bound).
* Caps (iii) are stated pointwise for any lower bound `δ ≤ max_k s_k(u) − s_j(u)`, which covers
  "replacing `δ_j(p)` by any lower bound preserves validity".
Not covered (declared): `lem:oos-potential` (that the fitted weights are `softmax(s(u)/ε)` resp. the
simplex projection of `s(u)/λ` — the caps here are about the scores); the certified outer band
(knapsack) of `prop:band-certificate`; the band-edge consequence of `lem:ext-solver-error`.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Finset Matrix

namespace StatFormal.OTFD.Bands

variable {n K : ℕ}

/-- The probability simplex `Δ^{n-1} = {w : w_i ≥ 0, Σ_i w_i = 1}`. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- Softmax weight `exp(x_j) / Σ_k exp(x_k)`. -/
def softmax (x : Fin n → ℝ) (j : Fin n) : ℝ := Real.exp (x j) / ∑ k, Real.exp (x k)

/-- `‖x‖²_M = xᵀ M x`. -/
def mnormSq (M : Matrix (Fin K) (Fin K) ℝ) (x : Fin K → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

/-- Entropic out-of-sample quantile map `Q̂_f(u) = Σ_i softmax_i((f_i − ‖u−Z_i‖²_M)/ε) Z_i`. -/
def Qent (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (u : Fin K → ℝ) : Fin K → ℝ :=
  ∑ i, softmax (fun j => (f j - mnormSq M (u - Z j)) / ε) i • Z i

/-- Affine scores `s_j(u) = a_j + ⟨b_j, u⟩`. -/
def score (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (j : Fin n) (u : Fin K → ℝ) : ℝ :=
  a j + b j ⬝ᵥ u

/-- Reachability gap `δ_j = inf_{u∈A} [max_k s_k(u) − s_j(u)]`. -/
def gap (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (j : Fin n) : ℝ :=
  sInf ((fun u => (⨆ k, score a b k u) - score a b j u) '' A)

/-- `q` is the Euclidean projection of `x` onto the simplex. -/
def IsSimplexProj (x q : Fin n → ℝ) : Prop :=
  q ∈ simplex n ∧ ∀ q' ∈ simplex n, ∑ i, (q i - x i) ^ 2 ≤ ∑ i, (q' i - x i) ^ 2

namespace Claims

/-- `prop:band-boundary` (i): for any selection `T(u) ∈ ½M⁻¹∂ψ(u)`, `s ↦ ⟨v, T(u + s M⁻¹ v)⟩` is
nondecreasing. -/
def band_boundary_mono : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (ψ : (Fin K → ℝ) → ℝ) (T : (Fin K → ℝ) → Fin K → ℝ),
    M.PosDef → ConvexOn ℝ Set.univ ψ →
    (∀ u y, ψ u + (2 • (M *ᵥ T u)) ⬝ᵥ (y - u) ≤ ψ y) →
      ∀ u v : Fin K → ℝ, Monotone (fun s : ℝ => v ⬝ᵥ T (u + s • (M⁻¹ *ᵥ v)))

/-- `prop:band-boundary` (ii): on a compact `A`, every value `⟨v, T(u)⟩`, `u ∈ A`, is dominated by a
value on the boundary of `A` (no convexity of `A`, no continuity or injectivity of `T`). -/
def band_boundary_sup : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (ψ : (Fin K → ℝ) → ℝ) (T : (Fin K → ℝ) → Fin K → ℝ),
    0 < K → M.PosDef → ConvexOn ℝ Set.univ ψ →
    (∀ u y, ψ u + (2 • (M *ᵥ T u)) ⬝ᵥ (y - u) ≤ ψ y) →
      ∀ (A : Set (Fin K → ℝ)), IsCompact A → ∀ v : Fin K → ℝ,
        ∀ u ∈ A, ∃ u' ∈ frontier A, v ⬝ᵥ T u ≤ v ⬝ᵥ T u'

/-- `prop:band-certificate` (i): on a nonempty compact region, `δ_j = 0` iff curve `j` attains the
maximal score somewhere in the region (and `δ_j ≥ 0`). -/
def band_gap_zero_iff : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (j : Fin n),
    IsCompact A → A.Nonempty →
      0 ≤ gap a b A j ∧ (gap a b A j = 0 ↔ ∃ u ∈ A, ∀ k, score a b k u ≤ score a b j u)

/-- `prop:band-certificate` (ii), dual certificate: for every `w ∈ Δ_n`,
`δ_j ≥ Σ_k w_k a_k − a_j − σ_A(v_j^w)`, `v_j^w = b_j − Σ_k w_k b_k`. -/
def band_dual_cert : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (j : Fin n)
    (w : Fin n → ℝ) (σA : ℝ),
    A.Nonempty → w ∈ simplex n →
    (∀ u ∈ A, (b j - ∑ k, w k • b k) ⬝ᵥ u ≤ σA) →
      ∑ k, w k * a k - a j - σA ≤ gap a b A j

/-- `prop:band-certificate` (iii), entropic cap: `q_j(u) = softmax_j(s(u)/ε) ≤ e^{−δ/ε}` for any
`δ ≤ max_k s_k(u) − s_j(u)`. -/
def band_cap_entropic : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (ε δ : ℝ) (j : Fin n) (u : Fin K → ℝ),
    0 < ε → δ ≤ (⨆ k, score a b k u) - score a b j u →
      softmax (fun k => score a b k u / ε) j ≤ Real.exp (-δ / ε)

/-- `prop:band-certificate` (iii), quadratic cap: with `q(u)` the Euclidean projection of `s(u)/λ`,
`λ = γ/m`, onto the simplex, `q_j(u) ≤ (1 − m δ/γ)_+` for any `δ ≤ max_k s_k(u) − s_j(u)`. -/
def band_cap_quadratic : Prop :=
  ∀ (n K m : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (γ δ : ℝ) (j : Fin n) (u : Fin K → ℝ)
    (q : Fin n → ℝ),
    0 < γ → 0 < m → δ ≤ (⨆ k, score a b k u) - score a b j u →
    IsSimplexProj (fun k => score a b k u / (γ / m)) q →
      q j ≤ max 0 (1 - m * δ / γ)

/-- `lem:ext-solver-error`: `|⟨v, Q̂_f(u) − Q̂_{f'}(u)⟩| ≤ tanh(osc(f−f')/(4ε)) (max_j⟨v,Z_j⟩ − min_j⟨v,Z_j⟩)`. -/
def ext_solver_error : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f f' : Fin n → ℝ)
    (u v : Fin K → ℝ),
    0 < n → 0 < ε → M.PosDef →
      |v ⬝ᵥ (Qent ε M Z f u - Qent ε M Z f' u)| ≤
        Real.tanh (((⨆ j, (f j - f' j)) - ⨅ j, (f j - f' j)) / (4 * ε)) *
          ((⨆ j, v ⬝ᵥ Z j) - ⨅ j, v ⬝ᵥ Z j)

/-- `lem:ext-solver-error`, sharpness: for `n = 2` the bound is attained at some `u ∈ ℝ^K`. -/
def ext_solver_sharp : Prop :=
  ∀ (K : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin 2 → Fin K → ℝ) (f f' : Fin 2 → ℝ)
    (v : Fin K → ℝ),
    0 < ε → M.PosDef →
      ∃ u : Fin K → ℝ, |v ⬝ᵥ (Qent ε M Z f u - Qent ε M Z f' u)| =
        Real.tanh (((⨆ j, (f j - f' j)) - ⨅ j, (f j - f' j)) / (4 * ε)) *
          ((⨆ j, v ⬝ᵥ Z j) - ⨅ j, v ⬝ᵥ Z j)

end Claims
end StatFormal.OTFD.Bands
