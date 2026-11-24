import StatFormal.Wave30tv.Statements
import StatFormal.Wave30ty.Statements
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tz: trimmed-mmd (jmlr v2), consistency of the split-sample lower bound `α̂_lo`

Source (READ-ONLY), frozen from: `trimmed-mmd/explore/lo_consistency/NOTE.md` (explore note of 2026-11-08, author decision
Q10; sha256 `c5e321c3f6f39b999bceea0c57c0d8bcedc011ab7e201633f62877b6d2b9d3ed`): Proposition 1 (§2), the §9 print block,
§1 conventions, Lemmas 1–7 (§4), the proofs (§5), Proposition 3, and the "Lean freeze list". The paper prints the result at
trimmed-mmd master `3bad3e7`: `jmlr/v2/sections/04_split.tex` §4.3, `prop:loconsistency` (sha256
`5091bcf4ada241cd6d96fbf9294ba4a6f0417a0dc4ed2a4fe4a0497b2d790b52`), proof in `jmlr/v2/appendix/C_split.tex` C.5 (sha256
`a3a7389e5f2ab7213ce6497a0467ec30585ad9114221f717f51661f1f680e521`: `eq:cutrank`, `lem:popramp`, `eq:fittedramp`,
`eq:betbounds`, "A witness fitted at α = 0"). Paper context: `sections/04_split.tex` (`lem:ramp`, `thm:betting`, `cor:lower`,
`eq:downclosed`, `eq:witness`), `appendix/C_split.tex` (`eq:fractions`), `appendix/B_analytic.tex` (`thm:twosided`),
`sections/02_regions.tex` (`ass:regularity`, `eq:qp`). Labels are the printed ones where printed, else "NOTE Lemma k".

Covered (NOTE numbering; printed labels in brackets):
* §1 convention (C) [`eq:cutrank`] and the quantiles that satisfy it: `numpy_bracket`, `exact_quantile_bracket`; §1
  "Fractions" [`eq:fractions`]: `fractions_bounds`;
* Lemma 1 [`lem:popramp`]: `pop_ramp_rkhs` (the printed lemma), `pop_ramp` (freeze item 6, corrected), `pop_ramp_freeze_false`
  (freeze item 6 as worded is false), `ramp_tv` (NOTE: "under (A3), TV = sup over ramps"; not printed);
* Lemma 2 [`eq:fittedramp` paragraph]: `crit_identity`, `crit_emp`, `crit_uniform`;
* Lemma 3 [`eq:fittedramp` paragraph]: `quantile_bracket`; freeze item 3: `order_stat_shift`;
* Lemma 4 [`eq:fittedramp`]: `fitted_ramp`, `theta_mono`;
* Lemma 5 [`eq:betbounds`, first bound]: `log_lower` (the Taylor step), `bet_power`, `bet_power_frac`;
* Lemma 6 [`eq:betbounds`, second bound]: `strict_null`, `strict_null_frac`;
* the assembly (§5, freeze item 9): `grid_events`, `mesh_point`;
* Proposition 1 [`prop:loconsistency`]: `lo_consistency` (the printed proposition and §9 at a fixed grid and fixed `δ`),
  `lo_refining` (its refining-grid sentence), `lo_upper` (the upper side for every `n, m`), `lo_lower_bound`, `lo_strict_bound`
  (the explicit bounds of §5), `lo_lower` (the lower side without (A3), uniform over `D_{α_i} ≥ d`), `lo_exact` (1, third and
  fourth bullets), `lo_vanishing` (part 2), `lo_refining_kernel` (part 3 without (A3));
* Lemma 7 and Proposition 3 ["A witness fitted at α = 0"]: `ramp_ks`, `alpha0_example` (the finite certificate),
  `alpha0_valid` (the validity bound of the `α = 0` variant, by the predictable indicator).
Not covered (declared on the card): Corollary 2 and Remarks 1–5; Proposition 3's convergence (`f̂_{0,b} → f₀` a.s.,
`KS⁺(f̂_{0,b}) = 0.4` eventually, "every level `α ≥ 0.4` is rejected with probability at most `δ + o(1)`"); the asymptotic
equivalence `log ε_N ∼ −σ²_min ϱ² N/8`; the existence of a measurable selection of the minimizer and cut points.

Encodings (see card `certify/cards/wave30tz.md`):
* kernel: as in `Wave30tr`, `Wave30ty`: `H` a real inner-product space (complete and separable where (A2) and the projection are
  used), `φ : 𝒳 → H` strongly measurable with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ x‖²`), `f(x) = ⟪f, φ x⟫`; `Dφ` any bound on
  `‖φ x − φ x'‖` (the printed `D_φ` is the least one); (A3) is the frozen `ZeroSet.Characteristic`; `α* = TV(P,Q)`;
* data `(x, y) ∈ 𝒳^n × 𝒳^m` under `sampleLaw P Q n m = P^{⊗n} ⊗ Q^{⊗m}`; no auxiliary randomness: the frozen `Wave30tv`
  definitions are used with `U = Unit` (`IsFitRule`, `IsFracRule`, `pairStat`, `rejects`);
* batches, pairs: `Wave30tv.IsBatchPairing` (any batch labels; the printed cut at fixed fractions `e` with `N_b = min(n_b, m_b)`
  pairs is an instance); the fitting sample of batch `b` is `fitSample` (the observations of the batches before `b`, in index
  order); the asymptotic regime (`IsSizedRun`): batches `≤ Bmax`, fitting sizes `≥ c n − C₀`, `≥ c m − C₀`, `N ≥ c min(n,m) − C₀`;
* the per-level witness (`IsWitnessRamp`): an exact minimizer `(w, v)` of `eq:qp` (`IsQPMin`), the witness `eq:witness`
  (`witness`, `0` when the minimum is `0`), the own-term values (`ownX`, `ownY`), any cut points satisfying convention (C)
  (`CutsC`, ranks `ι^±` = `rkLo`, `rkHi`, order statistics `ordStat`), the ramp of the witness (frozen `Wave30tq.ramp`);
  the rule bets on the batch iff `D̂ > 0` and `t̂ > û`; the minimizer and cut points may depend on the data in any way, and
  the paper's admissibility (joint measurability, dependence on earlier batches) is required of the resulting rule;
* fractions `eq:fractions` with a fixed floor `σ²_min > 0`: `λ_k ≤ λ̄_N` always, `λ_k ≥ λ_N` on the pairs of a batch with a
  ramp (for every realizable past, `Z_l ∈ [−1,1]`), `0` elsewhere (`lamHi`, `lamLo`; `λ_N = min{λ_max/(1+α), √(L/(2N))}` when
  `σ²_min ≤ 4`, and with `max(σ²_min, 4)` in place of `4` in general; `fractions_bounds` shows that the printed formula with
  `σ₀² ≤ 4` satisfies them); the explicit bounds `bet_power_frac`, `lo_lower_bound` take `σ²_min ≤ 4`, as the printed proof does;
* `α̂_lo` is the frozen `TrimmedMMD.Lower.alphaLo` (`eq:downclosed`); `α_{j*}` is `gridBelow α TV`; the mesh is `gridMesh`;
* asymptotic statements in explicit form: "for every `ε > 0` there is `N₀` with … for all `n, m ≥ N₀`".

Defects of the source found while freezing (declared on the card, with corrected wording):
* NOTE §5/§6, "when `α*` is a grid point, `P(α̂_lo ≥ α*) ≤ δ`" is false at `α* = 0 ∈ 𝒢` (then `α̂_lo ≥ 0 = α*` surely); true for
  `α* > 0` (`lo_upper`). The paper does not print it.
* freeze item 6 (`pop_ramp`, abstract form) is false as worded: the cut points must lie in the range of `f`
  (`pop_ramp_freeze_false`; corrected `pop_ramp`; the printed `lem:popramp` is right);
* freeze item 4's identity needs measures of equal mass (probability measures), not "finite measures"; freeze item 7 needs
  `λ ≥ 0` and `ϱ > 0`, as Lemma 5 states;
* the printed proposition takes any floor `σ²_min > 0`, its proof `σ²_min ≤ 4`; the asymptotic claims here hold for every
  `σ²_min > 0`.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30ty StatFormal.Wave30tp
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet

/-! ### Order statistics, the rank convention (C), the code's quantile -/

open Classical in
/-- The `k`-th order statistic `h_(k)` of `h_1, …, h_n` (`1 ≤ k ≤ n`): the least `v` such that at least `k` of the values are
`≤ v`. -/
def ordStat {n : ℕ} (h : Fin n → ℝ) (k : ℕ) : ℝ :=
  sInf {v : ℝ | k ≤ (Finset.univ.filter fun i => h i ≤ v).card}

/-- `ι⁻(n,p) = max(1, ⌈np⌉ − 1)`. -/
def rkLo (n : ℕ) (p : ℝ) : ℕ := max 1 (⌈(n : ℝ) * p⌉₊ - 1)

/-- `ι⁺(n,p) = min(n, ⌊np⌋ + 2)`. -/
def rkHi (n : ℕ) (p : ℝ) : ℕ := min n (⌊(n : ℝ) * p⌋₊ + 2)

/-- Convention (C) for the cut points `t` (of the values `h` at the `X`'s) and `u` (of the values `h'` at the `Y`'s) at level `α`:
`t ∈ [h_(ι⁻(n,1−α)), h_(ι⁺(n,1−α))]` and `u ∈ [h'_(ι⁻(m,α)), h'_(ι⁺(m,α))]`. -/
def CutsC {n m : ℕ} (α : ℝ) (h : Fin n → ℝ) (h' : Fin m → ℝ) (t u : ℝ) : Prop :=
  t ∈ Icc (ordStat h (rkLo n (1 - α))) (ordStat h (rkHi n (1 - α))) ∧
  u ∈ Icc (ordStat h' (rkLo m α)) (ordStat h' (rkHi m α))

/-- `numpy.quantile(h, p)` with its default linear interpolation: at the position `(n − 1)p` it interpolates between the order
statistics of ranks `⌊(n−1)p⌋ + 1` and `min(n, ⌊(n−1)p⌋ + 2)`. -/
def npQuantile {n : ℕ} (h : Fin n → ℝ) (p : ℝ) : ℝ :=
  ordStat h (⌊((n : ℝ) - 1) * p⌋₊ + 1) +
    (((n : ℝ) - 1) * p - ⌊((n : ℝ) - 1) * p⌋₊) *
      (ordStat h (min n (⌊((n : ℝ) - 1) * p⌋₊ + 2)) - ordStat h (⌊((n : ℝ) - 1) * p⌋₊ + 1))

open Classical in
/-- `q` is a `p`-quantile of the empirical law of `h_1, …, h_n`: `#{i : h_i < q} ≤ np ≤ #{i : h_i ≤ q}`. -/
def IsEmpQuantile {n : ℕ} (h : Fin n → ℝ) (p q : ℝ) : Prop :=
  ((Finset.univ.filter fun i => h i < q).card : ℝ) ≤ n * p ∧ (n : ℝ) * p ≤ (Finset.univ.filter fun i => h i ≤ q).card

/-! ### The empirical criterion (Lemmas 2, 3) -/

/-- `T(t) = t − (β/n) Σ_i (t − h_i)₊`. -/
def critT {n : ℕ} (α : ℝ) (h : Fin n → ℝ) (t : ℝ) : ℝ := t - beta α / n * ∑ i, max (t - h i) 0

/-- `U(u) = u + (β/m) Σ_j (h'_j − u)₊`. -/
def critU {m : ℕ} (α : ℝ) (h' : Fin m → ℝ) (u : ℝ) : ℝ := u + beta α / m * ∑ j, max (h' j - u) 0

/-- The hinge `ψ_x(z) = z₊` of `thm:twosided`, Step 2. -/
def hingePos {𝒳 : Type*} : 𝒳 → ℝ → ℝ := fun _ z => max z 0

/-! ### The quadratic program `eq:qp`, the witness `eq:witness` and its own-term values -/

section QP

variable {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The capped simplex of `eq:qp`: `0 ≤ w_i ≤ [n(1−α)]⁻¹` and `Σ_i w_i = 1`. -/
def IsCapped {n : ℕ} (α : ℝ) (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ 1 / (n * (1 - α))) ∧ ∑ i, w i = 1

/-- `Σ_i w_i φ(x_i)`. -/
def wsum (φ : 𝒳 → H) {n : ℕ} (x : Fin n → 𝒳) (w : Fin n → ℝ) : H := ∑ i, w i • φ (x i)

/-- The value `D̂ = ‖Σ_i w_i φ(x_i) − Σ_j v_j φ(y_j)‖` of a feasible point of `eq:qp`. -/
def qpVal (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) : ℝ :=
  ‖wsum φ x w - wsum φ y v‖

/-- `(w, v)` is an (exact) minimizer of `eq:qp`: both capped, and the objective `‖Σ w_i φ(x_i) − Σ v_j φ(y_j)‖²` is no larger
than at any other capped pair. -/
def IsQPMin (φ : 𝒳 → H) (α : ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) : Prop :=
  IsCapped α w ∧ IsCapped α v ∧
    ∀ w' v', IsCapped α w' → IsCapped α v' → qpVal φ x y w v ≤ qpVal φ x y w' v'

/-- The witness `eq:witness`: `f̂ = (Σ_i w_i φ(x_i) − Σ_j v_j φ(y_j)) / D̂`, `0` when `D̂ = 0`. -/
def witness (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) : H :=
  (qpVal φ x y w v)⁻¹ • (wsum φ x w - wsum φ y v)

/-- The own-term values at the `X`'s: `h̃_i = f̂(x_i) − w_i k(x_i, x_i)/D̂`. -/
def ownX (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (i : Fin n) : ℝ :=
  ⟪witness φ x y w v, φ (x i)⟫_ℝ - w i * ‖φ (x i)‖ ^ 2 / qpVal φ x y w v

/-- The own-term values at the `Y`'s: `h̃'_j = f̂(y_j) + v_j k(y_j, y_j)/D̂`. -/
def ownY (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (j : Fin m) : ℝ :=
  ⟪witness φ x y w v, φ (y j)⟫_ℝ + v j * ‖φ (y j)‖ ^ 2 / qpVal φ x y w v

/-- The per-level witness rule on a fitting sample `(x, y)`, with betting indicator `has` and ramp `g`: an empty side gives no
bet; otherwise, for some minimizer `(w, v)` of `eq:qp`, no bet if `D̂ = 0`, and if `D̂ > 0`, for some cut points `t, u`
satisfying (C) for the own-term values, the rule bets iff `t > u`, and then `g` is the ramp of `f̂` between `u` and `t`. -/
def IsWitnessRamp (φ : 𝒳 → H) (α : ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (has : Prop) (g : 𝒳 → ℝ) : Prop :=
  (n = 0 ∨ m = 0 → ¬ has) ∧
  (1 ≤ n → 1 ≤ m → ∃ w v, IsQPMin φ α x y w v ∧
    (qpVal φ x y w v = 0 → ¬ has) ∧
    (0 < qpVal φ x y w v → ∃ t u, CutsC α (ownX φ x y w v) (ownY φ x y w v) t u ∧ (has ↔ u < t) ∧
      (has → g = ramp (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u)))

end QP

/-- `Θ = D − β(Z + Z⁻) − β D_φ r − β²κ² r/(D − βZ⁻)` (Lemma 4). -/
def fitTheta (α D Zp Zm κ Dφ r : ℝ) : ℝ :=
  D - beta α * (Zp + Zm) - beta α * Dφ * r - beta α ^ 2 * κ ^ 2 * r / (D - beta α * Zm)

/-! ### The sequential certificate without auxiliary randomness -/

section Seq

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}

/-- The paper's admissible fitting rule (`Wave30tv.IsBatchRule` with no auxiliary randomness). -/
def IsFitRule (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ) : Prop :=
  IsBatchRule (U := Unit) lx ly bat (fun b _ => g b)

/-- Admissible fractions at level `α` with cap `c = λ_max` (`Wave30tv.IsBatchBetRule` with no auxiliary randomness). -/
def IsFracRule (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (α c : ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) : Prop :=
  IsBatchBetRule (U := Unit) lx ly bat α c (fun k _ => lam k)

/-- The pair statistics `Z_k` (`Wave30tv.seqZ`). -/
def pairStat (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n))
    (B : Fin N → Finset (Fin m)) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : Fin N → ℝ :=
  seqZ (U := Unit) (fun b _ => g b) bat A B () x y

/-- The fraction `λ_k = lam k x y (Z_0, …, Z_{k−1})` of pair `k`. -/
def fracAt (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    (k : Fin N) : ℝ :=
  lam k x y (past (pairStat g bat A B x y) k)

/-- The certificate rejects `H_{0,α}`: `max_{t ≤ N} K_t ≥ 1/δ` (`Wave30tv.seqReject`). -/
def rejects (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α δ : ℝ) (x : Fin n → 𝒳)
    (y : Fin m → 𝒳) : Prop :=
  seqReject (U := Unit) (fun k _ => lam k) (fun b _ => g b) bat A B α δ () x y

/-- The conditional mean of pair `k` given the earlier batches: `Δ_k = E_P g_b − E_Q g_b`, `b = bat k`. -/
def condMean (P Q : Measure 𝒳) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ) (bat : Fin N → ℕ) (x : Fin n → 𝒳)
    (y : Fin m → 𝒳) (k : Fin N) : ℝ :=
  (∫ z, g (bat k) x y z ∂P) - ∫ z, g (bat k) x y z ∂Q

open Classical in
/-- The number of observations of the batches before `b`. -/
def fitCard {p : ℕ} (l : Fin p → ℕ) (b : ℕ) : ℕ := (Finset.univ.filter fun i => l i < b).card

open Classical in
/-- The fitting sample of batch `b`: the observations of the batches before `b`, in index order. -/
def fitSample {p : ℕ} (l : Fin p → ℕ) (b : ℕ) (x : Fin p → 𝒳) : Fin (fitCard l b) → 𝒳 :=
  fun k => x ((Finset.univ.filter fun i => l i < b).orderEmbOfFin rfl k)

end Seq

/-- The lower fraction bound `λ_N = min{λ_max/(1+α), √(2L/(N max(σ²_min, 4)))}`, which is `min{λ_max/(1+α), √(L/(2N))}`
when `σ²_min ≤ 4` (each square of `eq:fractions` is at most `4`). -/
def lamLo (lmax α L s2 : ℝ) (N : ℕ) : ℝ := min (lmax / (1 + α)) (√(2 * L / (N * max s2 4)))

/-- The upper fraction bound `λ̄_N = min{λ_max/(1+α), √(2L/(N σ²_min))}`. -/
def lamHi (lmax α L s2 : ℝ) (N : ℕ) : ℝ := min (lmax / (1 + α)) (√(2 * L / (N * s2)))

/-- `ε_N(ϱ) = exp(−(σ²_min/(4L)) (ϱ√(NL/2) − L − 4L(1+α)²/σ²_min)₊²)` (Lemma 5). -/
def epsN (s2 α L : ℝ) (N : ℕ) (ρ : ℝ) : ℝ :=
  Real.exp (-(s2 / (4 * L)) * (max (ρ * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2)

/-! ### A run of the lower bound -/

/-- A run of the split-sample lower bound at sample sizes `n, m` on a grid of `J` levels: batch labels `lx, ly`, `N` pairs with
batches `bat` and blocks `A, B`, and for each level `j` the betting indicator `has j b x y` and the ramp `g j b x y` of batch `b`,
and the fractions `lam j k x y z` of pair `k` (`z` the earlier pair statistics). -/
structure LoRun (𝒳 : Type*) (J n m : ℕ) where
  lx : Fin n → ℕ
  ly : Fin m → ℕ
  N : ℕ
  bat : Fin N → ℕ
  A : Fin N → Finset (Fin n)
  B : Fin N → Finset (Fin m)
  has : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → Prop
  g : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ
  lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ

namespace LoRun

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {J n m : ℕ}

/-- `α̂_lo` of the run (`eq:downclosed` over the levels' rejections). -/
def alphaLo (R : LoRun 𝒳 J n m) (α : Fin J → ℝ) (δ : ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  StatFormal.TrimmedMMD.Lower.alphaLo α fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ x y

/-- The run is admissible (`thm:betting`, `cor:lower`): a batch pairing, admissible fitting rules and fractions (cap `λ_max`)
at every level. -/
def IsAdmissible (R : LoRun 𝒳 J n m) (α : Fin J → ℝ) (lmax : ℝ) : Prop :=
  IsBatchPairing R.lx R.ly R.bat R.A R.B ∧ (∀ j, IsFitRule R.lx R.ly R.bat (R.g j)) ∧
    ∀ j, IsFracRule R.lx R.ly R.bat (α j) lmax (R.lam j)

/-- Proposition 1's run: admissible, per-level witnesses with cut points satisfying (C) on the fitting sample of every batch
that holds a pair, and the fractions `eq:fractions` with the floor `s2 = σ²_min`, `L = log(1/δ)`. -/
def IsWitnessRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (R : LoRun 𝒳 J n m) (φ : 𝒳 → H)
    (α : Fin J → ℝ) (δ lmax s2 : ℝ) : Prop :=
  R.IsAdmissible α lmax ∧
  (∀ j (k : Fin R.N) x y, IsWitnessRamp φ (α j) (fitSample R.lx (R.bat k) x) (fitSample R.ly (R.bat k) y)
    (R.has j (R.bat k) x y) (R.g j (R.bat k) x y)) ∧
  ∀ j (k : Fin R.N) x y z,
    R.lam j k x y z ≤ lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N ∧
    (R.has j (R.bat k) x y → (∀ l, z l ∈ Icc (-1 : ℝ) 1) →
      lamLo lmax (α j) (Real.log (1 / δ)) s2 R.N ≤ R.lam j k x y z) ∧
    (¬ R.has j (R.bat k) x y → R.lam j k x y z = 0)

/-- The asymptotic regime (fixed batch fractions): every pair lies in a batch `≤ Bmax`, the fitting sample of its batch has at
least `c n − C₀` observations of `X` and `c m − C₀` of `Y`, and `N ≥ c min(n,m) − C₀`. -/
def IsSizedRun (R : LoRun 𝒳 J n m) (c C0 : ℝ) (Bmax : ℕ) : Prop :=
  (∀ k, R.bat k ≤ Bmax) ∧ (∀ k, c * n - C0 ≤ fitCard R.lx (R.bat k)) ∧ (∀ k, c * m - C0 ≤ fitCard R.ly (R.bat k)) ∧
    c * (min n m : ℕ) - C0 ≤ R.N

end LoRun

/-! ### The grid -/

/-- A grid of levels fixed in advance: `0 ≤ α_1 < ⋯ < α_J < 1`. -/
def IsGrid {J : ℕ} (α : Fin J → ℝ) : Prop := StrictMono α ∧ ∀ j, 0 ≤ α j ∧ α j < 1

open Classical in
/-- `α_{j*} = max{α_j : α_j < a}`, and `0` if no level is below `a`. -/
def gridBelow {J : ℕ} (α : Fin J → ℝ) (a : ℝ) : ℝ :=
  if h : (Finset.univ.filter fun j => α j < a).Nonempty then (Finset.univ.filter fun j => α j < a).sup' h α else 0

/-- The mesh `h = sup_{a ∈ [0,1)} dist(a, 𝒢 ∪ {0})`. -/
def gridMesh {J : ℕ} (α : Fin J → ℝ) : ℝ := ⨆ a : Ico (0 : ℝ) 1, Metric.infDist (a : ℝ) (insert 0 (range α))

/-! ### Proposition 3 -/

/-- `KS⁺(f) = sup_{x ∈ ℝ} {P(f(X) > x) − Q(f(Y) > x)}`. -/
def ksPlus {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) (f : 𝒳 → ℝ) : ℝ :=
  ⨆ x : ℝ, (P.real {z | x < f z} - Q.real {z | x < f z})

/-- The law `P = 0.4 δ_0 + Σ_{i=1}^{20} (0.2 i/210) δ_{20+10i} + 0.4 δ_{−100}` of the example. -/
def exP : Measure ℝ :=
  ENNReal.ofReal (2 / 5) • Measure.dirac 0 +
    ∑ i ∈ Finset.Icc (1 : ℕ) 20, ENNReal.ofReal ((i : ℝ) / 1050) • Measure.dirac (20 + 10 * (i : ℝ)) +
    ENNReal.ofReal (2 / 5) • Measure.dirac (-100)

/-- The law `Q = 0.3 δ_{0.5} + 0.3 δ_{300} + 0.4 δ_{−100}` of the example. -/
def exQ : Measure ℝ :=
  ENNReal.ofReal (3 / 10) • Measure.dirac (1 / 2) + ENNReal.ofReal (3 / 10) • Measure.dirac 300 +
    ENNReal.ofReal (2 / 5) • Measure.dirac (-100)

/-- The Gaussian kernel with `σ = 1` on `ℝ`: `k(a, x) = exp(−(a − x)²/2)`. -/
def gaussK (a x : ℝ) : ℝ := Real.exp (-(a - x) ^ 2 / 2)

/-- `MMD(P,Q) = (∫∫ k dP dP − 2 ∫∫ k dP dQ + ∫∫ k dQ dQ)^{1/2}` for the Gaussian kernel. -/
def mmdGauss (P Q : Measure ℝ) : ℝ :=
  √((∫ a, ∫ a', gaussK a a' ∂P ∂P) - 2 * (∫ a, ∫ b, gaussK a b ∂Q ∂P) + ∫ b, ∫ b', gaussK b b' ∂Q ∂Q)

/-- `f_0 = (μ_P − μ_Q)/MMD(P,Q)` as a function: `f_0(x) = (∫ k(a,x) dP(a) − ∫ k(b,x) dQ(b))/MMD(P,Q)`. -/
def exWitness (P Q : Measure ℝ) (x : ℝ) : ℝ := ((∫ a, gaussK a x ∂P) - ∫ b, gaussK b x ∂Q) / mmdGauss P Q

namespace Claims

/-! ### §1: convention (C), the code's quantile, the fractions -/

/-- §1, "The code's `numpy.quantile` satisfies (C)": for `n ≥ 1` and `p ∈ [0,1]`, `⌊(n−1)p⌋ + 1 ≥ ⌈np⌉ − 1` and
`⌊(n−1)p⌋ + 2 ≤ ⌊np⌋ + 2`, and `numpy.quantile(h, p)` lies in `[h_(ι⁻(n,p)), h_(ι⁺(n,p))]`. -/
def numpy_bracket : Prop :=
  ∀ (n : ℕ) (p : ℝ) (h : Fin n → ℝ), 1 ≤ n → 0 ≤ p → p ≤ 1 →
    ⌈(n : ℝ) * p⌉₊ - 1 ≤ ⌊((n : ℝ) - 1) * p⌋₊ + 1 ∧ ⌊((n : ℝ) - 1) * p⌋₊ + 2 ≤ ⌊(n : ℝ) * p⌋₊ + 2 ∧
    npQuantile h p ∈ Icc (ordStat h (rkLo n p)) (ordStat h (rkHi n p))

/-- §1, "The exact quantiles of `lem:cvar` satisfy (C) whenever they lie in the range of the values": a `p`-quantile `q` of the
empirical law of `h` with `min h ≤ q ≤ max h` lies in `[h_(ι⁻(n,p)), h_(ι⁺(n,p))]`. -/
def exact_quantile_bracket : Prop :=
  ∀ (n : ℕ) (p q : ℝ) (h : Fin n → ℝ), 1 ≤ n → 0 ≤ p → p ≤ 1 → IsEmpQuantile h p q →
    (∃ i, h i ≤ q) → (∃ i, q ≤ h i) → q ∈ Icc (ordStat h (rkLo n p)) (ordStat h (rkHi n p))

/-- §1, "Fractions": the running estimate `σ̂²_{k−1} = (w₀σ₀² + Σ_{i∈S}(Z_i − α − μ̂_{i−1})²)/(w₀ + |S|)`, with
`μ̂_{i−1} = Σ_{l∈S, l<i}(Z_l − α)/(w₀ + |{l ∈ S : l < i}|)`, the sums and counts over the set `S` of earlier pairs bet on, `w₀ > 0`,
`σ₀² ∈ [0,4]` and `Z_i ∈ [−1,1]`, lies in `[0, 4]`; floored at `σ²_min > 0` it lies in `[σ²_min, max(σ²_min, 4)]`, and then
the fraction `min{λ_max/(1+α), √(2L/(N σ̂²))}` of `eq:fractions` lies in `[λ_N, λ̄_N]`. -/
def fractions_bounds : Prop :=
  ∀ (K : ℕ) (Z : Fin K → ℝ) (S : Finset (Fin K)) (w0 s0 α s2 lmax L : ℝ) (N : ℕ),
    0 < w0 → 0 ≤ s0 → s0 ≤ 4 → 0 ≤ α → α < 1 → (∀ i, Z i ∈ Icc (-1 : ℝ) 1) → 0 < s2 → 0 ≤ L →
      0 ≤ (w0 * s0 + ∑ i ∈ S, (Z i - α - (∑ l ∈ S.filter (· < i), (Z l - α)) / (w0 + (S.filter (· < i)).card)) ^ 2) /
          (w0 + S.card) ∧
      (w0 * s0 + ∑ i ∈ S, (Z i - α - (∑ l ∈ S.filter (· < i), (Z l - α)) / (w0 + (S.filter (· < i)).card)) ^ 2) /
          (w0 + S.card) ≤ 4 ∧
      ∀ σ2 : ℝ, σ2 = max s2 ((w0 * s0 + ∑ i ∈ S, (Z i - α -
          (∑ l ∈ S.filter (· < i), (Z l - α)) / (w0 + (S.filter (· < i)).card)) ^ 2) / (w0 + S.card)) →
        s2 ≤ σ2 ∧ σ2 ≤ max s2 4 ∧
        lamLo lmax α L s2 N ≤ min (lmax / (1 + α)) (√(2 * L / (N * σ2))) ∧
        min (lmax / (1 + α)) (√(2 * L / (N * σ2))) ≤ lamHi lmax α L s2 N

/-! ### Lemma 1 (`lem:popramp`) -/

/-- Lemma 1, abstract form (freeze item 6, with the cut points inside the range of `f`, which the quantiles of Lemma 1 are):
for bounded measurable `f` with `f(x) − f(x') ≤ D_φ`, cuts `t ≤ sup f`, `u ≥ inf f`, and `θ(f; t, u) ≥ d > 0`: `t > u`,
`t − u ≤ D_φ` and the ramp has `E_P g − E_Q g − α ≥ d/(β D_φ)`. -/
def pop_ramp : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ) (t u Dφ d : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 → (∀ x x', f x - f x' ≤ Dφ) →
    t ≤ ⨆ x, f x → ⨅ x, f x ≤ u → 0 < d → d ≤ theta P Q α f t u →
      u < t ∧ t - u ≤ Dφ ∧ d / (beta α * Dφ) ≤ (∫ x, ramp f t u x ∂P) - (∫ y, ramp f t u y ∂Q) - α

/-- Freeze item 6 as worded ("if `θ(f;t,u) = D > 0` and `sup f − inf f ≤ D_φ`, then `E_P g − E_Q g − α ≥ D/(βD_φ)`", with no
condition on the cut points) is false. (Witness: `𝒳 = ℝ`, `f = (x ∨ 0) ∧ 1`, `P = δ_1`, `Q = δ_0`, `α = 0`, `t = 2`, `u = 0`,
`D_φ = 1`: `θ = 1`, but the ramp is `f/2` and its excess is `1/2`.) -/
def pop_ramp_freeze_false : Prop :=
  ¬ ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (α : ℝ) (f : 𝒳 → ℝ) (t u Dφ : ℝ),
      Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 → (∀ x x', f x - f x' ≤ Dφ) →
      0 < theta P Q α f t u →
        theta P Q α f t u / (beta α * Dφ) ≤ (∫ x, ramp f t u x ∂P) - (∫ y, ramp f t u y ∂Q) - α

/-- **Lemma 1** (`lem:popramp`, the population ramp), (A1)–(A2): let `α ∈ [0,1)` with `D_α > 0`, let `a ∈ 𝒞_α(P)`, `b ∈ 𝒞_α(Q)`
be nearest points (`‖a − b‖ = D_α`), `f* = (a − b)/‖a − b‖`, `t*` the smallest `(1−α)`-quantile of `f*(X)` and `u*` the largest
`α`-quantile of `f*(Y)`. Then `D_α ≤ t* − u* ≤ D_φ`, and the ramp `g*` of `f*` between `u*` and `t*` has
`E_P g* − E_Q g* − α ≥ D_α/(β(t* − u*)) ≥ D_α/(β D_φ)`. -/
def pop_ramp_rkhs : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ Dφ α : ℝ) (a b : H) (t u : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → 0 ≤ α → α < 1 →
    a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α → 0 < Dpop φ P Q α →
    IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) q} t →
    IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α q} u →
      Dpop φ P Q α ≤ t - u ∧ t - u ≤ Dφ ∧
      Dpop φ P Q α / (beta α * (t - u)) ≤
        (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
          (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α ∧
      Dpop φ P Q α / (beta α * Dφ) ≤ Dpop φ P Q α / (beta α * (t - u))

/-- Lemma 1, "Under (A3), therefore, `TV(P,Q) = sup{E_P g − E_Q g}`, the supremum over all ramps `g` of all `f ∈ B_H` between cuts
`t > u`" (least upper bound). -/
def ramp_tv : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
      IsLUB {r : ℝ | ∃ (f : H) (t u : ℝ), ‖f‖ ≤ 1 ∧ u < t ∧
          r = (∫ x, ramp (fun z => ⟪f, φ z⟫_ℝ) t u x ∂P) - ∫ y, ramp (fun z => ⟪f, φ z⟫_ℝ) t u y ∂Q}
        (StatFormal.Distances.tvDist P Q)

/-! ### Lemma 2 (the `eq:fittedramp` paragraph) -/

/-- Lemma 2, the identity: for probability measures and bounded measurable `f`, the constants cancel and
`θ_{P,Q}(f;t,u) − θ_{P',Q'}(f;t,u) = −β[(P − P')(t − f)₊ + (Q − Q')(f − u)₊]`. -/
def crit_identity : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q P' Q' : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure P'] [IsProbabilityMeasure Q'] (α : ℝ) (f : 𝒳 → ℝ) (t u : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      theta P Q α f t u - theta P' Q' α f t u =
        -(beta α) * (((∫ x, max (t - f x) 0 ∂P) - ∫ x, max (t - f x) 0 ∂P') +
          ((∫ y, max (f y - u) 0 ∂Q) - ∫ y, max (f y - u) 0 ∂Q'))

/-- Lemma 2, setting: `θ_n`, the criterion with the empirical measures, is `T(t) − U(u)` (`n, m ≥ 1`). -/
def crit_emp : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (α : ℝ) (f : 𝒳 → ℝ) (t u : ℝ),
    1 ≤ n → 1 ≤ m → Measurable f →
      theta (empirical x) (empirical y) α f t u = critT α (fun i => f (x i)) t - critU α (fun j => f (y j)) u

/-- **Lemma 2** (uniform control of the criterion): for any samples, all `f ∈ B_H` and all `t, u ∈ ℝ`,
`θ(f;t,u) − θ_n(f;t,u) ≥ −βZ`, `Z` the supremum of `thm:twosided` (`lem:hinge` with `ψ = (·)₊`, `r = 1`, `ρ₁ = ρ₂ = κ`); and the
hinge maps are constant outside `[−κ, κ]`: `(P − P_n)(t − f)₊` takes at every `t` a value it takes at some `t₀ ∈ [−κ, κ]`. -/
def crit_uniform : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ) (n m : ℕ)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) (f : H) (t u : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m → ‖f‖ ≤ 1 →
      -(beta α) * hingeZ P Q φ hingePos hingePos 1 κ κ (x, y) ≤
        theta P Q α (fun z => ⟪f, φ z⟫_ℝ) t u -
          (critT α (fun i => ⟪f, φ (x i)⟫_ℝ) t - critU α (fun j => ⟪f, φ (y j)⟫_ℝ) u) ∧
      ∃ t₀ ∈ Icc (-κ) κ, devPop P x (fun z => max (t - ⟪f, φ z⟫_ℝ) 0) = devPop P x (fun z => max (t₀ - ⟪f, φ z⟫_ℝ) 0)

/-! ### Lemma 3 (the `eq:fittedramp` paragraph) and the order statistics -/

/-- **Lemma 3** (near-quantile cuts): for reals `h_1, …, h_n` (`n ≥ 1`) with range `≤ R`, `h'_1, …, h'_m` (`m ≥ 1`) with range
`≤ R'`, and `α ∈ [0,1)`: (a) if `t ∈ [h_(ι⁻(n,1−α)), h_(ι⁺(n,1−α))]` then `T(t') − T(t) ≤ (β/n) R` for every `t'` (so
`max T − T(t) ≤ (β/n)(h_(n) − h_(1))`); (b) if `u ∈ [h'_(ι⁻(m,α)), h'_(ι⁺(m,α))]` then `U(u) − U(u') ≤ (β/m) R'` for every `u'`;
(c) `T` and `U` are Lipschitz with constant `max(1, β − 1)`. -/
def quantile_bracket : Prop :=
  ∀ (n m : ℕ) (α : ℝ) (h : Fin n → ℝ) (h' : Fin m → ℝ) (R R' : ℝ), 0 ≤ α → α < 1 →
    (1 ≤ n → (∀ i j, h i - h j ≤ R) → ∀ t ∈ Icc (ordStat h (rkLo n (1 - α))) (ordStat h (rkHi n (1 - α))),
      ∀ t', critT α h t' - critT α h t ≤ beta α / n * R) ∧
    (1 ≤ m → (∀ i j, h' i - h' j ≤ R') → ∀ u ∈ Icc (ordStat h' (rkLo m α)) (ordStat h' (rkHi m α)),
      ∀ u', critU α h' u - critU α h' u' ≤ beta α / m * R') ∧
    (∀ t t', |critT α h t - critT α h t'| ≤ max 1 (beta α - 1) * |t - t'|) ∧
    (∀ u u', |critU α h' u - critU α h' u'| ≤ max 1 (beta α - 1) * |u - u'|)

/-- Freeze item 3: if `h_i − ε ≤ h̃_i ≤ h_i` for all `i`, then `h_(k) − ε ≤ h̃_(k) ≤ h_(k)` (`1 ≤ k ≤ n`). -/
def order_stat_shift : Prop :=
  ∀ (n : ℕ) (h h' : Fin n → ℝ) (ε : ℝ) (k : ℕ), 1 ≤ k → k ≤ n → (∀ i, h i - ε ≤ h' i ∧ h' i ≤ h i) →
    ordStat h k - ε ≤ ordStat h' k ∧ ordStat h' k ≤ ordStat h k

/-! ### Lemma 4 (`eq:fittedramp`) -/

/-- **Lemma 4** (the fitted ramp), (A1)–(A2): on a fitting sample `(x, y)` (`n, m ≥ 1`), let `(w, v)` minimize `eq:qp`,
`D̂ = ‖Σ w_i φ(x_i) − Σ v_j φ(y_j)‖`, `Z`, `Z⁻` the suprema of `thm:twosided` for these samples, `r = 1/n + 1/m`, and suppose
`βZ⁻ < D_α`. Then `D̂ ≥ D_α − βZ⁻ > 0`, and for all cut points `t, u` satisfying (C) for the own-term values:
`D_φ ≥ t − u ≥ θ(f̂; t, u) ≥ Θ`; if `Θ > 0`, then `t > u` and the ramp `g` of `f̂` has `E_P g − E_Q g − α ≥ Θ/(β D_φ)` (fresh
`X ∼ P`, `Y ∼ Q`, the fitting sample fixed). -/
def fitted_ramp : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ Dφ α : ℝ) (n m : ℕ)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m →
    IsQPMin φ α x y w v → beta α * hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) < Dpop φ P Q α →
      Dpop φ P Q α - beta α * hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) ≤ qpVal φ x y w v ∧
      0 < qpVal φ x y w v ∧
      ∀ t u, CutsC α (ownX φ x y w v) (ownY φ x y w v) t u →
        t - u ≤ Dφ ∧ theta P Q α (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u ≤ t - u ∧
        fitTheta α (Dpop φ P Q α) (hingeZ P Q φ hingePos hingePos 1 κ κ (x, y))
            (hingeZm P Q φ hingePos hingePos 1 κ κ (x, y)) κ Dφ (1 / n + 1 / m) ≤
          theta P Q α (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u ∧
        (0 < fitTheta α (Dpop φ P Q α) (hingeZ P Q φ hingePos hingePos 1 κ κ (x, y))
            (hingeZm P Q φ hingePos hingePos 1 κ κ (x, y)) κ Dφ (1 / n + 1 / m) →
          u < t ∧
          fitTheta α (Dpop φ P Q α) (hingeZ P Q φ hingePos hingePos 1 κ κ (x, y))
              (hingeZm P Q φ hingePos hingePos 1 κ κ (x, y)) κ Dφ (1 / n + 1 / m) / (beta α * Dφ) ≤
            (∫ z, ramp (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u z ∂P) -
              (∫ z, ramp (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u z ∂Q) - α)

/-- Lemma 4, freeze item 5 ("`Θ` increases in `D` and decreases in `β`", used in §5): for `Z, Z⁻, r ≥ 0`, `0 ≤ α ≤ α' < 1` and
`D ≤ D'` with `β(α')Z⁻ < D`: `Θ(α', D) ≤ Θ(α, D')`. -/
def theta_mono : Prop :=
  ∀ (α α' D D' Zp Zm κ Dφ r : ℝ), 0 ≤ α → α ≤ α' → α' < 1 → 0 ≤ Zp → 0 ≤ Zm → 0 ≤ Dφ → 0 ≤ r →
    beta α' * Zm < D → D ≤ D' →
      fitTheta α' D Zp Zm κ Dφ r ≤ fitTheta α D' Zp Zm κ Dφ r

/-! ### Lemma 5 (`eq:betbounds`, first bound) -/

/-- Lemma 5, the Taylor step: for `a ∈ [0,1)` and `x ≥ −a`, `log(1 + x) ≥ x − x²/(2(1−a)²)`. -/
def log_lower : Prop :=
  ∀ a x : ℝ, 0 ≤ a → a < 1 → -a ≤ x → x - x ^ 2 / (2 * (1 - a) ^ 2) ≤ Real.log (1 + x)

/-- **Lemma 5** (power of the betting test): admissible rules and fractions with `λ_k ∈ [0, λ̄]`, `λ̄(1+α) ≤ a < 1`, `λ ≥ 0`,
`ϱ > 0`, and a measurable event `E` on which, for every pair `k`, `λ_k ≥ λ` and `Δ_k − α ≥ ϱ`. Then, with `c_a = 1/(2(1−a)²)`,
`P(E ∩ {max_{t≤N} K_t < 1/δ}) ≤ exp(−(Nλϱ − c_a N λ̄²(1+α)² − L)₊² / (2Nλ̄²))`, `L = log(1/δ)`. -/
def bet_power : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α δ c lo hi a ρ : ℝ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) (E : Set ((Fin n → 𝒳) × (Fin m → 𝒳))),
    IsBatchPairing lx ly bat A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < c → c ≤ 1 →
    IsFitRule lx ly bat g → IsFracRule lx ly bat α c lam →
    (∀ (k : Fin N) x y z, lam k x y z ≤ hi) → hi * (1 + α) ≤ a → a < 1 → 0 ≤ lo → 0 < ρ →
    MeasurableSet E → (∀ ω ∈ E, ∀ k : Fin N, lo ≤ fracAt lam g bat A B ω.1 ω.2 k ∧ α + ρ ≤ condMean P Q g bat ω.1 ω.2 k) →
      sampleLaw P Q n m (E ∩ {ω | ¬ rejects lam g bat A B α δ ω.1 ω.2}) ≤
        ENNReal.ofReal (Real.exp (-(max (N * lo * ρ - 1 / (2 * (1 - a) ^ 2) * N * hi ^ 2 * (1 + α) ^ 2 -
          Real.log (1 / δ)) 0) ^ 2 / (2 * N * hi ^ 2)))

/-- Lemma 5 for `eq:fractions` (`eq:betbounds`, first bound; `λ = λ_N`, `λ̄ = λ̄_N`, `a = λ_max ≤ 1/2`, `σ²_min ∈ (0,4]`),
when `N ≥ L(1+α)²/(2λ_max²)` (so `λ_N = √(L/(2N))`): the bound is at most `ε_N(ϱ)` (which implies the printed form, with
`16L/σ²_min` and `N ≥ 2L/λ_max²`, since `(1+α)² ≤ 4`); and `ε_N(ϱ') → 0` as `N → ∞` uniformly over `ϱ' ≥ ϱ > 0` and over
`0 < L ≤ ηN` for `η` small enough (fixed `δ`, or `L_δ = o(N)`). -/
def bet_power_frac : Prop :=
  (∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α δ lmax s2 ρ : ℝ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) (E : Set ((Fin n → 𝒳) × (Fin m → 𝒳))),
    IsBatchPairing lx ly bat A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → s2 ≤ 4 →
    IsFitRule lx ly bat g → IsFracRule lx ly bat α lmax lam →
    (∀ (k : Fin N) x y z, lam k x y z ≤ lamHi lmax α (Real.log (1 / δ)) s2 N) →
    Real.log (1 / δ) * (1 + α) ^ 2 / (2 * lmax ^ 2) ≤ N →
    MeasurableSet E → (∀ ω ∈ E, ∀ k : Fin N, lamLo lmax α (Real.log (1 / δ)) s2 N ≤ fracAt lam g bat A B ω.1 ω.2 k ∧
      α + ρ ≤ condMean P Q g bat ω.1 ω.2 k) →
      sampleLaw P Q n m (E ∩ {ω | ¬ rejects lam g bat A B α δ ω.1 ω.2}) ≤
        ENNReal.ofReal (epsN s2 α (Real.log (1 / δ)) N ρ)) ∧
  (∀ (s2 α ρ ε : ℝ), 0 < s2 → 0 ≤ α → 0 < ρ → 0 < ε → ∃ η > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L ρ' : ℝ,
    0 < L → L ≤ η * N → ρ ≤ ρ' → epsN s2 α L N ρ' ≤ ε)

/-! ### Lemma 6 (`eq:betbounds`, second bound) -/

/-- **Lemma 6** (strict nulls): if `TV(P,Q) ≤ α − ζ`, `ζ > 0`, and the fractions satisfy `λ_k ∈ [0, λ̄]`, then for every admissible
fitting rule `P(max_{t≤N} K_t ≥ 1/δ) ≤ exp(−2ζ log(1/δ)/λ̄)`. -/
def strict_null : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α δ c hi ζ : ℝ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    IsBatchPairing lx ly bat A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < c → c ≤ 1 →
    IsFitRule lx ly bat g → IsFracRule lx ly bat α c lam → (∀ (k : Fin N) x y z, lam k x y z ≤ hi) →
    0 < ζ → StatFormal.Distances.tvDist P Q ≤ α - ζ →
      sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
        ENNReal.ofReal (Real.exp (-(2 * ζ * Real.log (1 / δ) / hi)))

/-- Lemma 6 for `eq:fractions` (`eq:betbounds`, second bound; `λ̄ = λ̄_N`, cap `λ_cap = λ_max/(1+α)`): the rejection
probability is at most `δ^{2ζ/λ̄_N}`, at most `δ^{2ζ/λ_cap}` and at most `exp(−ζ σ_min √(2 N L))`, `σ_min = √σ²_min`; and
`δ^{2ζ/λ̄_N} ≤ exp(−ζ σ_min √(2 N L))` for `N ≥ 1`. -/
def strict_null_frac : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α δ lmax s2 ζ : ℝ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    IsBatchPairing lx ly bat A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < s2 →
    IsFitRule lx ly bat g → IsFracRule lx ly bat α lmax lam →
    (∀ (k : Fin N) x y z, lam k x y z ≤ lamHi lmax α (Real.log (1 / δ)) s2 N) →
    0 < ζ → StatFormal.Distances.tvDist P Q ≤ α - ζ →
      sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
        ENNReal.ofReal (δ ^ (2 * ζ / lamHi lmax α (Real.log (1 / δ)) s2 N)) ∧
      sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤ ENNReal.ofReal (δ ^ (2 * ζ / (lmax / (1 + α)))) ∧
      sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
        ENNReal.ofReal (Real.exp (-(ζ * √s2 * √(2 * N * Real.log (1 / δ))))) ∧
      (1 ≤ N → δ ^ (2 * ζ / lamHi lmax α (Real.log (1 / δ)) s2 N) ≤
        Real.exp (-(ζ * √s2 * √(2 * N * Real.log (1 / δ)))))

/-! ### The assembly (§5, freeze item 9) -/

/-- Freeze item 9, the down-closed rule (`eq:downclosed`) on a grid: (a) if `α̂_lo > α_{j*} = max{α_j : α_j < a}`, the first level
`α_{i₀} ≥ a` exists and `H_{0,α_{i₀}}` was rejected; (b) if `α̂_lo < α_i`, some `H_{0,α_j}`, `j ≤ i`, was not rejected. -/
def grid_events : Prop :=
  ∀ (J : ℕ) (α : Fin J → ℝ) (rej : Fin J → Prop) (a : ℝ), IsGrid α →
    (gridBelow α a < StatFormal.TrimmedMMD.Lower.alphaLo α rej →
      ∃ i₀, a ≤ α i₀ ∧ (∀ i < i₀, α i < a) ∧ rej i₀) ∧
    (∀ i, StatFormal.TrimmedMMD.Lower.alphaLo α rej < α i → ∃ j ≤ i, ¬ rej j)

/-- Freeze item 9, the mesh inequality: for `a ∈ [0,1)` there is a point of `𝒢 ∪ {0}` in `[a − 2h, a]`, `h` the mesh (so the
largest point of `𝒢 ∪ {0}` in `[0,a]` is `≥ a − 2h`). -/
def mesh_point : Prop :=
  ∀ (J : ℕ) (α : Fin J → ℝ) (a : ℝ), IsGrid α → 0 ≤ a → a < 1 →
    ∃ b ∈ insert 0 (range α), b ≤ a ∧ a - 2 * gridMesh α ≤ b

/-! ### Proposition 1 (`prop:loconsistency`) -/

/-- Proposition 1 (1), upper side, every `n, m`: for every admissible run, every pair `(P,Q)`, `δ ∈ (0,1)`, `λ_max ∈ (0,1]`:
`α̂_lo` is measurable, `P(α̂_lo > α_{j*}) ≤ δ`, `α_{j*} = max{α_j : α_j < TV(P,Q)}`, and, when `TV(P,Q) > 0` is a grid point,
`P(α̂_lo ≥ TV(P,Q)) ≤ δ` (which sharpens `cor:lower`; the NOTE's version without `TV > 0` is false at `TV = 0 ∈ 𝒢`). -/
def lo_upper : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J n m : ℕ) (α : Fin J → ℝ) (δ lmax : ℝ) (R : LoRun 𝒳 J n m),
    IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → R.IsAdmissible α lmax →
      Measurable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => R.alphaLo α δ ω.1 ω.2) ∧
      sampleLaw P Q n m {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < R.alphaLo α δ ω.1 ω.2} ≤
        ENNReal.ofReal δ ∧
      ((∃ j, α j = StatFormal.Distances.tvDist P Q) → 0 < StatFormal.Distances.tvDist P Q →
        sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q ≤ R.alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ)

/-- Proposition 1 (1), lower side, the explicit bound of §5 (and its uniformity): for a run of Proposition 1 with pairs in batches
`≤ B`, `σ²_min ≤ 4`, fitting samples nonempty with `1/n_{<b} + 1/m_{<b} ≤ r`, a grid level `α_i` with `0 < d ≤ D_{α_i}(P,Q)`, `β_* = β(α_i)`, the
size condition (S) `β_* D_φ r ≤ d/8`, `β_*²κ² r ≤ 7d²/64`, and `N ≥ L(1+α_i)²/(2λ_max²)`:
`P(α̂_lo < α_i) ≤ 2B exp(−2(τ_* − μ₁)₊²/(D_φ² r)) + J ε_N(ϱ_*)`, `τ_* = d/(8β_*)`, `μ₁ = 2(1+√2)κ√r`, `ϱ_* = d/(2β_* D_φ)`. -/
def lo_lower_bound : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 : ℝ) (R : LoRun 𝒳 J n m) (Bmax : ℕ) (i : Fin J)
    (d r : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) →
    IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ lmax s2 →
    (∀ k, R.bat k ≤ Bmax) → (∀ k, 1 ≤ fitCard R.lx (R.bat k) ∧ 1 ≤ fitCard R.ly (R.bat k)) →
    (∀ k, 1 / (fitCard R.lx (R.bat k) : ℝ) + 1 / (fitCard R.ly (R.bat k) : ℝ) ≤ r) →
    0 < d → d ≤ Dpop φ P Q (α i) →
    beta (α i) * Dφ * r ≤ d / 8 → beta (α i) ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64 →
    Real.log (1 / δ) * (1 + α i) ^ 2 / (2 * lmax ^ 2) ≤ R.N →
      sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤
        ENNReal.ofReal (2 * Bmax * Real.exp (-(2 * (max (d / (8 * beta (α i)) - 2 * (1 + √2) * κ * √r) 0) ^ 2 /
            (Dφ ^ 2 * r))) + J * epsN s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ)))

/-- Proposition 1 (1), upper side, the explicit strict-null bound of §5: if the first grid level `α_{i₀} ≥ TV(P,Q)` exceeds it by
at least `ζ > 0` (every level `≥ TV` is `≥ TV + ζ`), then for every admissible run whose fractions satisfy `λ_k ≤ λ̄_N`,
`P(α̂_lo > α_{j*}) ≤ δ^{2ζ/λ_max}` and `≤ exp(−ζ σ_min √(2NL))`. -/
def lo_strict_bound : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 ζ : ℝ) (R : LoRun 𝒳 J n m),
    IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < s2 → R.IsAdmissible α lmax →
    (∀ j (k : Fin R.N) x y z, R.lam j k x y z ≤ lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N) →
    0 < ζ → (∀ j, StatFormal.Distances.tvDist P Q ≤ α j → StatFormal.Distances.tvDist P Q + ζ ≤ α j) →
      sampleLaw P Q n m {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < R.alphaLo α δ ω.1 ω.2} ≤
        ENNReal.ofReal (δ ^ (2 * ζ / lmax)) ∧
      sampleLaw P Q n m {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < R.alphaLo α δ ω.1 ω.2} ≤
        ENNReal.ofReal (Real.exp (-(ζ * √s2 * √(2 * R.N * Real.log (1 / δ)))))

/-- Proposition 1 (1) and (2), lower side, in the form without (A3) and with the uniformity: a fixed grid, levels `δ_{n,m} ∈ (0,1)`
with `log(1/δ_{n,m}) = o(min(n,m))` (a fixed `δ` is an instance), runs of Proposition 1 in the asymptotic regime. For every grid
level `α_i` and `d > 0`: `P(α̂_lo < α_i) → 0` as `n, m → ∞`, uniformly over the pairs `(P,Q)` with `D_{α_i}(P,Q) ≥ d`. -/
def lo_lower : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (J : ℕ) (α : Fin J → ℝ) (δ : ℕ → ℕ → ℝ)
    (lmax s2 c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → IsGrid α →
    (∀ n m, 0 < δ n m ∧ δ n m < 1) →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → Real.log (1 / δ n m) ≤ η * (min n m : ℕ)) →
    0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c →
    (∀ n m, (R n m).IsWitnessRun φ α (δ n m) lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) →
      ∀ (i : Fin J) (d : ℝ), 0 < d → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        ∀ (P Q : Measure 𝒳), IsProbabilityMeasure P → IsProbabilityMeasure Q → d ≤ Dpop φ P Q (α i) →
          sampleLaw P Q n m {ω | (R n m).alphaLo α (δ n m) ω.1 ω.2 < α i} ≤ ENNReal.ofReal ε

/-- **Proposition 1** (`prop:loconsistency`), the §9 print block: Assumption `ass:regularity` ((A1)–(A3)), fixed batch fractions
(the asymptotic regime), a fixed grid, fixed `δ`, per-level witnesses with cut points satisfying (C), and `eq:fractions` floored at
a fixed `σ²_min > 0`. Then `P(α̂_lo > α_{j*}) ≤ δ` for all `n, m`; as `n, m → ∞`, `P(α̂_lo < α_{j*}) → 0`; and if `α* = TV(P,Q)`
is not a grid level, also `P(α̂_lo > α_{j*}) → 0`. -/
def lo_consistency : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ) (α : Fin J → ℝ) (δ lmax s2 c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Characteristic φ → IsGrid α →
    0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c →
    (∀ n m, (R n m).IsWitnessRun φ α δ lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) →
      (∀ n m, sampleLaw P Q n m
          {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ) ∧
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
          {ω | (R n m).alphaLo α δ ω.1 ω.2 < gridBelow α (StatFormal.Distances.tvDist P Q)} ≤ ENNReal.ofReal ε) ∧
      ((∀ j, α j ≠ StatFormal.Distances.tvDist P Q) → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
          {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal ε)

/-- Proposition 1 (1), third and fourth bullets, under the hypotheses of `lo_consistency`: if `α*` is not a grid level,
`P(α̂_lo = α_{j*}) → 1`; if `α*` is a grid level (`α* = α_{j*+1}`), `liminf P(α̂_lo = α_{j*}) ≥ 1 − δ`. -/
def lo_exact : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ) (α : Fin J → ℝ) (δ lmax s2 c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Characteristic φ → IsGrid α →
    0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c →
    (∀ n m, (R n m).IsWitnessRun φ α δ lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) →
      ((∀ j, α j ≠ StatFormal.Distances.tvDist P Q) → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
          ENNReal.ofReal (1 - ε) ≤ sampleLaw P Q n m
            {ω | (R n m).alphaLo α δ ω.1 ω.2 = gridBelow α (StatFormal.Distances.tvDist P Q)}) ∧
      ((∃ j, α j = StatFormal.Distances.tvDist P Q) → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
          ENNReal.ofReal (1 - δ - ε) ≤ sampleLaw P Q n m
            {ω | (R n m).alphaLo α δ ω.1 ω.2 = gridBelow α (StatFormal.Distances.tvDist P Q)})

/-- Proposition 1 (2) (vanishing level), (A1)–(A3): if `δ_{n,m} → 0` with `log(1/δ_{n,m}) = o(min(n,m))`, then
`P(α̂_lo = α_{j*}) → 1` in all cases (fixed grid). -/
def lo_vanishing : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ) (α : Fin J → ℝ) (δ : ℕ → ℕ → ℝ) (lmax s2 c C0 : ℝ) (Bmax : ℕ)
    (R : ∀ n m : ℕ, LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Characteristic φ → IsGrid α →
    (∀ n m, 0 < δ n m ∧ δ n m < 1) →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → δ n m ≤ η ∧ Real.log (1 / δ n m) ≤ η * (min n m : ℕ)) →
    0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c →
    (∀ n m, (R n m).IsWitnessRun φ α (δ n m) lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) →
      ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        ENNReal.ofReal (1 - ε) ≤ sampleLaw P Q n m
          {ω | (R n m).alphaLo α (δ n m) ω.1 ω.2 = gridBelow α (StatFormal.Distances.tvDist P Q)}

/-- Proposition 1 (3) (refining grid), (A1)–(A3): grids `𝒢_{n,m}` fixed in advance with mesh `h_{n,m} → 0` and
`log|𝒢_{n,m}| = o(min(n,m))`; levels `δ_{n,m}` eventually `≤ δ̄ < 1` with `log(1/δ_{n,m}) = o(min(n,m))` (a fixed `δ`, or `δ_{n,m}` as
in (2)). Then `α̂_lo → α* = TV(P,Q)` in probability. -/
def lo_refining : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ : ℕ → ℕ → ℝ) (δbar lmax s2 c C0 : ℝ)
    (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Characteristic φ →
    (∀ n m, IsGrid (α n m)) →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → gridMesh (α n m) ≤ η ∧ Real.log (J n m) ≤ η * (min n m : ℕ)) →
    (∀ n m, 0 < δ n m ∧ δ n m < 1) → δbar < 1 →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → δ n m ≤ δbar ∧ Real.log (1 / δ n m) ≤ η * (min n m : ℕ)) →
    0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c →
    (∀ n m, (R n m).IsWitnessRun φ (α n m) (δ n m) lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) →
      ∀ ε > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        sampleLaw P Q n m {ω | ε < |(R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 - StatFormal.Distances.tvDist P Q|} ≤
          ENNReal.ofReal η

/-- Proposition 1 (3) without (A3) ("every lower statement holds with `α*_k` in place of `α*`, every upper statement with
`α* = TV`"), under the hypotheses of `lo_refining` without `Characteristic φ`: for every `a` with `D_a(P,Q) > 0` (every
`a < α*_k`), `P(α̂_lo < a − ε) → 0`; and `P(α̂_lo > TV(P,Q) + ε) → 0`. -/
def lo_refining_kernel : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ : ℕ → ℕ → ℝ) (δbar lmax s2 c C0 : ℝ)
    (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) →
    (∀ n m, IsGrid (α n m)) →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → gridMesh (α n m) ≤ η ∧ Real.log (J n m) ≤ η * (min n m : ℕ)) →
    (∀ n m, 0 < δ n m ∧ δ n m < 1) → δbar < 1 →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → δ n m ≤ δbar ∧ Real.log (1 / δ n m) ≤ η * (min n m : ℕ)) →
    0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c →
    (∀ n m, (R n m).IsWitnessRun φ (α n m) (δ n m) lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) →
      (∀ a, 0 ≤ a → a < 1 → 0 < Dpop φ P Q a → ∀ ε > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        sampleLaw P Q n m {ω | (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 < a - ε} ≤ ENNReal.ofReal η) ∧
      (∀ ε > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q + ε < (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2} ≤
          ENNReal.ofReal η)

/-! ### Lemma 7 and Proposition 3 (C.5, "A witness fitted at α = 0") -/

/-- **Lemma 7** (ramps of a fixed direction), with the layer-cake identity: for measurable `f` and cuts `t > u`,
`E_P g − E_Q g = ∫_0^1 {P(f > u + λ(t−u)) − Q(f > u + λ(t−u))} dλ ≤ KS⁺(f)`; and more generally
`E_P h(f) − E_Q h(f) ≤ KS⁺(f)` for every nondecreasing `h : ℝ → [0,1]`. -/
def ramp_ks : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (f : 𝒳 → ℝ),
    Measurable f →
      (∀ t u : ℝ, u < t →
        (∫ x, ramp f t u x ∂P) - (∫ y, ramp f t u y ∂Q) =
          ∫ s in (0 : ℝ)..1, (P.real {z | u + s * (t - u) < f z} - Q.real {z | u + s * (t - u) < f z}) ∧
        (∫ x, ramp f t u x ∂P) - (∫ y, ramp f t u y ∂Q) ≤ ksPlus P Q f) ∧
      ∀ h : ℝ → ℝ, Monotone h → (∀ s, h s ∈ Icc (0 : ℝ) 1) →
        (∫ x, h (f x) ∂P) - (∫ y, h (f y) ∂Q) ≤ ksPlus P Q f

/-- **Proposition 3**, the example (finite certificate): for the Gaussian kernel with `σ = 1` on `ℝ` and the laws `exP`, `exQ`,
both are probability measures, `α* = TV(P,Q) = 0.6`, `MMD(P,Q) > 0`, `KS⁺(f_0) = 0.4` for `f_0 = (μ_P − μ_Q)/MMD(P,Q)`, and hence
every ramp `g` of `f_0` has `E_P g − E_Q g ≤ 0.4`. -/
def alpha0_example : Prop :=
  IsProbabilityMeasure exP ∧ IsProbabilityMeasure exQ ∧ StatFormal.Distances.tvDist exP exQ = 3 / 5 ∧
    0 < mmdGauss exP exQ ∧ ksPlus exP exQ (exWitness exP exQ) = 2 / 5 ∧
    ∀ t u : ℝ, u < t →
      (∫ x, ramp (exWitness exP exQ) t u x ∂exP) - (∫ y, ramp (exWitness exP exQ) t u y ∂exQ) ≤ 2 / 5

/-- **Proposition 3**, the validity bound for the variant: if at every batch `b` the ramp is `g_b = h ∘ f_b` for a direction `f_b`
fitted on the earlier batches (jointly measurable) and any nondecreasing `h : ℝ → [0,1]` (any cut points), then for every pair
`(P,Q)` the certificate rejects `H_{0,α}` with probability at most `δ + P(max_b KS⁺(f_b) > α)`. -/
def alpha0_valid : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α δ c : ℝ) (F g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    IsBatchPairing lx ly bat A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < c → c ≤ 1 →
    IsFitRule lx ly bat g → IsFracRule lx ly bat α c lam →
    (∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => F (bat k) p.1.1 p.1.2 p.2) →
    (∀ (k : Fin N) x x' y y', (∀ i, lx i < bat k → x i = x' i) → (∀ j, ly j < bat k → y j = y' j) →
      F (bat k) x y = F (bat k) x' y') →
    (∀ (k : Fin N) x y, ∃ h : ℝ → ℝ, Monotone h ∧ (∀ s, h s ∈ Icc (0 : ℝ) 1) ∧ g (bat k) x y = fun z => h (F (bat k) x y z)) →
      sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
        ENNReal.ofReal δ + sampleLaw P Q n m {ω | ∃ k : Fin N, α < ksPlus P Q (F (bat k) ω.1 ω.2)}

end Claims
end StatFormal.Wave30tz
