import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.ICL.Statements
import StatFormal.Archive.ICL.Cond.Statements
import StatFormal.Archive.ICL.Diag.Statements
import StatFormal.Archive.NNFibers.Wave1.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# FROZEN STATEMENTS — wave 12c (QUEUE rows 107–110): TM `thm:trimconsist`; ICL `thm:cond-dev`,
# `lem:cond-curvature`; NN `prop:exp-ident`

Sources (verbatim in `lean-formalisation/inventory/extracted/trimmed-mmd.md`, `context-distribution-icl.md`,
`proliferation-nns.md`; current text after the 2026-10-13/14 corrections):
* TM `thm:trimconsist` (`trimmed-mmd/paper.tex:1605-1641`, proof `supplement.tex:953-1035`, `rem:trimmeas`
  `:1037-1044`), with the set-up paragraph (`paper.tex:1583-1604`: `d*`, `t_α`, `eq:popdensity`, `A*`, `Â_n`,
  `k_n = ⌊n(1−α)⌋`, `ĝ_n`), `eq:etadef` and `prop:witnessstab` (`:1536-1570`), `prop:bangbang`(ii), `eq:region`
  and `ass:regularity`.
* ICL `thm:cond-dev` (`context-distribution-ICL/paper/v3/sections/06b_cond_theory.tex:32-51`, with `J_m`,
  `J_pool` at `:29-30`), proofs `supp/proofs_conditional.tex:327-345` ((i)) and `:376-416` ((ii)), the
  conventions `:21-55` (`eq:cond-center`, the internal-net bound `(1+2r/ε)^p`, `G`, `G^iid`, `𝓗`, `𝓗^iid`,
  `0 ≤ KL(w|u_n) ≤ log n`) and the frozen `lem:cond-osc`.
* ICL `lem:cond-curvature` (`supp/proofs_conditional.tex:163-221`), with `κ_M = binom(M,2)^{1/2}` (`:161`) and
  `‖ν‖_TV = |ν|(𝒵)` (`:33-35`).
* NN `prop:exp-ident` (`proliferation-and-geometry-in-nns/paper_revised.tex:382-406`), with `eq:net`,
  `ass:UA` (`:348-352`), `ρ` and functional minimality (`:354-363`), `ass:ident` (`:368-374`) and the sentence
  after it (`:376-379`: `ass:ident` fails for sigmoid, `tanh`, softplus and ReLU).
Reuses the frozen `Wave4b` (`etaNM`, `witness`), `TrimmedMMD` (`rn`), `TrimmedMMD/Concentration` (`region`),
`TrimmedMMD/BangBang` (`ord`, `kfloor`, `capped`, `qp`), `TrimmedMMD/Projection` (`IsMinNorm`), `ICL` (`Grisk`,
`InDeltaM`), `ICL/Cond` (`iidLaw`), `ICL/Diag` (`klUnif`), `NNFibers/Wave1` (`net`, `FunctionallyMinimal`,
`AssIdent`, `Generated`, `InLam`) statements and `Distances.tvDist` (already locked through the frozen `ZeroSet`
statements, imported via `Wave4b`), imported, not copied. No `Foundations` library file is imported directly.

Covered:
* `thm:trimconsist`: `trimconsist` (under `(Q)`, on one measurable event of probability `≥ 1 − δ`, provided
  `η < D` and `Λ_n ≤ ρ`: `|t̂_n − t_α| ≤ Λ_n`, `Â_n △ A* ⊆ {|d* − t_α| ≤ Λ_n}`, `P(Â_n △ A*) ≤ 2C_fΛ_n` and
  `∫|ĝ_n − g*| dP ≤ 2C_fΛ_n/(1−α)`, every empirical witness, every tie weight); `trimconsist_lower` (the first two
  statements "persist verbatim" under the lower density bound alone).
* `thm:cond-dev`: `cover_ball` (the internal-net bound `(1+2r/ε)^p` of the conventions, any finite-dimensional
  real normed space); `cond_dev_i_swor`, `cond_dev_i_iid` ((i), without-replacement and i.i.d. contexts);
  `cond_dev_ii_swor`, `cond_dev_ii_iid` ((ii), the gated mixture of context laws, simultaneously for all `η > 0`
  and all internal `η`-nets of the gate class).
* `lem:cond-curvature`: `curv_kl_finite` (`KL(μ_t|P₀) < ∞` on `[0,1]`, so `h` is real-valued), `curv_continuous`,
  `curv_twice_diff`, `curv_second` (`h'' ≥ (λ − κ_M B_L) ∫ u_t² dμ_t`, with `u_t² ∈ L¹(μ_t)`), `curv_chord`.
* `prop:exp-ident`: `exp_UA` (`exp` is continuous, `C¹` and not a polynomial), `exp_ident` (`ass:ident` holds for
  every functionally minimal `θ*_q` and every `m ≥ q`), `exp_exhaust` (hence `Λ^m_q = F^m_q`, the frozen
  `lem:exhaust` for `σ = exp`), and the sentence after `ass:ident`: `ident_fails_tanh`, `ident_fails_sigmoid`,
  `ident_fails_relu`, `ident_fails_softplus`.

Not covered (declared):
* `thm:trimconsist`: the rates `Λ_n = O((n∧m)^{-1/4})`, `O_P((n∧m)^{-1/4})`, and "both quantities tend to `0` in
  probability, but without a rate" under the lower bound alone; the Step-0 reading of `Â_n` as the kept set of
  every empirical optimum (`prop:bangbang`(ii), certified separately; here `Â_n` is the printed definition).
* `thm:cond-dev`: the "countable dense subset" measurability remarks are not statements (the claims give measurable
  events directly); the paragraph after the theorem (mixture of weights, `prop:cond-weight-mixing`) and the
  metric-retrieval constants (frozen `lem:cond-metric`).
* `lem:cond-curvature`: nothing beyond the encoding choices below.
* `prop:exp-ident`: `rmk:symmetry-factor` (frozen `NNFibers.Claims.symmetry_factor_false`); "universal approximator"
  in `ass:UA` (a citation).

Encodings (see card):
* `thm:trimconsist`: frozen `witnessstab` setting (`H` real separable Hilbert, `φ` strongly measurable with
  `‖φ‖ ≤ κ`, measurable singletons, samples `(X, Y) ∼ P^{⊗n} ⊗ Q^{⊗m}`, `β = α`). `d*` is any `IsMinNorm` element
  of `𝒞_{α,k}(P) − 𝒞_{α,k}(Q)` and `D = ‖d*‖`; `d(x) = ⟨d, φ(x)⟩` (`witFn`); the empirical witness is the frozen
  `witness` at any minimiser of `qp` over the capped simplices. `t_α = inf{t : F(t) ≥ 1 − α}` (`quantileAt`, real
  `sInf`: the set is nonempty and bounded below because `|d*(x)| ≤ κ‖d*‖` and `0 < 1 − α < 1`; `(Q)` forces
  `α ≥ c_f ρ > 0`). `(Q)` is `QDensity`: a measurable `f` with `c_f ≤ f ≤ C_f` on `I` and
  `P(d* ∈ A) = ∫_A f` for every Borel `A ⊆ I` (no `Measure.map`). `η = r_n(α,δ/3) + r_m(α,δ/3)` (`etaTC`),
  `ζ`, `Λ_n` (`zetaTC`, `lamTC`) as printed. `t̂_n = d̂_{(k_n+1)}` is the frozen `ord` at index `k_n` (0-based;
  `k_n < n` since `α > 0`, so no junk). `Â_n = {d̂ < t̂_n}`, `A* = {d* < t_α}`. The tie weights `γ` of `g*` and `γ̂`
  of `ĝ_n` are arbitrary in `[0, 1/(1−α)]` (`plugDensity`; the paper's `γ` fixing `E_P g* = 1` is one of them — a
  generalisation). `P(Â_n △ A*)` is in `ℝ≥0∞`; `∫|ĝ_n − g*| dP` is a Bochner integral of a bounded measurable
  function. "Fix `α < α*`" is dropped: it only serves `D > 0`, which `η < D` already gives (generalisation).
  "With probability `≥ 1 − δ`" is a measurable event of measure `≥ 1 − δ`.
* `thm:cond-dev`: conditionally on the pool, i.e. pool indices `Fin n` with the context loss abstracted:
  `L z S = L(z; z_S)` for `M`-subsets `S` (without replacement) and `L z j = L(z; z_j)` for index tuples
  `j : Fin M → Fin n` (i.i.d.), measurable in the query `z`, values in `[0, B_L]` (any pool loss is of this form —
  a generalisation; symmetry is not needed). Validation points `z̃ ∼ P₀^{⊗m}` on a measurable space `𝒵`;
  `J_m = m⁻¹ Σ f(z̃_i)`, `J_pool = ∫ f dP₀` (`empRisk`, `poolRisk`). `G = Grisk` (frozen CPS risk), `G^iid = Giid`
  (frozen `iidLaw`). Weights may depend on the whole query `z` (the paper's dependence through `x` is a special
  case). "sup" is "for every parameter" (no `sSup` junk). (i): `Θ ⊆` a closed Euclidean ball of radius `r_Θ` in
  `EuclideanSpace ℝ (Fin p)`, weights positive, summing to one, measurable in `z`, with the printed log-Lipschitz
  condition; `λ = 0`, `λ_cov = 0`, mean risk (so `f = G`). (ii): gates `g(z;γ) ∈ Δ^{R−1}`, measurable in `z`,
  continuous in `γ`, `Γ` a separable topological space that is also first countable (**added**, see the
  critic notes); components `w_r ∈ Δ^(M)` (frozen `InDeltaM`) without replacement, `w_r ∈ Δ^{n−1}` for i.i.d.; `f = Σ_r g_r(z;γ)[G(z;w_r) + λ KL(w_r|u_n)]` (frozen `klUnif`), `λ ≥ 0`,
  `B = B_L + λ log n`. `N_𝒢(η)` is encoded by quantifying over every internal `η`-net `N` (a `Finset Γ` with
  `sup_z ‖g(z;γ) − g(z;γ')‖₁ ≤ η` for some `γ' ∈ N`, every `γ`), with `log |N|` in the bound — equivalent to the
  minimal cardinality, and vacuous (as the printed `+∞` bound) when no finite net exists.
  `ℓ_n = M log(2en/M)`, resp. `M log(2n)`. `1 ≤ M ≤ n` and `1 ≤ m` are made explicit (implicit in the
  setting: `n ≥ M` is printed, `M ≥ 1` contexts, `m ≥ 1` validation points). `cover_ball` needs `r ≥ 0`.
* `lem:cond-curvature`: `𝒵` any measurable space (compactness and continuity of `L` are not used —
  generalisation); fixing `x`, `L̄_x` is any measurable `L̄ : 𝒵^M → [0, B_L]`. `μ_t = (1−t)μ₀ + tμ₁` (`mixAt`, `ℝ≥0`
  weights), `KL` is Mathlib's `klDiv` and `h(t) = ∫ L̄ dμ_t^{⊗M} + λ KL(μ_t|P₀).toReal` (`hCurv`; `curv_kl_finite`
  certifies that `toReal` never meets `⊤`). "Twice differentiable on `(0,1)`" is `DifferentiableAt h t ∧
  DifferentiableAt (deriv h) t`, and `h''(t) = deriv (deriv h) t`. `u_t = dσ/dμ_t` is any `μ_t`-integrable `u` with
  `μ₁(A) − μ₀(A) = ∫_A u dμ_t` for every measurable `A`. `‖σ‖_TV = |σ|(𝒵) = 2 tvDist(μ₀, μ₁)` (frozen `tvDist`,
  `sup_A |μ₀(A) − μ₁(A)|`). `κ_M = √binom(M,2)` (`kappaM`).
* `prop:exp-ident`: frozen `NNFibers/Wave1` encodings (`θ : Fin m → (ℝ^{d_in} × ℝ^{d_out})`, `θ ∼ θ*` = equality of
  `net` on all of `ℝ^{d_in}`, `ass:ident` = `AssIdent`, compositions = the inductive closure `Generated`). `ass:UA`
  for `exp`: `Continuous`, `ContDiff ℝ 1`, and no real polynomial agrees with `exp` everywhere. The refutations
  use `d_in = d_out = 1`, `q = 1`, `θ* = (ω = 1, a = 1)` (functionally minimal) and a fiber point that is not
  `Generated`: `tanh` at `m = 1` (`(−1,−1)`), sigmoid at `m = 2` (`(−1,−1),(0,2)`), ReLU at `m = 1` (`(2, ½)`); for softplus
  (`log(1 + e^u)`, odd part `u`) the representative is `θ* = ((1,1),(−1,−1))` (`oddRep`, `q = 2`, `f = x`) and the
  fiber point at `m = 2` is `((2,½),(−2,−½))`.

Critic notes:
* `thm:trimconsist`: dropping `α < α*` changes nothing (`η < D` gives `D > 0`, which is equivalent to `α < α*`
  by the frozen `eq:zeroeq`). The proof here replaces the Dvoretzky–Kiefer–Wolfowitz event by two one-sided Hoeffding
  bounds at the deterministic points `t_α ± (s_n + 1/n)/c_f` (each at level `δ/6`), which give the same `s_n` and
  `log(6/δ)`; this is the queue note's "DKW not needed". The constant `2κζ` in `Λ_n` is exactly what Steps 2–3 use
  (`Δ + ε ≤ 2κζ + (s_n + 1/n)/c_f`).
* `thm:cond-dev`(i): the proof's grid argument gives `B_L/√m` for the discretisation term (the printed `2B_L/√m` is
  a valid, loose upper bound); the union bound runs over `2|Θ_η|` one-sided Hoeffding events. (ii): symmetrisation,
  Massart and McDiarmid are applied to the centred class `f − B/2` over the countable class `Γ₀ × 𝓗̃^R` (`Γ₀` dense
  countable), using that `(P_m − P₀)` is additive over the `R` components and linear in each, so the supremum over
  `conv(𝓗̃)^R` is attained at vertices; the centred class gives the printed bound with room to spare.
  **Added hypothesis** `[FirstCountableTopology Γ]` in (ii): the proof's reduction to a countable dense `Γ₀`
  ("each such map is continuous in `γ` by dominated convergence") is a sequential argument and is not available
  for a merely separable `Γ` (dominated convergence fails for nets); every separable metrizable `Γ`, in particular
  the Euclidean gate parameters `(c_r, τ)` of `thm:cond-consistency`(ii), qualifies. Critic (2026-10-14): the step
  at `proofs_conditional.tex:413-415` does fail for separable non-first-countable `Γ`: `𝒵 = [0,1]`, `P₀` Lebesgue,
  `R = 2`, gates `γ, 1 − γ`, `Γ = 𝒲 ∪ {1_F : F finite} ⊂ {0,1}^{[0,1]}` (product topology, `𝒲` countable dense):
  the countable-sup reduction breaks, although the theorem's bound itself is not refuted. Suggested fix: "`Γ`
  separable metric" (or first countable), or require every `N_𝒢(η) < ∞`. To DEFECTS as S2/S3.
* `lem:cond-curvature` holds as printed.
* `prop:exp-ident` holds as printed. The sentence after `ass:ident` is certified for all four activations, without
  biases: `tanh`, sigmoid (`σ(u) = 1/(1+e^{−u})`) and ReLU at `θ* = (1,1)`, and softplus at the functionally minimal
  `θ* = ((1,1),(−1,−1))` (net `x`, by `softplus(u) − softplus(−u) = u`; a width-1 net `a·softplus(ωx)` would need
  `a log 2 = 0` at `x = 0`), whose fiber contains `((2,½),(−2,−½))` (critic, 2026-10-14; the earlier draft's claim
  that softplus needs a bias was wrong).
* No statement looks wrong; no refutation of the four items was needed (the `tanh`/sigmoid/ReLU/softplus claims certify
  the paper's own negative sentence after `ass:ident`, with witnesses inside the standing setting).
* Proof routes: `Wave12c/Route{TrimConsist,Cover,CondDev,CondDevII,Curvature,ExpIdent}.lean`, all 19 claims
  (collected in `Wave12c/Proofs.lean`), standard axioms `propext, Classical.choice, Quot.sound` only.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Finset InformationTheory
open scoped ENNReal NNReal InnerProductSpace Pointwise

namespace StatFormal.Wave12c

/-! ### TM `thm:trimconsist` -/

section Trim

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The witness function `d(x) = ⟨d, φ(x)⟩_𝓗`. -/
def witFn (d : H) (φ : 𝒳 → H) (x : 𝒳) : ℝ := ⟪d, φ x⟫_ℝ

/-- The (lower) `p`-quantile `inf{t : P(f ≤ t) ≥ p}` of `f` under `P`. -/
def quantileAt (P : Measure 𝒳) (f : 𝒳 → ℝ) (p : ℝ) : ℝ :=
  sInf {t : ℝ | p ≤ P.real {x | f x ≤ t}}

/-- `(Q)`: the law of `f` under `P` has a density `g` on `I = [t − ρ, t + ρ]` with `c_f ≤ g ≤ C_f` on `I`. -/
def QDensity (P : Measure 𝒳) (f : 𝒳 → ℝ) (t ρ cf Cf : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, Measurable g ∧ (∀ s ∈ Icc (t - ρ) (t + ρ), cf ≤ g s ∧ g s ≤ Cf) ∧
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - ρ) (t + ρ) →
      P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s)

/-- `(Q)` weakened to the lower density bound alone. -/
def QDensityLower (P : Measure 𝒳) (f : 𝒳 → ℝ) (t ρ cf : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, Measurable g ∧ (∀ s ∈ Icc (t - ρ) (t + ρ), cf ≤ g s) ∧
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - ρ) (t + ρ) →
      P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s)

/-- `η` of the theorem: `eq:etadef` with `δ/3` in place of `δ/2`, `β = α`. -/
def etaTC (κ α δ : ℝ) (n m : ℕ) : ℝ :=
  StatFormal.TrimmedMMD.rn κ α (δ / 3) n + StatFormal.TrimmedMMD.rn κ α (δ / 3) m

/-- `ζ_{n,m} = η + √(2ηD + η²)`. -/
def zetaTC (η D : ℝ) : ℝ := η + √(2 * η * D + η ^ 2)

/-- `Λ_n = 2κζ + c_f⁻¹(√(log(6/δ)/(2n)) + 1/n)`. -/
def lamTC (κ ζ cf δ : ℝ) (n : ℕ) : ℝ :=
  2 * κ * ζ + 1 / cf * (√(Real.log (6 / δ) / (2 * n)) + 1 / n)

/-- `eq:popdensity` at a witness `f` and threshold `t`: `(1−α)⁻¹ 1{f < t} + γ 1{f = t}`. -/
def plugDensity (α γ : ℝ) (f : 𝒳 → ℝ) (t : ℝ) (x : 𝒳) : ℝ :=
  if f x < t then 1 / (1 - α) else if f x = t then γ else 0

/-- `t̂_n = d̂_{(k_n+1)}`, the `(k_n+1)`-th smallest of `d̂(X_1), …, d̂(X_n)`, `k_n = ⌊n(1−α)⌋`. -/
def tHat {n : ℕ} (φ : 𝒳 → H) (d : H) (α : ℝ) (x : Fin n → 𝒳) : ℝ :=
  StatFormal.TrimmedMMD.BangBang.ord (fun i => witFn d φ (x i)) (StatFormal.TrimmedMMD.BangBang.kfloor n α)

end Trim

/-! ### ICL `thm:cond-dev` -/

section CondDev

variable {𝒵 : Type*} [MeasurableSpace 𝒵]

/-- `J_m = m⁻¹ Σ_i f(z̃_i)`. -/
def empRisk {m : ℕ} (f : 𝒵 → ℝ) (zt : Fin m → 𝒵) : ℝ := (1 / (m : ℝ)) * ∑ i, f (zt i)

/-- `J_pool = ∫ f dP₀`. -/
def poolRisk (P0 : Measure 𝒵) (f : 𝒵 → ℝ) : ℝ := ∫ z, f z ∂P0

/-- `G^iid(w) = Σ_{j ∈ [n]^M} Π_k w_{j_k} L(j)`. -/
def Giid {n : ℕ} (w : Fin n → ℝ) (M : ℕ) (L : (Fin M → Fin n) → ℝ) : ℝ :=
  ∑ j, StatFormal.ICL.Cond.iidLaw w M j * L j

/-- Risk plus penalty of the gated mixture of context laws, without replacement:
`f(z) = Σ_r g_r(z;γ) [G(z; w_r) + λ KL(w_r | u_n)]`. -/
def fGateSwor {Γ : Type*} {n R : ℕ} (M : ℕ) (g : 𝒵 → Γ → Fin R → ℝ) (L : 𝒵 → Finset (Fin n) → ℝ)
    (lam : ℝ) (γ : Γ) (W : Fin R → Fin n → ℝ) (z : 𝒵) : ℝ :=
  ∑ r, g z γ r * (StatFormal.ICL.Grisk (W r) M (L z) + lam * StatFormal.ICL.Diag.klUnif n (W r))

/-- The same with i.i.d. contexts `w_r^{⊗M}`. -/
def fGateIid {Γ : Type*} {n M R : ℕ} (g : 𝒵 → Γ → Fin R → ℝ) (L : 𝒵 → (Fin M → Fin n) → ℝ) (lam : ℝ)
    (γ : Γ) (W : Fin R → Fin n → ℝ) (z : 𝒵) : ℝ :=
  ∑ r, g z γ r * (Giid (W r) M (L z) + lam * StatFormal.ICL.Diag.klUnif n (W r))

/-- `N` is an internal `η`-net of the gate class in `sup_z ‖·‖₁`. -/
def IsGateNet {Γ : Type*} {R : ℕ} (g : 𝒵 → Γ → Fin R → ℝ) (η : ℝ) (N : Finset Γ) : Prop :=
  ∀ γ, ∃ γ' ∈ N, ∀ z, ∑ r, |g z γ r - g z γ' r| ≤ η

/-- `ℓ_n = M log(2en/M)` (without replacement). -/
def ellSwor (n M : ℕ) : ℝ := M * Real.log (2 * Real.exp 1 * n / M)

/-- `ℓ_n = M log(2n)` (i.i.d. contexts). -/
def ellIid (n M : ℕ) : ℝ := M * Real.log (2 * n)

/-- The bound of `thm:cond-dev`(i). -/
def devBoundI (BL rΘ Λ δ : ℝ) (p M m : ℕ) : ℝ :=
  2 * BL / √(m : ℝ) +
    BL * √((p * Real.log (1 + 2 * rΘ * Λ * M * √(m : ℝ)) + Real.log (2 / δ)) / (2 * m))

/-- The bound of `thm:cond-dev`(ii) at `η` and net size `N`, with `B` and `ℓ_n`. -/
def devBoundII (B ℓ η δ : ℝ) (R N m : ℕ) : ℝ :=
  B * η + 2 * B * √(2 * (R * ℓ + Real.log N + Real.log 2) / m) + B * √(Real.log (1 / δ) / (2 * m))

end CondDev

/-! ### ICL `lem:cond-curvature` -/

section Curvature

variable {𝒵 : Type*} [MeasurableSpace 𝒵]

/-- `μ_t = (1−t)μ₀ + tμ₁`. -/
def mixAt (μ0 μ1 : Measure 𝒵) (t : ℝ) : Measure 𝒵 := (1 - t).toNNReal • μ0 + t.toNNReal • μ1

/-- `h(t) = ∫ L̄ dμ_t^{⊗M} + λ KL(μ_t | P₀)`. -/
def hCurv {M : ℕ} (Lbar : (Fin M → 𝒵) → ℝ) (lam : ℝ) (P0 μ0 μ1 : Measure 𝒵) (t : ℝ) : ℝ :=
  ∫ x, Lbar x ∂(Measure.pi fun _ : Fin M => mixAt μ0 μ1 t) + lam * (klDiv (mixAt μ0 μ1 t) P0).toReal

/-- `κ_M = binom(M,2)^{1/2}`. -/
def kappaM (M : ℕ) : ℝ := √(M.choose 2 : ℝ)

end Curvature

/-! ### NN: the activations of the sentence after `ass:ident` -/

/-- The logistic sigmoid `σ(u) = 1/(1 + e^{−u})`. -/
def sigmoid (u : ℝ) : ℝ := 1 / (1 + Real.exp (-u))

/-- ReLU `u ↦ max(u, 0)`. -/
def relu (u : ℝ) : ℝ := max u 0

/-- Softplus `u ↦ log(1 + e^u)`. -/
def softplus (u : ℝ) : ℝ := Real.log (1 + Real.exp u)

/-- The width-two representative `θ* = ((1,1),(−1,−1))` (`d_in = d_out = 1`); its softplus net is `x`. -/
def oddRep : Fin 2 → StatFormal.NNFibers.Wave1.Neuron 1 1 :=
  ![(fun _ => 1, fun _ => 1), (fun _ => -1, fun _ => -1)]

/-- The width-one representative `θ* = (ω = 1, a = 1)` with `d_in = d_out = 1`. -/
def unitRep : Fin 1 → StatFormal.NNFibers.Wave1.Neuron 1 1 := fun _ => (fun _ => 1, fun _ => 1)

namespace Claims

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection
  StatFormal.NNFibers.Wave1

/-! ### TM `thm:trimconsist` -/

/-- `thm:trimconsist`, under `(Q)`: on one measurable event of probability `≥ 1 − δ`, provided `η < D` and
`Λ_n ≤ ρ`, every empirical witness `d̂` and all tie weights `γ, γ̂ ∈ [0, (1−α)⁻¹]` satisfy `eq:trimrate` and
`∫|ĝ_n − g*| dP ≤ 2C_fΛ_n/(1−α)`. -/
def trimconsist : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H)
    (κ α δ ρ cf Cf : ℝ) (n m : ℕ) (dstar : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 →
    IsMinNorm (region φ α P - region φ α Q) dstar →
    0 < ρ → 0 < cf →
    QDensity P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf Cf →
    etaTC κ α δ n m < ‖dstar‖ →
    lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n ≤ ρ →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (pr : (Fin n → ℝ) × (Fin m → ℝ)) (γ γh : ℝ),
          pr ∈ capped n α ×ˢ capped m α →
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
          0 ≤ γ → γ ≤ 1 / (1 - α) → 0 ≤ γh → γh ≤ 1 / (1 - α) →
          let dh := StatFormal.Wave4b.witness φ z.1 z.2 pr
          let tα := quantileAt P (witFn dstar φ) (1 - α)
          let th := tHat φ dh α z.1
          let Λ := lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n
          |th - tα| ≤ Λ ∧
          symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα} ⊆
            {x | |witFn dstar φ x - tα| ≤ Λ} ∧
          P (symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα}) ≤
            ENNReal.ofReal (2 * Cf * Λ) ∧
          ∫ x, |plugDensity α γh (witFn dh φ) th x - plugDensity α γ (witFn dstar φ) tα x| ∂P ≤
            2 * Cf * Λ / (1 - α)}

/-- `thm:trimconsist`, last sentence: under the lower density bound alone, the first two statements of
`eq:trimrate` persist verbatim. -/
def trimconsist_lower : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H)
    (κ α δ ρ cf : ℝ) (n m : ℕ) (dstar : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 →
    IsMinNorm (region φ α P - region φ α Q) dstar →
    0 < ρ → 0 < cf →
    QDensityLower P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf →
    etaTC κ α δ n m < ‖dstar‖ →
    lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n ≤ ρ →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ pr : (Fin n → ℝ) × (Fin m → ℝ),
          pr ∈ capped n α ×ˢ capped m α →
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
          let dh := StatFormal.Wave4b.witness φ z.1 z.2 pr
          let tα := quantileAt P (witFn dstar φ) (1 - α)
          let th := tHat φ dh α z.1
          let Λ := lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n
          |th - tα| ≤ Λ ∧
          symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα} ⊆
            {x | |witFn dstar φ x - tα| ≤ Λ}}

/-! ### ICL `thm:cond-dev` -/

/-- Conventions of `supp/proofs_conditional.tex`: a subset of a ball of radius `r` in a `p`-dimensional real
normed space has an internal `ε`-net with at most `(1 + 2r/ε)^p` points. -/
def cover_ball : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : Set E) (c : E)
    (r ε : ℝ), 0 ≤ r → 0 < ε → A ⊆ Metric.closedBall c r →
      ∃ N : Finset E, (↑N : Set E) ⊆ A ∧ (∀ a ∈ A, ∃ b ∈ N, ‖a - b‖ ≤ ε) ∧
        (N.card : ℝ) ≤ (1 + 2 * r / ε) ^ Module.finrank ℝ E

/-- `thm:cond-dev`(i), contexts without replacement. -/
def cond_dev_i_swor : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (n M m p : ℕ)
    (Θ : Set (EuclideanSpace ℝ (Fin p))) (c : EuclideanSpace ℝ (Fin p)) (rΘ Λ BL δ : ℝ)
    (w : 𝒵 → EuclideanSpace ℝ (Fin p) → Fin n → ℝ) (L : 𝒵 → Finset (Fin n) → ℝ),
    1 ≤ M → M ≤ n → 1 ≤ m → 0 < δ → δ < 1 → Θ ⊆ Metric.closedBall c rΘ → 0 ≤ Λ →
    (∀ z, ∀ θ ∈ Θ, ∀ j, 0 < w z θ j) → (∀ z, ∀ θ ∈ Θ, ∑ j, w z θ j = 1) →
    (∀ θ ∈ Θ, ∀ j, Measurable fun z => w z θ j) →
    (∀ z, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, ∀ j, |Real.log (w z θ j) - Real.log (w z θ' j)| ≤ Λ * ‖θ - θ'‖) →
    (∀ S, Measurable fun z => L z S) → (∀ z S, 0 ≤ L z S ∧ L z S ≤ BL) →
      ∃ E : Set (Fin m → 𝒵), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin m => P0).real E ∧
        E ⊆ {zt | ∀ θ ∈ Θ,
          |empRisk (fun z => StatFormal.ICL.Grisk (w z θ) M (L z)) zt -
              poolRisk P0 (fun z => StatFormal.ICL.Grisk (w z θ) M (L z))| ≤
            devBoundI BL rΘ Λ δ p M m}

/-- `thm:cond-dev`(i), i.i.d. contexts. -/
def cond_dev_i_iid : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (n M m p : ℕ)
    (Θ : Set (EuclideanSpace ℝ (Fin p))) (c : EuclideanSpace ℝ (Fin p)) (rΘ Λ BL δ : ℝ)
    (w : 𝒵 → EuclideanSpace ℝ (Fin p) → Fin n → ℝ) (L : 𝒵 → (Fin M → Fin n) → ℝ),
    1 ≤ M → M ≤ n → 1 ≤ m → 0 < δ → δ < 1 → Θ ⊆ Metric.closedBall c rΘ → 0 ≤ Λ →
    (∀ z, ∀ θ ∈ Θ, ∀ j, 0 < w z θ j) → (∀ z, ∀ θ ∈ Θ, ∑ j, w z θ j = 1) →
    (∀ θ ∈ Θ, ∀ j, Measurable fun z => w z θ j) →
    (∀ z, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, ∀ j, |Real.log (w z θ j) - Real.log (w z θ' j)| ≤ Λ * ‖θ - θ'‖) →
    (∀ j, Measurable fun z => L z j) → (∀ z j, 0 ≤ L z j ∧ L z j ≤ BL) →
      ∃ E : Set (Fin m → 𝒵), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin m => P0).real E ∧
        E ⊆ {zt | ∀ θ ∈ Θ,
          |empRisk (fun z => Giid (w z θ) M (L z)) zt - poolRisk P0 (fun z => Giid (w z θ) M (L z))| ≤
            devBoundI BL rΘ Λ δ p M m}

/-- `thm:cond-dev`(ii), contexts without replacement: simultaneously for all `η > 0` and all internal `η`-nets. -/
def cond_dev_ii_swor : Prop :=
  ∀ (𝒵 Γ : Type) [MeasurableSpace 𝒵] [TopologicalSpace Γ] [TopologicalSpace.SeparableSpace Γ]
    [FirstCountableTopology Γ] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (n M m R : ℕ)
    (g : 𝒵 → Γ → Fin R → ℝ)
    (L : 𝒵 → Finset (Fin n) → ℝ) (BL lam δ : ℝ),
    1 ≤ M → M ≤ n → 1 ≤ m → 0 ≤ lam → 0 < δ → δ < 1 →
    (∀ z γ r, 0 ≤ g z γ r) → (∀ z γ, ∑ r, g z γ r = 1) → (∀ z r, Continuous fun γ => g z γ r) →
    (∀ γ r, Measurable fun z => g z γ r) →
    (∀ S, Measurable fun z => L z S) → (∀ z S, 0 ≤ L z S ∧ L z S ≤ BL) →
      ∃ E : Set (Fin m → 𝒵), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin m => P0).real E ∧
        E ⊆ {zt | ∀ η : ℝ, 0 < η → ∀ N : Finset Γ, IsGateNet g η N →
          ∀ (γ : Γ) (W : Fin R → Fin n → ℝ), (∀ r, StatFormal.ICL.InDeltaM (W r) M) →
            |empRisk (fGateSwor M g L lam γ W) zt - poolRisk P0 (fGateSwor M g L lam γ W)| ≤
              devBoundII (BL + lam * Real.log n) (ellSwor n M) η δ R N.card m}

/-- `thm:cond-dev`(ii), i.i.d. contexts. -/
def cond_dev_ii_iid : Prop :=
  ∀ (𝒵 Γ : Type) [MeasurableSpace 𝒵] [TopologicalSpace Γ] [TopologicalSpace.SeparableSpace Γ]
    [FirstCountableTopology Γ] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (n M m R : ℕ)
    (g : 𝒵 → Γ → Fin R → ℝ)
    (L : 𝒵 → (Fin M → Fin n) → ℝ) (BL lam δ : ℝ),
    1 ≤ M → M ≤ n → 1 ≤ m → 0 ≤ lam → 0 < δ → δ < 1 →
    (∀ z γ r, 0 ≤ g z γ r) → (∀ z γ, ∑ r, g z γ r = 1) → (∀ z r, Continuous fun γ => g z γ r) →
    (∀ γ r, Measurable fun z => g z γ r) →
    (∀ j, Measurable fun z => L z j) → (∀ z j, 0 ≤ L z j ∧ L z j ≤ BL) →
      ∃ E : Set (Fin m → 𝒵), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin m => P0).real E ∧
        E ⊆ {zt | ∀ η : ℝ, 0 < η → ∀ N : Finset Γ, IsGateNet g η N →
          ∀ (γ : Γ) (W : Fin R → Fin n → ℝ), (∀ r, (∀ j, 0 ≤ W r j) ∧ ∑ j, W r j = 1) →
            |empRisk (fGateIid g L lam γ W) zt - poolRisk P0 (fGateIid g L lam γ W)| ≤
              devBoundII (BL + lam * Real.log n) (ellIid n M) η δ R N.card m}

/-! ### ICL `lem:cond-curvature` -/

/-- `lem:cond-curvature`: `μ_t` has finite relative entropy for every `t ∈ [0,1]`. -/
def curv_kl_finite : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 μ0 μ1 : Measure 𝒵) [IsProbabilityMeasure P0]
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1],
    klDiv μ0 P0 ≠ ∞ → klDiv μ1 P0 ≠ ∞ → ∀ t ∈ Icc (0 : ℝ) 1, klDiv (mixAt μ0 μ1 t) P0 ≠ ∞

/-- `lem:cond-curvature`: `h` is continuous on `[0,1]`. -/
def curv_continuous : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 μ0 μ1 : Measure 𝒵) [IsProbabilityMeasure P0]
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] (M : ℕ) (Lbar : (Fin M → 𝒵) → ℝ) (BL lam : ℝ),
    Measurable Lbar → (∀ x, 0 ≤ Lbar x ∧ Lbar x ≤ BL) → 0 ≤ lam →
    klDiv μ0 P0 ≠ ∞ → klDiv μ1 P0 ≠ ∞ →
      ContinuousOn (hCurv Lbar lam P0 μ0 μ1) (Icc 0 1)

/-- `lem:cond-curvature`: `h` is twice differentiable on `(0,1)`. -/
def curv_twice_diff : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 μ0 μ1 : Measure 𝒵) [IsProbabilityMeasure P0]
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] (M : ℕ) (Lbar : (Fin M → 𝒵) → ℝ) (BL lam : ℝ),
    Measurable Lbar → (∀ x, 0 ≤ Lbar x ∧ Lbar x ≤ BL) → 0 ≤ lam →
    klDiv μ0 P0 ≠ ∞ → klDiv μ1 P0 ≠ ∞ →
      ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (hCurv Lbar lam P0 μ0 μ1) t ∧
        DifferentiableAt ℝ (deriv (hCurv Lbar lam P0 μ0 μ1)) t

/-- `lem:cond-curvature`: `h''(t) ≥ (λ − κ_M B_L) ∫ u_t² dμ_t` on `(0,1)`, `u_t = dσ/dμ_t`. -/
def curv_second : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 μ0 μ1 : Measure 𝒵) [IsProbabilityMeasure P0]
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] (M : ℕ) (Lbar : (Fin M → 𝒵) → ℝ) (BL lam : ℝ),
    Measurable Lbar → (∀ x, 0 ≤ Lbar x ∧ Lbar x ≤ BL) → 0 ≤ lam →
    klDiv μ0 P0 ≠ ∞ → klDiv μ1 P0 ≠ ∞ →
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : 𝒵 → ℝ, Integrable u (mixAt μ0 μ1 t) →
        (∀ A, MeasurableSet A → μ1.real A - μ0.real A = ∫ x in A, u x ∂(mixAt μ0 μ1 t)) →
          Integrable (fun x => u x ^ 2) (mixAt μ0 μ1 t) ∧
          (lam - kappaM M * BL) * ∫ x, u x ^ 2 ∂(mixAt μ0 μ1 t) ≤
            deriv (deriv (hCurv Lbar lam P0 μ0 μ1)) t

/-- `lem:cond-curvature`: if `λ ≥ κ_M B_L`, then
`h(t) ≤ (1−t)h(0) + t h(1) − (λ − κ_M B_L)‖σ‖²_TV t(1−t)/2` on `[0,1]`, `‖σ‖_TV = 2 tvDist(μ₀, μ₁)`. -/
def curv_chord : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 μ0 μ1 : Measure 𝒵) [IsProbabilityMeasure P0]
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] (M : ℕ) (Lbar : (Fin M → 𝒵) → ℝ) (BL lam : ℝ),
    Measurable Lbar → (∀ x, 0 ≤ Lbar x ∧ Lbar x ≤ BL) → 0 ≤ lam →
    klDiv μ0 P0 ≠ ∞ → klDiv μ1 P0 ≠ ∞ → kappaM M * BL ≤ lam →
      ∀ t ∈ Icc (0 : ℝ) 1,
        hCurv Lbar lam P0 μ0 μ1 t ≤
          (1 - t) * hCurv Lbar lam P0 μ0 μ1 0 + t * hCurv Lbar lam P0 μ0 μ1 1 -
            (lam - kappaM M * BL) * (2 * StatFormal.Distances.tvDist μ0 μ1) ^ 2 * (t * (1 - t) / 2)

/-! ### NN `prop:exp-ident` -/

/-- `σ = exp` satisfies `ass:UA`: continuous, `C¹`, not a polynomial. -/
def exp_UA : Prop :=
  Continuous Real.exp ∧ ContDiff ℝ 1 Real.exp ∧ ¬ ∃ p : Polynomial ℝ, ∀ x, Real.exp x = p.eval x

/-- `prop:exp-ident`: for `σ = exp`, `ass:ident` holds for every functionally minimal `θ*_q` and every `m ≥ q`. -/
def exp_ident : Prop :=
  ∀ (din dout q m : ℕ) (θs : Fin q → Neuron din dout),
    FunctionallyMinimal Real.exp θs → q ≤ m → AssIdent Real.exp θs m

/-- `prop:exp-ident` with the frozen `lem:exhaust`: for `σ = exp`, `Λ^m_q = F^m_q`. -/
def exp_exhaust : Prop :=
  ∀ (din dout q m : ℕ) (θs : Fin q → Neuron din dout), FunctionallyMinimal Real.exp θs → q ≤ m →
    {θ : Fin m → Neuron din dout | InLam θs θ} = {θ | net Real.exp θ = net Real.exp θs}

/-- After `ass:ident`: it fails for `tanh` (`θ* = (1,1)`, `m = 1`). -/
def ident_fails_tanh : Prop :=
  FunctionallyMinimal Real.tanh unitRep ∧ ¬ AssIdent Real.tanh unitRep 1

/-- After `ass:ident`: it fails for the sigmoid (`θ* = (1,1)`, `m = 2`). -/
def ident_fails_sigmoid : Prop :=
  FunctionallyMinimal sigmoid unitRep ∧ ¬ AssIdent sigmoid unitRep 2

/-- After `ass:ident`: it fails for ReLU (`θ* = (1,1)`, `m = 1`). -/
def ident_fails_relu : Prop :=
  FunctionallyMinimal relu unitRep ∧ ¬ AssIdent relu unitRep 1

/-- After `ass:ident`: it fails for softplus (`θ* = ((1,1),(−1,−1))`, `m = 2`). -/
def ident_fails_softplus : Prop :=
  FunctionallyMinimal softplus oddRep ∧ ¬ AssIdent softplus oddRep 2

end Claims

end StatFormal.Wave12c
