import StatFormal.Archive.Wave29i.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import StatFormal.Lib.Distances.TV
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Ring.Periodic

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tj: trimmed MMD, JMLR version — `lem:trimlinear` (asymptotic linearity of a trimmed
# mean, with the set-up paragraph `eq:lowertrim`) and the kernel-blindness construction quoted after `thm:impossible`

Source: `trimmed-mmd/jmlr/` (the JMLR version; `main.tex` inputs `sections/*.tex`, `appendix/*.tex`; read 2026-11-07,
`appendix/B_split.tex` sha256 `5af5088a…`).
* Set-up paragraph `appendix/B_split.tex:31-43`: for `U` with law `F` on `[−κ, κ]`, `β = (1 − α)⁻¹`,
  `ψ_s(u) = s − β (s − u)_+`, the mean of the lower `(1−α)`-fraction `inf {E_F[gU] : 0 ≤ g ≤ β, E_F g = 1}` equals
  `L(F) = sup_{s ∈ ℝ} ∫ ψ_s dF = sup_{s ∈ [−κ,κ]} ∫ ψ_s dF` (`eq:lowertrim`); for the empirical law `F_n`, `L(F_n)` is
  the lower trimmed mean of `eq:splitstat` (`sections/06_splitting.tex:69-76`, boundary order statistic weighted as in
  `lem:trimmedmean`); `s ↦ ∫ ψ_s dF` is concave with right and left derivatives `1 − βF(s)`, `1 − βF(s−)`, so its
  maximisers are the `s` with `F(s−) ≤ 1 − α ≤ F(s)`.
* `lem:trimlinear` (`appendix/B_split.tex:45-55`): `U_1, U_2, …` i.i.d. with law `F` on `[−κ, κ]`, `α ∈ (0,1)`, `F` has a
  positive density in a neighbourhood of a `(1−α)`-quantile `q`. Then `q` is the unique maximiser in `eq:lowertrim`,
  `√n (L(F_n) − L(F)) = n^{−1/2} Σ_i (ψ_q(U_i) − E ψ_q(U)) + o_P(1) ⇒ N(0, β² Var (q − U)_+)`, and the conditional law of
  `√n (L(F_n*) − L(F_n))` (`F_n*` the empirical law of a bootstrap sample drawn from `F_n`) converges in probability to
  the same normal law. Proof `:57-81` (variance `Var ψ_q(U) = β² Var (q − U)_+`, `:71-72`).
* Kernel blindness (`appendix/B_split.tex:172-184`; quoted in `sections/06_splitting.tex:180-183` and
  `sections/01_introduction.tex:117-118`, "For any fixed bounded kernel there are laws at total variation `½` whose
  kernel means are arbitrarily close"): on `[0,1]`, `P₀` uniform, `s` 1-periodic, mean zero, `|s| = 1`,
  `q_N = 1 + s(N·)`: `q_N ≥ 0`, `∫ q_N = 1`, `TV(P₀, Q_N) = ½ ∫ |s(Nx)| dx = ½` for every `N`;
  `μ_{Q_N} − μ_{P₀} = ∫₀¹ φ(x) s(Nx) dx → 0` in `ℋ` (Riemann–Lebesgue for Bochner integrals: `φ` bounded and strongly
  measurable under `ass:regularity`, hence in `L¹([0,1]; ℋ)`; "no continuity of `φ` is needed"); `μ_P ∈ 𝒞_{α,k}(P)`, so
  `D_{α,k} ≤ MMD_k` for every `α`, and the whole trimmed path is uniformly small while `TV` stays at `½`.

Imports the frozen `Wave29i` statements (`splitTrimLo`, `splitAss`; through them `TrimmedMMD/BangBang` `capped`, `cap`,
`kfloor`, `ord`, `TrimmedMMD/Concentration` `region`, `empirical`), `TrimmedMMD/Unconditional` (`Dpop`) and
`Distances` (`tvDist`), not copied; Mathlib otherwise.

New definitions: `psi` (`ψ_s`), `lowerTrim` (`L(F)`), `lowerTrimVals` (`{E_F[gU]}`), `trimBootCdf` (the bootstrap
cdf of the root), `unifLaw` (`P₀`), `blindLaw` (`Q_N`), `mmd` (`MMD_k`).

Covered (9 claims):
* `lowertrim_value` — set-up paragraph, `eq:lowertrim`: for `F` a probability law on `ℝ` with `F([−κ,κ]) = 1` and
  `α ∈ [0,1)`: `L(F)` is the infimum (`IsGLB`) of `{E_F[gU]}`, and the supremum (`IsLUB`) of `{∫ ψ_s dF : s ∈ ℝ}` and of
  `{∫ ψ_s dF : s ∈ [−κ,κ]}`.
* `lowertrim_shape` — set-up paragraph, last sentence: `s ↦ ∫ ψ_s dF` is concave on `ℝ`, has right derivative
  `1 − βF(s)` and left derivative `1 − βF(s−)` at every `s` (`HasDerivWithinAt` on `[s, ∞)`, `(−∞, s]`), and `s` is a
  maximiser iff `F(s−) ≤ 1 − α ≤ F(s)`.
* `lowertrim_empirical` — set-up paragraph: for `n ≥ 1` values `v`, `L(F_n) = min_{w ∈ Δ_α(n)} Σ w_i v_i`
  (`splitTrimLo`, the statistic of `eq:splitstat`) `= c Σ_{i ≤ k} v_(i) + (1 − kc) v_(k+1)` (`lem:trimmedmean`).
* `trimlinear` — `lem:trimlinear` in full, under the printed hypotheses: (b) `q ∈ [−κ,κ]` is the unique maximiser;
  (c) asymptotic linearity; the variance identity `Var ψ_q(U) = β² Var (q − U)_+`; (d) the normal limit; (e) the
  bootstrap: for every `t`, the conditional cdf of the root at `t` converges in probability to the `N(0, β² Var (q−U)_+)`
  cdf.
* `riemann_lebesgue_periodic` — the Riemann–Lebesgue lemma used: for any real Banach space `E`, any `f` Bochner
  integrable on `[0,1]` (no continuity) and any measurable 1-periodic `s` with `|s| ≤ 1` and mean zero,
  `∫₀¹ s(Nx) f(x) dx → 0`.
* `dpop_le_mmd` — "`μ_P ∈ 𝒞_{α,k}(P)` … so `D_{α,k} ≤ MMD_k` for every `α`", for every pair of laws.
* `blind_construction` — `q_N ≥ 0`, `∫ q_N = 1`, `Q_N` a probability law, `TV(P₀, Q_N) = ½ ∫ |s(Nx)| dx = ½` (`N ≥ 1`).
* `blind_mmd` — for every bounded strongly measurable feature map: `μ_{Q_N} − μ_{P₀} = ∫₀¹ s(Nx) φ(x) dx`,
  `MMD_k(P₀, Q_N) → 0`, `D_{α,k}(P₀, Q_N) ≤ MMD_k(P₀, Q_N)` for every `α ∈ [0,1)`, and the whole trimmed path is
  uniformly small: for every `ε > 0`, eventually `D_{α,k}(P₀, Q_N) ≤ ε` for all `α ∈ [0,1)` at once.
* `blind_witness` — an `s` as required exists (measurable, 1-periodic, `|s| = 1`, mean zero: the square wave), so the
  printed existential ("there are pairs with `TV = ½` and `MMD_k` arbitrarily small") is not vacuous.

Encodings (to be checked by the critic):
* `F` is a probability measure on `ℝ` with `F([−κ,κ]) = 1` ("law `F` on `[−κ,κ]`"; forces `κ ≥ 0`). The samples
  `U : ℕ → Ω → ℝ` are measurable, `iIndepFun`, with `μ.map (U i) = F` (maps guarded by measurability); they take values
  in `[−κ,κ]` only almost surely (as printed). `U_1, …, U_n` are `U 0, …, U (n−1)`.
* `L(F) = ⨆_s ∫ ψ_s dF` (`lowerTrim`); the claims assert `IsLUB`, so the `iSup` is genuine (not the junk `0` of an
  unbounded family). `{E_F[gU]}` uses bounded measurable `g` with `0 ≤ g ≤ 1/(1−α)` everywhere and `∫ g dF = 1`, as the
  frozen `region` (`L^∞(F)` classes are represented by bounded measurable functions).
* `F(s) = F.real (Iic s)`, `F(s−) = F.real (Iio s)`. Right/left derivatives are `HasDerivWithinAt` on `Ici s`/`Iic s`.
  "Maximiser" is `IsMaxOn … univ s`; "unique maximiser in `eq:lowertrim`" is: `q` is a maximiser over `ℝ`, every
  maximiser over `ℝ` equals `q`, and `q ∈ [−κ,κ]` (so it is also the unique maximiser over `[−κ,κ]`).
* "positive density in a neighbourhood of a `(1−α)`-quantile `q`" is the frozen `splitAss F id (1−α) q` (Wave 29i, the
  `ass:split` encoding: `F(q−) ≤ 1 − α ≤ F(q)` and a measurable `ρ > 0` on `(q − ε, q + ε)` with
  `F((a,b]) = ∫_{(a,b]} ρ` there).
* `F_n` is the frozen `empirical` (`Σ_i n⁻¹ δ_{U_i}`); `o_P(1)` is `TendstoInMeasure` to `0`; `⇒` is Mathlib
  `TendstoInDistribution` to `id` under `gaussianReal 0 σ²` (`σ² = β² Var_F (q − ·)_+`, `toNNReal` of a nonnegative
  number); `β = (1 − α)⁻¹`, written `(1 − α)⁻¹`.
* Bootstrap: a bootstrap sample from `F_n` is `(U_{I(1)}, …, U_{I(n)})` with `I : [n] → [n]` uniform (i.i.d. uniform
  indices); `F_n*` is the empirical law of `v ∘ I`; "the conditional law converges in probability" is encoded as in the
  frozen Wave 29l `split_boot_clt`: for every `t`, the exact conditional cdf `trimBootCdf` (an average over the `n^n`
  equally likely index maps) of `√n (L(F_n*) − L(F_n))` at `t` converges in probability to the limit cdf at `t` (the
  limit is continuous, its variance being positive under the hypotheses).
* Kernel blindness: as the frozen `thm:impossible`, laws on `[0,1]` are laws on `ℝ` carried by `[0,1]`: `P₀ = λ|_{[0,1]}`
  (`unifLaw`), `Q_N = P₀` with density `ofReal (1 + s(Nx))` (`blindLaw`); `N ∈ ℕ` with `N ≥ 1`. The kernel enters
  through its feature map (as `TrimmedMMD/Concentration`): `ℋ` a real Hilbert space, `φ : ℝ → ℋ` strongly measurable,
  `‖φ‖ ≤ κ` ((A1); the step "(A1)-(A2) ⇒ `φ` strongly measurable" (Pettis, `B_split.tex:180-181`) is taken as the
  encoding, as in the frozen `TrimmedMMD/Concentration`; a kernel on `[0,1]` is extended arbitrarily off `[0,1]`, which
  the laws do not see); separability
  (A2) and characteristicness (A3) are NOT assumed (generalisation). `MMD_k(P,Q) = ‖∫ φ dP − ∫ φ dQ‖` (`mmd`),
  `D_{α,k} = ` the frozen `Dpop` (distance of the frozen regions), `TV` the frozen `tvDist` (`sup_A |P(A) − Q(A)|`).
  "Mean zero" is `∫₀¹ s = 0`; "`|s| = 1`" holds everywhere (`riemann_lebesgue_periodic` needs only `|s| ≤ 1`);
  measurability of `s` is implicit in the print (needed for the integrals). `N ≥ 1` is needed: at `N = 0`,
  `q_0 = 1 + s(0) ∈ {0, 2}` and `∫ q_0 ≠ 1`.

Junk-value audit:
* `lowerTrim` is an `iSup` in `ℝ`; every claim that uses it at a population law also asserts (or follows from a claim
  asserting) `IsLUB`, so it is never the junk value of an unbounded family; at the empirical law it is identified with
  `splitTrimLo` (`n ≥ 1`). At `n = 0` (`empirical` is the zero measure, `lowerTrim = 0`) only one index of an
  asymptotic statement is affected; `trimBootCdf` at `n = 0` likewise (`0^0 = 1`).
* `∫ ψ_s dF`: `ψ_s` is continuous and `F`-a.e. bounded (`F([−κ,κ]) = 1`), so the integrals are genuine; `∫ g u * u dF`
  likewise. `Var` of `(q − ·)_+` (a.e. bounded) and of `ψ_q` is genuine.
* `(1 − α)⁻¹` with `α < 1`: no `/0`. `1 / (1 − α)` likewise. `√n⁻¹` at `n = 0` is `0` (one index).
* `Dpop` is an `sInf` over the nonempty set of distances of the (nonempty, `α ∈ [0,1)`) regions; nonnegative, so not
  the junk `sInf ∅ = 0`. `∫ φ` of a bounded strongly measurable `φ` against a finite measure is a genuine Bochner
  integral; `∫ s(Nx) • f x` over `[0,1]` likewise (`|s| ≤ 1`, `f` integrable). `withDensity` of `ofReal (1 + s(N·))`
  (`≥ 0`, so `ofReal` loses nothing). `tvDist` of two probability measures is a bounded `iSup`.

Non-vacuity: `lowertrim_*`: any `F` on `[−κ,κ]`, e.g. `δ₀`. `trimlinear`: `U_i` i.i.d. uniform on `[0,1]`, `κ = 1`,
`α = ½`, `q = ½` (`splitAss` holds: frozen `Wave29i` route `splitAss_uniform`). Kernel blindness: the square wave
`s = 1` on `[0, ½)`, `−1` on `[½, 1)`, extended periodically; any bounded `φ`.

DRAFT — not yet in `certify/statements.lock`; on approval it is hashed there (with its imports), and AI agents must not
edit it.
-/

noncomputable section

namespace StatFormal.Wave30tj

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

open StatFormal.TrimmedMMD.Concentration (empirical region)
open StatFormal.TrimmedMMD.BangBang (capped cap kfloor ord)
open StatFormal.Wave29i (splitTrimLo splitAss)
open StatFormal.TrimmedMMD.Unconditional (Dpop)

/-- `ψ_s(u) = s − β (s − u)_+`, `β = (1 − α)⁻¹`. -/
def psi (α s u : ℝ) : ℝ := s - (1 - α)⁻¹ * max (s - u) 0

/-- `L(F) = sup_{s ∈ ℝ} ∫ ψ_s dF` (`eq:lowertrim`). -/
def lowerTrim (F : Measure ℝ) (α : ℝ) : ℝ := ⨆ s : ℝ, ∫ u, psi α s u ∂F

/-- The values `E_F[g U]` over the trimming densities `0 ≤ g ≤ 1/(1 − α)`, `E_F g = 1`. -/
def lowerTrimVals (F : Measure ℝ) (α : ℝ) : Set ℝ :=
  {v | ∃ g : ℝ → ℝ, Measurable g ∧ (∀ u, 0 ≤ g u ∧ g u ≤ 1 / (1 - α)) ∧ ∫ u, g u ∂F = 1 ∧
    v = ∫ u, g u * u ∂F}

/-- The bootstrap cdf of the root `√n (L(F_n*) − L(F_n))` at `t`, given the data `v = (U_1, …, U_n)`: the proportion of
the `n^n` equally likely resampling index maps `I : [n] → [n]` (a bootstrap sample `v ∘ I` drawn from `F_n`) with
`√n (L(F_n*) − L(F_n)) ≤ t`, `F_n*` the empirical law of `v ∘ I`. -/
def trimBootCdf (n : ℕ) (α : ℝ) (v : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((n : ℝ) ^ n)⁻¹ * ∑ I : Fin n → Fin n,
    if √(n : ℝ) * (lowerTrim (empirical (v ∘ I)) α - lowerTrim (empirical v) α) ≤ t then (1 : ℝ) else 0

/-- `P₀`, the uniform law on `[0,1]` (Lebesgue measure restricted to `[0,1]`). -/
def unifLaw : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- `Q_N`, the law on `[0,1]` with density `q_N(x) = 1 + s(N x)` with respect to `P₀`. -/
def blindLaw (s : ℝ → ℝ) (N : ℕ) : Measure ℝ :=
  unifLaw.withDensity fun x => ENNReal.ofReal (1 + s (N * x))

/-- `MMD_k(P, Q) = ‖μ_P − μ_Q‖`, `μ_P = ∫ φ dP` the kernel mean embedding. -/
def mmd {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H)
    (P Q : Measure 𝒳) : ℝ :=
  ‖∫ x, φ x ∂P - ∫ x, φ x ∂Q‖

namespace Claims

/-- Set-up paragraph of `lem:trimlinear`, `eq:lowertrim`: the lower `(1−α)`-trimmed mean
`inf {E_F[gU] : 0 ≤ g ≤ β, E_F g = 1}` equals `L(F) = sup_{s ∈ ℝ} ∫ ψ_s dF = sup_{s ∈ [−κ,κ]} ∫ ψ_s dF`. -/
def lowertrim_value : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (κ α : ℝ), F (Icc (-κ) κ) = 1 → 0 ≤ α → α < 1 →
    IsGLB (lowerTrimVals F α) (lowerTrim F α) ∧
    IsLUB (range fun s => ∫ u, psi α s u ∂F) (lowerTrim F α) ∧
    IsLUB ((fun s => ∫ u, psi α s u ∂F) '' Icc (-κ) κ) (lowerTrim F α)

/-- Set-up paragraph, last sentence: `s ↦ ∫ ψ_s dF` is concave, with right derivative `1 − βF(s)` and left derivative
`1 − βF(s−)`, and its maximisers are exactly the `s` with `F(s−) ≤ 1 − α ≤ F(s)`. -/
def lowertrim_shape : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (κ α : ℝ), F (Icc (-κ) κ) = 1 → 0 ≤ α → α < 1 →
    ConcaveOn ℝ univ (fun s => ∫ u, psi α s u ∂F) ∧
    (∀ s, HasDerivWithinAt (fun s => ∫ u, psi α s u ∂F) (1 - (1 - α)⁻¹ * F.real (Iic s)) (Ici s) s) ∧
    (∀ s, HasDerivWithinAt (fun s => ∫ u, psi α s u ∂F) (1 - (1 - α)⁻¹ * F.real (Iio s)) (Iic s) s) ∧
    ∀ s, IsMaxOn (fun s => ∫ u, psi α s u ∂F) univ s ↔ (F.real (Iio s) ≤ 1 - α ∧ 1 - α ≤ F.real (Iic s))

/-- Set-up paragraph: for the empirical law `F_n` of `v_1, …, v_n`, `L(F_n)` is the lower trimmed mean of
`eq:splitstat`, `min_{w ∈ Δ_α(n)} Σ w_i v_i = c Σ_{i ≤ k} v_(i) + (1 − kc) v_(k+1)` (`c = [n(1−α)]⁻¹`, `k = ⌊n(1−α)⌋`,
last term `0` when `k = n`; `ord v j = v_(j+1)`), the boundary order statistic weighted as in `lem:trimmedmean`. -/
def lowertrim_empirical : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ) (α : ℝ), 0 < n → 0 ≤ α → α < 1 →
    lowerTrim (empirical v) α = splitTrimLo n α v ∧
    lowerTrim (empirical v) α = cap n α * ∑ j ∈ Finset.range (kfloor n α), ord v j +
      (if kfloor n α < n then (1 - kfloor n α * cap n α) * ord v (kfloor n α) else 0)

/-- `lem:trimlinear`: for `U_1, U_2, …` i.i.d. with law `F` on `[−κ,κ]`, `α ∈ (0,1)`, and a positive density of `F` in a
neighbourhood of a `(1−α)`-quantile `q`: (b) `q` is the unique maximiser in `eq:lowertrim`; (c)
`√n (L(F_n) − L(F)) − n^{−1/2} Σ_{i<n} (ψ_q(U_i) − E ψ_q(U)) → 0` in probability; `Var ψ_q(U) = β² Var (q − U)_+`;
(d) `√n (L(F_n) − L(F)) ⇒ N(0, β² Var (q − U)_+)`; (e) the conditional law of `√n (L(F_n*) − L(F_n))` converges in
probability to the same normal law (its cdf at every `t`). -/
def trimlinear : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (κ α q : ℝ),
    (∀ i, Measurable (U i)) → iIndepFun U μ → (∀ i, μ.map (U i) = F) → F (Icc (-κ) κ) = 1 →
    0 < α → α < 1 → splitAss F id (1 - α) q →
      (q ∈ Icc (-κ) κ ∧ IsMaxOn (fun s => ∫ u, psi α s u ∂F) univ q ∧
        ∀ s, IsMaxOn (fun s => ∫ u, psi α s u ∂F) univ s → s = q) ∧
      TendstoInMeasure μ (fun (n : ℕ) ω =>
          √(n : ℝ) * (lowerTrim (empirical fun i : Fin n => U i ω) α - lowerTrim F α) -
            (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (psi α q (U i ω) - ∫ u, psi α q u ∂F)) atTop (fun _ => 0) ∧
      Var[fun u => psi α q u; F] = (1 - α)⁻¹ ^ 2 * Var[fun u => max (q - u) 0; F] ∧
      TendstoInDistribution (fun (n : ℕ) ω =>
          √(n : ℝ) * (lowerTrim (empirical fun i : Fin n => U i ω) α - lowerTrim F α)) atTop id (fun _ => μ)
        (gaussianReal 0 ((1 - α)⁻¹ ^ 2 * Var[fun u => max (q - u) 0; F]).toNNReal) ∧
      ∀ t : ℝ, TendstoInMeasure μ (fun (n : ℕ) ω => trimBootCdf n α (fun i : Fin n => U i ω) t) atTop
        (fun _ => (gaussianReal 0 ((1 - α)⁻¹ ^ 2 * Var[fun u => max (q - u) 0; F]).toNNReal).real (Iic t))

/-- The Riemann–Lebesgue lemma behind the construction (Bochner integrals, no continuity): for `f` integrable on
`[0,1]` with values in a real Banach space and a measurable 1-periodic mean-zero `s` with `|s| ≤ 1`,
`∫₀¹ s(Nx) f(x) dx → 0`. -/
def riemann_lebesgue_periodic : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (s : ℝ → ℝ),
    IntegrableOn f (Icc 0 1) → Measurable s → Function.Periodic s 1 → (∀ x, |s x| ≤ 1) →
    ∫ x in (0 : ℝ)..1, s x = 0 →
      Tendsto (fun N : ℕ => ∫ x in Icc (0 : ℝ) 1, s (N * x) • f x) atTop (𝓝 0)

/-- "`μ_P ∈ 𝒞_{α,k}(P)` and `μ_Q ∈ 𝒞_{α,k}(Q)`, so `D_{α,k} ≤ MMD_k` for every `α`" (any two laws). -/
def dpop_le_mmd : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      ∫ x, φ x ∂P ∈ region φ α P ∧ Dpop φ P Q α ≤ mmd φ P Q

/-- The construction: `q_N = 1 + s(N·) ≥ 0`, `∫₀¹ q_N = 1`, `Q_N` is a probability law and
`TV(P₀, Q_N) = ½ ∫₀¹ |s(Nx)| dx = ½` for every `N ≥ 1`. -/
def blind_construction : Prop :=
  ∀ (s : ℝ → ℝ), Measurable s → Function.Periodic s 1 → (∀ x, |s x| = 1) → ∫ x in (0 : ℝ)..1, s x = 0 →
    ∀ N : ℕ, 0 < N →
      (∀ x, 0 ≤ 1 + s (N * x)) ∧ ∫ x in Icc (0 : ℝ) 1, (1 + s (N * x)) = 1 ∧
      IsProbabilityMeasure (blindLaw s N) ∧
      StatFormal.Distances.tvDist unifLaw (blindLaw s N) = 1 / 2 * ∫ x in Icc (0 : ℝ) 1, |s (N * x)| ∧
      StatFormal.Distances.tvDist unifLaw (blindLaw s N) = 1 / 2

/-- The construction, kernel side, for any bounded (strongly measurable) feature map: `μ_{Q_N} − μ_{P₀} =
∫₀¹ s(Nx) φ(x) dx`, `MMD_k(P₀, Q_N) → 0`, `D_{α,k}(P₀, Q_N) ≤ MMD_k(P₀, Q_N)` for every `α ∈ [0,1)`, and the whole
trimmed path is uniformly small: for every `ε > 0`, eventually in `N`, `D_{α,k}(P₀, Q_N) ≤ ε` for all `α ∈ [0,1)`. -/
def blind_mmd : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H) (κ : ℝ)
    (s : ℝ → ℝ), StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    Measurable s → Function.Periodic s 1 → (∀ x, |s x| = 1) → ∫ x in (0 : ℝ)..1, s x = 0 →
      (∀ N : ℕ, 0 < N →
        ∫ x, φ x ∂(blindLaw s N) - ∫ x, φ x ∂unifLaw = ∫ x in Icc (0 : ℝ) 1, s (N * x) • φ x) ∧
      Tendsto (fun N : ℕ => mmd φ unifLaw (blindLaw s N)) atTop (𝓝 0) ∧
      (∀ N : ℕ, 0 < N → ∀ α : ℝ, 0 ≤ α → α < 1 → Dpop φ unifLaw (blindLaw s N) α ≤ mmd φ unifLaw (blindLaw s N)) ∧
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ α : ℝ, 0 ≤ α → α < 1 → Dpop φ unifLaw (blindLaw s N) α ≤ ε

/-- The construction is not vacuous: a measurable 1-periodic mean-zero `s` with `|s| = 1` exists (the square wave). -/
def blind_witness : Prop :=
  ∃ s : ℝ → ℝ, Measurable s ∧ Function.Periodic s 1 ∧ (∀ x, |s x| = 1) ∧ ∫ x in (0 : ℝ)..1, s x = 0

end Claims

end StatFormal.Wave30tj
