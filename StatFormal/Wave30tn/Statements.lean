import StatFormal.Archive.Wave30dd.Statements
import StatFormal.Archive.Wave30ah.Statements
import StatFormal.Archive.TrimmedMMD.Lower.Statements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tn: trimmed MMD, JMLR version — the finite-sample split certificate
# (`prop:splitfs`, `eq:trimlip`), its corollary for the lower confidence bound (`cor:lower`, finite-sample clause and
# the general regime), the restated split certificate (`thm:split`: the clauses not covered by the frozen claims), and
# two trimming lemmas (`lem:unique`, `lem:popthreshold`)

Source: `trimmed-mmd/jmlr/` (JMLR version; working tree read 2026-11-07 after commit `e1869dd`, read-only; the text is
still being edited, so line numbers are approximate and labels are authoritative).
* `eq:trimlip` (`appendix/B_split.tex:31-49`, label `:48`): for `U` with law `F` on `[−κ,κ]`, `β = (1−α)⁻¹`, `ψ_s(u) = s − β(s − u)_+`,
  `L(F) = sup_{s∈ℝ} ∫ ψ_s dF` (`eq:lowertrim`); "For `s ∈ [−κ,κ]`, `∫(s−u)_+ dF(u) = ∫_{−κ}^s F(u) du`, so for any two laws
  `F, F'` on `[−κ,κ]` … `|L(F) − L(F')| ≤ sup_{s∈[−κ,κ]} β|∫_{−κ}^s (F − F')(u) du| ≤ 2κβ‖F − F'‖_∞`".
* `prop:splitfs` (`sections/06_splitting.tex:134-144`, Proposition 17 of the PDF; proof `appendix/B_split.tex:150-159`):
  "Let Assumption 1 hold, condition on the first fold as in Theorem `thm:split`, and let `f̂` be any element of `ℋ` with
  `‖f̂‖ ≤ 1`. Fix `α ∈ [0,1)` and `δ ∈ (0,1)`, and put `β = (1−α)⁻¹` and `e_n(δ) = √(log(4/δ)/(2n))`. For every pair
  `(P,Q)` and all `n₂, m₂ ≥ 1`, `P(|T̂ − T| > 2κβ[e_{n₂}(δ) + e_{m₂}(δ)]) ≤ δ`. Hence rejecting `H_{0,α}` when
  `T̂ > 2κβ[e_{n₂}(δ) + e_{m₂}(δ)]` has level at most `δ` for every sample size, with no condition on the laws of `f̂(X)`
  and `f̂(Y)`."
* `cor:lower` (`sections/06_splitting.tex:153-167`, Corollary 18; proof `appendix/B_split.tex:161-170`): grid
  `α_1 < ⋯ < α_J` fixed in advance, each `H_{0,α_j}` tested by `thm:split` (ass:split at every grid level for the
  witness used there), `α̂_lo` of `eq:downclosed`; "Then `limsup P(α̂_lo > TV(P,Q)) ≤ δ` … If each level is tested
  instead by Proposition `prop:splitfs`, then `P(α̂_lo > TV(P,Q)) ≤ δ` for all `n₂, m₂ ≥ 1`, without Assumption `ass:split`."
* `thm:split` (`sections/06_splitting.tex:90-119`, Theorem 16; remark after it `:121-124`; proof `appendix/B_split.tex:92-148`): "… let
  `n₂, m₂ → ∞` in any manner. Then: (i) if `σ_{n₂,m₂} > 0`, which holds whenever `α > 0`, then
  `(T̂ − T)/σ_{n₂,m₂} ⇒ N(0,1)`; (ii) if `σ_{n₂,m₂} > 0`, the standard error `ŝe*` of the nonparametric bootstrap that
  resamples the two second-fold samples of scalars independently satisfies `ŝe*/σ_{n₂,m₂} → 1` in probability, and the
  conditional law of `(T̂* − T̂)/σ_{n₂,m₂}` converges weakly to `N(0,1)` in probability; (iii) … If `f̂ = 0` the statistic
  is identically zero and the rule never rejects." (with `σ²_{n₂,m₂} = β²[Var(q−U)_+/n₂ + Var(V−q')_+/m₂]`, at `α = 0`
  read as `Var U/n₂ + Var V/m₂`).
* `lem:unique` (`appendix/C_recover.tex:41-46`, Lemma 34; proof `:48-59`): "Let Assumption 1 hold, suppose that the
  singletons of `𝒳` are measurable, let `α, β ∈ [0,1)`, and suppose that `X_1, …, X_n, Y_1, …, Y_m` are pairwise
  distinct. Then `D̂_{α,k} > 0` and `𝒯_α` is a singleton." (`𝒯_α` of `eq:trimset-emp`, `sections/08_trimming.tex:14-25`,
  levels `α` for the first sample and `β` for the second; `D̂²_{α,k}` the optimal value of `eq:qp`, `sections/03_regions.tex:59-68`.)
* `lem:popthreshold` (`appendix/C_recover.tex:198-206`, Lemma 39; proof `:208-227`): "Let Assumption 1 hold, let
  `α, β ∈ [0,1)`, and suppose that `dist(𝒞_{α,k}(P), 𝒞_{β,k}(Q)) > 0`. Let `d*` be the minimum-norm element of
  `𝒞_{α,k}(P) − 𝒞_{β,k}(Q)`, write `d* = a* − b*` with `a* = E_P[g*φ]` for some `g* ∈ 𝒢_α(P)` and `b* ∈ 𝒞_{β,k}(Q)`, and
  let `t` be any `(1−α)`-quantile of `d*(X)` for `X ∼ P`. Then `g* = (1−α)⁻¹` `P`-almost surely on `{d* < t}` and
  `g* = 0` `P`-almost surely on `{d* > t}`."

Imports the frozen statement files of wave 30dd (through it 30da `splitSdAny`, 29l `splitBootRep`/`splitBootSE`/
`splitBootPerc`, 29i `splitTrimLo`/`splitTrimUp`/`splitSE`/`splitAss`, 17a `sepVal`, `TrimmedMMD/Concentration` `region`,
`Distances` `tvDist`), wave 30dd's own `splitSdZero`, wave 30ah (`trimSetEmp`; through it `TrimmedMMD/BangBang`
`capped`, `qp` and `TrimmedMMD/ZeroSet` `Characteristic`, `IsTrimDensity`, and `TrimmedMMD/Unconditional` `setDist`),
`TrimmedMMD/Lower` (`alphaLo`); Mathlib otherwise.

New definitions: `psi`, `lowerTrim` (verbatim the bodies of `psi`, `lowerTrim` of the wave-30tj statements of the JMLR
branch, which certify `eq:lowertrim`; restated here because that wave is not on this branch), `dkwRad` (`e_n(δ)`),
`splitBootCdfStd` (the bootstrap cdf of the standardised root).

Covered (11 claims):
* `trimlip` — `eq:trimlip` with its lead-in: the integral identity, and both inequalities of the display.
* `splitfs` — `prop:splitfs`: the probability bound for all `n₂, m₂ ≥ 1` and every `(P,Q)`, and the level of the
  finite-sample test.
* `cor_lower_fs` — `cor:lower`, finite-sample clause: each level tested by `prop:splitfs` (any witnesses `‖f_j‖ ≤ 1`),
  `P(α̂_lo > TV) ≤ δ` for all `n₂, m₂ ≥ 1`, no density condition.
* `cor_lower_boot_any`, `cor_lower_split_any` — `cor:lower`, asymptotic clause, with each level tested by `thm:split`
  (bootstrap SE as printed in (iii); plug-in SE of the remark) as `n₂, m₂ → ∞` in any manner (the frozen wave-30at
  claims are in the ratio regime only).
* `split_normal_ass` — `thm:split` (i) at `α ∈ (0,1)` under the printed `ass:split`: `σ_{n₂,m₂} > 0` for all sizes
  ("which holds whenever `α > 0`") and the normal limit, any `n₂, m₂ → ∞`.
* `split_boot_ass` — `thm:split` (ii) at `α ∈ (0,1)` under `ass:split`: `ŝe*/σ → 1` and the bootstrap CLT of the
  standardised root, any `n₂, m₂ → ∞`.
* `split_zero_boot_any` — `thm:split` (ii) at `α = 0` (`σ > 0`, i.e. `Var U + Var V > 0`): the same two conclusions.
* `split_witness_zero` — "If `f̂ = 0` the statistic is identically zero and the rule never rejects" (with the bootstrap
  SE of (iii), and also with the plug-in SE and the percentile limit of the remark).
* `unique_trim` — `lem:unique`.
* `popthreshold` — `lem:popthreshold`.

Encodings (to be checked by the critic):
* Setting of the frozen split claims (waves 29i/29l/30da/30dd): `ℋ` a real Hilbert space, `φ : 𝒳 → ℋ` strongly
  measurable with `‖φ x‖ ≤ κ` (`ass:regularity` (A1) with the kernel `k(x,x') = ⟨φ x, φ x'⟩`; (A2) enters as strong
  measurability; (A3) only in `unique_trim`, as the frozen `ZeroSet.Characteristic`); `f̂(x) = ⟨f, φ x⟩`; the first fold
  is fixed, i.e. `f̂ = f` is a fixed element of `ℋ` (as printed: "condition on the first fold"); second-fold samples
  `X, Y : ℕ → Ω → 𝒳` measurable, `iIndepFun`, laws `μ.map (X i) = P`, `μ.map (Y i) = Q` (maps guarded by measurability);
  at sizes `n₂ = n`, `m₂ = m` the statistic is `T̂ = splitTrimLo n α (f̂(X_0..X_{n−1})) − splitTrimUp m α (f̂(Y_0..Y_{m−1}))`
  (`eq:splitstat` through `lem:trimmedmean`), and `T = sep(f; 𝒞_α(P), 𝒞_α(Q))` (frozen `sepVal`, identified with a real
  `T`); "probability" of a possibly non-measurable event is the outer measure (an upper bound on it is the stronger
  statement). `H_{0,α}` is `tvDist P Q ≤ α`. The X–Y independence premise of the frozen claims is dropped where it is not
  needed (generalisation). `cor_lower_*_any` impose no `‖f_j‖ ≤ 1` (generalisation: the rules are scale-invariant in `f_j`
  and `f_j = 0` never rejects). `cor_lower_split_any` is `cor:lower` with the plug-in test of the remark after `thm:split`,
  in the general regime (a generalisation of the remark, which may be read as scoped to the ratio regime).
* "`n₂, m₂ → ∞` in any manner": sizes `n, m : ℕ → ℕ`, `n_k, m_k ≥ 1`, tending to `atTop` (as waves 30da, 30dd).
* `‖F − F'‖_∞ = ⨆_u |F(u) − F'(u)|`, `F(u) = F.real (Iic u)`; a law on `[−κ,κ]` is a probability measure on `ℝ` with
  `F([−κ,κ]) = 1` (as wave 30tj); `∫_{−κ}^s` is the interval integral.
* Bootstrap (as frozen wave 29l): the ideal bootstrap, uniform over all `n^n m^m` pairs of index maps `(I, J)`, each
  second-fold sample resampled within itself, independently ("resamples the two second-fold samples of scalars
  independently"); "the conditional law of `(T̂* − T̂)/σ` converges weakly to `N(0,1)` in probability" is encoded as in
  the frozen `split_boot_clt`: for every `t` the exact conditional cdf `splitBootCdfStd` at `t` converges in probability
  to `Φ(t)` (the limit is continuous, so this is equivalent to weak convergence in probability).
* `α̂_lo` is the frozen `alphaLo` of `eq:downclosed`, grid `StrictMono α`, `α_j ∈ [0,1)`; witness `f_j` per level ("a
  different witness at each `α`"); `ass:split` at every `α_j > 0` (no condition at `α_j = 0`, as printed in `ass:split`).
* `unique_trim`: the samples are `x : Fin n → 𝒳`, `y : Fin m → 𝒳` (`n, m ≥ 1`), "pairwise distinct" is `x`, `y`
  injective and `x i ≠ y j`; `[MeasurableSingletonClass 𝒳]`; `𝒯_α` is the frozen `trimSetEmp (φ ∘ x) (φ ∘ y) α β`;
  `D̂_{α,k} = √(min eq:qp)` over `Δ_α(n) × Δ_β(m)`, written `√(sInf (qp '' (capped n α ×ˢ capped m β)))`.
* `popthreshold`: `𝒢_α(P)` is the frozen `IsTrimDensity P α` (measurable, `0 ≤ g ≤ 1/(1−α)` everywhere, `∫ g dP = 1`,
  the encoding of the frozen `region`); "minimum-norm element `d*` of `𝒞_α(P) − 𝒞_β(Q)`" is `‖d‖ ≤ ‖z‖` for every `z` of
  the pointwise difference set (membership of `d` follows from the decomposition `d = a − b`); `d*(x) = ⟨d, φ x⟩`
  (reproducing property); `dist` is the frozen `setDist`; a `(1−α)`-quantile `t` of `d*(X)` is
  `P(d* < t) ≤ 1 − α ≤ P(d* ≤ t)`. Existence of `d*` and of its decomposition is presupposed by the print ("Let `d*` be
  …, write …") and is a hypothesis here, not a conclusion; `dist > 0` is printed and kept, though the conclusion holds
  without it.

Junk-value audit:
* `lowerTrim` is an `iSup` in `ℝ`; for a law on `[−κ,κ]`, `∫ ψ_s dF ≤ ∫ u dF ≤ κ`, so the family is bounded above and the
  `iSup` is genuine (wave 30tj proves `IsLUB`). The `sSup` over the image of `[−κ,κ]` is of a nonempty (`κ ≥ 0` is forced
  by `F([−κ,κ]) = 1`) set bounded by `2κβ`; `⨆_u |F(u) − F'(u)|` is bounded by `1`. The interval integrals are of bounded
  monotone (hence measurable) functions on a bounded interval. `(1 − α)⁻¹` with `α < 1`.
* `dkwRad n δ`: `log(4/δ) > 0` for `δ ∈ (0,1)`, division by `2n` with `n ≥ 1`, `√` of a positive number.
* `splitTrimLo/Up` at sizes `≥ 1` are genuine extrema over the nonempty compact capped simplex. `sepVal` identified with
  a real (no `⊤ − ⊤`). `splitSdAny`, `splitSdZero` divide by sizes `≥ 1`; `split_normal_ass` proves `splitSdAny > 0`, and
  in `split_zero_boot_any` `splitSdZero > 0` follows from `Var_P h + Var_Q h > 0`; so the divisions in the standardised
  root and in `splitBootCdfStd` are by positive numbers. `splitBootSE` is the `√` of a finite average over
  `n^n m^m ≥ 1` resamples (frozen audit). `splitBootPerc` is a finite min–max (frozen audit).
* `alphaLo` is a `sup'` over a nonempty finset or `0` (frozen). `limsup` of `ℝ≥0∞`-valued sequences is genuine.
* `unique_trim`: `sInf` of the image of the nonempty compact feasible set (`n, m ≥ 1`) under the continuous `qp ≥ 0`;
  `√` of a nonnegative number.
* `popthreshold`: `setDist` is an `sInf` of norms over the nonempty regions (nonnegative, bounded below);
  `∫ g • φ dP` is a Bochner integral of a bounded strongly measurable function.

Non-vacuity: `trimlip`, `splitfs`, `cor_lower_fs`: any `F, F'` on `[−κ,κ]`; `P = Q` uniform on `[0,1]`, the clamped `φ`
of the frozen witnesses, `f = 1`. `cor_lower_*_any`, `split_normal_ass`, `split_boot_ass`: the frozen witness
`Wave29i.splitAss_uniform` (uniform law on `[0,1]`, `α = ½`) with `n_k = k + 1`, `m_k = 2^k`. `split_zero_boot_any`: the
clamped `φ`, `f = 1`, `P = Q` uniform (`Var = 1/12`). `unique_trim`: `𝒳 = Fin N`, `φ` the one-hot embedding into
`EuclideanSpace ℝ (Fin N)` (characteristic: the embedding of a probability vector is the vector), any distinct points.
`popthreshold`: any `P, Q` with `TV(P,Q) > max(α, β)`-type separation, e.g. `P = δ_0`, `Q = δ_1` on `ℝ` with `φ` the
clamped identity, where both regions are singletons at distance `1`.

FROZEN 2026-11-07 — hashed in `certify/statements.lock` (with its imports) after the critic's review; AI agents must not
edit it. Critic (2026-11-07, independent, blind back-translation of each claim): ACCEPT ×8, ACCEPT-WITH-NOTE ×3
(`cor_lower_boot_any`, `cor_lower_split_any`: no `‖f_j‖ ≤ 1`, declared; `popthreshold`: existence of `d*` presupposed,
declared); docstring locators and the encodings above corrected before freezing; see `certify/cards/wave30tn.md`.
-/

noncomputable section

namespace StatFormal.Wave30tn

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.TrimmedMMD.BangBang (capped qp)
open StatFormal.TrimmedMMD.ZeroSet (Characteristic IsTrimDensity)
open StatFormal.TrimmedMMD.Unconditional (setDist)
open StatFormal.TrimmedMMD.Lower (alphaLo)
open StatFormal.Wave29i (splitTrimLo splitTrimUp splitSE splitAss)
open StatFormal.Wave29l (splitBootRep splitBootSE splitBootPerc)
open StatFormal.Wave30da (splitSdAny)
open StatFormal.Wave30dd (splitSdZero)
open StatFormal.Wave30ah (trimSetEmp)

/-- `ψ_s(u) = s − β (s − u)_+`, `β = (1 − α)⁻¹` (verbatim the wave-30tj `psi`). -/
def psi (α s u : ℝ) : ℝ := s - (1 - α)⁻¹ * max (s - u) 0

/-- `L(F) = sup_{s ∈ ℝ} ∫ ψ_s dF` (`eq:lowertrim`; verbatim the wave-30tj `lowerTrim`). -/
def lowerTrim (F : Measure ℝ) (α : ℝ) : ℝ := ⨆ s : ℝ, ∫ u, psi α s u ∂F

/-- `e_n(δ) = √(log(4/δ)/(2n))` (`prop:splitfs`). -/
def dkwRad (n : ℕ) (δ : ℝ) : ℝ := √(Real.log (4 / δ) / (2 * n))

/-- The bootstrap cdf of the standardised root `(T̂* − T̂)/s` at `t`: the proportion of the `n^n m^m` equally likely pairs
of resampling index maps `(I, J)` (each second-fold sample resampled within itself, independently) with
`(T̂*(I,J) − T̂)/s ≤ t`, `T̂*(I,J)` the frozen `splitBootRep`, `T̂ = L_n(v_x) − U_m(v_y)`. -/
def splitBootCdfStd (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (s t : ℝ) : ℝ :=
  ((n : ℝ) ^ n * (m : ℝ) ^ m)⁻¹ * ∑ I : Fin n → Fin n, ∑ J : Fin m → Fin m,
    if (splitBootRep n m α vx vy I J - (splitTrimLo n α vx - splitTrimUp m α vy)) / s ≤ t then (1 : ℝ) else 0

namespace Claims

/-- `eq:trimlip` with its lead-in (`appendix/B_split.tex:43-48`): for laws `F, F'` on `[−κ,κ]` and `α ∈ [0,1)`,
`∫(s−u)_+ dF(u) = ∫_{−κ}^s F(u) du` for `s ∈ [−κ,κ]`, and
`|L(F) − L(F')| ≤ sup_{s∈[−κ,κ]} β|∫_{−κ}^s (F − F')(u) du| ≤ 2κβ‖F − F'‖_∞`. -/
def trimlip : Prop :=
  ∀ (F F' : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure F'] (κ α : ℝ),
    F (Icc (-κ) κ) = 1 → F' (Icc (-κ) κ) = 1 → 0 ≤ α → α < 1 →
      (∀ s ∈ Icc (-κ) κ, ∫ u, max (s - u) 0 ∂F = ∫ u in (-κ)..s, F.real (Iic u)) ∧
      |lowerTrim F α - lowerTrim F' α| ≤
        sSup ((fun s => (1 - α)⁻¹ * |∫ u in (-κ)..s, (F.real (Iic u) - F'.real (Iic u))|) '' Icc (-κ) κ) ∧
      sSup ((fun s => (1 - α)⁻¹ * |∫ u in (-κ)..s, (F.real (Iic u) - F'.real (Iic u))|) '' Icc (-κ) κ) ≤
        2 * κ * (1 - α)⁻¹ * ⨆ u : ℝ, |F.real (Iic u) - F'.real (Iic u)|

/-- `prop:splitfs`: for a fixed witness `‖f‖ ≤ 1`, every pair `(P,Q)`, `α ∈ [0,1)`, `δ ∈ (0,1)` and all `n₂, m₂ ≥ 1`,
`P(|T̂ − T| > 2κβ[e_{n₂}(δ) + e_{m₂}(δ)]) ≤ δ`; hence under `H_{0,α}` rejecting when `T̂ > 2κβ[e_{n₂}(δ) + e_{m₂}(δ)]`
has probability at most `δ`, with no condition on the laws of `f̂(X)`, `f̂(Y)`. -/
def splitfs : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α δ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → ‖f‖ ≤ 1 → 0 ≤ α → α < 1 → 0 < δ → δ < 1 →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) → 1 ≤ n → 1 ≤ m →
      ∃ T : ℝ, sepVal f (region φ α P) (region φ α Q) = (T : EReal) ∧
        μ {ω | 2 * κ * (1 - α)⁻¹ * (dkwRad n δ + dkwRad m δ) <
          |splitTrimLo n α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪f, φ (Y j ω)⟫) - T|} ≤
          ENNReal.ofReal δ ∧
        (StatFormal.Distances.tvDist P Q ≤ α →
          μ {ω | 2 * κ * (1 - α)⁻¹ * (dkwRad n δ + dkwRad m δ) <
            splitTrimLo n α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪f, φ (Y j ω)⟫)} ≤
            ENNReal.ofReal δ)

/-- `cor:lower`, finite-sample clause: with each grid level `α_j` tested by `prop:splitfs` (witness `f_j`, `‖f_j‖ ≤ 1`,
reject `H_{0,α_j}` iff `T̂_j > 2κβ_j[e_{n₂}(δ) + e_{m₂}(δ)]`) and the grid read upward (`eq:downclosed`),
`P(α̂_lo > TV(P,Q)) ≤ δ` for all `n₂, m₂ ≥ 1`, with no condition on the laws (no `ass:split`). -/
def cor_lower_fs : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ δ : ℝ)
    (J : ℕ) (α : Fin J → ℝ) (f : Fin J → H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ j, ‖f j‖ ≤ 1) → StrictMono α → (∀ j, α j ∈ Ico (0 : ℝ) 1) →
    0 < δ → δ < 1 →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) → 1 ≤ n → 1 ≤ m →
      μ {ω | StatFormal.Distances.tvDist P Q < alphaLo α (fun j =>
          2 * κ * (1 - α j)⁻¹ * (dkwRad n δ + dkwRad m δ) <
            splitTrimLo n (α j) (fun i => ⟪f j, φ (X i ω)⟫) - splitTrimUp m (α j) (fun i => ⟪f j, φ (Y i ω)⟫))} ≤
        ENNReal.ofReal δ

/-- `cor:lower`, asymptotic clause, with each level tested by `thm:split` as printed in (iii) (bootstrap standard
error, reject iff `T̂ − z ŝe* > 0`, `Φ̄(z) = δ`), `ass:split` at every grid level `α_j > 0` for the witness used
there, and `n₂, m₂ → ∞` in any manner: `limsup P(α̂_lo > TV(P,Q)) ≤ δ`. -/
def cor_lower_boot_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' δ z : ℝ)
    (J : ℕ) (α : Fin J → ℝ) (f : Fin J → H) (q q' : Fin J → ℝ)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → StrictMono α → (∀ j, α j ∈ Ico (0 : ℝ) 1) →
    (∀ j, 0 < α j → splitAss P (fun x => ⟪f j, φ x⟫) (1 - α j) (q j) ∧
      splitAss Q (fun x => ⟪f j, φ x⟫) (α j) (q' j)) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    (gaussianReal 0 1).real (Ioi z) = δ →
      limsup (fun k => μ {ω | StatFormal.Distances.tvDist P Q < alphaLo α (fun j =>
          0 < splitTrimLo (n k) (α j) (fun i => ⟪f j, φ (X i ω)⟫) - splitTrimUp (m k) (α j) (fun i => ⟪f j, φ (Y i ω)⟫) -
            z * splitBootSE (n k) (m k) (α j) (fun i => ⟪f j, φ (X i ω)⟫) (fun i => ⟪f j, φ (Y i ω)⟫))}) atTop ≤
        ENNReal.ofReal δ

/-- `cor:lower`, asymptotic clause, with each level tested by `thm:split` with the plug-in standard error (the remark
after `thm:split`), `n₂, m₂ → ∞` in any manner: `limsup P(α̂_lo > TV(P,Q)) ≤ δ`. -/
def cor_lower_split_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' δ z : ℝ)
    (J : ℕ) (α : Fin J → ℝ) (f : Fin J → H) (q q' : Fin J → ℝ)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → StrictMono α → (∀ j, α j ∈ Ico (0 : ℝ) 1) →
    (∀ j, 0 < α j → splitAss P (fun x => ⟪f j, φ x⟫) (1 - α j) (q j) ∧
      splitAss Q (fun x => ⟪f j, φ x⟫) (α j) (q' j)) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    (gaussianReal 0 1).real (Ioi z) = δ →
      limsup (fun k => μ {ω | StatFormal.Distances.tvDist P Q < alphaLo α (fun j =>
          0 < splitTrimLo (n k) (α j) (fun i => ⟪f j, φ (X i ω)⟫) - splitTrimUp (m k) (α j) (fun i => ⟪f j, φ (Y i ω)⟫) -
            z * splitSE (n k) (m k) (α j) (fun i => ⟪f j, φ (X i ω)⟫) (fun i => ⟪f j, φ (Y i ω)⟫))}) atTop ≤
        ENNReal.ofReal δ

/-- `thm:split` (i) at `α ∈ (0,1)` under the printed `ass:split` (both sides), `n₂, m₂ → ∞` in any manner:
`σ_{n₂,m₂} > 0` for all sizes `n₂, m₂ ≥ 1` ("which holds whenever `α > 0`") and `(T̂ − T)/σ_{n₂,m₂} ⇒ N(0,1)`. -/
def split_normal_ass : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
      (∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < splitSdAny P Q (fun x => ⟪f, φ x⟫) α q q' a b) ∧
      ∃ T : ℝ, sepVal f (region φ α P) (region φ α Q) = (T : EReal) ∧
        TendstoInDistribution (fun k ω =>
            (splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) - T) /
              splitSdAny P Q (fun x => ⟪f, φ x⟫) α q q' (n k) (m k))
          atTop id (fun _ => μ) (gaussianReal 0 1)

/-- `thm:split` (ii) at `α ∈ (0,1)` under `ass:split`, `n₂, m₂ → ∞` in any manner: the bootstrap standard error
satisfies `ŝe*/σ_{n₂,m₂} → 1` in probability, and the conditional law of `(T̂* − T̂)/σ_{n₂,m₂}` converges weakly to
`N(0,1)` in probability (its cdf at every `t` converges in probability to `Φ(t)`). -/
def split_boot_ass : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
      TendstoInMeasure μ (fun (k : ℕ) ω =>
          splitBootSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) /
            splitSdAny P Q (fun x => ⟪f, φ x⟫) α q q' (n k) (m k)) atTop (fun _ => 1) ∧
      ∀ t : ℝ, TendstoInMeasure μ (fun (k : ℕ) ω =>
          splitBootCdfStd (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)
            (splitSdAny P Q (fun x => ⟪f, φ x⟫) α q q' (n k) (m k)) t) atTop
          (fun _ => (gaussianReal 0 1).real (Iic t))

/-- `thm:split` (ii) at `α = 0` (both terms sample means, no condition on the laws), when `σ_{n₂,m₂} > 0`, i.e.
`Var U + Var V > 0`, `n₂, m₂ → ∞` in any manner: `ŝe*/σ_{n₂,m₂} → 1` in probability and the conditional law of
`(T̂* − T̂)/σ_{n₂,m₂}` converges weakly to `N(0,1)` in probability, `σ²_{n₂,m₂} = Var U/n₂ + Var V/m₂`. -/
def split_zero_boot_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    0 < Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] →
      TendstoInMeasure μ (fun (k : ℕ) ω =>
          splitBootSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) /
            splitSdZero P Q (fun x => ⟪f, φ x⟫) (n k) (m k)) atTop (fun _ => 1) ∧
      ∀ t : ℝ, TendstoInMeasure μ (fun (k : ℕ) ω =>
          splitBootCdfStd (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)
            (splitSdZero P Q (fun x => ⟪f, φ x⟫) (n k) (m k)) t) atTop
          (fun _ => (gaussianReal 0 1).real (Iic t))

/-- `thm:split`, "If `f̂ = 0` the statistic is identically zero and the rule never rejects": for the witness `0`, at
every level, all sizes `n₂, m₂ ≥ 1` and every sample, `T̂ = 0`, `ŝe* = 0`, and none of the lower limits `T̂ − z ŝe*` (the theorem's),
`T̂ − z ŝe` (plug-in) and the percentile limit (the software's) is `> 0`. -/
def split_witness_zero : Prop :=
  ∀ (𝒳 H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (α δ z : ℝ)
    (Ω : Type) (X Y : ℕ → Ω → 𝒳) (n m : ℕ) (ω : Ω), 1 ≤ n → 1 ≤ m →
      splitTrimLo n α (fun i => ⟪(0 : H), φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪(0 : H), φ (Y j ω)⟫) = 0 ∧
      splitBootSE n m α (fun i => ⟪(0 : H), φ (X i ω)⟫) (fun j => ⟪(0 : H), φ (Y j ω)⟫) = 0 ∧
      ¬ (0 < splitTrimLo n α (fun i => ⟪(0 : H), φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪(0 : H), φ (Y j ω)⟫) -
          z * splitBootSE n m α (fun i => ⟪(0 : H), φ (X i ω)⟫) (fun j => ⟪(0 : H), φ (Y j ω)⟫)) ∧
      ¬ (0 < splitTrimLo n α (fun i => ⟪(0 : H), φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪(0 : H), φ (Y j ω)⟫) -
          z * splitSE n m α (fun i => ⟪(0 : H), φ (X i ω)⟫) (fun j => ⟪(0 : H), φ (Y j ω)⟫)) ∧
      ¬ (0 < splitBootPerc n m α δ (fun i => ⟪(0 : H), φ (X i ω)⟫) (fun j => ⟪(0 : H), φ (Y j ω)⟫))

/-- `lem:unique`: under (A1)–(A3), measurable singletons, `α, β ∈ [0,1)` and pairwise distinct
`X_1, …, X_n, Y_1, …, Y_m` (`n, m ≥ 1`): `D̂_{α,k} = √(min eq:qp) > 0` and the empirical trimming set `𝒯_α`
(minimisers of `eq:qp` over `Δ_α(n) × Δ_β(m)`) is a singleton. -/
def unique_trim : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (φ : 𝒳 → H) (κ : ℝ) (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (α β : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ → 0 < n → 0 < m →
    0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
    Function.Injective x → Function.Injective y → (∀ i j, x i ≠ y j) →
      0 < √(sInf (qp (φ ∘ x) (φ ∘ y) '' (capped n α ×ˢ capped m β))) ∧
      ∃ p, trimSetEmp (φ ∘ x) (φ ∘ y) α β = {p}

/-- `lem:popthreshold`: under (A1), `α, β ∈ [0,1)` and `dist(𝒞_α(P), 𝒞_β(Q)) > 0`, let `d` be the minimum-norm element
of `𝒞_α(P) − 𝒞_β(Q)`, decomposed as `d = a − b` with `a = E_P[g φ]`, `g ∈ 𝒢_α(P)`, `b ∈ 𝒞_β(Q)`, and let `t` be any
`(1−α)`-quantile of `d(X) = ⟨d, φ(X)⟩`, `X ∼ P`. Then `g = (1−α)⁻¹` `P`-a.s. on `{d(X) < t}` and `g = 0` `P`-a.s. on
`{d(X) > t}`. -/
def popthreshold : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α β t : ℝ)
    (d a b : H) (g : 𝒳 → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
    0 < setDist (region φ α P) (region φ β Q) →
    (∀ z ∈ region φ α P - region φ β Q, ‖d‖ ≤ ‖z‖) →
    IsTrimDensity P α g → a = ∫ x, g x • φ x ∂P → b ∈ region φ β Q → d = a - b →
    P.real {x | ⟪d, φ x⟫ < t} ≤ 1 - α → 1 - α ≤ P.real {x | ⟪d, φ x⟫ ≤ t} →
      (∀ᵐ x ∂P, ⟪d, φ x⟫ < t → g x = 1 / (1 - α)) ∧ (∀ᵐ x ∂P, t < ⟪d, φ x⟫ → g x = 0)

end Claims

end StatFormal.Wave30tn
