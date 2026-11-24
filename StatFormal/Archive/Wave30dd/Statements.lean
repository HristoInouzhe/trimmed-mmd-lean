import StatFormal.Archive.Wave30da.Statements
import StatFormal.Archive.Wave29l.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30dd: trimmed-mmd `thm:split` in the general regime `n₂, m₂ → ∞` — the printed
# bootstrap clause (`α ∈ [0,1)`, bootstrap-SE consistency and the bootstrap-SE certificate) and the case `α = 0`
# (plain sample means: CLT, plug-in coverage, unconditional level/certification)

Source (pCloud = GitHub master, copied 2026-10-27 to `~/.cache/tm`): `trimmed-mmd/paper.tex` `thm:split`
(`:1063-1076`): "Let Assumptions `ass:regularity` and `ass:split` hold and fix `α ∈ [0,1)`. Hold the first fold
fixed, so that `f̂` is a fixed unit vector, and let only the second fold grow. Then `T̂` in `eq:splitstat` is
asymptotically normal as `n₂, m₂ → ∞`, with a variance consistently estimated by the nonparametric bootstrap on the
scalars `f̂(X_i^{(2)})`, `f̂(Y_j^{(2)})`. Let `T̂_δ` be the resulting one-sided `1 − δ` lower confidence limit. Then
the rule reject `H_{0,α}` if `T̂_δ > 0` has asymptotic level `δ`, and rejection certifies `TV(P,Q) > α`";
`ass:split` (`:1050-1062`: "If `α = 0` both terms are sample means and no condition is imposed"); proof
`supplement.tex:747-791` ("the nonparametric bootstrap is consistent for them … the asymptotic variance of `T̂`,
`(1−α)^{-2}[Var_P(q − f̂(X))_+/n₂ + Var_Q(f̂(Y) − q')_+/m₂]`"). The print states NO ratio condition on `n₂, m₂`.
Frozen coverage, ratio regime `m(n)/n → κ ∈ (0, ∞)` only: the bootstrap for `α > 0` (wave 29l `split_boot_se`,
`split_level_bootstrap`, `split_boot_clt`, `split_boot_percentile`), `α = 0` with the plug-in SE (wave 29w
`split_zero_asymp_normal`, `split_zero_coverage`, `split_zero_level`) and with the bootstrap (wave 30d
`split_zero_boot_*`). The general regime for `α > 0` with the plug-in SE is the draft wave 30da
(`split_normal_any`, `split_level_any`), whose definition `splitSdAny` is reused here.

Imports the statement files of wave 30da (`splitSdAny`; through it the frozen wave 29i `splitTrimLo`, `splitTrimUp`,
`splitSE`, `splitUQ`, `splitAss`, wave 17a `sepVal`, `TrimmedMMD/Concentration` `region`, `Distances` `tvDist`) and
the frozen wave 29l (`splitBootSE`: the exact ideal bootstrap standard error, over all `n^n m^m` resamples). New
definition: `splitSdZero` (the asymptotic standard deviation `√(Var_P h/n + Var_Q h/m)` at `α = 0`).

Setting of every claim: the frozen wave-29i/29l/29w setting verbatim (`h = ⟨f, φ⟩`, `φ` strongly measurable and
bounded, `X`, `Y` i.i.d. samples from `P`, `Q`), with the ratio premise `0 < κ`, `m(n)/n → κ` replaced by
ARBITRARY sizes `n, m : ℕ → ℕ` with `n_k, m_k ≥ 1`, `n_k → ∞`, `m_k → ∞`; the statistic at stage `k` is
`T̂_k = splitTrimLo (n_k) α (h(X)) − splitTrimUp (m_k) α (h(Y))`.

Covered (7 claims).
Part 1, the bootstrap clause, `α ∈ (0,1)` (`split_boot_se_any` is vacuous at `α = 0`: quantile uniqueness at `p = 1` fails;
the `α = 0` bootstrap clause is `split_zero_boot_se_any`), under quantile uniqueness (`α > 0` under `ass:split`):
* `split_boot_se_any` — "a variance consistently estimated by the nonparametric bootstrap": `ŝe*_k / se_k → 1` in
  probability, `ŝe*_k = splitBootSE (n_k) (m_k) α` (frozen 29l), `se_k = √(Var_P(q − h)_+/n_k +
  Var_Q(h − q')_+/m_k)/(1 − α)` (wave 30da `splitSdAny`, the printed variance), under the frozen `split_boot_se`
  premises (quantile uniqueness both sides, no fold independence) minus the ratio, plus `Var_P(q − h)_+ > 0`,
  `Var_Q(h − q')_+ > 0` (declared; as in wave 30da `split_normal_any`: they make `se_k > 0`; both follow from
  `ass:split` at `α > 0`).
* `split_level_bootstrap_any` — the frozen `split_level_bootstrap` (printed `ass:regularity` + `ass:split`,
  `0 < α < 1`, `Φ̄(z) = δ`) in the general regime: asymptotic coverage `≥ 1 − δ − η` of `T̂_δ = T̂_k − z ŝe*_k`,
  asymptotic level `δ` under `TV ≤ α`, certification on the coverage event.
Part 2, `α = 0` (no condition on the laws, as printed in `ass:split`):
* `split_zero_normal_any` — "asymptotically normal as `n₂, m₂ → ∞`": `sep(f; 𝒞₀(P), 𝒞₀(Q)) = P h − Q h` and
  `(T̂_k − (P h − Q h))/sd_k ⇒ N(0,1)`, `sd_k = splitSdZero = √(Var_P h/n_k + Var_Q h/m_k)`, when
  `Var_P h + Var_Q h > 0` (declared; needed for `sd_k > 0`; one of the two variances may vanish).
* `split_zero_coverage_any` — the frozen `split_zero_coverage` (plug-in `ŝe = splitSE … 0`) in the general regime,
  `Var_P h + Var_Q h > 0`: `P(T̂_k − z ŝe_k ≤ sep) → Φ(z)` for every `z`.
* `split_zero_level_any` — the frozen `split_zero_level` (UNCONDITIONAL: also when `Var_P h = Var_Q h = 0`) in the
  general regime: coverage, level `δ` under `TV ≤ 0`, certification `TV > 0`, for `T̂_k − z ŝe_k`.
* `split_zero_boot_se_any` — the bootstrap clause at `α = 0`: `ŝe*_k / sd_k → 1` in probability
  (`ŝe*_k = splitBootSE (n_k) (m_k) 0`), `Var_P h + Var_Q h > 0`, no fold independence (as the frozen 30d
  `split_zero_boot_se`).
* `split_zero_level_bootstrap_any` — the frozen 30d `split_zero_level_bootstrap` (UNCONDITIONAL) in the general
  regime, for `T̂_k − z ŝe*_k`.

Encodings (to be checked by the critic): those of the frozen claims (`splitTrimLo/Up` through the capped simplex,
`splitSE`, `splitBootSE`, `splitUQ`, `splitAss`, `sepVal` in `EReal`, "in probability" = `TendstoInMeasure` to a
constant, `TendstoInDistribution` to `id` under `N(0,1)`, `H_{0,α}` = `tvDist P Q ≤ α`, `δ = Φ(Ioi z)`); a
"sequence `n₂, m₂ → ∞`" is a pair `n, m : ℕ → ℕ` tending to `atTop` (as in wave 30da); `n_k, m_k ≥ 1` (declared;
sample sizes) excludes the `/0` of `splitSdAny`, `splitSdZero`, `splitSE` and the empty-sample conventions of
`splitTrimLo/Up` and loses nothing asymptotically. The frozen first conjuncts `n ŝe*² → σ²` (29l, 30d) are
replaced by the ratio `ŝe*_k/se_k → 1` (no common scale `√n`); a scale-free analogue `(ŝe*_k² − sd_k²)/(1/n_k + 1/m_k) → 0`,
which would also cover the degenerate case, is not stated.

Not covered (declared): the bootstrap CLT of the root and the percentile lower limit (frozen 29l
`split_boot_clt`, `split_boot_percentile`, 30d `split_zero_boot_clt`, `split_zero_boot_percentile`) in the general
regime — they belong to the proof's implementation remark ("The implementation takes the percentile bootstrap
limit"), not to the printed theorem, and remain certified in the ratio regime; `α = 0` normality when
`Var_P h = Var_Q h = 0` (degenerate; the level claim covers that case); the bootstrap-SE ratio when one of the two
variances vanishes (`α > 0`); a `B`-replicate Monte Carlo bootstrap (ideal bootstrap, as frozen); the first fold is
fixed (`f̂ = f`, as printed).

Non-vacuity: the premises of `split_level_bootstrap_any` are those of wave 30da `split_level_any` (frozen
`split_level_discharged` minus the ratio, plus `n_k, m_k ≥ 1`), met by the frozen witness
`Wave29i.splitAss_uniform` (uniform law on `[0,1]`, `P = Q`, `α = 1/2`) with `n_k = k + 1`, `m_k = 2^k` (outside
every ratio regime: `m_k/n_k → ∞`); those of `split_boot_se_any` then hold too (`splitAss ⇒ splitUQ`, positive
influence variances, proved in the routes). For part 2 the premises are those of the frozen 29w/30d claims minus the
ratio; `Var_P h + Var_Q h > 0` holds for the clamped `φ x = max 0 (min x 1)` (bounded, as frozen 29i), `f = 1`, `P = Q`
uniform on `[0,1]` (`Var = 1/12`); the `α > 0` witness `splitAss_uniform` likewise uses the clamped `φ`, and the
unconditional claims also have the degenerate witness `f = 0`. Route `RouteChecks` (not a target) checks that
`n_k = k + 1`, `m_k = 2^k` meet the size premises (`wdd_sizes`) and restates the frozen `ass:split` witness; the
i.i.d. sampling premises are those of the frozen claims (critic-checked there).

Proof notes (draft author, 2026-10-27; `#print axioms`: propext, Classical.choice, Quot.sound for all 7 claims; no
`sorry`): `RouteBoot` — the one-sample bootstrap consistency `tip0_bootLo_var` (no ratio) on each side along
`n_k`, `m_k`, the exact split `bootVar2_eq` of the bootstrap variance over the two independent resamples, a
convex-combination ratio bound, and the wave-30da general-regime normal limit `wda_normal` (subsequence /
Bolzano–Weierstrass on the weights); `RouteZero` — a variant `wdd_core` of the wave-30da core with Gaussian limits
of arbitrary variance (a side with `Var = 0` contributes `A ≡ 0`, `N(0,0)`), the sample-mean identities
`statT_zero`, plug-in consistency `tip0_varLo_zero`, the degenerate case `Var_P h = Var_Q h = 0` (a.s. constant
samples), the frozen `Wave22c.split_level`, `Wave29w.sep_zero`, `Wave30d.splitBootSE_zero`.

Junk audit: `splitSdAny`, `splitSdZero`, `splitSE` divide by `n_k, m_k ≥ 1` only; the ratios divide by `se_k > 0`,
`sd_k > 0` (positive variances); `splitBootSE` is the `√` of a genuine finite average over `n^n m^m ≥ 1` resamples
(frozen audit); `√` of variances; `splitTrimLo/Up` at `n_k, m_k ≥ 1` are genuine extrema over the nonempty compact
capped simplex; `toNNReal` only of `1` (`N(0,1)`).

FROZEN 2026-10-27 — hashed in `certify/statements.lock` (with its imports) after the critic's review; AI agents must not edit it.
Critic (2026-10-27): ACCEPT (splitSdZero and 4 claims), ACCEPT-WITH-NOTE (split_boot_se_any, split_zero_normal_any,
split_zero_boot_se_any); see certify/cards/wave30dd.md.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace StatFormal.Wave30dd

/-- The asymptotic standard deviation of `T̂` at `α = 0` and sizes `n₂ = n`, `m₂ = m` (`supplement.tex:765-766` at
`α = 0`, where `(q − h)_+ = q − h`, `(h − q')_+ = h − q'` at the extreme quantiles):
`sd_{n,m} = √(Var_P h / n + Var_Q h / m)`. -/
def splitSdZero {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) (h : 𝒳 → ℝ) (n m : ℕ) : ℝ :=
  √(Var[h; P] / n + Var[h; Q] / m)

namespace Claims

open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.Wave29i (splitTrimLo splitTrimUp splitSE splitUQ splitAss)
open StatFormal.Wave29l (splitBootSE)
open StatFormal.Wave30da (splitSdAny)

/-- `thm:split`, "a variance consistently estimated by the nonparametric bootstrap", GENERAL regime: for any sizes
`n_k, m_k ≥ 1` with `n_k, m_k → ∞`, the ideal bootstrap standard error `ŝe*_k` of `T̂_k` satisfies
`ŝe*_k / se_k → 1` in probability, `se_k = √(Var_P(q − h)_+/n_k + Var_Q(h − q')_+/m_k)/(1 − α)`, under quantile
uniqueness on both sides and positive influence variances (the frozen `split_boot_se` minus the ratio). -/
def split_boot_se_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 ≤ α → α < 1 →
    splitUQ P (fun x => ⟪f, φ x⟫) (1 - α) q → splitUQ Q (fun x => ⟪f, φ x⟫) α q' →
    0 < Var[fun x => max (q - ⟪f, φ x⟫) 0; P] → 0 < Var[fun x => max (⟪f, φ x⟫ - q') 0; Q] →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
      TendstoInMeasure μ (fun (k : ℕ) ω =>
          splitBootSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) /
            splitSdAny P Q (fun x => ⟪f, φ x⟫) α q q' (n k) (m k)) atTop (fun _ => 1)

/-- `thm:split` with the bootstrap standard error, GENERAL regime, UNCONDITIONAL: coverage, asymptotic level `δ`
and certification for `T̂_δ = T̂_k − z ŝe*_k`, under `ass:regularity` and `ass:split` (`0 < α < 1`) — the frozen
`split_level_bootstrap` with `m(n)/n → κ > 0` replaced by arbitrary sizes `n_k, m_k ≥ 1`, `n_k, m_k → ∞`. -/
def split_level_bootstrap_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ α P) (region φ α Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ α →
          ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, μ {ω | 0 < splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) -
            splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)} ≤
              ENNReal.ofReal (δ + η)) ∧
      (∀ k, ∀ ω, ((splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ α P) (region φ α Q) →
          0 < splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) →
          α < StatFormal.Distances.tvDist P Q)

/-- `thm:split` at `α = 0`, asymptotic normality, GENERAL regime, no condition on the laws beyond
`Var_P h + Var_Q h > 0`: the population separation at `α = 0` is `T₀ = E_P h − E_Q h` (`h = ⟨f, φ⟩`) and
`(T̂_k − T₀)/√(Var_P h/n_k + Var_Q h/m_k) ⇒ N(0,1)` for any sizes `n_k, m_k ≥ 1`, `n_k, m_k → ∞`. -/
def split_zero_normal_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    0 < Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] →
      sepVal f (region φ 0 P) (region φ 0 Q) = ((∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q : ℝ) : EReal) ∧
        TendstoInDistribution (fun k ω =>
            (splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
              (∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q)) / splitSdZero P Q (fun x => ⟪f, φ x⟫) (n k) (m k))
          atTop id (fun _ => μ) (gaussianReal 0 1)

/-- `thm:split` at `α = 0`, coverage of the plug-in normal lower limit, GENERAL regime: if `Var_P h + Var_Q h > 0`,
`P(T̂_k − z ŝe_k ≤ sep) → Φ(z)` for every `z` (the frozen `split_zero_coverage` minus the ratio). -/
def split_zero_coverage_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    0 < Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] →
      ∀ z : ℝ, Tendsto (fun k => μ.real {ω |
          ((splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q)}) atTop (𝓝 ((gaussianReal 0 1).real (Iic z)))

/-- `thm:split` at `α = 0`, GENERAL regime, UNCONDITIONAL (no condition on the laws, no non-degeneracy): with the
plug-in lower limit `T̂_δ = T̂_k − z ŝe_k` (`Φ(Ioi z) = δ`), coverage `≥ 1 − δ − η` eventually, asymptotic level `δ`
under `TV(P,Q) ≤ 0`, and certification `TV(P,Q) > 0` on the coverage event — the frozen `split_zero_level` with the
ratio replaced by arbitrary sizes `n_k, m_k ≥ 1`, `n_k, m_k → ∞`. -/
def split_zero_level_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ 0 →
          ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, μ {ω | 0 < splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) -
            splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)} ≤
              ENNReal.ofReal (δ + η)) ∧
      (∀ k, ∀ ω, ((splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q) →
          0 < splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) →
          0 < StatFormal.Distances.tvDist P Q)

/-- `thm:split` at `α = 0`, "a variance consistently estimated by the nonparametric bootstrap", GENERAL regime:
`ŝe*_k / √(Var_P h/n_k + Var_Q h/m_k) → 1` in probability when `Var_P h + Var_Q h > 0` (no condition on the laws,
no fold independence; the frozen 30d `split_zero_boot_se` minus the ratio). -/
def split_zero_boot_se_any : Prop :=
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
            splitSdZero P Q (fun x => ⟪f, φ x⟫) (n k) (m k)) atTop (fun _ => 1)

/-- `thm:split` at `α = 0` with the bootstrap standard error, GENERAL regime, UNCONDITIONAL: coverage, asymptotic
level `δ` and certification `TV(P,Q) > 0` for `T̂_δ = T̂_k − z ŝe*_k` — the frozen 30d `split_zero_level_bootstrap`
with the ratio replaced by arbitrary sizes `n_k, m_k ≥ 1`, `n_k, m_k → ∞`. -/
def split_zero_level_bootstrap_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ 0 →
          ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, μ {ω | 0 < splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) -
            splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)} ≤
              ENNReal.ofReal (δ + η)) ∧
      (∀ k, ∀ ω, ((splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q) →
          0 < splitTrimLo (n k) 0 (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) 0 (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitBootSE (n k) (m k) 0 (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) →
          0 < StatFormal.Distances.tvDist P Q)

end Claims

end StatFormal.Wave30dd
