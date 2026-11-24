import StatFormal.Archive.Wave29i.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 29l: trimmed MMD `thm:split` with the printed bootstrap — consistency of the bootstrap
# standard error, the bootstrap-SE certificate, the bootstrap CLT for the root, and the percentile certificate

Sources (current text, read 2026-10-20, `trimmed-mmd/`): `thm:split` (`paper.tex:1165-1178`: "asymptotically normal
… with a variance consistently estimated by the nonparametric bootstrap on the scalars `f̂(X_i^{(2)})`,
`f̂(Y_j^{(2)})`. Let `T̂_δ` be the resulting one-sided `1 − δ` lower confidence limit. Then the rule reject `H_{0,α}`
if `T̂_δ > 0` has asymptotic level `δ`, and rejection certifies `TV(P,Q) > α`"), `eq:splitstat` (`:1145-1151`),
`ass:split` (`:1153-1163`), `ass:regularity` (`:545-560`); the proof of `thm:split` (`supplement.tex:400-414`: "the
nonparametric bootstrap is consistent for them [vdV Thm 19.3, Lem 21.4, §23.2] … The implementation takes the
percentile bootstrap limit of the resampled statistic rather than a variance estimate and a normal quantile; the two
are first-order equivalent here").
Imports the frozen `Wave29i` statements (`splitTrimLo`, `splitTrimUp`, `splitStat`, `splitSigma2`, `splitUQ`,
`splitAss`; the route checks use `split_level_boot`, `split_asymp_normal`; through them `Wave22c` `split_level`,
`TrimmedMMD/BangBang` `capped`, `TrimmedMMD/Concentration` `region`, `Wave17a` `sepVal`, `Distances` `tvDist`), not
copied; Mathlib otherwise.

Covered:
* `split_boot_se` (the printed "variance consistently estimated by the nonparametric bootstrap"): with
  `ŝe*_n = splitBootSEn` the conditional standard deviation of the bootstrap replicate `T̂*` given the data (both
  second-fold samples resampled independently with replacement), under quantile UNIQUENESS (as the frozen
  `split_asymp_normal`; generalises `ass:split`; no independence between the folds' `X` and `Y` needed) and
  `m(n)/n → κ > 0`: `n ŝe*_n² → σ²` in probability, and, if `σ² > 0`, `ŝe*_n / se_n → 1` in probability
  (`se_n = σ/√n`) — exactly the hypothesis of the frozen conditional `split_level_boot`.
* `split_level_bootstrap`: `thm:split` with the bootstrap standard error, UNCONDITIONAL: coverage
  `liminf P(T̂_δ ≤ sep) ≥ 1 − δ`, asymptotic level `δ` of "reject if `T̂_δ > 0`" under `H_{0,α}`, and rejection on
  the coverage event certifies `TV(P,Q) > α`, with `T̂_δ = T̂_n − z ŝe*_n`, `Φ(Ioi z) = δ`. Same hypotheses as the
  frozen `split_level_discharged`. Route `split_boot_check` (not a target): frozen `Wave29i.split_level_boot` +
  `split_boot_se` ⇒ `split_level_bootstrap` (a corollary of the two; stated because the author asked for the
  printed bootstrap-SE certificate as a claim).
* `split_boot_clt` (the bootstrap CLT behind "the nonparametric bootstrap is consistent"): for every `t`, the
  bootstrap cdf `splitBootCdfn` of the root `√n (T̂* − T̂)` at `t` converges in probability to `Φ_σ(t) =
  N(0, σ²)(−∞, t]` (the conditional law of the root converges weakly to `N(0, σ²)` in probability), under quantile
  uniqueness, `σ² > 0`, `m(n)/n → κ > 0`.
* `split_boot_percentile` (the implementation: "the percentile bootstrap limit of the resampled statistic"):
  coverage, asymptotic level `δ` and certification, UNCONDITIONAL, for the percentile lower limit
  `T̂_δ = splitBootPercn` (the bootstrap `δ`-quantile of `T̂*`), same hypotheses as `split_level_bootstrap`.
  Route `split_perc_check` (not a target): frozen `Wave29i.split_asymp_normal` + `split_boot_clt` + frozen
  `Wave22c.split_level` ⇒ `split_boot_percentile`.

Not covered (declared):
* `α = 0` (inherits the frozen `thm:split` encoding: `ass:split` is unsatisfiable there, DEFECTS #110); the
  general `n₂, m₂ → ∞` regime (only `m(n)/n → κ ∈ (0,∞)`); the first fold is fixed (`f̂ = f`).
* Monte Carlo approximation of the bootstrap: `ŝe*`, the bootstrap cdf and the percentile limit are the exact
  (ideal) bootstrap quantities, over all `n^n m^m` resamples; a `B`-replicate Monte Carlo approximation is not
  formalised. The "first-order equivalent" sentence is reflected only in that both limits have asymptotic level
  `δ`; their difference `o_P(n^{−1/2})` is not stated.
* For the percentile form, only `liminf` coverage `≥ 1 − δ` is stated (as in the frozen claims, which is what the
  level and certification need); the matching `limsup ≤ 1 − δ` (same argument at `σ(−θ − z)`) is not proved.

Encodings (to be checked by the critic):
* Frozen `thm:split` objects: `T̂_n = splitStat`, `v_x = (⟪f, φ X_i⟫)_{i<n}`, `v_y = (⟪f, φ Y_j⟫)_{j<m(n)}`,
  `σ² = splitSigma2`, `splitUQ`, `splitAss`, the coverage/level/certification triple of the frozen
  `split_level_discharged`, verbatim with `T̂_n − z splitSEn` replaced by `T̂_n − z splitBootSEn`, resp. by
  `splitBootPercn`.
* Bootstrap: resampling with replacement = a uniformly random index map `I : Fin n → Fin n` (i.i.d. uniform draws),
  independent of `J : Fin m → Fin m`; the replicate `T̂*(I,J) = splitTrimLo n α (v_x ∘ I) − splitTrimUp m α (v_y ∘ J)`
  (`splitBootRep`: the printed statistic `eq:splitstat` recomputed on the resample), its conditional mean
  `splitBootMean = (n^n m^m)⁻¹ Σ_{I,J} T̂*(I,J)` and conditional variance `splitBootVar = (n^n m^m)⁻¹ Σ_{I,J}
  (T̂*(I,J) − splitBootMean)²` (exact finite averages over the `n^n m^m` equally likely resamples, i.e. the
  conditional law given the data), `splitBootSE = √splitBootVar`; the conditional cdf of the root
  `splitBootCdf t = (n^n m^m)⁻¹ #{(I,J) : √n (T̂*(I,J) − T̂) ≤ t}`; the percentile limit `splitBootPerc` = the
  `⌈δ n^n m^m⌉`-th smallest replicate, as `min_{|S| = k} max_{p ∈ S} T̂*(p)` (the frozen `splitOrdStat` form on the
  resample index type). `…n` variants evaluate at the sample. This is the implementation
  (`trimmed-mmd/src/trimmedmmd/splitting.py:143-148`: each second-fold sample resampled with replacement within
  itself, independently; the statistic recomputed on the resample; `lower = np.quantile(boots, delta)`, i.e.
  Efron's percentile limit, not the basic `2T̂ − q*_{1−δ}`), with the `B`-replicate Monte Carlo replaced by the
  ideal bootstrap and `np.quantile`'s interpolation by the `⌈δN⌉`-th order statistic (both asymptotically
  negligible; not formalised). Efron's form is valid here because the limit `N(0, σ²)` is symmetric.
* "In probability" is `TendstoInMeasure` to the constant (as in the frozen `split_level_boot`); `Φ_σ(t)` is
  `(gaussianReal 0 σ².toNNReal).real (Iic t)`; `δ ∈ (0,1)` enters as `Φ(Ioi z) = δ` (as in the frozen claims).

Junk-value audit:
* `(n:ℝ)^n m^m ≥ 1` always (`0^0 = 1`; `Fin 0 → Fin 0` has one element), so the averages are genuine; `√` of a
  variance (a nonnegative average of squares) is genuine. `splitTrimLo/Up` at `n = 0` are `sInf ∅ = sSup ∅ = 0` only
  for finitely many `n` (asymptotic claims). Division by `√σ²/√n` only under `σ² > 0`, `n ≥ 1` eventually; `/0`
  at `n = 0` is one index. `σ² = splitSigma2` is a genuine variance of bounded measurable functions; `toNNReal` of
  `σ² > 0` is faithful.
* `splitBootPerc`: `k = ⌈δ n^n m^m⌉₊ ∈ [1, n^n m^m]` for `0 < δ < 1` (implied by `Φ(Ioi z) = δ`), so the `⨅` is over
  a nonempty finite family and each `⨆` over a nonempty finite set: a genuine order statistic (proved:
  `fOrd_le_iff`). No `sInf`/`sSup` of unbounded or empty sets in `ℝ`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section

namespace StatFormal.Wave29l

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

open StatFormal.Wave29i (splitTrimLo splitTrimUp splitStat splitSigma2 splitUQ splitAss)

/-- The bootstrap replicate `T̂*(I, J) = L_n(v_x ∘ I) − U_m(v_y ∘ J)` of the split statistic at the resampling index
maps `I : [n] → [n]`, `J : [m] → [m]` (frozen `splitTrimLo`, `splitTrimUp`). -/
def splitBootRep (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (I : Fin n → Fin n) (J : Fin m → Fin m) : ℝ :=
  splitTrimLo n α (vx ∘ I) - splitTrimUp m α (vy ∘ J)

/-- The bootstrap mean `E*[T̂*] = (n^n m^m)⁻¹ Σ_{I,J} T̂*(I, J)` (uniform over the `n^n m^m` resamples). -/
def splitBootMean (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ :=
  ((n : ℝ) ^ n * (m : ℝ) ^ m)⁻¹ * ∑ I : Fin n → Fin n, ∑ J : Fin m → Fin m, splitBootRep n m α vx vy I J

/-- The bootstrap variance `Var*[T̂*] = (n^n m^m)⁻¹ Σ_{I,J} (T̂*(I, J) − E*[T̂*])²`. -/
def splitBootVar (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ :=
  ((n : ℝ) ^ n * (m : ℝ) ^ m)⁻¹ *
    ∑ I : Fin n → Fin n, ∑ J : Fin m → Fin m, (splitBootRep n m α vx vy I J - splitBootMean n m α vx vy) ^ 2

/-- The bootstrap standard error `ŝe* = √Var*[T̂*]`. -/
def splitBootSE (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ := √(splitBootVar n m α vx vy)

/-- The bootstrap standard error of `T̂_n` at the sample. -/
def splitBootSEn {Ω 𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (f : H)
    (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ) (α : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  splitBootSE n (m n) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)

/-- The bootstrap cdf of the root `√n (T̂* − T̂)` at `t`: the conditional probability, given the data, that
`√n (T̂*(I, J) − T̂) ≤ t` (`T̂ = L_n(v_x) − U_m(v_y)`). -/
def splitBootCdf (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (t : ℝ) : ℝ :=
  ((n : ℝ) ^ n * (m : ℝ) ^ m)⁻¹ * ∑ I : Fin n → Fin n, ∑ J : Fin m → Fin m,
    if √(n : ℝ) * (splitBootRep n m α vx vy I J - (splitTrimLo n α vx - splitTrimUp m α vy)) ≤ t then (1 : ℝ)
    else 0

/-- The bootstrap cdf of the root at the sample. -/
def splitBootCdfn {Ω 𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (f : H)
    (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ) (α : ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  splitBootCdf n (m n) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) t

/-- The percentile lower limit: the `⌈δ n^n m^m⌉`-th smallest of the `n^n m^m` bootstrap replicates `T̂*(I, J)`,
`min_{|S| = ⌈δ n^n m^m⌉} max_{(I,J) ∈ S} T̂*(I, J)` (the bootstrap `δ`-quantile of `T̂*`, Efron's percentile limit). -/
def splitBootPerc (n m : ℕ) (α δ : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ :=
  ⨅ S : {S : Finset ((Fin n → Fin n) × (Fin m → Fin m)) // S.card = ⌈δ * ((n : ℝ) ^ n * (m : ℝ) ^ m)⌉₊},
    ⨆ p : S.1, splitBootRep n m α vx vy p.1.1 p.1.2

/-- The percentile lower limit at the sample. -/
def splitBootPercn {Ω 𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (f : H)
    (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ) (α δ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  splitBootPerc n (m n) α δ (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)

namespace Claims

open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

/-- `thm:split`, "a variance consistently estimated by the nonparametric bootstrap": under quantile uniqueness and
`m(n)/n → κ > 0`, `n ŝe*_n² → σ²` in probability and, when `σ² > 0`, `ŝe*_n / (σ/√n) → 1` in probability. -/
def split_boot_se : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 ≤ α → α < 1 →
    splitUQ P (fun x => ⟪f, φ x⟫) (1 - α) q → splitUQ Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
      TendstoInMeasure μ (fun (n : ℕ) ω => (n : ℝ) * splitBootSEn φ f X Y m α n ω ^ 2) atTop
          (fun _ => splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ) ∧
        (0 < splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ →
          TendstoInMeasure μ (fun (n : ℕ) ω => splitBootSEn φ f X Y m α n ω /
              (√(splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ) / √(n : ℝ))) atTop (fun _ => 1))

/-- `thm:split` with the bootstrap standard error, UNCONDITIONAL: coverage, asymptotic level `δ` and certification
for `T̂_δ = T̂_n − z ŝe*_n`, under `ass:regularity` and `ass:split`. -/
def split_level_bootstrap : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitStat φ f X Y m α n ω - z * splitBootSEn φ f X Y m α n ω : ℝ) : EReal) ≤
            sepVal f (region φ α P) (region φ α Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ α →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
            μ {ω | 0 < splitStat φ f X Y m α n ω - z * splitBootSEn φ f X Y m α n ω} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ n, ∀ ω, ((splitStat φ f X Y m α n ω - z * splitBootSEn φ f X Y m α n ω : ℝ) : EReal) ≤
          sepVal f (region φ α P) (region φ α Q) →
          0 < splitStat φ f X Y m α n ω - z * splitBootSEn φ f X Y m α n ω → α < StatFormal.Distances.tvDist P Q)

/-- The proof of `thm:split`, "the nonparametric bootstrap is consistent": the conditional law of the root
`√n (T̂* − T̂)` given the data converges weakly to `N(0, σ²)` in probability — for every `t`, the bootstrap cdf at `t`
converges in probability to `Φ_σ(t)` (quantile uniqueness, `σ² > 0`, `m(n)/n → κ > 0`). -/
def split_boot_clt : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 ≤ α → α < 1 →
    splitUQ P (fun x => ⟪f, φ x⟫) (1 - α) q → splitUQ Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    0 < splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ →
      ∀ t : ℝ, TendstoInMeasure μ (fun (n : ℕ) ω => splitBootCdfn φ f X Y m α n ω t) atTop
        (fun _ => (gaussianReal 0 (splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ).toNNReal).real (Iic t))

/-- `thm:split` with the percentile bootstrap lower limit (the implementation, `supplement.tex:407-409`),
UNCONDITIONAL: coverage `liminf P(T̂_δ ≤ sep) ≥ 1 − δ`, asymptotic level `δ`, and certification, for
`T̂_δ = splitBootPercn` (the bootstrap `δ`-quantile of `T̂*`), under `ass:regularity` and `ass:split`;
`δ = Φ(Ioi z) ∈ (0, 1)` as in the frozen claims (`z` enters only through `δ`). -/
def split_boot_percentile : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitBootPercn φ f X Y m α δ n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ α →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
            μ {ω | 0 < splitBootPercn φ f X Y m α δ n ω} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ n, ∀ ω, ((splitBootPercn φ f X Y m α δ n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q) →
          0 < splitBootPercn φ f X Y m α δ n ω → α < StatFormal.Distances.tvDist P Q)

end Claims

end StatFormal.Wave29l
