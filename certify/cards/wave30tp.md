# Fidelity card — wave 30tp: trimmed-mmd (JMLR revision), the plug-in common trimming — NOTE Theorem P (closed form), Lemma P0, Lemma P1, Lemma 1, kernel constants, coupled constants

Lean: `StatFormal/Wave30tp/Statements.lean` (frozen 2026-11-07, sha256 `34738a1491562ca707f890f50e8abc7925a65c762a4917c2dbcb96342e8f459b`, locked
with its imports), routes `RouteMcDiarmid2`, `RouteBernstein2`, `RouteMoments`, `RouteDet`, `RouteLevel`; `Proofs.lean` checks all 13 claims.
Paper id `trimmed-mmd (jmlr)`. Imports, not copies, the frozen `TrimmedMMD` (`alphaHat`), `TrimmedMMD/Concentration` (`region`, `empirical`),
`TrimmedMMD/Unconditional` (`setDist`, `Demp`), `TrimmedMMD/ZeroSet` (through it `StatFormal.Distances.tvDist`).
Critic (independent AI reviewer, before the freeze, 2026-11-07): 13 claims, none false, no counterexample; one CHANGE applied before freezing
(`plugin_one_event` for every pair: the draft's extra hypothesis `TV < 1` dropped, the `α̂` clause guarded by `TV < 1`), one coverage addition
(`plugin_det_zero`, the remark after Lemma P0), both source hashes and a "Not covered" list added.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-07 — PASS with notes
(13 claims faithful; notes: third source hash and line offsets, `λ_X = λ_Y = 1` proof-internal, "on nonempty `𝒳`", `prop:georep` lines — all
applied below).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Printed source (labels to be remapped)
The printed source is **`trimmed-mmd/explore/sharper_threshold/NOTE.md`**, a research note for the JMLR revision (read-only, still being edited
elsewhere while this wave ran). The targets carry provisional labels (`thm:plugin`, `lem:plugin-det`, `lem:plugin-moments`,
`lem:monotone-event`, `def:kernel-constants`, `rem:plugin-coupled`) with the NOTE's own names in parentheses. **They must be remapped to the
paper's labels when the JMLR text is revised.**
* Frozen from the snapshot read 2026-11-07 ~22:55, sha256 `b1141e28273d09af58af5ae5e31eb41278364110c2649fea2be331203607b5ed`. The file later
  hashed `5e80a476ff8218c397b9a73b63c053cb621d8b18b12255ed0bd491ab7a3322dc`. That version differs only at §5 lines 489–496 (the Theorem A centring
  remark), which lies outside the frozen §1 and §3.1–3.3.
* At the end of this wave the file hashed `b6f1aab476e51d1aba9b146074cbe93bbaae7311638a485d0f9cd8511565d284` (§0 lines 44–50 → 44–61, §5, §8–9
  changed). Checked: snapshot lines 57–394 (§1 through §3) are byte-identical to lines 68–405 of that version, so the frozen text is unchanged
  and shifted by +11 lines there.
* Line numbers below refer to the snapshot `b1141e28` (also valid for `5e80a476`; add 11 for `b6f1aab4`):
  * §1 kernel constants: `:59-70`.
  * Lemma 1: `:75-82`, proof `:84-88`.
  * Lemma P0: `:204-214`, proof `:216-235`.
  * Remark at α = 0: `:237-239`.
  * Lemma P1: `:241-249`, proof `:251-265`.
  * Theorem P: `:269-284`, proof `:286-318`, uniformity `:320-322`.
  * Coupled constants: `:362-369`.
* Paper context (read-only), `trimmed-mmd/jmlr/`:
  * `sections/03_regions.tex:20-31` — `ass:regularity` (A1)–(A3);
  * `:95-112` — `prop:georep`;
  * `sections/04_test.tex:4-10` — `H_{0,α}`;
  * `sections/01_introduction.tex:28` — `eq:tvintersect`.

## Definitions (locked)
* `sNM n m = 1/n + 1/m` (`s`), `cNM n m = max(1/n, 1/m)` (`c`).
* `T1 D v α δ n m = √(β v² s) + β D √(s L/2)` and `T2 α δ n m = √(2(β−1) s L) + c L/3`, with `β = 1/(1−α)` and `L = log(6/δ)`.
* `tauP D v ρ̄ α δ n m`: `v√s + D√(s log(1/δ)/2)` if `α = 0`, else `T1 + ρ̄·T2`. This is the printed `τ_P`.
* `trCov φ R = ∫ ‖φ − ∫φ dR‖² dR`, the printed `tr Cov_R(φ)`.
* `rhoR φ R = ⨆_x ‖φ x − ∫φ dR‖`, the printed `ρ_R`.
* `KernelConsts φ D v ρ̄`:
  * `‖φ x − φ x'‖ ≤ D` for all `x, x'`;
  * `0 ≤ v`;
  * `trCov φ R ≤ v²` for every probability `R`;
  * `‖φ x − μ_R‖ ≤ ρ̄` for every `x` and every probability `R`.
* `IsDensityLe R P α a`: `a` measurable, `0 ≤ a ≤ β` everywhere, and `R = P.withDensity (ofReal ∘ a)`. This encodes "`a = dR/dP ≤ β`, a version with
  values in `[0,β]`".
* `wMeanDev a φ μ x = n⁻¹ Σ a(x_i)(φ(x_i) − μ)` (`A`), `wMass a x = n⁻¹ Σ a(x_i)` (`S_X`).
* `sampleLaw P Q n m = P^{⊗n} ⊗ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)`.

## Covered (13 claims), with back-translation
In every claim, `H` is a real Hilbert space, `φ : 𝒳 → H` is strongly measurable with `‖φ‖ ≤ κ`, and `𝒳` is any measurable space.
* `kernel_consts` (§1), for every bound `κ` on `‖φ‖` and `D` on `‖φ(x) − φ(x')‖`:
  * `v = √min(κ², D²/2)` and `ρ̄ = D` satisfy `KernelConsts`;
  * `‖φ(x) − φ(x')‖ ≤ 2κ`;
  * if `⟪φx, φy⟫ ≥ 0` and `⟪φx, φx⟫ = κ²`, then `‖φ(x) − φ(x')‖ ≤ √2 κ`.
* `monotone_event` (**Lemma 1**). Hypotheses: `0 ≤ δ`, `n, m ≥ 1`, and `τ` nonnegative and nondecreasing on `[0,1)` with
  `P'^{⊗n}⊗Q'^{⊗m}{D̂_α > τ(α)} ≤ δ` for every `α ∈ [0,1)` and every pair `P', Q'` with `TV ≤ α`. Then for every pair with `α* = TV(P,Q) < 1`:
  * `{D̂_{α*} ≤ τ(α*)}` contains a measurable event of probability `≥ 1 − δ`;
  * every sample in that set has `D̂_α ≤ τ(α)` for all `α ∈ [α*,1)`, `α̂ = inf{α ∈ [0,1) : D̂_α ≤ τ(α)} ≤ α*`, and every rejected level
    `α ∈ [0,1)` (`τ(α) < D̂_α`) `< α*`;
  * for every grid `G ⊆ [0,1)`, the largest rejected grid level, when it exists, is `< α*`.
* `plugin_det` (**Lemma P0**). For `α ∈ [0,1)`, `n, m ≥ 1`, and a probability `R` with `IsDensityLe R P α a` and `IsDensityLe R Q α b`: for
  every sample `x, y`, `D̂_α ≤ max{‖A−B‖, ‖A‖, ‖B‖} + ρ_R[(1−S_X)_+ + (1−S_Y)_+]`, where `A, B` are the weighted mean deviations about
  `μ_R = ∫φ dR`.
* `plugin_det_zero` (**remark after Lemma P0**, `α = 0`):
  * `a = 1` `P`-a.e. and `b = 1` `Q`-a.e.;
  * `P = R` and `Q = R`;
  * a.s. under `P^{⊗n} ⊗ Q^{⊗m}`: `S_X = S_Y = 1` and `D̂_0 ≤ ‖A − B‖`.
* `plugin_moments_i` (**Lemma P1 (i)**), for `R = a·P` with `0 ≤ a ≤ β`:
  * `∫ a(φ − μ_R) dP = 0`;
  * `∫ ‖a(φ − μ_R)‖² dP ≤ β tr Cov_R(φ)`;
  * `β tr Cov_R ≤ β v²` whenever `tr Cov_{R'} ≤ v²` for all `R'`.
* `plugin_moments_ii` (**(ii)**): `‖a(x)(φ(x) − μ_R)‖ ≤ β ρ_R`, and `‖ξ(x) − ξ(x')‖ ≤ β D` for every bound `D`.
* `plugin_moments_iii` (**(iii)**), for `W = 1 − a(X)`, `X ∼ P`:
  * `∫ W dP = 0` and `1 − β ≤ W ≤ 1`;
  * `variance W P ≤ β − 1`;
  * `∫ e^{λW} dP ≤ β⁻¹e^{λ(1−β)} + (1 − β⁻¹)e^λ` for `λ ≥ 0`.
* `plugin_moments_iv` (**(iv)**), for every probability `R`:
  * `ρ_R ≤ D` and `tr Cov_R ≤ min(κ², D²/2)` for every bound `D`;
  * if `k ≥ 0` and `k(x,x) = κ²`: `tr Cov_R = κ² − ‖μ_R‖²` and `ρ_R² ≤ κ² + ‖μ_R‖²`.
* `plugin_level` (**Theorem P**, level). For `KernelConsts φ D v ρ̄`, `α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1`, and every pair with `TV(P,Q) ≤ α`:
  `P^{⊗n}⊗Q^{⊗m}{D̂_α > τ_P(α,δ)} ≤ δ`.
* `plugin_monotone` (**Theorem P**, monotonicity): for `D, v, ρ̄ ≥ 0` (implied by `KernelConsts` on nonempty `𝒳`, automatic once a
  probability measure exists), `δ ∈ (0,1)` and `n, m ≥ 1`, `τ_P(·,δ)` is
  nonnegative and nondecreasing on `[0,1)`.
* `plugin_one_event` (**Theorem P**, "so Lemma 1 applies … for every pair"). For every pair there is a measurable event of probability `≥ 1 − δ`
  on which:
  * `D̂_α ≤ τ_P(α,δ)` for every `α ∈ [0,1)` with `TV ≤ α`;
  * every rejected level is `< TV`;
  * `α̂ ≤ TV` when `TV < 1`.
* `plugin_level_explicit`: Theorem P with `v = √min(κ², D²/2)` and `ρ̄ = D`.
* `plugin_coupled` (**§3.3 coupled constants**, closed-form analogue). For `k ≥ 0`, `k(x,x) = κ²`, any bound `D`, `α`, `δ`, `n, m` as above, and
  every pair with `TV ≤ α`: every `t ≥ τ_P(α,δ; v = √(κ² − u), ρ̄ = √(κ² + u))` for all `u ∈ [0,κ²]` (that is, `t ≥ sup_u`) has
  `P{D̂_α > t} ≤ δ`.

## Hypotheses used vs printed (declared)
* **(A1)–(A2) are weakened** to "`φ` strongly measurable and bounded":
  * this is what (A1)+(A2) give by Pettis;
  * separability of `H` is not assumed;
  * (A3) is not assumed (the NOTE says the level never uses it).
  This is a generalisation.
* **`D_φ`, `κ`.** These are any bounds (the printed `D_φ = sup‖φ(x) − φ(x')‖` and `κ = sup k(x,x)^{1/2}` are the least bounds):
  * every threshold claim is monotone in `D`;
  * the Lemma P1 bounds hold for every bound, hence for the supremum.
  This is a generalisation.
* **`v`.** `v ≥ 0` is the square root of the printed `v²`. The printed `v√s` and `√(βv²s)` presuppose `v = √(v²) ≥ 0`, so this is not an extra
  assumption.
* **`n, m ≥ 1`.** Assumed in Lemma P0 (printed only in Theorem P; `n⁻¹` needs it). This is the standing assumption.
* **Lemma 1 adds `0 ≤ δ`.** This is a junk guard. For `δ < 0` the printed hypothesis "`Pr ≤ δ`" is unsatisfiable, but the encoding's
  `ofReal δ = 0` would make it satisfiable with a false conclusion. The printed `τ ≥ 0` is kept, though unused.
* **Lemma P1 (iv) and the §1 claims are stated for every probability `R`**, not only common trimmings. This is a generalisation.
* **`plugin_one_event` follows the printed "for every pair".**
  * When `TV = 1` the first two clauses are vacuous, the rejected-level clause is trivial, and the event is everything.
  * The `α̂` clause is guarded by `TV < 1`, because `α̂ ≤ α*` comes from Lemma 1, which assumes `α* < 1`.
* **Coupled constants: the printed sentence is about the numerically inverted `τ_{P'}`; frozen here for the closed form `τ_P`** (task
  brief). The "sup over `u`" is encoded as "every upper bound `t` of the family is a valid threshold", which is equivalent: validity is
  monotone in `t`, and the supremum is the least upper bound. This avoids `sSup` junk.

## Encodings and junk-value audit
* **Division and square roots.**
  * `1/n`, `1/m` with `n, m ≥ 1`, and `β = 1/(1−α)` with `α < 1`, are genuine.
  * Every `√` argument is `≥ 0` on the domain used: `β − 1 ≥ 0`, `log(1/δ) ≥ 0` and `log(6/δ) > 0` for `δ ∈ (0,1)`.
* **`rhoR` (real `iSup`).** The family is bounded by `2κ`, and `𝒳` is nonempty whenever a probability measure exists, so this is the genuine
  supremum (`le_rhoR`, `rhoR_le`).
* **`alphaHat` (`sInf` of the crossing set).** On the event, the set contains `α*` and is bounded below by 0.
* **`setDist` / `Demp`.** The empirical regions are nonempty for `n, m ≥ 1`.
* **Bochner integrals.** All integrands are bounded and strongly measurable (`φ`, `a·(φ − μ_R)`, `exp(λW)`).
* **`variance`.** `1 − a` is bounded, hence in `L²`, so `variance` is genuine.
* **`ofReal`.** `ofReal δ`, `ofReal (1 − δ)` with `δ ∈ [0,1]`.
* **No `Measure.map`** in any statement.
* **Probabilities.** "`Pr(D̂_α > τ) ≤ δ`" is the measure of `{D̂_α > τ}`. Measurability of `D̂_α` is not proved here, so this is the outer
  measure: the set lies in a measurable event of probability `≤ δ`, which is the content of the printed bound.
* **"An event of probability `≥ 1 − δ`"** is a measurable event of probability `≥ 1 − δ` inside the claimed set (convention of
  `TrimmedMMD/Unconditional`).
* **Vacuity: none.** `P = Q = R`, `a = b = 1`, `κ` any bound, `D = 2κ`, `v = κ`, `ρ̄ = 2κ` satisfy every hypothesis set (`kernel_consts`
  certifies `KernelConsts` for such constants).

## Not covered (declared)
* **Theorem A** (§2, joint one-sided supremum) is not attempted. It needs two-sample signed symmetrization and contraction (the library has the
  one-sample versions).
* **The numerically inverted `τ_{P'}`** (§3.3: Pinelis' Bennett bound in Hilbert space, `Ψ_H`, `Ψ_R`, the split set `F`) is not attempted.
  Pinelis' inequality is not in Mathlib; this is a **software refinement of the certified closed form**.
* `τ^{cpl}_{P'}` and its 20-cell grid bound; Corollary C; the "11–14%" gains.
* Monotonicity and the one-event form of the coupled threshold (the printed text says only "valid").
* The Gaussian line of §1 (`κ = 1, D_φ = √2, v² = 1, ρ̄ = √2`) and "equality on an unbounded domain".
* In the remark after Lemma P0, "`λ_X = λ_Y = 1`": the `λ`'s exist only inside the proof of Lemma P0. The remark's conclusions (`a = b = 1` a.s.,
  `S_X = S_Y = 1` a.s., `D̂_0 ≤ ‖A − B‖` a.s., `P = Q = R`) are covered by `plugin_det_zero`.
* §3.4, the "Uniformity" sentence (it is visible in the form of `tauP`, which does not involve `P, Q`), and every numerical or table claim.

## Proof route (untrusted)
* **New library-grade lemmas** (in the wave, to move to `Lib/` at the next archive run):
  * `RouteMcDiarmid2.mcdiarmid_two_sample` — **McDiarmid for `P^{⊗n} ⊗ Q^{⊗m}`** with per-block constants. One `P⊗Q` draw per index of
    `Fin n ⊕ Fin m`; `map_splitMap` shows the pushforward is `P^{⊗n} ⊗ Q^{⊗m}` (`measurePreserving_sumPiEquivProdPi`, `pi_map_pi`,
    `map_prod_map`); Tau Ceti's McDiarmid then applies with coordinate-dependent constants. No triangle-inequality fallback was needed.
  * `RouteMcDiarmid2.twoDev_tail` — **Hilbert two-sample mean**:
    * `E‖A − B‖² = E‖ψ₁‖²/n + E‖ψ₂‖²/m` (cross term 0 by Fubini; reuses `HilbertMean.integral_norm_meanDev_sq`);
    * Jensen;
    * the tail `√(σ₁/n + σ₂/m) + √((c₁²/n + c₂²/m)L/2)` at `e^{−L}`, with the zero-oscillation case handled.
  * `RouteBernstein2.bernstein_two_sample` — **one-sided Bernstein (sub-gamma) for two independent samples with non-identical summands**:
    * the MGF bound uses only `W ≤ c` (rescaled `Lib/Bernstein.exp_mul_le_bernstein`);
    * the MGF factorises over the product (`integral_prod_mul`, `integral_exp_mul_sum_eq`);
    * Chernoff at `λ = a/(V + ca/3)`, `a = √(2VL)`.
* **Lemma P0** (`RouteDet`): explicit weights.
  * `S ≥ 1`: `w = w⁰/S`.
  * `S < 1`: `w = w⁰ + θ(β/n − w⁰)`, `θ = (1−S)/(β−S)`.
  * The vertex bound comes in two cases. Feasibility is the certified `Wave8a.georep_empirical` (ties allowed); then `setDist ≤ ‖a − b‖`.
* **Theorem P** (`RouteLevel.level_core`) is stated for a **fixed** common trimming `R`, needing the constants for that `R` only, which also
  gives `plugin_coupled`.
  * `α = 0`: `P = Q = R`; uniform weights; one two-sample McDiarmid event at `δ`.
  * `α > 0`: three McDiarmid events (`‖A−B‖`, `‖A‖`, `‖B‖` with `ψ₂ = 0` or `ψ₁ = 0`) and three Bernstein events, each at `δ/6`; union bound.
  * The common trimming is the certified `ZeroSet.tvintersect` (`eq:tvintersect`).
* **Lemma 1**: nested regions (`WaveP1a.region_mono`, `setDist_anti`) and `toMeasurable` of the rejection set.
* **Reused certified claims**: `Wave8a.georep_empirical`, `TrimmedMMD.ZeroSet.tvintersect`.
* **Reused library**: `Lib/Concentration/HilbertMean`, `Lib/Bernstein` (pointwise inequality and product MGF), Tau Ceti `McDiarmid`, and route
  lemmas from `WaveP1a`, `Unconditional`, `Concentration`.

## Remarks on the printed text
* **Theorem P proof, monotonicity (`:317-318`).** "`lim_{α↓0} τ_P(α,δ) = … > τ_P(0,δ)`": the strict inequality fails when `D_φ = ρ̄ = 0` (`φ`
  constant). Only `≥` is needed, and the statement is unaffected. Suggested wording: "`≥ τ_P(0,δ)`".
* **Theorem P proof, repair part.** The Bennett form `V/c²(e^{λc} − 1 − λc)` is used with the upper bounds `V ≤ (β−1)s` and `c`. Only the
  upper bound `W_k ≤ c` and the variance bound enter; the certified proof uses the equivalent sub-gamma MGF directly.
* **No other defect found.** All statements of §1 and §3.1–3.2 hold as printed under the declared encodings. The critic re-derived each, and
  the formulas reproduce the NOTE's table values (`τ_P = 0.223` at `α = 0` and `0.501` at `α = 0.2`, Gaussian kernel, `n = m = 300`,
  `δ = 0.05`).
