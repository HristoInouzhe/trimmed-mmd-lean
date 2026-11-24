# Fidelity card — wave 30tu: trimmed-mmd (JMLR revision v2), the estimator side re-certified for the v2 threshold `τ_{n,m}` and the two-sided tool `τ^A`

Lean: `StatFormal/Wave30tu/Statements.lean` (32 claims, the results for ANY valid threshold and ANY two-sided tool),
`StatFormal/Wave30tu/Instance/Statements.lean` (12 claims, the same results at `τ_{n,m} = min(τ^P, τ^A)` and `τ^A`; imports the frozen
Wave 30tp and Wave 30tr statements), `StatFormal/Wave30tu/Full/Statements.lean` (12 claims, at the paper's full `τ_{n,m} =
min{τ^A, τ^P, τ^{P'}}` and its coupled and grid versions; imports the frozen Wave 30ts statements) and
`StatFormal/Wave30tu/Crossing/Statements.lean` (2 claims, `lem:crossing` without continuity of `τ`, generic and at the full `τ_{n,m}`).
Routes `RouteBasic`, `RouteMain`, `RouteConsistency`, `RouteRatecond`, `Instance/Route`, `Full/Route`, `Crossing/Route`; `Proofs.lean` checks
all 58 claims. Paper id `trimmed-mmd (jmlr)`; labels are the paper's with " (v2)".
Branch `tmmd-jmlr-est2`, based on `tmmd-jmlr-est` (Wave 30tl), with `tmmd-jmlr-thmA` (Wave 30tp Theorem P, Wave 30tr Theorem A, and
master's Wave 30dv) and then `tmmd-jmlr-pinelis` (Wave 30ts, the sharper candidate and Corollary C) merged in at the coordinator's request
for the instance files.
Critic (independent AI reviewer, before each freeze, 2026-11-08): first draft 29 claims ACCEPT (none false), deltas after the source moved
to `0c41fb5` ACCEPT, instance file 10 claims ACCEPT (header overclaim fixed, two instances added), full-instance file 10 claims ACCEPT
(header updated to `9b754c8`; the coupled and grid rate-condition claims added for the printed Gaussian case, ACCEPT), crossing file 2 claims
ACCEPT.
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
Frozen from `trimmed-mmd/jmlr/` at commit `0c41fb5` ("JMLR revision v2, batch 1b: fixes from the independent re-check"; line numbers in the
frozen docstrings refer to it), re-checked at master `adb8e08` ("JMLR v2: print fixes from the printed-vs-Lean audit"), read-only,
2026-11-08. sha256:

| file | `0c41fb5` | `adb8e08` |
|---|---|---|
| `sections/04_test.tex` | `65b98e826426d014ca89507df5f2d4d2af9b24b905669f35eb119a1ff40cbe73` | `26902166091d40b7d8bb16a6f16db1d7c5957acc23ff417b03fe1a59564f2b66` |
| `sections/05_estimator.tex` | `d1d8f75aae60f6c454d8d39ab05f4311d84e9a847b0b0be2388de77842966a0e` | `d1d8f75aae60f6c454d8d39ab05f4311d84e9a847b0b0be2388de77842966a0e` (unchanged) |
| `sections/06_splitting.tex` | `2c720b0a2bbb668870e54fc88fb59aab49aae0bf983583b7a3018a736a198163` | `b45e89bb18ce3acbda273c467b9c1ca3511cc2393fe5872ee016a1d9b6de387d` |
| `appendix/A_basic.tex` | `5f05deab18c50e03cce389031e5db0657c6d1e9f1a0e175e27fca93eb8db1da7` | `a55a42f637378d9d972ccc06e757545ee0428e148849bc467e2b99cb438adcdf` |
| `appendix/B_split.tex` | `4385b5d91c4cd2e6ded1d7a9d7fc45b9d23f9c8efb39af40914f5f7cb07a690c` | `4385b5d91c4cd2e6ded1d7a9d7fc45b9d23f9c8efb39af40914f5f7cb07a690c` (unchanged) |

`0c41fb5 → adb8e08` touches no target statement: `04_test.tex` changes only `lem:plugin` (densities with versions in `[0,β]`, `:139-140`,
same line count); `06_splitting.tex` changes `lem:ramp` and `thm:betting` (`cor:upperfs` moves by one line to `:233-242`, the sentence
after it to `:244-248`); `A_basic.tex` adds "(If `D_φ = 0`, `φ` is constant and `Z = 0`)" to the proof of `thm:twosided` (`:380`) and, in
the sharper threshold (`:437-472` now), "the smallest such values in `[0,∞)`", "the smallest `t ≥ 0` with `Ψ_H(t;1,s,c) ≤ δ`" (`:455`,
which `sharpZero` already encoded), `K` as lists, and `u ∈ [0,κ²)` with a sentence for `‖μ_R‖ = κ` (the coupled case used in
`ratecond_gauss` is `u = 0`, inside `[0,κ²)`); the proof of `lem:oneevent` moves to `:474-478`.

The full-instance file was frozen from master `9b754c8` (sha256 04 `26902166…`, 05 `d1d8f75a…`, 06 `58506daf3593e08f9a99f91daab8441bc4357140a19fbd6b89c1f006fbb46074`,
A `68f0303159d937b72b5413603fc098e4637ea1811861e5936f6f6a6bd91437fe` (last changed at `9f11e18`), B `4355a4d882b65df8b4efc11e813595740398393e42bdcba59db98445b74e26a7`):
`adb8e08 → 9b754c8` rewords the sharper roots ("`t₁ ≥ 0` … `t₂ ≥ 0` …, the infima of such values in `[0,∞)`, which are again admissible by
continuity of the measure", `A_basic.tex:451-456`) and moves `cor:upperfs` to `06_splitting.tex:238-247` (sentence after it `:249-253`) and
its proof to `B_split.tex:201-208`, verbatim unchanged; the meaning of every frozen definition is unchanged. It also rewrote the betting
certificate (`06_splitting.tex` `thm:betting`, the certificate paragraph, `cor:lower`; `B_split.tex`, proof of `thm:betting`), which holds no
target of this wave. The review was against the committed `9b754c8`; the paper's working tree then had uncommitted edits at
`04_test.tex:127` and `06_splitting.tex:141-143` (the constants `8.5/13.9` and `2.45/1.645/1.75/2.2` turned into macros; commentary, same
line counts).

The first draft was written against the working tree on top of `5e18aa4` as read then (04 `09bf90ff…`, 05 `934f31e4…`, 06 `f0f1d63c…`, A `6771acd9…`, B `4385b5d9…`; the committed `5e18aa4` files 04 and A hash `e86822f5…`, `059ce80c…`). Before the
freeze the paper moved to `0c41fb5`: `τ_{n,m}` became `min(plug-in thresholds, τ^A)` (`r_n + r_m` no longer a candidate), the quantifiers of
`thm:twosided` were fixed, the rate-condition example uses `τ^A` instead of `r_n + r_m`, `rem:grid` and the monotonicity of the sharper
threshold across `α = 0` were reworded. The frozen files follow `0c41fb5`. Target passages (at `0c41fb5`): `04_test.tex:106-122`
(`thm:twosided`), `:156-170` (`thm:plugin`), `:177-189` (`τ_{n,m}`, `lem:oneevent`); `05_estimator.tex:17-43` (`eq:alphaest`, `rem:grid`),
`:79-122` (`thm:consistency`, `cor:consistency`, the rate-condition sentence), `:126-175` (`ass:margin`, `thm:rate`, `ω^←`, `cor:confset`,
the width sentence); `06_splitting.tex:232-247` (`cor:upperfs` and the sentence after it); `A_basic.tex:226-339` (proofs, `eq:pathwise`,
`lem:crossing` and the paragraph after it, the rate-condition argument `:303-311`), `:437-471` (sharper threshold), `:473-477`
(`lem:oneevent`); `B_split.tex:199-206`.

## Declared generalisation (the frozen form)
The printed results are about the specific `τ_{n,m}` and `τ^A_{n,m}`. They are frozen for any threshold and any two-sided tool with the
properties that the printed proofs use:
* `ValidThreshold φ n m δ τ`: `τ ≥ 0` and nondecreasing on `[0,1)`, and `P(D̂_α > τ(α)) ≤ δ` for every `α ∈ [0,1)` and every pair with
  `TV ≤ α` (literally the hypothesis of `lem:oneevent`). Continuity on `(0,1)` (`lem:crossing`) and `τ → ∞` as `α → 1` (`eq:alphaest`)
  are separate hypotheses, used only where printed.
* `LowerTool φ P Q n m δ τA`: `τ^A ≥ 0` nondecreasing on `[0,1)`, and the event `E⁻` of `thm:twosided` for the pair at level `δ`
  (measurable, probability `≥ 1 − δ`, not depending on `α`, `D̂_α ≥ D_α − τ^A(α)` for every `α`). `UpperTool` is `E⁺`; it is used only for
  "`τ^A` is valid because `D = 0` under the null" (`upper_valid`). The estimator results use only `E⁻`.
* Decay, where a limit in the sample sizes is taken: `τ_{n,m}(α,δ) ≤ r_n(α,δ/2) + r_m(α,δ/2)` and `τ^A_{n,m}(α,δ) ≤ r_n(α,δ/2) +
  r_m(α,δ/2)` (`= TrimmedMMD.tau κ α δ n m`), as in the printed proofs (`A_basic.tex:238-239, 294-295`: `τ_{n,m} ≤ τ^A ≤ r_n + r_m`).
* (A3) (`Characteristic φ`) only in `consistency_ii`, `cor_consistency` and their instances; dropped elsewhere.

## Instantiation map (paper's `τ_{n,m}` and `τ^A`)
| hypothesis | certified by |
|---|---|
| `τ^P` valid for every pair, `≥ 0`, nondecreasing on `[0,1)` | Wave 30tp `plugin_level_explicit` (`v = √min(κ², D²/2)`, `ρ̄ = D`), `plugin_level`, `plugin_monotone` (branch `tmmd-jmlr-plugin`, merged here) |
| `τ^P` continuous on `(0,1)`, `→ ∞` (`D > 0`) | here, inside `Instance.tauNM_threshold` (route lemmas `tauP_continuousOn`, `tauNM_tendsto`) |
| `τ^A`: `E⁺`, `E⁻` per pair; `≥ 0`, nondecreasing, `= βτ^A(0)`; `≤ r_n + r_m` | Wave 30tr `thmA`, `tauA_scale`, `thmA_compare` (branch `tmmd-jmlr-thmA`, merged here) → `Instance.tauA_tool` |
| `τ^A` valid | `upper_valid` (from `E⁺` and `zero_of_tv_le`) |
| minimum of valid thresholds valid, nondecreasing, continuous, `→ ∞`; `τ_{n,m} ≤ τ^A` | `threshold_min`, `Instance.tauNM_threshold` |
| one event for every level, every pair | `oneevent`, `Instance.tauNM_oneevent` (cf. Wave 30tp `monotone_event`, `plugin_one_event` for `τ^P` alone) |
| the sharper candidate (numerically inverted, coupled or not) and the full minimum | Wave 30ts `corollary_C`, `corollary_C_coupled`, `corollary_C_grid` (valid, nondecreasing, nonnegative, one event for `min{τ_A, τ_P, τ_{P'}}` and the coupled/grid versions, `τ_A` a hypothesis discharged by Wave 30tr `thmA`), `sharp_tau_monotone` (branch `tmmd-jmlr-pinelis`, merged here) → `Full.tauFull*_threshold`. Not certified in Wave 30ts: continuity of `τ_{P'}` on `(0,1)` and `τ_{P'} → ∞`. The generic `crossing`, `crossing_meas` assume continuity for all their clauses (the frozen Full header's "Not stated" list is incomplete in this respect), so `lem:crossing` at the full `τ_{n,m}` is supplied by the continuity-free `Crossing.crossing_nc` and its instance `Crossing.crossing_full`: `(α̂,1) ⊆ S`, `D̂_{α̂} ≤ τ(α̂+)` and `α̂` measurable (unconditionally). Not stated at the full `τ_{n,m}`: "`S = [α̂,1)` if `α̂ > 0`", "`= τ(α̂)` when `α̂ > 0`", the union formula for `{α̂ < a}`, and the well-definedness sentence after `eq:alphaest` (`S ≠ ∅` for every realization, which needs `τ_{P'} → ∞`). For the rate-condition example the value at `α = 0` is identified with `sharpZero` (the two encodings of `Ψ_H` agree up to argument order) |
| the v1 threshold `r_n + r_m` (archive, `cor:uniform`/`thm:concentration` + `lem:nullbound`) | `hausdorff_valid` (from Wave 30tl `test_level`), `hausdorff_lower` (lower half of `eq:pathwise`, from `Unconditional.exists_events`; the two-sided form is the archive `Unconditional.events`); non-vacuity witnesses |

The 12 `Full` claims: `tauFull_threshold`, `tauFullCpl_threshold`, `tauFullGrid_threshold` (the paper's `τ_{n,m}`, general kernel, coupled,
grid as implemented: valid, nondecreasing, `≤ τ^A`, `≤ r_n + r_m` for `D ≤ 2κ`, one event for every pair); `consistency_i_full`,
`consistency_ii_full`, `cor_consistency_full`, `rate_full`, `confset_full`, `upperfs_interval_full` (the printed results at the full
general-kernel `τ_{n,m}`; at the coupled and grid versions, and for the polynomial case, the width sentence and `rem:grid`, they are the
same direct compositions of the generic claims with `tauFull_threshold`, `tauFullCpl_threshold`, `tauFullGrid_threshold` and
`Instance.tauA_tool`); `ratecond_full` (general kernel at
the Gaussian constants), `ratecond_full_cpl`, `ratecond_full_grid` (the printed Gaussian case: `k ≥ 0`, constant diagonal, with the
coupled, resp. grid, candidate: `τ_{n,n} ≥ D_φ` on `[0,1)` and `α̂_{n,n} = 0`; the coupled family at `α = 0` is bounded above by the
McDiarmid root and its `u = 0` member is `≥ D_φ`; the grid cell containing `u = 0` has `v_j ≥ κ`). With `ratecond_noconv`, no convergence.

The 12 `Instance` claims are the printed `thm:consistency` (i), (ii), `cor:consistency`, `thm:rate` (and its polynomial display), `cor:confset`
(and the width sentence), `cor:upperfs` (and the `1 − 2δ` sentence) at `τ_{n,m} = min(τ^P, τ^A)` without the sharper candidate, and
`τ^A` of Theorem A. `rem:grid`, the well-definedness sentence after `eq:alphaest` and `lem:crossing` at `τ_{n,m}` are direct compositions of
`grid_*`, `alphaest_wellDefined`, `crossing*` with `tauNM_threshold` (not restated; the well-definedness for `D > 0`, and for `D = 0`
`D̂ ≡ 0` gives `S = [0,1)` via `Demp_le_Dphi`). For the rate-condition example, `ratecond_gauss` takes
the three candidates (closed form, sharper, `τ^A`) as nondecreasing functions with the printed values at `α = 0`; if the coupled and
uncoupled sharper versions count as two candidates (four in all), the coverage is `threshold_min` and `ratecond_zero` (any finite family)
with `ratecond_sharp` at `ρ̄ = D_φ` and at `ρ̄ = κ`, `ratecond_gauss` being the three-candidate packaging; `τ^P` and `τ^A` match the frozen `tauP` (`if α = 0`
branch, `sNM n n = 1/n + 1/n`) and `tauA` (`β = 1`, `e₁ = ek n`, `e₂ = ek n`, `ek ≥ 0`) by unfolding; the sharper one is discharged at the full `τ_{n,n}` by `Full.ratecond_full*`.

## Covered (58 claims)
The 12 `Full` and 2 `Crossing` claims are listed above and below the instantiation map; the 44 generic and `Instance` claims:
Generic (`StatFormal.Wave30tu.Claims`):
* `lem:oneevent`: `oneevent` (event measurable, probability `≥ 1 − δ`, `D̂_α ≤ τ(α)` on `[α*,1)`). Definition of `τ_{n,m}`:
  `threshold_min` (finite minimum of valid nondecreasing thresholds; continuity and `→ ∞` preserved), `upper_valid`.
* `eq:alphaest`: `alphaest_wellDefined` (`D̂ ≤ 2κ`, crossing set nonempty when `τ → ∞`), `tauRight_spec` (the right limit).
* `lem:crossing` (restated): `crossing` (path continuous nonincreasing, `(α̂,1) ⊆ S`, `D̂_{α̂} ≤ τ(α̂+)`, `S = [α̂,1)` if `α̂ > 0`),
  `crossing_meas` (`{α̂ < a} = ⋃_{q ∈ ℚ ∩ (0,a)} {D̂_q ≤ τ(q)}` for every real `a`; `α̂` measurable).
* `rem:grid`: `grid_mesh` (`α̂_grid ≤ α̂ + h`, rejected levels `≤ α̂`), `grid_prob` (one event: `α̂_grid ≤ α* + h`, `α* > α_last`).
* `thm:consistency`: `consistency_i`, `consistency_ii`. `cor:consistency`: `cor_consistency`.
* Rate condition: `Demp_le_Dphi`, `ratecond_closed`, `ratecond_tauA`, `pinelis_ineq`, `ratecond_mcd`, `ratecond_pin`, `ratecond_sharp`,
  `ratecond_zero`, `ratecond_noconv`, `ratecond_gauss` (the schedule `δ = e^{−n}` violating the rate condition is the unchanged Wave 30tl
  `ratecond_schedule`).
* `thm:rate`: `rate_eps` (encoding check), `rate`, `rate_poly` (explicit constant 24 for the `O(·)`).
* `cor:confset`: `confset`, `confset_width`. `cor:upperfs`: `upperfs`, `alphaHi_le`, `upperfs_interval`.
* Instances of the v1 threshold: `hausdorff_valid`, `hausdorff_lower` (lower half of `eq:pathwise`).
* The paragraph after `lem:crossing` (`A_basic.tex:288-291`, the candidates satisfy the hypotheses): covered for `τ^P` and `τ^A`
  (`Instance.tauNM_threshold`) and for `r_n + r_m` (`hausdorff_valid`); for the numerical candidates not certified (Wave 30ts gives validity, monotonicity and one event, not
  continuity or `→ ∞`); `lem:crossing` without continuity: `Crossing.crossing_nc`, `Crossing.crossing_full`.
Instance (`StatFormal.Wave30tu.Instance.Claims`): `tauNM_threshold`, `tauNM_oneevent`, `tauA_tool`, `consistency_i_inst`, `consistency_ii_inst`,
`cor_consistency_inst`, `rate_inst`, `rate_poly_inst`, `confset_inst`, `confset_width_inst`, `upperfs_inst`, `upperfs_interval_inst`.

## Hypotheses vs printed (declared)
* Generalisation to any `τ`, `τ^A` (above). The bundles carry `τ^A ≥ 0` nondecreasing (true for the printed `τ^A`, `tauA_scale`).
* (A3) dropped except in (ii) and the corollary (generalisation; `D_{α*−ε} > 0` needs it).
* `crossing`, `crossing_meas`: the printed "`S` assumed nonempty" is per realization (`crossing`) and for every realization (measurability).
  `confset`, `alphaHi_le`, `grid_*` do not need continuity of `τ` (generalisation).
* `consistency_ii`, `cor_consistency`: the decay through `≤ r_n + r_m` (printed). `N` may depend on `(P,Q)`, `κ` (as printed implicitly).
* `rate`: `ε_{n,m}` is any `ε ∈ [0,α*]` with `ω(ε) = t_{n,m}`; `rate_eps` shows it exists uniquely when `0 ≤ t ≤ ω(α*)`. `rate_poly`:
  `O(·)` as an explicit constant 24 (inside the power `1/γ`), under the printed decay.
* `thm:rate`: `α* < 1` is assumed (implicit in the print: `τ_{n,m}(α*,δ)` is defined on `[0,1)` only, and the `O(·)` contains `(1−α*)^{-1}`).
* Rate-condition example: `ratecond_closed` for any `v > 0`, `D ≥ 0`, `ratecond_tauA` for any `κ > 0`, `D ≥ 0`, `e₁, e₂ ≥ 0` (Gaussian:
  `v = κ`, `D_φ = √2κ`, `e₁ = e₂ = e_n`); `ratecond_mcd`,
  `ratecond_pin` for every `β ≥ 1` (printed: `β = 1`); `ratecond_sharp`: every admissible `t` exceeds `D_φ` and the smallest is `≥ D_φ`
  (the printed "exceeds" for the infimum is not needed for `α̂ = 0`); `ratecond_gauss`: the "Gaussian kernel" enters only through its
  constants `‖φ‖ ≤ κ`, `D_φ = √2κ`, `v = κ` (the identity `D_φ = √2κ` for the Gaussian kernel on an unbounded domain, `04_test.tex:102-103`,
  is not formalised; Wave 30tp `kernel_consts` certifies `D_φ ≤ √2κ` for `k ≥ 0` with constant diagonal); "exceeds `D_φ` at every `α`" is
  certified as `≥ D_φ`.
* Instances: `D` any bound on `‖φ(x) − φ(x')‖`; `D ≤ 2κ` assumed where `τ^A ≤ r_n + r_m` is used (holds for `D = D_φ`); `Nonempty 𝒳` in
  `tauNM_threshold` (needed: with empty `𝒳` and `κ = D = −1`, `τ^A < 0`); `D > 0` for `→ ∞` (needed: `D = 0` gives `τ^P ≡ 0` on `(0,1)`).

## Encodings (declared)
* Samples on `(Fin n → 𝒳) × (Fin m → 𝒳)` with `P^{⊗n} ⊗ Q^{⊗m}` (= Wave 30tp `sampleLaw`); probabilities as measurable events inside the
  claimed set; validity as the outer measure of `{τ < D̂}`. `α* = tvDist`, `D = Dpop`, `D̂ = Demp`, `α̂ = alphaHat` (`sInf`).
* `τ(a+) = tauRight τ a = inf_{(a,1)} τ` (`tauRight_spec`). `ω^← = omegaGen`, `α̂_hi = alphaHi`, `KnownMargin` (Wave 30tl). `Margin`
  (`ass:margin`): strictly increasing, continuous on `[0,α*]`, `ω(0) = 0`, `ω ≥ 0`, `ω(ε) ≤ D_{α*−ε}`.
* Convergence in probability: the frozen Wave 18b encoding (any filter of schedules). Grids: Wave 30tl `MeshGrid` (first level `≤ h`,
  gaps `≤ h`), `GridReturn` (smallest non-rejected level, or the last level), `LastRejected`.
* Sharper threshold: `psiMcD`, `psiPin`, `psiH` literal from `A_basic.tex:440-447` with `a = βρ̄c'`, `b² = βv²s'`; `sharpZero` = `sInf`
  of `{t ≥ 0 : Ψ_H(t;1,s,c) ≤ δ}` (`t ≥ 0`: implicit at `0c41fb5`, printed from `adb8e08` on, `A_basic.tex:455`; the set is certified nonempty in `ratecond_sharp`).

## Proof route (untrusted)
The printed proofs, on `E⁰ = {D̂_{α*} ≤ τ(α*)}` (validity at the true null) and `E⁻`; union bound `P(A ∩ B) ≥ 1 − a − b`. Upward closure of
the crossing set; `D̂_{α̂} ≤ τ(α̂+)` by `a ↓ α̂` (Mathlib `MonotoneOn.tendsto_nhdsWithin_Ioo_right`). `thm:rate` without the limit
`ε ↓ ε_{n,m}`: a crossing point `s < α* − ε` gives `ω(ε) < ω(α* − s) ≤ D_s ≤ D̂_s + τ^A(s) ≤ τ(α*) + τ^A(α*) = ω(ε)`. (ii): `c(ε) > 0` by the
certified `zeroeq`, `r_n → 0`; schedule: `1/min(n,m) ≤ log(1/δ)/min(n,m)` once `δ < e^{−1}`. `D̂ ≤ D_φ`: Wave 8a `georep_empirical` and convex
weights. Reused certified claims: Wave 30tl `test_level`, `crossing_*` route lemmas, `upperfs_onEvent`, `omegaGen` lemmas; Wave 18b
`continuity_cont`; ZeroSet `zero_of_tv_le`, `zeroeq`; Unconditional `exists_events`; Wave 30tp `plugin_level_explicit`, `plugin_monotone`;
Wave 30tr `thmA`, `tauA_scale`, `thmA_compare`.

## Junk-value audit
* `alphaHat = sInf crossSet`: every claim either assumes the set nonempty, or works on `E⁰` where `α* ∈ S`, or proves `0 ∈ S`; bounded
  below by 0; `α̂ ∈ [0,1)`. `tauRight`: `sInf` of `τ((a,1))` with `a < 1`, bounded below by `τ(a)`.
* `omegaGen ⊆ [0,1]`, `≥ 0` at `sSup ∅`; with `ω(0) = 0` and nonnegative arguments its set contains 0; `alphaHi_le` holds for every `ω`.
* `psiMcD` at `D = 0` (`x/0 = 0` gives tail 1 > `e^{−n}`): `ratecond_mcd` vacuous there, still true. `psiPin`: `a, b² > 0` assumed; `t ≥ 0`
  (for `t < 0` the `log` of a negative number would be live). `sharpZero`: nonempty set certified. `rate_poly`: `Real.rpow` only at
  nonnegative bases (`t ≥ 0` since `τ, τ^A ≥ 0`). `log(1/e^{−n}) = n`; `min(n,m) ≥ 1`. `crossing_meas`: for `a > 1` the union contains
  `q ≥ 1` (junk `D̂_q`), harmless since both sides are everything. No `toReal`, no `Measure.map`.

## Non-vacuity
The v1 threshold satisfies `ValidThreshold` and `LowerTool` (`hausdorff_valid`, `hausdorff_lower`), and so do `τ_{n,m} = min(τ^P, τ^A)` and
`τ^A` (`tauNM_threshold`, `tauA_tool`), for every bounded strongly measurable feature map. Pairs with `0 < TV < 1` and polynomial `ω`
satisfy the margin hypotheses (e.g. `𝒳 = Bool`, `P = δ₀`, `Q = Bern(½)`).

## Paper notes (printed v2 text)
Fixed between `5e18aa4` and `0c41fb5` (reported by this wave's critic, already in the text):
1. `thm:twosided` (`5e18aa4` `04_test.tex:108-110`): "there are events `E⁺`, `E⁻` … such that for every `α` and every pair `(P,Q)`"
   made the events independent of the pair, which is false. Counterexample: Gaussian kernel on ℝ, `n = m = 100`, `δ = 1/2`; under
   `(δ₀, δ₃)` the sample `(0^n; 3^m)` is a.s., so it lies in `E⁺`, and the pair `(δ₀, δ₀)` (`D₀ = 0`) then needs `1.406 ≤ τ^A(0,1/2) ≈ 0.72` (exact `e₁₀₀ = 0.0796`; `≤ 0.80` with `e_k ≤ k^{−1/2}`).
   `0c41fb5`: "for every pair `(P,Q)`, all `n,m ≥ 1` and `δ` there are events …".
2. `rem:grid` (`5e18aa4` `05_estimator.tex:38`): "the non-rejected levels form the interval `[α̂,1)`" is false when `τ_{n,m}` jumps at 0
   (`τ(0) < D̂_0 ≤ τ(0+)` gives `S = (0,1)`); `0c41fb5`: "contain `(α̂,1)` and are contained in `[α̂,1)`". The frozen Wave 30tl `grid_mesh`
   clause "rejected grid levels `< α̂`" is about the v1 threshold only; for v2 the certified clause is `≤ α̂` (`grid_mesh`).
3. Monotonicity of the sharper threshold across `α = 0` (committed `5e18aa4` `A_basic.tex:452-453`) was asserted from monotonicity in `β`, which does
   not cover the change of construction at `α = 0`; `0c41fb5` `A_basic.tex:468-471` gives the argument.
Remaining at `0c41fb5`, `adb8e08` and `9b754c8` (minor; no certified statement affected):
4. `05_estimator.tex:27-28` and `A_basic.tex:290-291`: "`τ_{n,m}(α,δ) → ∞` as `α → 1`" / "every candidate tends to infinity" fail for a
   constant feature map (`D_φ = 0` gives `v = ρ̄ = 0`, so `τ^P ≡ 0` on `(0,1)` and the minimum stays bounded). The set is still nonempty
   (`D̂ ≡ 0`). Suggested: add "(if `D_φ = 0`, then `D̂ ≡ 0` and the set is `[0,1)`)".
5. `lem:crossing` (`A_basic.tex:271`): "`⋃_{q ∈ ℚ ∩ (0,a)}`" includes `q ≥ 1`, outside the domain of `τ`, when `a > 1`; write `(0, min(a,1))`
   or restrict to `a ∈ (0,1]` (nit; the identity is true for every real `a` with the junk values).
6. `lem:oneevent` (`04_test.tex:188`): "for every `α ≥ α*`" should read `α ∈ [α*,1)` (nit).
7. `05_estimator.tex:119-120`: "every threshold entering `τ_{n,n}` exceeds `D_φ`": for the sharper threshold (an infimum over admissible
   `t`) the argument gives `≥ D_φ` unless the infimum is attained; `≥` is all that `α̂ = 0` needs (nit).
No mathematical error found in the target statements or proofs at `0c41fb5`, `adb8e08` or `9b754c8`.

## Not covered (declared)
* At the full `τ_{n,m}`: continuity on `(0,1)` and `→ ∞` (not certified for `τ_{P'}` in Wave 30ts), hence `lem:crossing`'s
  "`S = [α̂,1)` if `α̂ > 0`" (and "`τ(α̂+) = τ(α̂)` when `α̂ > 0`") and the well-definedness sentence after `eq:alphaest`; the other
  clauses of `lem:crossing` except the union formula (it needs `S ≠ ∅` for every realization, i.e. `τ_{P'} → ∞`), and the measurability
  of `α̂` (unconditional), are certified there by `Crossing.crossing_full`; the coupled closed form as a function of `α` (Wave 30tp
  `plugin_coupled` certifies only the validity of any `t` above the supremum over `u`).
* `06_splitting.tex:247-249` at `0c41fb5` (`:253-255` at `9b754c8`; `[α̂_lo, α̂_hi]` from `cor:lower` and `cor:upperfs` at `δ/2` each): the lower end is the betting branch.
* Commentary: "computable from the data", "how large depends on how fast the path leaves zero", "a `min(n,m)^{−1/(2γ)}` rate" (immediate
  from `rate_poly`), the `8.5` vs `13.9` constants, `e_k ≤ k^{−1/2}` (Wave 30tr `ek_le`, not used here).

## Sign-off
- [x] Claude (drafter, prover) · [x] critic before each freeze (independent AI reviewer, 2026-11-08) · [x] fidelity audit · [x] Author
  (automatic on AI-audit PASS)

## Fidelity review
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes (44 targets; each claim
back-translated blind and compared with the printed text at `0c41fb5`, the diff to `adb8e08` checked; labels and paper id checked). All 44
claims ACCEPT (`ratecond_closed`, `ratecond_tauA`, `ratecond_gauss`, `rate`, `hausdorff_valid`, `hausdorff_lower` with notes), none flagged;
every deviation is a declared generalisation or encoding; no junk value live; hypotheses satisfiable (`hausdorff_*`, `tauNM_threshold`,
`tauA_tool`). The sharper candidate is declared pending everywhere and no claim or coverage note overclaims (each instance uses `τ_{n,m}`
only through `ValidThreshold` and `≤ τ^A`; continuity and `→ ∞` only in `tauNM_threshold`). Paper notes 1–7 verified (counterexample of
note 1 checked; notes 4–7 still present at `adb8e08`); no new printed defect. Notes (applied above): the `5e18aa4` hashes were of the working
tree (relabelled; note 3's line); `τ^A(0,1/2) ≈ 0.72` with the exact `e₁₀₀`; "remaining at `0c41fb5` and `adb8e08`"; `t ≥ 0` printed from
`adb8e08`; the well-definedness composition needs `D > 0`; `hausdorff_lower` is the lower half of `eq:pathwise`; the paragraph after
`lem:crossing` added to the coverage list; constants of `ratecond_closed`/`ratecond_tauA`; three vs four candidates; `α* < 1` in `thm:rate`.
The frozen generic header's "and the paragraph after it (`:288-291`)" is covered only for `τ^P`, `τ^A`, `r_n + r_m` (numerical candidates
pending), as the coverage list now says.

Extension (same reviewer, method v1, 2026-11-08), the 12 `Full` claims against master `9b754c8` (the diff `adb8e08 → 9b754c8` checked): all
ACCEPT (`tauFull*`, `tau{P'}`, `tauCpl`, `tauGrid` match the printed `τ_{n,m}`, `A_basic.tex:437-473`; the two `Ψ_H` encodings agree term by
term; `tauCpl` is a genuine supremum for `κ > 0`; `tauFullGrid_threshold` a declared generalisation of the printed grid; `ratecond_full*`
cover the printed Gaussian case). Card-level FLAG: the card said only "`S = [α̂,1)`" and well-definedness were missing at the full `τ_{n,m}`,
but the generic `crossing`/`crossing_meas` assume continuity for every clause, so no `τ`-dependent clause of `lem:crossing`, nor the
measurability of `α̂`, was certified there. Resolved by the continuity-free `Crossing.crossing_nc` and `Crossing.crossing_full` (critic
ACCEPT before freeze) and the corrected coverage text above; notes N1–N6 (claim count, compositions with `tauFull_threshold`, stale
"pending", the betting diff and the uncommitted macro edits, notes 4–7 still present at `9b754c8`, line numbers of the `[α̂_lo, α̂_hi]`
sentence) applied.

Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes (58 targets: the 44 above, the 12
`Full` and the 2 `Crossing` claims, all ACCEPT; the card-level FLAG on the coverage of `lem:crossing` at the full `τ_{n,m}` was raised and
resolved by `Crossing.crossing_nc`, `Crossing.crossing_full` and the corrected coverage text; R1 (the union formula is not certified at the
full `τ_{n,m}`) applied).
