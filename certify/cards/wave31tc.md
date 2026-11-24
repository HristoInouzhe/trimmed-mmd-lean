# Fidelity card — wave 31tc: trimmed-mmd (JMLR **v3**, `jmlr/v3/`), `rem:qdens` (a sufficient condition for (Q))

Lean: `StatFormal/Wave31tc/Statements.lean` (4 claims and the definition `levelDens`; frozen 2026-11-12 before any proof, commit `ef962a2`,
sha256 `84711f515b74f64340069ef8ad648d63ab1cffa9ba9872536ca71d392e890f15`, locked with its 16 imports). Route `RouteCore` (untrusted);
`Proofs.lean` imports it; the gate checks `example : Claims.c := c` and `#print axioms` for each (`[propext, Classical.choice, Quot.sound]`).
Paper id `trimmed-mmd (jmlr)`; label `rem:qdens (v3)` (+ a short description). Branch `tmmd-jmlr-v3qdens`, based on `tmmd-jmlr-v2map` at
`07dfad9` (wave 31ta).
Critic (independent AI reviewer, before the freeze, 2026-11-12): 4 claims, 3 ACCEPT and 1 ACCEPT-WITH-NOTE (`qdens_Q_Qprime`: the quantile
property, `D_α > 0`, the RKHS and the population witness are dropped — generalisations; composing with `cor_trimrate_v2` still needs its
own hypotheses), none false, verdict READY TO FREEZE. It re-derived the proof route, checked vacuity (`h = e^{−x²}`, `t = 1/2`, standard
normal `p`), and checked the Lean `levelDens` by quadrature and 2·10⁷-draw Monte Carlo against `P(h(X) ∈ A)` in four designs (`e^{−x²}`;
`x e^{−x²}` at two levels, one with a shifted normal; a two-bump `h` with four preimages per level): quadrature matches the exact
probabilities to `1.5e−15`, every Monte Carlo `|z| ≤ 1.02`. Applied before hashing: the printed-source paragraph (the remark had meanwhile
appeared in the v3 tex), the generalisation and junk-value wording, the `comap` filter note, the completeness of the declared
conditionalisations, the `qdens_Q_Qprime` docstring.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-12 — PASS with notes (4 claims back-translated blind
and compared with NEW_STATEMENTS.md and `jmlr/v3/sections/05_trimming.tex` as re-read at the audit, all faithful; hashes, lock, freeze commit
and labels checked; the printed remark re-derived and found true, the `d ≥ 2` prose included; notes at the end of this card, applied).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md`, section `rem:qdens` (frozen by the author 2026-11-12; sha256
`6b4825f20f0253ee1dfff276ed801cfcbb906e5bafca87a16106b2ce3557c238`), with its "Formal target (univariate core, d = 1)". The remark is
printed in the v3 tex at `jmlr/v3/sections/05_trimming.tex:66-74` (sha256 `2f72ce1f40ca5e1a4d46fc1e13c5b046fb4b9226e17cbe7cf9ed025c122f0eef`,
re-read at the audit; the file was re-edited 2026-11-12 11:37 UTC, after the freeze `ef962a2` at 11:28: the `:66-78`, sha256 `3fa3cba1…0040` and
the "`d = 1` sentence" in the frozen docstring and in the lock note describe the pre-edit wording; the `d = 1` sum is now printed only in the
proof, `D_trimming.tex:330-332`; the current remark agrees with NEW_STATEMENTS.md, so the claims are unaffected), proof
`jmlr/v3/appendix/D_trimming.tex:312-333` (sha256 `291e0ac8…ea7c`); read-only, read 2026-11-12; trimmed-mmd master `d5cdddb` with `jmlr/v3/`
untracked (the v3 revision in progress). The definitions of (Q), (Q′): `jmlr/v3/sections/05_trimming.tex:54-61` ((Q) at `:55-57`, (Q′) at
`:58-60`).

## Targets (4, all in `certify/targets.toml`, module `StatFormal.Wave31tc.Proofs`)
| label | claim / theorem `StatFormal.Wave31tc.(Claims.)…` |
|---|---|
| `rem:qdens (v3)`, "`L` is compact", every dimension | `level_compact` |
| `rem:qdens (v3)`, the frozen univariate target in the form (Q) | `qdens_univariate` |
| `rem:qdens (v3)`, the univariate target with the explicit continuous density | `qdens_formula` |
| `rem:qdens (v3)`, conclusion and last sentence: (Q) and (Q′) with one `r_Q`, witness form | `qdens_Q_Qprime` |

## Encodings (declared)
* "`X` has a Lebesgue density `p`": the law of `X` on `𝒳 = ℝ` is `P = volume.withDensity (fun x => ENNReal.ofReal (p x))`, `p : ℝ → ℝ`.
  "The law of `h(X)` has on `[t−r,t+r]` a density with values in `[c,C]`" is the frozen `Wave12c.QDensity P h t r c C` (a measurable `g`
  with `c ≤ g ≤ C` on the window and `P(h⁻¹A) = ∫⁻_A ofReal ∘ g` for every Borel `A` in the window) — the encoding of (Q) consumed by the
  frozen `Wave30tx` and `Wave31ta.cor_trimrate_v2` claims; (Q′) is `Wave12c.QDensityLower`.
* "continuous on a neighbourhood of `L`": an open `U ⊇ L` with `ContinuousOn p U` (quantified as data with hypotheses; equivalent to "∃ a
  neighbourhood"). "continuously differentiable": `ContDiff ℝ 1 h`; `h′ = deriv h` (genuine: `h` is differentiable everywhere).
* "`h(x) → 0` as `|x| → ∞`": `Tendsto h atTop (𝓝 0) ∧ Tendsto h atBot (𝓝 0)` for `d = 1`; on `ℝ^d = EuclideanSpace ℝ (Fin d)`,
  `Tendsto h (comap (‖·‖) atTop) (𝓝 0)` (that filter is `cobounded` = `cocompact`; for `d = 0` it is `⊥`, a trivial case).
* The density formula: `levelDens h p s = ∑ᶠ x ∈ {x | h x = s}, p x / |deriv h x|`.
* The witness: `d⋆(x) = ⟨d⋆, φ(x)⟩_𝓗` is `Wave12c.witFn dstar φ`, any real inner product space `H`, any `φ : ℝ → H`, any `dstar ∈ H`.

## Covered — back-translations and deviations
* **`level_compact`** ("The level set is compact", `05_trimming.tex:71`; proof `D_trimming.tex:316-317`). For every `d`, every continuous
  `h : ℝ^d → ℝ` with `h(x) → 0` as `‖x‖ → ∞` and every `t ≠ 0`, `{x : h(x) = t}` is compact. Generalisation: only continuity and decay are
  assumed (no smoothness, no nonemptiness, no gradient condition). This is the only part of the remark stated in every dimension.
* **`qdens_univariate`** (the frozen formal target). For `h : ℝ → ℝ` `C¹` with `h → 0` at `±∞`, `t ≠ 0`, `L = {h = t}` nonempty, `h′ ≠ 0` on
  `L`, `p` continuous on an open `U ⊇ L` and positive on `L`: there are `r > 0` and `0 < c ≤ C` with `QDensity (p·λ) h t r c C`. As frozen.
  Generalisations: `P = p·λ` need not be a probability (or finite) measure; `p` need not be integrable, measurable outside `U`, or
  nonnegative off `L` (only `ENNReal.ofReal ∘ p` enters).
* **`qdens_formula`** (the target's parenthetical and the printed "continuous positive density", `05_trimming.tex:71-72`; the `d = 1` sum `D_trimming.tex:330-332`). Same
  hypotheses; conclusion: `L` is finite, and there are `r > 0`, `0 < c ≤ C` such that `h′ ≠ 0` on `h⁻¹[t−r,t+r]`, each level
  `s ∈ [t−r,t+r]` has finitely many preimages, `levelDens h p` is continuous on `[t−r,t+r]` with values in `[c,C]`, and
  `P(h⁻¹A) = ∫⁻_A ofReal(levelDens h p)` for every Borel `A ⊆ [t−r,t+r]`. Strengthens `qdens_univariate` (it gives the density itself).
* **`qdens_Q_Qprime`** ("Then (Q) holds … The same conditions at `u_α` under `Q` give (Q′)", `05_trimming.tex:68-73`, `𝒳 = ℝ`). For a witness
  `x ↦ ⟨d⋆, φ(x)⟩` that is `C¹` and tends to `0` at `±∞`, the level-set conditions for `(P = p·λ, t_α)` and for `(Q = q·λ, u_α)` give
  `r_Q > 0`, `0 < c_f ≤ C_f`, `c'_f > 0` with `QDensity P d⋆ t_α r_Q c_f C_f` and `QDensityLower Q d⋆ u_α r_Q c'_f` — one common `r_Q`, as
  (Q′) is printed with the `r_Q` of (Q). Generalisations: `t_α`, `u_α` need not be quantiles, `D_α(P,Q) > 0` is not used, `dstar` and `φ`
  are arbitrary. Composition with `cor_trimrate_v2` (not a certified claim): that claim takes `∀ ρ` before `∃ N`, so `ρ := r_Q` works; it
  also needs `P, Q` probability measures and the quantile hypotheses (`IsQuantile`), which the paper's setting supplies.

**Proof route** (untrusted, `RouteCore`; the printed proof `D_trimming.tex:312-333` at `d = 1`): `band_compact` (the band
`{|h − t| ≤ |t|/2}` is closed and inside `[b, a]` where `|h| < |t|/2` beyond); `level_finite` (`L` is a closed subset of the band, its points
are isolated by `HasDerivAt.eventually_ne`, finite subcover); `local_data` (inverse function theorem
`HasStrictFDerivAt.toOpenPartialHomeomorph` at each `x ∈ L`: an open `V ∋ x` inside `U` and a T2-separating `W x`, where `p > 0`, `h′ ≠ 0`,
`h` injective with open image and continuous inverse `g_x`); `formula_core` (the `V_x` are disjoint; `[t−r,t+r] ⊆ ⋂_x h(V_x)` for small
`r` — finite intersection of open sets around `t`; `h⁻¹[t−r,t+r] ⊆ ⋃ V_x` for small `r` — minimum of `|h − t|` on the compact band minus
`⋃ V_x`; then `{h = s} = {g_x(s)}`, `levelDens = Σ_x p(g_x)/|h′(g_x)|`, continuous and positive; the 1-D change of variables
`lintegral_image_eq_lintegral_abs_deriv_mul` on each `h⁻¹A ∩ V_x`; `c, C` = minimum and maximum on the window); `qdens_univariate` takes
`g` = `levelDens` on the window and `0` off it (`ContinuousOn.measurable_piecewise`); `qdens_Q_Qprime` applies it twice and shrinks to
`min(r_1, r_2)` (`QDensity_mono`). The route is the printed one; the printed "minimum and maximum of `h` on `[t_α − r_Q, t_α + r_Q]`" is
literally how `c, C` are chosen.

## Junk-value audit
* `p x / |deriv h x|` in `levelDens`: used only at points of `h⁻¹[t−r,t+r]`, where `qdens_formula` asserts `deriv h ≠ 0`.
* `∑ᶠ` over an infinite set is `0`: used only at levels whose preimage is asserted finite.
* `ENNReal.ofReal` of a negative number is `0`: `ofReal (levelDens h p s)` only for `s` in the window, where `levelDens ≥ c > 0` is asserted;
  `ofReal ∘ p` in `withDensity` is the declared encoding (negative values of `p` count as `0`; near `L`, `p > 0`).
* `withDensity` of a possibly non-measurable `ofReal ∘ p`: `withDensity_apply` needs only a measurable set; the only values used are on
  `h⁻¹[t−r,t+r] ⊆ U` (proof), where `p` is continuous. No `Measure.map` (the law of `h(X)` is `P(h⁻¹ ·)`, with `h` continuous).
* `deriv h`: `h` is `C¹`, so `deriv` is the genuine derivative.
* Vacuity: `h(x) = e^{−x²}`, `t = 1/2`, `p` the standard normal density, `U = ℝ` satisfy every hypothesis (`L = {±√log 2}`); for
  `qdens_Q_Qprime`, `H = ℝ`, `φ(x) = e^{−x²}`, `d⋆ = 1`, `t_α = 1/2`, `u_α = 1/4`. For `level_compact`, any Gaussian bump.

## Defects in the printed text
None. The remark is true as printed (the d-dimensional parts by the printed coarea/flow argument, which the critic and this wave checked
but did not formalize). Cosmetic only: the printed proof uses `h` for the density of `d⋆(X)`, while the formal target uses `h` for the
function (`d⋆`); no clash inside either text.

## Certified results reused (not re-proved)
Definitions only: `Wave12c.QDensity`, `Wave12c.QDensityLower`, `Wave12c.witFn`. Mathlib: `lintegral_image_eq_lintegral_abs_deriv_mul`
(`MeasureTheory/Function/JacobianOneDim`), `HasStrictDerivAt.hasStrictFDerivAt_equiv`, `HasStrictFDerivAt.toOpenPartialHomeomorph`,
`HasDerivAt.eventually_ne`, `Set.Finite.t2_separation`, `IsCompact.exists_isMinOn`/`exists_isMaxOn`. No textbook bridge is formalized; the Gaussian-kernel facts (Steinwart–Christmann
2008, Cor. 4.36, Thm 4.21, Lemma 4.23) enter as hypotheses (see Not covered).

## Not covered (declared)
* The `d ≥ 2` density statements: "near `t_α` the law of `d⋆(X)` has the continuous positive density `∫_{d⋆=t} p/|∇d⋆| dℋ^{d−1}`" and hence
  "(Q) holds" for `d ≥ 2` (Mathlib has no coarea formula; the author's frozen formal target is `d = 1`). Only "`L` is compact" is certified
  in every dimension.
* The Gaussian-kernel facts "`d⋆` is infinitely differentiable and vanishes at infinity" (Steinwart–Christmann 2008, Cor. 4.36, Thm 4.21,
  Lemma 4.23): hypotheses here (`C¹` and decay of `x ↦ ⟨d⋆, φ(x)⟩`), not proved — a conditionalisation; for `d = 1` these two facts are
  all the argument uses.
* The composed statement "under the remark's conditions the rates of `cor:trimrate` hold" is not a separate claim (see the composition
  note under `qdens_Q_Qprime`).

## Coverage note (COVERAGE.md row)
`rem:qdens`: "certified for d = 1 (the author's frozen formal target): h C^1 vanishing at +-infinity, t != 0, L nonempty, h' != 0 on L, p
continuous near L and positive on L give (Q) (QDensity) with the explicit continuous density sum p/|h'| over the level, L finite, and (Q),
(Q') with one r_Q in the witness form; 'L is compact' in every dimension; the Gaussian-kernel smoothness and decay of d* are hypotheses,
the d >= 2 coarea density is not covered (Wave31tc)".

## AI audit notes (2026-11-12, PASS with notes; applied)
1. `jmlr/v3/sections/05_trimming.tex` was re-edited after the freeze (sha256 now `2f72ce1f…0eef`; the remark at `:66-74`, without the `d = 1`
   sentence, which now sits only in the proof `D_trimming.tex:330-332`). The frozen docstring and the lock note describe the pre-edit
   wording; recorded under Source (the frozen file is not edited). The claims are unaffected: the current remark agrees clause by clause
   with NEW_STATEMENTS.md (unchanged, sha256 verified).
2. Line numbers in Source and Covered updated to the current tex (`:71`, `:71-72`, `:68-73`, (Q)/(Q′) at `:54-61`).
3. "No textbook bridge" reworded: none is formalized; the Gaussian-kernel facts enter as hypotheses.
4. Optional polish for the author (not a defect): in `D_trimming.tex:332-333` say "take `r_Q` below both bands' `η`" for the common `r_Q` of
   (Q) and (Q′). The Steinwart–Christmann item numbers were not verified by the auditor (book not available); the argument is standard.
