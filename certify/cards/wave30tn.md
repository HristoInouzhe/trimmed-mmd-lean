# Fidelity card — wave 30tn: trimmed MMD (JMLR) prop:splitfs, eq:trimlip, cor:lower, thm:split restated, lem:unique, lem:popthreshold

Lean: `StatFormal/Wave30tn/Statements.lean` (approved 2026-11-07; imports the frozen Archive statements of waves 30dd (through it 30da, 29l, 29i,
17a, `TrimmedMMD/Concentration`, `Distances`), 30ah (through it `TrimmedMMD/BangBang`, `ZeroSet`, `Unconditional`) and `TrimmedMMD/Lower`),
routes `RouteTrimLip`, `RouteSplitFS`, `RouteLower`, `RouteBootSeq`, `RouteBootAny`, `RouteUnique`, `RoutePop`, `Proofs.lean`.
New definitions (locked): `psi`, `lowerTrim` (bodies verbatim those of `psi`, `lowerTrim` in the wave-30tj statements of branch
`tmmd-jmlr-wave`, not on this branch), `dkwRad` (`e_n(δ) = √(log(4/δ)/(2n))`), `splitBootCdfStd` (the exact bootstrap cdf of
`(T̂* − T̂)/s`, an average over the `n^n m^m` pairs of index maps).
Source: `trimmed-mmd/jmlr/` working tree read 2026-11-07 after commit `e1869dd` (read-only; still being edited, so line numbers are
approximate): `sections/06_splitting.tex` thm:split `:90-119` (Theorem 16 of the PDF) and the remark `:121-124`, prop:splitfs `:134-144`
(Proposition 17), cor:lower `:153-167` (Corollary 18); `appendix/B_split.tex` eq:lowertrim/eq:trimlip `:31-49`, proofs `:92-170`;
`appendix/C_recover.tex` lem:unique `:41-46` (Lemma 34), proof `:48-59`, lem:popthreshold `:198-206` (Lemma 39), proof `:208-227`.
Build: `lake build StatFormal.Wave30tn.Proofs` succeeds; `#print axioms` of all 11 theorems: `[propext, Classical.choice, Quot.sound]`.
Critic (pre-freeze, 2026-11-07, independent subagent, blind back-translation): ACCEPT ×8, ACCEPT-WITH-NOTE ×3 (notes applied to the docstring
before freezing). **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Targets (paper `trimmed-mmd (jmlr)`, module `StatFormal.Wave30tn.Proofs`)
| label | claim / theorem `StatFormal.Wave30tn.(Claims.)…` | printed result |
|---|---|---|
| `eq:trimlip (trimlip)` | `trimlip` | eq:trimlip with its lead-in identity |
| `prop:splitfs (splitfs)` | `splitfs` | Proposition 17 |
| `cor:lower (cor_lower_fs)` | `cor_lower_fs` | Corollary 18, finite-sample clause (NEW) |
| `cor:lower (cor_lower_boot_any)` | `cor_lower_boot_any` | Corollary 18, asymptotic clause, test of thm:split (iii), any `n₂, m₂ → ∞` |
| `cor:lower (cor_lower_split_any)` | `cor_lower_split_any` | Corollary 18 with the plug-in test of the remark, any `n₂, m₂ → ∞` |
| `thm:split (split_normal_ass)` | `split_normal_ass` | Theorem 16 (i) at `α > 0` with "which holds whenever `α > 0`" |
| `thm:split (split_boot_ass)` | `split_boot_ass` | Theorem 16 (ii) at `α > 0` |
| `thm:split (split_zero_boot_any)` | `split_zero_boot_any` | Theorem 16 (ii) at `α = 0` |
| `thm:split (split_witness_zero)` | `split_witness_zero` | Theorem 16, "If `f̂ = 0` …" |
| `lem:unique (unique_trim)` | `unique_trim` | Lemma 34 |
| `lem:popthreshold (popthreshold)` | `popthreshold` | Lemma 39 |

## thm:split [Theorem 16], restated — clause-by-clause map
Setting shared by every claim below (frozen waves 29i/29l/29w/30d/30da/30dd and this wave): `φ : 𝒳 → ℋ` strongly measurable, `‖φ‖ ≤ κ`
(ass:regularity (A1)–(A2)); `f̂ = f` a fixed element of `ℋ` ("condition on the first fold"; `‖f‖ ≤ 1` and `f ≠ 0` not needed:
generalisations); `X`, `Y` i.i.d. `P`, `Q` (X–Y independence kept where the frozen claim has it); `T̂ = splitTrimLo n₂ α (f̂(X)) −
splitTrimUp m₂ α (f̂(Y))` (eq:splitstat via lem:trimmedmean), `T = sepVal f (𝒞_α(P)) (𝒞_α(Q))` (identified with a real);
`σ_{n₂,m₂} = splitSdAny` (`α > 0`), `splitSdZero` (`α = 0`, the printed reading); `ass:split` = frozen `splitAss` on both sides;
"`n₂, m₂ → ∞` in any manner" = size sequences `n_k, m_k ≥ 1`, `→ ∞`, no ratio condition; `z_{1−δ}` = `z` with `Φ̄(z) = δ`;
ideal bootstrap over all `n^n m^m` index pairs.

| printed clause | `α ∈ (0,1)` (under ass:split) | `α = 0` (no condition on the laws) |
|---|---|---|
| (i) `σ > 0` "which holds whenever `α > 0`" | **`split_normal_ass`** (NEW: `σ_{a,b} > 0` for all `a, b ≥ 1`) | — (`σ > 0` is a hypothesis at `α = 0`) |
| (i) `(T̂ − T)/σ ⇒ N(0,1)`, any `n₂, m₂ → ∞` | **`split_normal_ass`** (NEW, from ass:split); frozen 30da `split_normal_any` (under quantile uniqueness + positive influence variances, the premises `split_normal_ass` derives) | frozen 30dd `split_zero_normal_any` (`σ > 0` ⟺ `Var U + Var V > 0`) |
| (ii) `ŝe*/σ → 1` in probability | **`split_boot_ass`** (NEW, from ass:split); frozen 30dd `split_boot_se_any` (uniqueness + positive variances) | frozen 30dd `split_zero_boot_se_any`; restated in **`split_zero_boot_any`** |
| (ii) conditional law of `(T̂* − T̂)/σ` ⇒ `N(0,1)` in probability, any `n₂, m₂ → ∞` | **`split_boot_ass`** (NEW; before this wave only the ratio regime, frozen 29l `split_boot_clt`) | **`split_zero_boot_any`** (NEW, incl. one vanishing variance; before: ratio regime, frozen 30d `split_zero_boot_clt`) |
| (iii) `liminf P(T̂_δ ≤ T) ≥ 1 − δ`, `T̂_δ = T̂ − z ŝe*` | frozen 30dd `split_level_bootstrap_any` (1st conjunct) | frozen 30dd `split_zero_level_bootstrap_any` (1st conjunct, incl. `σ = 0`) |
| (iii) "If `H_{0,α}` holds then `T ≤ 0`" | frozen 22c `split_null_nonpos` (every `f`, `α ∈ [0,1)`) | same |
| (iii) `limsup P(reject) ≤ δ` | `split_level_bootstrap_any` (2nd conjunct) | `split_zero_level_bootstrap_any` (2nd) |
| (iii) "a rejection certifies `TV(P,Q) > α`" | `split_level_bootstrap_any` (3rd: on the coverage event, `T̂_δ > 0 ⇒ TV > α`) | `split_zero_level_bootstrap_any` (3rd) |
| "If `f̂ = 0` the statistic is identically zero and the rule never rejects" | **`split_witness_zero`** (NEW; every `α`, all sizes `≥ 1`, every sample; also for the plug-in and percentile rules) | same |
| "All probabilities are conditional on the first fold … for each pair `(P,Q)`, not uniformly" | encoding (fixed `f`; every claim is `∀ P Q`) | same |
| remark: the percentile limit satisfies (iii) "when `m₂/n₂` converges to a positive constant" | frozen 29l `split_boot_percentile` (ratio regime) | frozen 30d `split_zero_boot_percentile` (ratio regime) |
| remark: "the plug-in standard error … does too" | frozen 30da `split_level_any` (any regime); ratio regime 29i `split_level_discharged` | frozen 30dd `split_zero_level_any` (any regime); ratio regime 29w `split_zero_level` |

Declared encodings for the map: the ratio-regime claims index the sizes by `n₂` (`m₂ = m(n₂)`, `m(n)/n → κ > 0`); this is equivalent to
"along any size sequence with `m₂/n₂ → κ > 0`" (a failing sequence has a subsequence with strictly increasing `n₂`, which extends to a
function `m(·)` with the same ratio limit). The general-regime claims of 30da/30dd that assume positive influence variances are superseded at
`α > 0` by `split_normal_ass` and `split_boot_ass`, which are stated directly under ass:split. cor:lower with the percentile rule of the
software (text after the corollary) is the frozen wave-30at `cor_lower_perc` (ratio regime, the scope of the remark). With this wave the restated Theorem 16 is
**covered clause by clause** (supersedes the "covered as printed" note of `wave30dd.md`, which was written for the old statement without
the explicit bootstrap-CLT clause in (ii)).

## Covered — back-translations (plain mathematics of the frozen claims)
* **`trimlip`** — For probability laws `F, F'` on `ℝ` with `F([−κ,κ]) = F'([−κ,κ]) = 1` and `α ∈ [0,1)`, `β = (1−α)⁻¹`,
  `L(F) = sup_{s∈ℝ} ∫ (s − β(s−u)_+) dF(u)`: (a) `∫(s−u)_+ dF(u) = ∫_{−κ}^s F(u) du` for `s ∈ [−κ,κ]`; (b) `|L(F) − L(F')| ≤
  sup_{s∈[−κ,κ]} β|∫_{−κ}^s (F − F')|`; (c) that supremum is `≤ 2κβ sup_u |F(u) − F'(u)|`. As printed.
* **`splitfs`** — For every pair `(P,Q)`, `‖f‖ ≤ 1`, `α ∈ [0,1)`, `δ ∈ (0,1)` and all `n, m ≥ 1`, with `T = sep(f; 𝒞_α(P), 𝒞_α(Q))` (a real):
  `P(|T̂ − T| > 2κβ[e_n(δ) + e_m(δ)]) ≤ δ`; and if `TV(P,Q) ≤ α`, `P(T̂ > 2κβ[e_n(δ) + e_m(δ)]) ≤ δ`. As printed ("no condition on the laws").
* **`cor_lower_fs`** — Grid `α_1 < ⋯ < α_J` in `[0,1)`, witnesses `‖f_j‖ ≤ 1`, reject `H_{0,α_j}` iff `T̂_j > 2κβ_j[e_n(δ)+e_m(δ)]`,
  `α̂_lo` of eq:downclosed: `P(α̂_lo > TV(P,Q)) ≤ δ` for all `n, m ≥ 1`, no density condition. As printed.
* **`cor_lower_boot_any`** / **`cor_lower_split_any`** — Same grid, `ass:split` at every `α_j > 0` for `f_j`, reject iff `T̂_j − z ŝe_j > 0`
  with the bootstrap / plug-in SE, sizes `n_k, m_k → ∞` arbitrarily: `limsup_k P(α̂_lo > TV) ≤ δ`.
* **`split_normal_ass`** — Under ass:split at `α ∈ (0,1)`: `σ_{a,b} > 0` for all `a, b ≥ 1`, and `(T̂_k − T)/σ_{n_k,m_k} ⇒ N(0,1)`.
* **`split_boot_ass`** — Under ass:split at `α ∈ (0,1)`: `ŝe*_k/σ_k → 1` in probability, and for every `t`, `P*((T̂* − T̂)/σ_k ≤ t) → Φ(t)` in
  probability.
* **`split_zero_boot_any`** — At `α = 0`, if `Var U + Var V > 0`: the same two conclusions with `σ_k² = Var U/n_k + Var V/m_k`.
* **`split_witness_zero`** — If `f = 0`: for every `α, δ, z`, all sizes `≥ 1` and every sample, `T̂ = 0`, `ŝe* = 0`, and none of
  `T̂ − z ŝe*`, `T̂ − z ŝe`, the percentile limit is `> 0`.
* **`unique_trim`** — Measurable singletons, (A1), (A3) (frozen `Characteristic`: equal Bochner embeddings of probability measures ⇒ equal
  measures), `α, β ∈ [0,1)`, `n, m ≥ 1`, `X_1..X_n, Y_1..Y_m` pairwise distinct: `√(min_{Δ_α(n)×Δ_β(m)} eq:qp) > 0` and the set of
  minimisers of eq:qp is a singleton. As printed.
* **`popthreshold`** — (A1), `α, β ∈ [0,1)`, `dist(𝒞_α(P), 𝒞_β(Q)) > 0`, `d` of minimum norm in `𝒞_α(P) − 𝒞_β(Q)`, `d = a − b`,
  `a = ∫ gφ dP`, `g ∈ 𝒢_α(P)`, `b ∈ 𝒞_β(Q)`, `t` a `(1−α)`-quantile of `⟨d, φ(X)⟩`: `g = (1−α)⁻¹` a.e. on `{⟨d,φ⟩ < t}` and `g = 0` a.e. on
  `{⟨d,φ⟩ > t}`. As printed.

## Deviations and encodings (declared)
* **Generalisations.** X–Y independence dropped in `splitfs`, `cor_lower_fs`, `split_boot_ass`, `split_zero_boot_any` (not needed: union bound;
  the bootstrap law is a convolution of two one-sample conditional laws). `cor_lower_*_any`: no `‖f_j‖ ≤ 1` (the rules are scale-invariant in
  `f_j`). `cor_lower_split_any`: the plug-in rule in the general regime (the remark may be read as scoped to the ratio regime). (A2) and (A3)
  not assumed except (A3) in `unique_trim`; `f ≠ 0`, `‖f‖ ≤ 1` not assumed in the thm:split claims. `split_witness_zero` holds for every `α`.
  `popthreshold`: the printed `dist > 0` is kept but unused (the conclusion holds without it).
* **Encodings.** As in the setting above; "probability" of a possibly non-measurable event is the outer measure (an upper bound on it is the
  stronger statement); "converges weakly in probability" of the conditional law = for every `t` the exact conditional cdf converges in
  probability to `Φ(t)` (equivalent, the limit being continuous; as frozen 29l). `D̂_{α,k} = √(min eq:qp)` over `Δ_α(n) × Δ_β(m)` (eq:qp,
  the two-level problem of Section 8). `𝒢_α(P)` = frozen `IsTrimDensity` (everywhere-bounded representatives; the conclusion is a.e.).
  Existence of `d*` and of its decomposition is presupposed by the print ("Let `d*` be … write …") and is a hypothesis.
* **Specialisations.** None. **Conditionalisations.** None (every new claim is unconditional; no textbook bridge).

## Junk-value audit
`lowerTrim` is an `iSup` of a family bounded above by `κ` (`ψ_s(u) ≤ u`; proved, `bdd_psi`); the `sSup` is over the image of the nonempty
`[−κ,κ]` (`κ ≥ 0` forced) of a function bounded by `2κβ`; `⨆_u |F − F'|` is bounded by 1. `dkwRad`: `log(4/δ) > 0`, `n ≥ 1`. `splitTrimLo/Up`,
`splitSE`, `splitBootSE`, `splitBootPerc` at sizes `≥ 1` are genuine (frozen audits); in `split_witness_zero` all values are 0 (an `sInf`/`sSup` of
a subset of `{0}`) — sizes `≥ 1` added so no instance rests on an empty extremum; for `α ∉ [0,1)` (not a printed level) the claim holds through
junk values (empty capped set, `/0` in `splitSE`), harmless since the `α ∈ [0,1)` case is genuine. `splitSdAny > 0` (proved), `splitSdZero > 0` (from
`Var U + Var V > 0`), so `splitBootCdfStd` divides by positive numbers. `sepVal` is identified with a real. `alphaLo` frozen. `sInf` of `qp` over
a nonempty compact set; `setDist` nonneg. Bochner integrals of bounded strongly measurable integrands only. No `Measure.map` of a
non-measurable map (maps guarded by measurability). Non-vacuity: `trimlip`, `splitfs`, `cor_lower_fs`: `F = F' = δ₀`; `P = Q` uniform with the
clamped `φ`; thm:split claims: frozen `Wave29i.splitAss_uniform` (`α = ½`) with `n_k = k+1`, `m_k = 2^k`; `split_zero_boot_any`: clamped `φ`,
`f = 1`, `Var = 1/12`; `unique_trim`: `𝒳 = Fin N`, one-hot `φ`; `popthreshold`: `P = δ₀`, `Q = δ₁`, clamped identity.

## Route
* eq:trimlip: Tonelli on `1{u ≤ t}` over `F ⊗ λ|_{[−κ,s]}`; every `s` dominated by `−κ` or `κ` (`β ≥ 1`); `|sup a − sup b| ≤ sup |a − b|`.
* prop:splitfs: `min_{𝒞_α(R)}⟨f,·⟩ = L(law of ⟨f,φ⟩)` (weak duality + the library minimiser at the frozen wave-12c quantile); `L(F_n) =
  splitTrimLo` (library duality); eq:trimlip twice; DKW–Massart (library `DKW.Massart.massart`, score `e^h`, via `Measure.pi`);
  `2e^{−2n e_n²} = δ/2`; union bound; level via frozen `split_null_nonpos`.
* cor:lower: frozen `downclosed_pathwise` (first grid level `≥ TV`); general regime via the wave-30at `lower_generic` and frozen 30da/30dd level claims.
* thm:split (ii): new deterministic general-regime bootstrap CLT `boot_std_seq` (characteristic functions factorise over the two resamples,
  library `tendsto_char_side` along subsequences on which the variance share converges (Bolzano–Weierstrass), remainder `√(2s²E*D²/S_k)`,
  Lévy + portmanteau), uniformised by contradiction (`boot_std_unif`), in probability from the one-sample library consistency
  (`tip0_varLo`, `tip0_bootD`; `tip0_varLo_zero`, `bootD_zero` at `α = 0`; an almost surely constant side when one variance is 0).
* lem:unique: (A3) on finitely many distinct points makes a signed weight vector of mass 0 with zero embedding vanish (`signed_zero`); applied to
  `(w, −v)` (zero value) and to the difference of two minimisers (unique witness, frozen `bangbang_i`); a minimiser exists (frozen `bangbang_set`).
* lem:popthreshold: first-order condition from convexity of `𝒢_α(P)`; comparison with the bathtub density `ḡ = β̄1{Z<t} + θ1{Z=t}`:
  `(g − ḡ)(Z − t) ≥ 0` has integral `≤ 0`, hence vanishes a.e. (instead of the printed mass-transfer contradiction).

## Overlap with branch `tmmd-jmlr-wave` (for the integration pass)
`eq:trimlip` is also certified there (wave 30tk `trimlip`, committed 2026-11-07 20:32, the suprema encoded through upper bounds); this wave's
`trimlip` states the same three parts with the literal `sSup`/`⨆` and is the lemma the `splitfs` proof uses. Keep both or drop one target.
`psi`/`lowerTrim` here are verbatim the wave-30tj definitions (provably `rfl`-equal once both are on one branch).

## Paper notes
* `appendix/B_split.tex:150` (proof of prop:splitfs), committed text `e1869dd`: "`T̂ − T = [L(F_{n₂}) − L(F)] − [L(G_{m₂}) − L(G)]`" has the wrong
  sign (the second term of eq:splitstat is `−L(G_{m₂})`, so `T̂ = L(F_{n₂}) + L(G_{m₂})`); harmless (absolute values follow). Already corrected to
  `+` in the working tree read 2026-11-07. S5.
* `lem:popthreshold`: the hypothesis `dist > 0` is not needed for the conclusion (optional).
* `lem:unique`: (A2) is not used (optional).

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-07 — PASS with notes (11 targets, each claim back-translated blind from
`Statements.lean` and the frozen definitions before reading the paper or this card, then compared clause by clause with the JMLR text; every
row of the thm:split map spot-checked against the cited frozen Lean claims; `lake build StatFormal.Wave30tn.Proofs` re-run).
Notes:
* All 11 faithful; no hypothesis stronger than printed; no smuggling; witnesses checked (δ₀; `splitAss_uniform` at `α = ½`; one-hot `φ`;
  δ₀ vs δ₁). Labels, paper id and line numbers correct.
* Map wording "informative … because ass:split implies them" overstated what is certified (only `σ_{a,b} > 0` and the `α > 0` conclusions under
  ass:split); reworded above. Coverage unaffected.
* `split_witness_zero` at `α ∉ [0,1)` holds through junk values; sentence added to the junk audit.
* Optional: a cor:lower target for the percentile rule — already the frozen wave-30at `cor_lower_perc` (ratio regime); noted in the map.
* eq:trimlip is also certified on branch `tmmd-jmlr-wave` (wave 30tk); resolve the duplicate label at integration.
* Paper notes confirmed (B_split.tex:150 sign now "+" in the working tree; `dist > 0` unused in lem:popthreshold; (A2) unused in lem:unique).
