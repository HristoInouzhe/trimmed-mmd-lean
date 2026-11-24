# Fidelity card — wave 31tn: trimmed-mmd (**Annals of Statistics version of 2026-11-20**): `prop:lower2pt`, `lem:twopointmargin`, `cor:minimax`, `prose:nouniformrate`, and (second freeze) `prose:diffrac`, `prose:rhcrules`, `prose:kinkclass`

Lean: `StatFormal/Wave31tn/Statements.lean` (8 claims, S1–S4; new definitions `mixAt`, `hStar`, `clo`, `InM`, `rootLevels`,
`rootGrid`; frozen 2026-11-20 before any proof, commit `1b5fcf3`, locked with its imports) and `StatFormal/Wave31tn/Referee/Statements.lean`
(5 claims, S5–S7, no new definition; second freeze 2026-11-20 before any proof, commit `29319df`). Routes `RouteTV`, `RouteKL`, `RouteS1`,
`RouteS2`, `RouteS4`, `RouteS3i`, `RouteS3ii`, `RouteS3iii` and `Referee/RouteReferee` (untrusted; WIP commits `7210827`, `2711851`,
`84376cc`, `3a6a1d1`, `d2a7a28`, `79748d6`); `Proofs.lean` and `Referee/Proofs.lean` define the 13 theorems and check
`example : Claims.X := X`; all proved, axioms propext, Classical.choice, Quot.sound.
Paper id `trimmed-mmd (jmlr)` (the trimmed-mmd paper face `Papers/TrimmedMMDJMLR`), labels suffixed "(AoS 2026-11-20)". Branch
`tmmd-aos-minimax` (worktree `~/projects/StatFormal-tmmd-aos`), from local master `7f68669`.
Critic (independent AI reviewer, before each freeze, 2026-11-20): S1–S4 READY TO FREEZE — `lower2pt_tv`, `lower2pt_c`, `twopointmargin`,
`nouniformrate` ACCEPT; `lower2pt`, `minimax_i`, `minimax_ii`, `minimax_iii` ACCEPT-WITH-NOTE; R1–R5 header/docstring-only, applied (R6, an
optional non-vacuity claim for the run predicate, not applied). S5–S7 READY TO FREEZE — `diffrac`, `rhcrules_a` ACCEPT; `rhcrules_b`,
`kinkclass_sep`, `kinkclass_kink` ACCEPT-WITH-NOTE; R1–R5 header/docstring-only, applied. No Lean term changed by either review.
Gate (2026-11-20, branch `tmmd-aos-minimax`): `CERTIFIED: 3966 targets; statements frozen; axioms within ['Classical.choice',
'Quot.sound', 'propext']`. `tools/check_aliases.py`: `ALIASES OK: 3909 aliases in 16 paper files; each is literally a certified
theorem under its frozen claim; all 3898 targets of the 16 paper pages covered (68 targets have no page)`.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-20 — PASS with notes (blind back-translation of all
13 claims written from the frozen files before comparison; both Statements hashes match the lock, both source hashes match; faithful,
deviations declared; no undeclared stronger hypothesis, unguarded junk value or restated conclusion; labels exist in the AoS source;
audit done on the frozen statements before the proofs were finished; notes at the end, applied to this card).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`~/projects/tmmd-aos-brief/NEW_STATEMENTS.md` (frozen statements of the AoS version, 2026-11-20). S1–S4: lines 1–120, sha256
`23660a336c7b7498c8804106718fdd6db6f8feb724d36e0ac51f82892039866c` (the whole file as first read). S5–S7 appended the same day: whole file
`467357fecbacc9c72c39ae6c212daab755171b462decd15baf209ccd3d854162`, lines 1–120 unchanged. Setting of `jmlr/v3` §2 (trimmed-mmd `b41ea67`).
Printed-notation change (2026-11-20, does not affect the frozen text): the paper writes `n∧m` (and `n_1`) where S3 writes `N` (`N₁`).
Printed locations (AoS source `trimmed-mmd/aos/`, read-only, 2026-11-20): `prop:lower2pt` Proposition 5.5, `sections/05_rates.tex:110`
(part (c) is the prose after it, `:126-129`; the "(c)" of the target label follows NEW_STATEMENTS); `cor:minimax` Corollary 5.6,
`05_rates.tex:135`; `lem:twopointmargin` Lemma S4.7 of the supplement, `supplement/S4_rates.tex:430-438` (in the supplement, not in the
main text as the frozen S1–S4 header says); `prose:nouniformrate` `05_rates.tex:21-24` (also `01_introduction.tex:68`); `prose:diffrac`
`02_regions.tex:38-42`; `prose:rhcrules` `07_numerical.tex:148-151`; `prose:kinkclass` `05_rates.tex:162-165`.

## Targets (13 claims; modules `StatFormal.Wave31tn.Proofs` (S1–S4) and `StatFormal.Wave31tn.Referee.Proofs` (S5–S7))
| label | claim / theorem |
|---|---|
| `prop:lower2pt` (a): `TV(P_a,Q_a) = a`, `TV(P_{a,h},Q_a) = TV(P_a,Q_{a,h}) = a+h` | `StatFormal.Wave31tn.(Claims.)lower2pt_tv` |
| `prop:lower2pt` (b): `P(TV − α̃ ≥ h) ≥ 1 − δ − h√(n/(2a(1−a)))` (resp. `m`) | `StatFormal.Wave31tn.(Claims.)lower2pt` |
| `prop:lower2pt` (c): at `h = ((1−δ)/2)√(2a(1−a)/(n∧m))`, probability `≥ (1−δ)/2` | `StatFormal.Wave31tn.(Claims.)lower2pt_c` |
| `lem:twopointmargin`: `D_{α⋆−ε} ≥ ε/‖f‖` for both perturbed pairs | `StatFormal.Wave31tn.(Claims.)twopointmargin` |
| `cor:minimax` (i): lower bound `c_lo(n∧m)^{-1/2}` with probability `≥ (1−δ)/2` over `𝓜` | `StatFormal.Wave31tn.(Claims.)minimax_i` |
| `cor:minimax` (ii): analytic `α̂` valid and within `C(n∧m)^{-1/2}` uniformly over `𝓜` | `StatFormal.Wave31tn.(Claims.)minimax_ii` |
| `cor:minimax` (iii): `α̂_lo` on `{j(n∧m)^{-1/2}}` valid and within `C(n∧m)^{-1/2}` uniformly | `StatFormal.Wave31tn.(Claims.)minimax_iii` |
| `prose:nouniformrate`: no valid lower bound over `𝒫₂` has a uniform rate `r < 1` | `StatFormal.Wave31tn.(Claims.)nouniformrate` |
| `prose:diffrac`: `P′ ∈ R_{α₁}(P) ∩ R_{α₂}(Q)` ⟹ `α₁ ∨ α₂ ≥ TV(P,Q)` | `StatFormal.Wave31tn.Referee.(Claims.)diffrac` |
| `prose:rhcrules` (a): `0.089·5735, 0.098·5735 < 0.30·2184` | `StatFormal.Wave31tn.Referee.(Claims.)rhcrules_a` |
| `prose:rhcrules` (b): `k_X + k_Y ≤ ⌊0.098·5735⌋` ⟹ `max(k_X/2184, k_Y/3551) < 0.30` | `StatFormal.Wave31tn.Referee.(Claims.)rhcrules_b` |
| `prose:kinkclass` (a): `ex:separated` pairs with `‖f‖ ≤ 2/c₀`, `α⋆ ∈ [a₀,a₁]` lie in `𝓜` | `StatFormal.Wave31tn.Referee.(Claims.)kinkclass_sep` |
| `prose:kinkclass` (b): slope `s ≥ c₀` of the rescaled path gives `PolyMargin` with `c₀`, `γ = 1` | `StatFormal.Wave31tn.Referee.(Claims.)kinkclass_kink` |

## Encodings (declared; full list in the two Lean headers)
* (A1) `φ : 𝒳 → H` strongly measurable, `‖φ x‖ ≤ κ`, `H` a real complete inner-product space; (A2) separability only where the
  certified rate results need it (S3 (ii), (iii), S7 (b)); (A3) nowhere (no proof uses it). `Δ_φ` is any `Dφ ≥ ‖φ x − φ x′‖` with
  `Dφ ≤ 2κ`. `D_α` is `Dpop` (= the printed infimum `dTrim` by the certified `Wave8a.georep_dist`; S2 states both).
* `P_a = (1−a)R + aP₀ = mixAt R P₀ a`, `P_{a,h} = mixAt R P₀ (a+h)`; "concentrated on pairwise disjoint measurable sets" as in the certified
  `Wave31tb.separated`.
* Randomised estimators: a measurable `T` of `((X_{1:n}, Y_{1:m}), U)`, `U ∼ ρ` on any probability space, law `(sampleLaw P Q n m).prod ρ`
  (S4: `dataLaw` on `ℝ`), as in the certified `thm:impossible` (`Wave31ta.impossible_two`): no deviation from its randomisation model.
* `𝓜(a₀,a₁,c₀) = InM`: probability measures with `a₀ ≤ TV ≤ a₁` and `PolyMargin φ P Q c₀ 1`. `sup_𝓜 P(·) ≤ c`: for all pairs of `𝓜`;
  `sup_𝓜 P(·) ≥ c` (S3 (i)): some pair of `𝓜` (stronger). "`C, N₁` depending only on …" (S3 (ii), (iii)): `∃ C N₁` placed right after
  those parameters and before `𝒳`, `φ`, `n`, `m`, the pair (and, in (iii), `a₀` and the run) — the equivalent form allowed by the brief.
  `N^{-1/2}` is `1/√(n∧m)`.
* S3 (iii): the grid `{j(n∧m)^{-1/2} : j ≥ 1} ∩ (0,1)` is `rootGrid`, `⌈√(n∧m)⌉ − 1` levels; the run is `IsWitnessRun … (1/2) s2 ∧
  IsDefaultRun`, `0 < s2 ≤ 4`, as in the certified `Wave31tl.lorate_O` (with its inherited generalisations: any cut points satisfying (C),
  any fractions within `[lamLo, lamHi]`).
* S3 (i) needs no measurable singletons (the sets are level sets of `⟪f, φ ·⟫`). `‖f‖` is the norm in `H`; for the canonical feature map it
  is the RKHS norm, so the printed statement is an instance. S4: `𝒫₂` (densities `≤ 2`) is narrower than the printed "bounded
  densities", so the Lean form is the stronger statement; `δ, δ′ > 0` loses nothing (boundary cases follow by enlarging `δ`).
* S5: one `P′ ∈ trimSet P α₁ ∩ trimSet Q α₂`. S6: decimals in `ℝ`, integers in `ℕ`, `⌊·⌋₊`. S7 (b): "the path" is the rescaled path
  `u(α) = (1−α)D_α` (see Defects).

## Covered — back-translation and deviations
* `lower2pt_tv`: `R, P₀, Q₀` probability measures on pairwise disjoint measurable sets, `a ∈ (0,1)`, `h ∈ [0,1−a)`: the three TV values.
  Faithful.
* `lower2pt`: same setting, any `n, m`, any measurable randomised `T` with `P_{P_a,Q_a}(T > a) ≤ δ`; for `h ∈ (0,1−a)`:
  `P_{P_{a,h},Q_a}(h ≤ TV(P_{a,h},Q_a) − T) ≥ 1 − δ − h√(n/(2a(1−a)))` and the `Q`-perturbed bound with `m`. Generalisation: `δ` any real.
  The exact printed constant is stated (not weakened).
* `lower2pt_c`: same with `n, m ≥ 1`, `δ ∈ [0,1]`, `hStar = ((1−δ)/2)√(2a(1−a)/(n∧m)) < 1 − a`: `n ≤ m` ⟹ the `P`-perturbed pair has
  probability `≥ (1−δ)/2`; `m ≤ n` ⟹ the `Q`-perturbed pair does. At `n = m` both (stronger than "one of the two"). `n, m ≥ 1`: junk guard.
* `twopointmargin`: (A1), `f = 0, 1, −1` on `S_R, S_P, S_Q`: `‖f‖ > 0`; both perturbed pairs have `TV = a+h` and, for `ε ∈ [0,a+h]`,
  `ε/‖f‖ ≤ dTrim` and `≤ Dpop` at level `a+h−ε`; `PolyMargin` with `c₀ = 1/‖f‖`, `γ = 1`. Faithful (strengthened by the extra conjuncts).
* `minimax_i`: (A1), `⟪f,φ x₁⟫ = 1`, `⟪f,φ x₂⟫ = 0`, `⟪f,φ x₃⟫ = −1`, `0 < a₀ < a₁ < 1`, `0 < c₀ ≤ 1/‖f‖`, `δ ∈ (0,1)`,
  `n∧m ≥ c_lo²/(a₁−a₀)²`, measurable randomised `T` with `P(T > TV) ≤ δ` on all of `𝓜`: some `(P,Q) ∈ 𝓜` has
  `P(c_lo/√(n∧m) ≤ TV − T) ≥ (1−δ)/2`. Faithful (existential stronger than sup).
* `minimax_ii`: for `κ, Dφ, 0 < a₀ < a₁ < 1, c₀ > 0, δ, δ′ ∈ (0,1)` there are `C, N₁` such that for all (A1)–(A2) `φ` with `‖φ‖ ≤ κ`,
  `‖φ x − φ x′‖ ≤ Dφ ≤ 2κ`, all `n∧m ≥ N₁` and `(P,Q) ∈ 𝓜`: `P(α̂ > TV) ≤ δ` and `P(TV − α̂ > C/√(n∧m)) ≤ δ + δ′`, `α̂` at the paper's `τ_{n,m}`
  (`tauFull`). Generalisation: no three points, no `f`, no (A3).
* `minimax_iii`: for `κ, Dφ, 0 < a₁ < 1, c₀ > 0, s2 ∈ (0,4], δ, η ∈ (0,1)` there are `C, N₁` such that for every `a₀ ∈ (0,a₁)`, (A1)–(A2)
  `φ` with `‖φ‖ ≤ κ`, `‖φ x − φ x′‖ ≤ Dφ ≤ 2κ`, `n∧m ≥ max(N₁, 10)`, `(P,Q) ∈ 𝓜` and run on `rootGrid`: `P(α̂_lo > TV) ≤ δ` and `P(TV − α̂_lo > C/√(n∧m)) ≤ η`. Faithful; same
  generalisations as (ii).
* `nouniformrate`: `n, m ≥ 1`, `δ, δ′ > 0`, `δ + δ′ < 1`, `r < 1`, measurable randomised `T` on `ℝ`-samples: not both
  `P(T > TV) ≤ δ` and `P(TV − T > r) ≤ δ′` on all of `𝒫₂`. Generalisation: `r < 0` allowed.
* `diffrac`: `P, Q` probability measures, `α₁, α₂ ∈ [0,1)`, `P′ ∈ trimSet P α₁`, `P′ ∈ trimSet Q α₂`: `TV(P,Q) ≤ max(α₁,α₂)`. Faithful.
* `rhcrules_a`, `rhcrules_b`: the printed arithmetic. Faithful.
* `kinkclass_sep`: (A1), the `ex:separated` pair with `α⋆ ∈ (0,1) ∩ [a₀,a₁]`, `c₀ > 0`, `‖f‖ ≤ 2/c₀`: `PolyMargin … c₀ 1` and `InM`.
* `kinkclass_kink`: (A1)–(A2), `0 < α⋆ < 1`, `c₀ > 0`, `u(α⋆−ε)/ε → s` as `ε ↓ 0`, `s ≥ c₀`: `PolyMargin … c₀ 1`, and `InM` when
  `α⋆ ∈ [a₀,a₁]`.

## Proof route (untrusted)
* `lower2pt_tv` (`RouteTV.tv_mixAt`, `RouteS1`): on `A`, `P_s(A) − Q_t(A) = (t−s)R(A) + sP₀(A) − tQ₀(A) ∈ [−max, max]`; `S_P` attains `s`,
  `S_Q` attains `−t`, so `TV(P_s,Q_t) = max(s,t)`.
* `lower2pt` (`RouteKL`, `RouteS1`): `P_{a,h} = P_a.withDensity g`, `g = (a+h)/a` on `S_P`, `(1−a−h)/(1−a)` off it; Mathlib's
  `klDiv_eq_lintegral_klFun_of_ac` and `klFun y ≤ (y−1)²` (`log y ≤ y − 1`) give `KL(P_{a,h}‖P_a) ≤ χ² = h²/a + h²/(1−a) = h²/(a(1−a))`
  (computed exactly by `lintegral_piecewise`); the library's `tvDist_pi_le_sqrt_klDiv` (Pinsker + `klDiv_pi_eq`) gives
  `TV(P_{a,h}^n, P_a^n) ≤ h√(n/(2a(1−a)))`; the other sample and the randomiser are common factors (`tvDist_prod_left_le`,
  `tvDist_prod_right_le`); Le Cam (`measureReal_ge_sub_tvDist`) on `{α̃ ≤ a}`, where the error at the perturbed pair is `≥ h`. The printed
  route, with the exact constant; no Hellinger step.
* `lower2pt_c`: (b) at `h = hStar`, `h√(N/(2a(1−a))) = (1−δ)/2`; `δ = 1` separately (`h = 0`, bound `0`).
* `twopointmargin` (`RouteS2`): for `z ∈ 𝒞_α(P_s)`, `⟪f,z⟫ = 1 − (1−s)E_R g = sE_{P₀}g ≥ 0` (certified `Wave31tb.inner_mix`) and
  `(1−α)⟪f,z⟫ ≥ s − α`; symmetrically on `𝒞_α(Q_t)`; Cauchy–Schwarz and `le_csInf` give `D_α ≥ (max(s,t) − α)/‖f‖`; `dTrim` by the
  certified `Wave8a.georep_dist`. The printed route through the regions (no explicit optimal trimming needed).
* `minimax_i` (`RouteS3i`): `lower2pt_c` at `a = a₀` with the point masses at `x₂, x₁, x₃` on the level sets of `⟪f,φ·⟫`;
  `h = c_lo/√N ≤ a₁ − a₀`; the three pairs in `𝓜` by `lower2pt_tv`, `twopointmargin` and monotonicity of `PolyMargin` in `c₀`.
* `minimax_ii` (`RouteS3ii`): `C′ = 2κK/(1−a₁)`, `K = 2√2 + 4 + √log(1/δ) + √log(1/δ′)`, `C = C′/c₀`, `N₁ = max(1,(C′/(c₀a₀))²)`; the bound
  `t ≤ C′/√N ≤ c₀a₀ ≤ c₀α⋆` from the certified `tauFull_threshold` (`τ_{n,m} ≤ τ^A`) and `Wave31ti.tauA_le_printed` (free of the rate
  hypothesis, which the bound inside `rate_v3_full` is not); the event of the certified `Wave31ti.rate_v3_full` at `γ = 1`; validity from
  the certified `Wave30tu.Full.consistency_i_full`. Route difference: the print's `s ≤ 2/N`, `c = 1/N`, `e_k ≤ k^{-1/2}` are inside
  `tauA_le_printed`.
* `minimax_iii` (`RouteS3iii`): the certified `Wave31tl.lorate_i` at `ε = C_ε/√N`, `h₀ = 1/√N` (the exact gap of `rootGrid`), `γ = 1`,
  `B = 2`; `J_ε ≤ 2(1+C_ε)`; `r₁ ≤ 12/N`, `R.N ≥ N/2` (certified `lorate_batches`); `T_fit ≤ A/√N`, `T_bet ≤ (b₀ + b₁√log(4(1+C_ε)/η))/√N`,
  `C_ε = max(1, A/c′, 2b₀/c′, 32b₁²/(ηc′²))`, `c′ = c₀(1−a₁)` (`log y ≤ y`); `a_ε ≥ α⋆ − ε − 1/√N` on `rootGrid`; `C = C_ε + 1`,
  `N₁ = 10`, free of `a₀`; when `ε > α⋆` the event is empty (`α̂_lo ≥ 0`); validity from the certified `Wave30tz.lo_upper`
  (`gridBelow α⋆ ≤ α⋆`). Route difference: the print uses `thm:lorate` (iii) for the constants; here the explicit `T_fit`, `T_bet` of (i).
* `nouniformrate` (`RouteS4`): the printed route with the certified `Wave31ta.impossible_two` (same randomisation model) and
  `Wave31tf.density2_unif`.
* `diffrac`: `P′(A) ≤ (1−α)⁻¹P(A)` (`setLIntegral_rnDeriv`), `P′(Aᶜ) ≤ (1−α)⁻¹Q(Aᶜ)`, `α = α₁ ∨ α₂`, both signs; no densities w.r.t.
  `P + Q` needed. `rhcrules_a/b`: `norm_num`, `⌊562.03⌋₊ = 562`. `kinkclass_sep`: the certified `Wave31tb.separated`;
  `kinkclass_kink`: the certified `Wave31ti.pathconvex_ii`.

## Junk-value audit
`mixAt` weights `ofReal(1−t)`, `ofReal t` only at `t ∈ (0,1)`; `√(n/(2a(1−a)))`, `√(2a(1−a)/N)` with `a ∈ (0,1)`; `hStar`, `c_lo/√N` with
`N ≥ 1` (assumed in S1 (c); forced in S3 (i) by `N ≥ c_lo²/(a₁−a₀)² > 0`); `C/√N` in S3 (ii) at `N ≥ N₁` with the witness `N₁ ≥ 1`, in (iii)
at `N ≥ 10`; `rootGrid` divides by `√N > 0`, `rootLevels = ⌈√N⌉₊ − 1 ≥ 3` (ℕ subtraction harmless); `ε/‖f‖` with `‖f‖ > 0` (proved);
`Dpop`, `dTrim` at levels in `[0,1)` over nonempty regions (the law itself is a trimming, so no `sInf ∅`); `tvDist` of probability
measures; `PolyMargin` at `γ = 1`; `Measure.real` of measurable sets; `trimSet` at `α < 1`; `2/c₀` with `c₀ > 0`; `u(α⋆−ε)/ε` only near
`0⁺`; `Nat.floor` of a positive real. No `Measure.map`, no `klDiv`, no `toReal ⊤` in the statements. Vacuity: every hypothesis set has
a witness (three-point laws with a rank-one or Gaussian kernel; `P = Q = P′` for S5), and for S3 (iii) a run satisfying
`IsWitnessRun ∧ IsDefaultRun` is evident (not checked in Lean) on a finite `𝒳` with the discrete σ-algebra, where every selection is
measurable, QP minimisers exist on the compact capped simplex, the (C) intervals are nonempty and `lamLo` (or `0` without a bet) meets
the fraction clauses; only the measurable selection for a general `𝒳` is assumed and uncertified (inherited from `lorate_O`).

## Defects / wording in the printed text
* S7 `prose:kinkclass` (AoS §5.3, `aos/sections/05_rates.tex:164`): "every pair … whose path leaves zero with a kink of slope at least
  `c₀`" (the wording frozen in NEW_STATEMENTS) is false if "path" is the population path `α ↦ D_α` of §2 (`02_regions.tex:112-113`): counterexample `𝒳 = {x₁,x₂,x₃}`,
  `H = ℝ`, `φ = 1, 0, −1`, `P = ½δ_{x₂} + ½δ_{x₁}`, `Q = ½δ_{x₂} + ½δ_{x₃}`: `α⋆ = ½`, `D_{½−ε} = 2ε/(½+ε)`, slope `4` at `α⋆`, but
  `PolyMargin` with `c₀ = 4` fails for every `ε ∈ (0,½]`. Fix: "whose rescaled path `(1−α)D_α(P,Q)` leaves zero with a kink of slope at
  least `c₀`" (equivalently, `D_α` has slope `≥ c₀/(1−α⋆)` at `α⋆`). The formal target S7 (b) already uses the rescaled path. Status: the AoS source of 2026-11-20 22:03 already reads "whose rescaled
  path `(1−α)D_α(P,Q)` leaves zero with slope at least `c₀`" (`05_rates.tex:164`); the auditor saw the old wording at 21:26.

## Not covered (declared)
The prose half of S4 (validity and consistency for every pair: certified earlier as `thm:consistency`, `cor:lower`,
`prop:loconsistency`; "a condition on the laws is needed for any rate": informal); the interpolation remark of S3 (certified as
`Wave31tg.interpolation` for finite sets); the `h = 0` comparison with `ex:separated` in S2; the prose sentence after S3 (the
conjunction of (i)–(iii)) and the two sentences after `cor:minimax` on "the same quantile of the error" and on `γ > 1` (not known
whether sharp); the data reading of S6 (sample fractions vs. population fractions; the data's counts 508 and 561 are `≤ 562`).

## Coverage note (COVERAGE.md rows)
Rows added to `docs/planning/inventory/COVERAGE.md` (section trimmed-mmd-jmlr, now 71/71) and to the extracted inventory, with the AoS
source locations: `prop:lower2pt`, `lem:twopointmargin`, `cor:minimax` ((iii) with the inherited run generalisations and the uncertified
existence of a run; the two sentences after it not covered), `prose:nouniformrate` (formal half only), `prose:diffrac`, `prose:rhcrules`
(arithmetic only), `prose:kinkclass` ("rescaled path (1−α)D_α"; the `D_α` reading refuted). Paper face `Papers/TrimmedMMDJMLR`
regenerated (347 targets); the labels carry "(AoS 2026-11-20)" since the face tooling has one page per paper id.

## AI audit notes (2026-11-20, method v1, PASS with notes; all applied above)
1. Defects: the population path is defined at `02_regions.tex:112-113`; the auditor saw `05_rates.tex:164` unfixed at 21:26 (fixed in
   the source of 22:03, recorded).
2. Printed locations recorded (Source); `lem:twopointmargin` is in the supplement (Lemma S4.7), not the main text; `prop:lower2pt` (c)
   is the prose after the proposition.
3. Junk-value audit: the run of S3 (iii) is evident on a finite `𝒳` with the discrete σ-algebra; only the general measurable selection
   is uncertified.
4. Covered: "the exact printed constant is stated (not weakened)" (the proof claim belongs to the gate line).
5. Covered: `0 < a₀` and `‖φ x − φ x′‖ ≤ Dφ ≤ 2κ` listed for `minimax_ii`, `minimax_iii`.
6. Encodings: no measurable singletons in S3 (i); `𝒫₂` narrower than "bounded densities" in S4 (Lean stronger); `‖f‖` the `H` norm.
7. COVERAGE rows: (iii) caveat, "rescaled path", formal half of S4, the two uncovered sentences after `cor:minimax`.
8. No question for the author beyond the printed-text fix at `05_rates.tex:164` (already made).
