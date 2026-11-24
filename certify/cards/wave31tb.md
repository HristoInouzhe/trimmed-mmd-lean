# Fidelity card — wave 31tb: trimmed-mmd (JMLR **v3**, `jmlr/v3/`), `ex:separated` (separated contamination satisfies the margin with `γ = 1`)

Lean: `StatFormal/Wave31tb/Statements.lean` (1 claim; frozen 2026-11-12 before any proof, commit `3078bf5`, sha256
`89b2bbab48c54666ddab1e45f9ddb34b0bf925acf15c284c4e380b5fdcbe9d4c`, locked with its 9 imports). Route `RouteSeparated` (untrusted); `Proofs.lean` imports it; the gate
checks `example : Claims.separated := separated` and `#print axioms` (`[propext, Classical.choice, Quot.sound]`). Paper id
`trimmed-mmd (jmlr)`; label `ex:separated (v3)`. Branch `tmmd-jmlr-v3sep`, based on `tmmd-jmlr-v2map` at `07dfad9` (wave 31ta and everything
it merged).
Critic (independent AI reviewer, before the freeze, 2026-11-12): ACCEPT-WITH-NOTE, every conjunct true, verdict READY TO FREEZE. It
back-translated the claim blind, typechecked a witness of all hypotheses in scratch Lean (`𝒳 = H = ℝ`, `φ` = clamp to `[−1,1]`, `κ = 1`,
`R = δ₀`, `P₀ = δ₁`, `Q₀ = δ₋₁`, the singletons, `α⋆ = 1/2`, `f = 1`), and checked the bound numerically (capped-simplex QP certified from below
by the Frank–Wolfe gap; `f` the minimum-norm interpolant, `‖f‖² = vᵀK⁻¹v`): equality on the whole `α` grid for the three-point Gaussian
example with `x₂` equidistant from `x₁` and `x₃` (`σ = 0.5, 1, 2`) and for rank-one kernels, never violated on 349 random Gaussian configurations (3,839 levels, minimum slack
`−8.3e−14`, float zero). Applied before hashing: the provenance lines of the header (the `02_regions.tex` hash and the `ass:margin` line
numbers are those of `jmlr/v2` at `d5cdddb`; the `jmlr/v3/sections/` copies are being edited).
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-12 — PASS with notes (the claim back-translated blind
and compared with `NEW_STATEMENTS.md` §`ex:separated` and the live v3 tex, faithful; a witness of every hypothesis typechecked; the card's
facts, proof-route summary, coverage note and inventory row checked; notes at the end of this card, applied).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md`, section `ex:separated` ("New statements of jmlr/v3 (frozen 2026-11-12)"; sha256
`6b4825f20f0253ee1dfff276ed801cfcbb906e5bafca87a16106b2ce3557c238`), read-only, read 2026-11-12. `jmlr/v3/` is not committed in trimmed-mmd
(master `d5cdddb`). The notation (`eq:trimset`, `eq:trimMMDpop`, `ass:regularity`, `eq:region`) is that of `jmlr/v2/sections/02_regions.tex`
(sha256 `1cf7137b…`), `ass:margin` that of `jmlr/v2/sections/03_analytic.tex:180-184` (sha256 `8e52b514…`), both restated in the header of
`NEW_STATEMENTS.md`. The live `jmlr/v3/sections/03_analytic.tex` prints the example (`\begin{example}[Separated contamination]`, at line 144,
`\label{ex:separated}` at 145 when audited, at 147 when the statement was frozen; the file is being edited and the lines move) with the same statement, without the parenthetical "(the polynomial case `γ = 1`)";
its proof is `jmlr/v3/appendix/B_analytic.tex`, subsection "Proof of Example `ex:separated`" (same route as the five-line route of
`NEW_STATEMENTS.md`).

## Target (1, in `certify/targets.toml`, module `StatFormal.Wave31tb.Proofs`)
| label | claim / theorem `StatFormal.Wave31tb.(Claims.)…` |
|---|---|
| `ex:separated (v3)` | `separated` |

Paper alias: `Papers.TrimmedMMDJMLR.ex_separated.separated`.

## Encodings (declared)
* (A1)–(A2) as in every reused trimmed-mmd wave: `𝓗` a real Hilbert space (`InnerProductSpace ℝ H`, `CompleteSpace H`), `φ : 𝒳 → 𝓗` strongly
  measurable with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ(x)‖² ≤ κ²`); `𝒳` any measurable space. Separability of `𝓗` (A2) is **not assumed** (the proof does
  not use it): generalisation. Under (A2) the canonical feature map of (A1) is strongly measurable (Pettis), which is why the repository
  encodes (A1)+(A2) this way.
* `f ∈ ℋ` acts as `x ↦ ⟪f, φ x⟫` (reproducing property) and `‖f‖_ℋ` is `‖f‖`. For the RKHS itself (`φ(x) = k(x,·)`) this is literal. For
  another feature space the claim is no stronger than printed: `k_φ(x,x′) = ⟪φx, φx′⟫` satisfies (A1)–(A2) (a strongly measurable `φ` has
  separable range); `v ↦ ⟪v, φ(·)⟫` is an isometry from the closed span `V` of `φ(𝒳)` onto the RKHS of `k_φ` taking `∫φ dP′` to `μ_{P′}`, so
  `D_α` is the same in both; and `x ↦ ⟪f, φx⟫` is the RKHS element of norm `‖P_V f‖ ≤ ‖f‖`, so the printed statement for `k_φ` gives the
  claim with `‖P_V f‖`, hence with `‖f‖`. The claim is for every `H`, so at `H` = the RKHS it is the printed statement.
* `R_α(P)` = `Wave8a.trimSet` (probability measures `P' ≪ P` with `dP'/dP ≤ (1−α)⁻¹` `P`-a.s., Mathlib `rnDeriv`), `D_α(P,Q)` = `Wave8a.dTrim`
  (real `sInf` of `‖∫φ dP' − ∫φ dQ'‖` over `R_α(P) × R_α(Q)`, `eq:trimMMDpop`). The bound is also stated for `TrimmedMMD.Unconditional.Dpop`, the
  distance between the trimmed regions `𝒞_α(P)`, `𝒞_α(Q)` (`eq:setdist`), equal to `dTrim` by the certified `Wave8a.georep_dist`
  (`prop:georep`); `Dpop` is the `D_α` of every certified estimator claim, including `ass:margin` below.
* `TV` = `Distances.tvDist` (`sup_A |P(A) − Q(A)|` over measurable `A`, the paper's `TV`).
* "concentrated on `S`": `R S_Rᶜ = 0`, `P₀ S_Pᶜ = 0`, `Q₀ S_Qᶜ = 0`; "pairwise disjoint measurable sets": `MeasurableSet` and three `Disjoint`.
* `P = (1−α⋆)R + α⋆P₀`: `P = ofReal(1−α⋆)•R + ofReal(α⋆)•P₀` (Mathlib measure sum, `ℝ≥0∞` scalars), likewise `Q`; `P`, `Q` are variables
  with these equations as hypotheses.
* "some `f ∈ ℋ` takes the value `0` on `S_R`, `1` on `S_P`, `−1` on `S_Q`, then [bound in `‖f‖`]": `∀ f`, `⟪f, φ x⟫ = 0, 1, −1` for every `x` in
  `S_R`, `S_P`, `S_Q`, then the conclusions (the bound names `f`, so "some `f`" is a universally quantified hypothesis).
* "Assumption 2 holds with `ω(ε) = c₀ε`, `c₀ = 2/‖f‖`": the frozen `Wave30tu.Margin φ P Q (fun ε => 2/‖f‖ * ε)` (`ass:margin` at
  `α⋆ = TV(P,Q)`: `ω` strictly increasing and continuous on `[0,α⋆]`, `ω(0) = 0`, `ω ≥ 0`, `D_{α⋆−ε} ≥ ω(ε)` for `ε ∈ [0,α⋆]`, with
  `D = Dpop`), the hypothesis of the certified `Wave30tu.rate`. "(the polynomial case `γ = 1`)": `0 < c₀` and `c₀ε^(1:ℝ) ≤ D_{α⋆−ε}` on
  `[0, TV(P,Q)]`, literally the hypothesis of the certified `Wave30tu.rate_poly` at `c₀ = 2/‖f‖`, `γ = 1`.
* `0 < ‖f‖` is an added conclusion (the proof's "`f` is not `0`"), so the divisions are genuine.
* `𝒳, H : Type` (universe 0), the repository convention.

## Covered — back-translation
**`separated`**. Let `𝒳` be a measurable space, `H` a real Hilbert space, `φ : 𝒳 → H` strongly measurable with `‖φ‖ ≤ κ`. Let `R, P₀, Q₀` be
probability measures and `S_R, S_P, S_Q` measurable, pairwise disjoint sets with `R(S_Rᶜ) = P₀(S_Pᶜ) = Q₀(S_Qᶜ) = 0`; let `0 < α⋆ < 1`,
`P = (1−α⋆)R + α⋆P₀`, `Q = (1−α⋆)R + α⋆Q₀`. Then (a) `TV(P,Q) = α⋆`; and (b) for every `f ∈ H` with `⟪f,φ(x)⟫` equal to `0` on `S_R`, `1` on
`S_P`, `−1` on `S_Q`: `‖f‖ > 0`; for every `α ∈ [0,α⋆]`, `2(α⋆−α)/((1−α)‖f‖)` is at most `D_α(P,Q)` (infimum of MMD over the `α`-trimmings)
and at most the distance between the trimmed regions, and `2(α⋆−α)/‖f‖ ≤ 2(α⋆−α)/((1−α)‖f‖)`; `ass:margin` holds with `ω(ε) = (2/‖f‖)ε`;
and `c₀ = 2/‖f‖ > 0` with `c₀ε¹ ≤ D_{α⋆−ε}(P,Q)` for `ε ∈ [0, TV(P,Q)]`.
**Deviations**: separability of `𝓗` dropped (generalisation); the bound also for `Dpop` and `0 < ‖f‖` (added conclusions, true); the
`γ = 1` parenthetical encoded as the `rate_poly` hypothesis. Nothing weaker than printed.

**Proof route** (untrusted, `RouteSeparated`): the printed one. TV: `P(A) − Q(A) = α⋆(P₀(A) − Q₀(A))` (`mix_real`), at most `α⋆`, and `= α⋆`
at `A = S_P` (`Q₀(S_P) ≤ Q₀(S_Qᶜ) = 0`) (`tv_mix`). Regions: for `z = E_P[gφ] ∈ 𝒞_α(P)`, `⟪f,z⟫ = E_P[g f] = (1−α⋆)E_R[g f] + α⋆E_{P₀}[g f]`
`= α⋆E_{P₀}g = 1 − (1−α⋆)E_R g ≥ 1 − (1−α⋆)/(1−α)` (`f = 0` `R`-a.e., `f = 1` `P₀`-a.e., `E_P g = 1`; `inner_mix`, `region_inner`), and
`⟪f,w⟫ ≤ −(1 − (1−α⋆)/(1−α))` for `w ∈ 𝒞_α(Q)`; Cauchy–Schwarz and `le_csInf` over the nonempty set of distances (`g ≡ 1`) (`dpop_bound`).
`dTrim` by the certified `Wave8a.georep_dist`. Margin and `γ = 1`: substitute `α = α⋆ − ε`, `1 − α ≤ 1`, `ε^(1:ℝ) = ε`. The proof uses the
disjointness only through `S_P ∩ S_Q = ∅` (for TV) and the hypotheses on `f` (which already force `S_R`, `S_P`, `S_Q` to be disjoint).

## Junk-value audit
* Division: `‖f‖ > 0` is proved (a conclusion): `P₀(S_P) = 1` makes `S_P` nonempty and `⟪f,φ x⟫ = 1` there; `1 − α ≥ 1 − α⋆ > 0`.
* `sInf` in `dTrim` and in `setDist` (`Dpop`): the sets are nonempty (`P ∈ R_α(P)`; `g ≡ 1` gives `μ_P ∈ 𝒞_α(P)`, since `1 ≤ (1−α)⁻¹`) and bounded
  below by `0`, so the infima are genuine; a junk value `0` would make the lower bound false, not vacuous.
* Bochner integrals: `φ` bounded and strongly measurable, `g` bounded measurable, finite measures: every integral is of an integrable function;
  `CompleteSpace H` is assumed (without it the Bochner integral is `0`).
* `ENNReal.ofReal` of `1 − α⋆`, `α⋆`, `(1−α)⁻¹`: all positive. `rnDeriv`: `P` finite, `P' ≪ P`. `ε ^ (1 : ℝ)`: `Real.rpow` at `ε ≥ 0`.
* `tvDist` of probability measures (`P`, `Q` are probability measures, `mix_isProb`): genuine supremum.
* No `Measure.map`, `deriv`, `toReal ⊤`, ℕ subtraction.
* Vacuity: the hypotheses are jointly satisfiable, including the `f`-clauses (the critic's typechecked witness above, retypechecked by the
  auditor; there `D_α = (1−2α)/(1−α)`, exactly the bound; the three-point Gaussian example with `x₂` equidistant from `x₁` and `x₃`
  (`k(x₁,x₂) = k(x₃,x₂)`) and the interpolant `f = (φ(x₁) − φ(x₃))/(1 − k(x₁,x₃))`).

## Not covered (declared)
The paragraph after the example (prose, not a formal target): existence of such `f` when the three sets are finite and `k` is strictly
positive definite on their union (interpolation), the three-point instance, and the Matérn-kernel case (Sobolev RKHS, Wendland 2005 Ch. 10).

## Doubts about the printed statement
None. The statement is true as printed, and the first bound is attained (the symmetric three-point Gaussian example, `k(x₁,x₂) = k(x₂,x₃)`,
and rank-one kernels give equality on the whole `α` grid; for an asymmetric placement it is strict, e.g. `x = 0, 1, 3`, `σ = 1`, minimum-norm
interpolant: `D₀ ≈ 0.703 > 0.647`), so it cannot be strengthened in general. The frozen docstring's "attained … for the three-point laws …
with the Gaussian kernel and the interpolating `f`" holds for the symmetric placement (docstring only, not part of the claim; not edited,
frozen). Cosmetic: the frozen `NEW_STATEMENTS.md` has the parenthetical "(the
polynomial case `γ = 1`)", the live v3 tex does not; both readings are certified.

## Certified results reused (not re-proved)
Wave 8a `georep_dist` (`dTrim = Dpop`). Library: `Distances.tvDist_le_of_forall`, `abs_measureReal_sub_le_tvDist`.

## Coverage note (COVERAGE.md row, v3)
* `ex:separated`: "certified as frozen (v3, jmlr/v3/NEW_STATEMENTS.md): TV(P,Q) = alpha*; for f with values 0, 1, -1 on S_R, S_P, S_Q,
  D_alpha >= 2(alpha* - alpha)/((1 - alpha) norm f) >= 2(alpha* - alpha)/norm f on [0, alpha*] for the infimum over trimmings and the regions'
  distance, ass:margin with omega(eps) = (2/norm f) eps and the polynomial case gamma = 1 (Wave31tb); the existence of f (finite supports,
  Matern kernels) is prose, not covered".

## AI audit notes (2026-11-12, PASS with notes; applied)
1. Attainment and the closed-form interpolant `f = (φ(x₁) − φ(x₃))/(1 − k(x₁,x₃))` hold for the symmetric three-point placement
   (`k(x₁,x₂) = k(x₃,x₂)`); for an asymmetric one the bound is strict (`x = 0, 1, 3`, `σ = 1`: `D₀ ≈ 0.703 > 0.647`) — "symmetric" added to the
   critic summary, the vacuity bullet and "Doubts"; the frozen docstring's remark is qualified there (not edited).
2. The RKHS sentence of the encodings made precise ((A1)–(A2) for `k_φ`, the isometry `V → ℋ_{k_φ}`, `D_α` unchanged, `‖P_V f‖ ≤ ‖f‖`).
3. Line numbers: the frozen header gives the label at line 147 (at the freeze), the card, coverage row and inventory row give 144 (the
   `\begin{example}` line; `\label` at 145 when audited) — said in the Source section; the live file keeps moving.
4. Recording lines written.
