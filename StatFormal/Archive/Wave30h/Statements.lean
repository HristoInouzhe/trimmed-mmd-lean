import StatFormal.Archive.Wave9b.Statements
import StatFormal.Archive.Wave24d.Statements
import StatFormal.Archive.Wave24e.Statements
import StatFormal.Archive.Wave24f.Statements
import StatFormal.Archive.Wave25a.Statements
import Mathlib.Data.Fin.Tuple.Sort

/-!
# FROZEN STATEMENTS — wave 30h: SB journal version (`data-fairness-repair (journal)`), the standardisation-field
# family: `def:standardisable` (MODIFIED), `ass:marg` (NEW), `lem:transfer`, `lem:quantiles`, `lem:reldev`,
# `lem:scores`, `lem:compose` (NEW), `thm:field` against the new definition, `cor:field-ell`, `cor:field-cop`,
# `cor:field-npn`, `cor:field-local` (MODIFIED), `prop:copulatransport` (NEW)

Sources (journal version checked out 2026-10-20, `data-fairness-repair-journal/journal/`; labels are stable between
the long paper and the journal version):
* `def:standardisable` (`main/m_field.tex:22-40`, old statement `formalization_delta.tex:168-182`): (iii) now reads
  "`S_μ⁻¹` extends to an `L`-Lipschitz map on all of `ℝ^d`, and the estimated inverse can be written
  `Ŝ_μ⁻¹ − S_μ⁻¹ = h_n + k_n` with `sup_z ‖h_n(z)‖ = O_P(r_n)`, `Lip(k_n) = O_P(1)` and `‖k_n‖_{L²(γ)} = O_P(r_n)`";
  the inverse error in (ii) is dropped.
* `thm:field` (`m_field.tex:49-66`, proof `supp/s_proofs_field.tex:184-225`, via `lem:transfer`).
* `ass:marg` (`m_field.tex:103-107`): every marginal is supported on a compact interval with a density in `[1/L, L]`.
* `lem:transfer`, `lem:quantiles`, `lem:reldev`, `lem:scores`, `lem:compose` (`s_proofs_field.tex:44-182`).
* `cor:field-ell` (`s_proofs_field.tex:237-266`), `cor:field-cop` (`m_field.tex:118-140`, proof
  `s_proofs_field.tex:268-285`), `cor:field-npn` (`m_field.tex:147-170`, proof `s_proofs_field.tex:287-336`),
  `cor:field-local` (`m_field.tex:226-236`, proof `s_proofs_field.tex:444-467`), `prop:copulatransport`
  (`m_field.tex:254-286`, with `eq:copulatransport` `:248-251`; proof `s_proofs_field.tex:469-488`).
* `cor:field-vine` (`s_proofs_field.tex:341-442`, summary `cor:field-vine-main` `m_field.tex:178-192`).
Imports the frozen statements of Wave 9b (`Standardises`, `BigOP`, `LipschitzWhp`; `Claims.field_rate` for the route
check), Wave 24d (`meanVec`, `covMat`, `IsSpherical`, `mvec` through OTFD Wave 8c), Wave 24e (`copStd`, `copInv`),
Wave 24f (`marg`, `stdPhi`, `stdPhiInv`, `zScore`, `InNPN`, `invSqrt`, `npnStd`) and Wave 25a (`meanV`, `covM`, `corrMap`), not copied; Mathlib (`Tuple.sort`,
`multivariateGaussian`, `cdf`), Tau Ceti (`wassersteinEDist`, `quantile`) otherwise.
New definitions: `supNorm`, `LipBoundedP`, `InvStdzJ` (the new (iii)), `AssMarg`, `empCdf`, `ordStat`, `ramp`,
`clamp01`, `interpCdf`, `interpQuant`, `clipN`, `chain`, `copStdHat`, `copInvHat`, `sMean`, `sCov`, `ellStd`,
`ellInv`, `ellStdHat`, `ellInvHat`, `npnInv`, `zScoreHat`, `npnStdHat`, `npnInvHat`, `copTrans`, `corrMat`.

Covered:
* `def:standardisable`: `stdz_old_to_new` (the author's decision: a law standardisable in the OLD sense — `S_ν⁻¹`
  `L`-Lipschitz on a set of full `γ`-measure, `‖Ŝ_ν⁻¹ − S_ν⁻¹‖_{L²(γ)} = O_P(r_n)`, `Ŝ_ν⁻¹` `L`-Lipschitz w.p. → 1 —
  satisfies the NEW (iii), with `h_n = 0`).
* `lem:transfer`: `transfer_lip`. `lem:compose`: `compose_perturbed`.
* `lem:quantiles`: `quantiles_cdf` (`sup|F̃_n − F| ≤ ε_n + 1/n`), `quantiles_quant`
  (`sup_{u∈(0,1)} |Q̃_n(u) − F⁻¹(u)| ≤ L(ε_n + 2/n)` under `ass:marg`), `quantiles_dkw` (`ε_n = O_P(n^{-1/2})`).
* `lem:reldev`: `reldev_bound`. `lem:scores`: `scores_mse`.
* `thm:field` (journal): `fieldJ_bound` (the deterministic chain of the proof: `‖T̂_s − T_s‖_{L²(R_s)}`,
  `W₂((T̂_s)_#R_s, ν)` and the parity gap), `fieldJ_rate` (the parity gap is `O_P(r_n)`). Exactness is unchanged
  (frozen Wave 9b `field_exact`, (i) is unchanged).
* `cor:field-ell`: `fieldell_fwd` ((ii)), `fieldell_inv` ((iii), `h_n = 0`), `fieldell_rate` (parity gap
  `O_P(n^{-1/2})`); (i) is the frozen Wave 24d `field_ell`.
* `cor:field-cop`: `fieldcop_fwd` ((ii), interpolated empirical cdfs, rate `√(d/n)`), `fieldcop_inv` ((iii) under
  `ass:marg`: the extension of `S_ν⁻¹` is `L`-Lipschitz, `Ŝ_ν⁻¹ − S_ν⁻¹ = h_n`, `k_n = 0`), `fieldcop_rate` (parity
  gap `O_P(√(d/n))`). (i) is the frozen Wave 24e `field_cop_standardises`; the exact forward order `d/(6n)` (for the
  STEP empirical cdfs, as the journal now says) is the frozen Wave 27d `field_cop_rate_fwd`.
* `cor:field-npn`: `fieldnpn_fwd` ((ii) at rate `n^{-1/2} log n`), `fieldnpn_inv` ((iii), at rate `n^{-1/2}`),
  `fieldnpn_rate` (parity gap `O_P(n^{-1/2} log n)`); (i) is the frozen Wave 24f `field_npn_std`.
* `cor:field-local` (journal): `fieldlocal_bound` (deterministic), `fieldlocal_rate` (`O_P(r_n) + O_P(δ_n)`). The
  DEFECTS #82 instance is checked at route level (`RouteLocalCx.fieldlocal_counterexample_delta`: there the journal
  misspecification `δ_n` IS the population parity gap, `≥ δ^{3/4}/100`, so the corollary no longer claims `O(δ)`).
* `prop:copulatransport`: `coptransport_marginals` ((i)), `coptransport_copula` ((ii), first part),
  `coptransport_exact_iff` ((ii), second part), `coptransport_corrected` ((iii), corrected map: exact for every affine
  map, in particular at every `ε > 0`), `coptransport_uncorrected` ((iii), uncorrected: the copula of `(T_s)_#R_s` is
  Gaussian with the correlation matrix of `P_s`, and its marginals are `G_i`).

Not covered (declared):
* `cor:field-vine` (regular vines, simplified pair-copula constructions and Rosenblatt transforms are not available;
  only its ingredients `lem:compose`, `lem:quantiles` are covered).
* `prop:copulatransport`(iii): "the parity defect … is of order `ε`" (`eq:Ps` itself is certified — SB
  `paritydefect_expansion`, Wave 30g `defect_bound`, `defect_cov` — but the step from `P₀ − P₁ = O(ε)` to a defect of
  the repaired laws is not formalised: smoothness of `corrMat` at `B`, a Gaussian `W₂` bound and, on the feature scale,
  Lipschitz `G_i⁻¹`; only the Gaussian-copula identification is stated).
* `cor:field-ell` "for Gaussian `Y` this recovers `prop:corrected`" (informal; cf. Wave 25a `corrected_gaussian`);
  uniformity of the constants in `λ` ("for fixed `d` and `λ`"); that the entropic barycentric map between centred
  Gaussians is affine/linear (cited; the claims quantify over all such maps).
* `cor:field-npn` Step 3 (the cited rank-correlation results and the Brenier rotation): the correlation estimators
  enter through the hypothesis `‖R̂ − R‖_op = O_P(n^{-1/2})`, as printed.
* `thm:field`: "If `r_n = n^{-1/2}`, all three properties of Table `tab:trilemma` hold" (informal table).
* `cor:field-local`: "In particular, if `δ_n = O(n^{-1/2})` the model error is of the order of the estimation
  error" (immediate from the `O_P(r_n + δ_n)` form).

Encodings (to be checked by the critic):
* `ℝ^d = EuclideanSpace ℝ (Fin d)` (`Euc d`); `W₂ = wassersteinEDist 2`, `L²` norms `eLpNorm · 2` (`ℝ≥0∞`); `‖h‖_∞` is
  `supNorm h = ⨆ z, ‖h z‖ₑ` (`ℝ≥0∞`); `O_P(r_n)` is the frozen Wave 9b `BigOP` (measurable-event convention, eventual
  in `n`); `Lip(k_n) = O_P(1)` is `LipBoundedP` (for every `η > 0`, `K`, `N` and measurable events of probability
  `≥ 1 − η` on which `k_n` is `K`-Lipschitz); "with probability tending to one" is the frozen `LipschitzWhp`.
* The new (iii) (`InvStdzJ`): an `L`-Lipschitz `S'` on `ℝ^d` equal to `S_ν⁻¹` `γ`-a.e. ("extends": `S_ν` is
  invertible `γ`-a.e., so `S_ν⁻¹` is determined `γ`-a.e.), and maps `h_n`, `k_n` with `Ŝ_ν⁻¹ − S' = h_n + k_n` on all
  of `ℝ^d`; as in Wave 9b, (iii) is only required of the target `ν` (the proof uses no other inverse), and (i) is the
  frozen `Standardises`. Estimators are maps indexed by `(n, ω)`, measurable in the space variable; in the corollaries
  they are built from the first `n` terms of i.i.d. sequences (`iIndepFun`, common law), on one probability space for
  all groups (no independence across groups is needed).
* `ass:marg` (`AssMarg L a b F`): `a < b` and `L⁻¹·Leb|_{[a,b]} ≤ F ≤ L·Leb|_{[a,b]}` (equivalent to a density with
  values in `[1/L, L]` on `[a, b]` and `F([a,b]ᶜ) = 0`).
* Empirical objects: `empCdf x t = #{i : x_i ≤ t}/n`; the order statistics `ordStat x j = X_{(j+1)}` through
  `Tuple.sort` (`j < n`; the value `0` for `j ≥ n` is never used); `interpCdf` (`F̃_n`) is `0` below `X_{(1)}`,
  `1` from `X_{(n)}` on, and linear between consecutive order statistics through the values of `F_n` at them (written as
  `n⁻¹(1{t ≥ X_{(1)}} + Σ_{j<n−1} ramp(X_{(j+1)}, X_{(j+2)}, t))`, a tie giving a jump); `interpQuant` (`Q̃_n`) is the
  linear interpolation of the points `((k − ½)/n, X_{(k)})`, constant outside `[1/(2n), 1 − 1/(2n)]` (written as
  `X_{(1)} + Σ_{j<n−1} (X_{(j+2)} − X_{(j+1)}) clamp₀₁(nu − (j + ½))`); `clipN n u = min{max{u, 1/(2n)}, 1 − 1/(2n)}`;
  `ε_n = ⨆_t |F_n(t) − F(t)|` in `ℝ≥0∞` (`quantiles_dkw`), or any `ε` bounding all `|F_n(t) − F(t)|` (deterministic
  claims; the least such `ε` is `ε_n`). The uniform law on `[0,1]` is `volume.restrict (Icc 0 1)`.
* `lem:quantiles`: the bound on `Q̃_n` is stated for `u ∈ (0,1)` against Tau Ceti's quantile (whose values at `0`
  are junk; `F⁻¹` extends continuously to `[0,1]`, so the supremum over `[0,1]` is the same); the sample is assumed in
  `[a, b]` (an a.s. event). `lem:scores`: `F` atomless only; the conditional expectation given the sample is the
  integral `∫ (…)² dF` at the fixed sample.
* `lem:compose`: one metric space `X` for all intermediate values (subsets of Euclidean spaces embed isometrically in
  one `ℝ^N`, maps being relevant only on the sets `A_k`); `chain f k = f_{k−1} ∘ ⋯ ∘ f_0` (0-indexed: `f k` is the
  paper's `f_{k+1}`, `A k` its `A_{k+1}`).
* `cor:field-ell`: `𝔐 = {(z ↦ Az + b)_#γ : A invertible}` with `γ` the generator law (spherical where the
  standardisation is used; mean `0`, covariance `I`, `∫‖y‖⁴ dγ < ∞`); `S_μ(x) = Cov(μ)^{-1/2}(x − Eμ)` with the frozen
  `invSqrt`, `S_μ⁻¹(z) = Cov(μ)^{1/2}z + Eμ` (`CFC.sqrt`); the sample mean and the `1/n` sample covariance;
  `Σ̂^{-1/2} = invSqrt Σ̂` (junk on the event `Σ̂` singular, whose probability tends to `0`).
* `cor:field-cop`: `S_μ = copStd μ` (frozen), `S_ν⁻¹ = copInv ν` (frozen), `γ = (S_ν)_#ν`; `Ŝ_μ = (F̃_{n,i})_i`,
  `Ŝ_ν⁻¹ = (Q̃_{n,i})_i` (`copStdHat`, `copInvHat`); `ass:marg` for the target marginals (the forward step uses no
  hypothesis on `μ`; the printed continuity is unused); rate `√(d/n)` (fixed `d`).
* `cor:field-npn`: the class through the frozen `InNPN`; `S_μ = npnStd μ R` (frozen); `S_μ⁻¹ = npnInv`; the clipped
  normal scores `zScoreHat`, `Ŝ_μ = R̂^{-1/2} Ẑ` (`npnStdHat`), `Ŝ_ν⁻¹ = (Q̃_{n,i}(Φ([R̂^{1/2}z]_i)))_i` (`npnInvHat`);
  the correlation estimators `R̂` are arbitrary symmetric random matrices with `‖R̂ − R‖_op = O_P(n^{-1/2})`
  (operator norm `Matrix.Norms.L2Operator`), `λ_min(R) ≥ λ` as `λ • 1 ≤ R` (Loewner order).
* `cor:field-local`: the approximating members enter only through their (measurable) forward maps `S̃_s = S_{μ̃_s}`
  (membership `μ̃_s ∈ 𝔐` is not used: a generalisation); laws and forward maps may depend on `n`; `δ_n ≥ 0`.
* `prop:copulatransport`: `W_s = zScore R_s` (frozen, Tau Ceti quantile of `N(0,1)`), `V_s = M_s(W_s)`,
  `H_{s,i}` the marginal cdfs of `(M_s ∘ W_s)_#R_s`, `copTrans`; the copula of a law `μ` is `(copStd μ)_#μ` (frozen
  Wave 24e); "exact repair" in (ii) is parity `(T₀)_#R₀ = (T₁)_#R₁`; (iii): Gaussian copula `InNPN R_s A_s`,
  `InNPN ν B` with `A_s`, `B` positive definite and `B` a correlation matrix (unit diagonal); the corrected map is
  the frozen `corrMap` of ANY affine map `x ↦ Mx + c` from `N(0, A_s)` (the barycentric projection of the entropic plan
  between centred Gaussians is affine for every `ε > 0`), with the frozen square-root hypotheses of
  `corrected_gaussian`; the uncorrected map is ANY linear map `G` (`P_s = G A_s Gᵀ ≻ 0`; the barycentric projection
  `CᵀA⁻¹` gives `P_s = CᵀA⁻¹C`, `eq:Ps`), `corrMat P = diag(P)^{-1/2} P diag(P)^{-1/2}`.

Junk audit: every `Measure.map` is of a measurable map (hypothesised, or proved for the estimators); `L²`, `W₂`,
`‖·‖_∞` live in `ℝ≥0∞`; Tau Ceti quantiles are evaluated at levels in `(0,1)` (Gaussian `Φ`, clipped scores, `H(V)`
a.s.), except `copInv`, `npnInv` at levels `0`/`1` on `γ`-null sets; `x/0` only at `n = 0` (rates, `empCdf`), which
`BigOP` never sees (eventual in `n`), and in `ramp` only under `a < b`; `√` of nonnegative quantities; `invSqrt` of a
singular estimate (vanishing-probability event); `corrMat` divides by `√(P_ii P_jj) > 0` for `P ≻ 0`.

Proof notes (author of the draft, 2026-10-20): all claims are proved in `Wave30h/Route{OP,Transfer,FieldJ,LocalCx,
Quantiles,DKW,RelDev,Scores,FieldEll,FieldEllRate,FieldCop,CopTransport,FieldNPN}.lean` (`#print axioms`: propext,
Classical.choice, Quot.sound), on the new libraries `Foundations/NormalScores/{Gauss,Atomless,Bound}`,
`Foundations/MatrixSqrtPerturb/{Basic,BigOPCalc,SampleMoments,RootRates}` and the certified `Foundations/DKW/Massart`,
`Foundations/Bernstein/Bernstein`, Wave 9b `field_exact_one`/`w2_map_map_le`, Wave 24d `field_ell`, Wave 24e
`field_cop_standardises`, Wave 24f `field_npn_std`/`mvG_map`, Wave 24g `field_local_gap_lower`/`muB_map_SbE`, Wave 25a
`corrected_gaussian`.
* `transfer_lip`: Minkowski on every coupling, then the infimum (no optimal coupling; `K = 0` via the product coupling).
* `fieldJ_*`, `fieldlocal_*`: one core estimate (`core_one`) for `‖Ŝ_ν⁻¹ ∘ Ŝ − S' ∘ S̃‖_{L²(R)}` with `S̃` the true or an
  approximating standardiser; `fieldJ_rate` is `fieldlocal_rate` at `δ = 0`. Route check `fieldJ_route_old`: the frozen
  Wave 9b `field_rate` conclusion follows from `fieldJ_rate` + `stdz_old_to_new` once the OLD clause "`S_ν⁻¹`
  `L`-Lipschitz on `supp γ`" is added. NB: neither is an instance of the other (the frozen `field_rate` dropped that clause;
  the journal one drops the Lipschitz property of `Ŝ_ν⁻¹`), but when liminf r_n = 0 the frozen hypotheses imply the
  old clause a.e., so the frozen claim is subsumed (critic 1);
  the journal statement generalises the long paper's printed theorem, as the author's decision says.
* `stdz_old_to_new`: coordinatewise McShane extension (`√d·L`; Kirszbraun would keep `L`), `h_n = 0`,
  `k_n = Ŝ_ν⁻¹ − S'`, `Lip(k_n) ≤ L + √d L` on the events of `LipschitzWhp`.
* `quantiles_quant`: Abel summation writes `Q̃_n(u) − F⁻¹(u)` as a convex combination of `X_{(j+1)} − F⁻¹(u)` over
  `|u − (j+1)/n| < 3/(2n)`; `|F(X_{(j+1)}) − (j+1)/n| ≤ ε` uses only the continuity of `F` (no "no ties").
* `scores_mse`: `φ(Φ⁻¹u) ≥ min(u,1−u)/√(2π)` replaces the paper's Mills-ratio fact (derivative free); bulk/tail split at
  `κ_n = 64 log n/n` as printed. `reldev_bound`: the certified one-sided Bernstein inequality at `δ = n^{-2}`.
* `fieldcop_inv`: `S'(u) = (g_i(clamp₀₁ u_i))_i`, `g_i` the McShane extension of `F_i^{-1}` from `(0,1)`; the clamp is
  needed for the choice `k_n = 0` (with a bare McShane extension `‖Ŝ⁻¹ − S'‖_∞ = ∞`, and the difference would go into
  `k_n`);
  `Q̃_n = Q̃_n ∘ clamp₀₁`, closure argument from `(0,1)` to `[0,1]`.
* No tautology: no conclusion is among the hypotheses. Unused hypotheses (generalisations): `fieldcop_fwd` does not
  use the continuity of the marginals (`F_n ≤ F̃_n ≤ F_n + 1/n` holds for every law); `coptransport_corrected` does
  not use `A ≻ 0` (implied for `d ≥ 1` by the `Ph` hypothesis); `coptransport_marginals` needs no continuity of
  `F_{s,i}`, `G_i`; `fieldnpn_inv` does not use `InNPN ν B` (`S'` equals `npnInv ν B` everywhere);
  `fieldell_fwd`/`fieldell_inv` do not need sphericity (only `fieldell_rate`, through (i)).

Manuscript notes: (1) `def:standardisable`: (iii) is used only for the target `ν`; "every family standardisable in the
old sense is standardisable in the new one" needs a Lipschitz EXTENSION of `S_ν⁻¹` from `supp γ` (Kirszbraun) — worth
one clause in the decision text/proof. (2) `lem:quantiles`: the "almost surely there are no ties" step is unnecessary
(`|F(X_{(k)}) − k/n| ≤ ε_n` holds with ties by continuity of `F`); the bound is in fact `L(ε_n + 3/(2n))`; at `u = 0`
the statement needs the convention `F⁻¹(0) = inf supp F` (the generalised inverse is `−∞`/junk there). (3)
`cor:field-cop`: the remark after the corollary gives the exact forward order `d/(6n)` for the STEP empirical cdfs (the
certified Wave 27d `field_cop_rate_fwd`), while the corollary uses the INTERPOLATED cdfs; since `0 ≤ F̃_n − F_n ≤ 1/n`
the two forward errors differ by at most `√d/n` in `L²`, so the exact order transfers — say so. (ii) needs no
`ass:marg`. (4) `cor:field-cop` proof: the constant extension of `F⁻¹_{μ,i}` outside `[0,1]` is convenient, not
essential: it gives `k_n = 0`; with any other `L`-Lipschitz extension `S''`, `k_n = S_const − S''` is `2L`-Lipschitz and
vanishes on `[0,1]^d ⊇ supp γ`, so (iii) is independent of the extension (critic 2). DEFECTS #86: the step quantile is
replaced by the interpolated one; Gaussian targets are excluded by `ass:marg` (compact support), not handled. (5) `cor:field-npn`: (iii) holds at rate `n^{-1/2}` (only (ii) carries the `log n`). (6)
`cor:field-local` (journal): correct; membership `μ̃_s ∈ 𝔐` is not used, and the laws may depend on `n`. The DEFECTS #82
counterexample is genuinely avoided: there the journal `δ_n` equals the population parity gap itself (`≥ δ^{3/4}/100`),
so the corollary no longer claims a gap `O(δ)`; the price is that `δ_n` is no longer a distance between the data law and
the model (cf. `rem:local-scope`). (7) `prop:copulatransport`(iii): "of order `ε`" names no metric; on the copula scale it follows from `eq:Ps`
(certified, `paritydefect_expansion`), on the feature scale it needs regularity of `G_i⁻¹`; the proof's "the correlation
matrices differ at order ε unless A₀ = A₁" is not justified (normalising to correlations can cancel part of the
first-order term; numerically it survives in d = 2). (8) `lem:scores` proof (`s_proofs_field.tex:149-150`): the
containment `{ψ ≥ κ_n} ⊂ [κ_n, 1−κ_n]` follows from `ψ ≤ min(u,1−u)`, not from the cited lower bound. (9)
`m_field.tex:121` Lean comment points to Wave 27d (step quantiles); for the interpolated estimators the upper bound is
Wave 30h `fieldcop_rate`. Critics (2026-10-20, two halves): 26 targets accepted (several with notes);
`fieldlocal_counterexample_delta` moved to route `RouteLocalCx`. No statement found false.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti Matrix
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Wave9b (Standardises BigOP LipschitzWhp)
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave8c (mvec)
open StatFormal.Wave24d (meanVec covMat IsSpherical)
open StatFormal.Wave24e (copStd copInv)
open StatFormal.Wave24f (marg stdPhi stdPhiInv zScore InNPN invSqrt npnStd)
open StatFormal.Wave25a (meanV covM corrMap)

/-! ### `def:standardisable` (iii), journal form -/

section Stdz
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- `‖h‖_∞ = sup_z ‖h(z)‖`, in `[0, ∞]`. -/
def supNorm {E F : Type*} [ENorm F] (h : E → F) : ℝ≥0∞ := ⨆ z, ‖h z‖ₑ

/-- `Lip(k_n) = O_P(1)`: for every `η > 0` there are `K` and `N` such that for every `n ≥ N` some measurable event of
probability `≥ 1 − η` carries `Lip(k_n) ≤ K`. -/
def LipBoundedP (P : Measure Ω) (k : ℕ → Ω → Euc d → Euc d) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ≥0, ∃ N : ℕ, ∀ n ≥ N, ∃ A : Set Ω, MeasurableSet A ∧
    ENNReal.ofReal (1 - η) ≤ P A ∧ ∀ ω ∈ A, LipschitzWith K (k n ω)

/-- `def:standardisable`(iii), journal form, for the target: `S_ν⁻¹` extends to an `L`-Lipschitz map `S'` on all of
`ℝ^d` (`S' = S_ν⁻¹` `γ`-a.e.), and `Ŝ_ν⁻¹ − S' = h_n + k_n` with `‖h_n‖_∞ = O_P(r_n)`, `Lip(k_n) = O_P(1)` and
`‖k_n‖_{L²(γ)} = O_P(r_n)`. -/
def InvStdzJ (P : Measure Ω) (r : ℕ → ℝ) (L : ℝ≥0) (γ : Measure (Euc d)) (Sinv : Euc d → Euc d)
    (Sinvhat : ℕ → Ω → Euc d → Euc d) : Prop :=
  ∃ (S' : Euc d → Euc d) (h k : ℕ → Ω → Euc d → Euc d), LipschitzWith L S' ∧ S' =ᵐ[γ] Sinv ∧
    (∀ n ω z, Sinvhat n ω z - S' z = h n ω z + k n ω z) ∧
    BigOP P r (fun n ω => supNorm (h n ω)) ∧ LipBoundedP P k ∧
    BigOP P r (fun n ω => eLpNorm (k n ω) 2 γ)

/-- `ass:marg` for one marginal law `F`: carried by the compact interval `[a, b]`, on which it has a density between
`1/L` and `L` (as `L⁻¹·Leb|_{[a,b]} ≤ F ≤ L·Leb|_{[a,b]}`). -/
def AssMarg (L : ℝ≥0) (a b : ℝ) (F : Measure ℝ) : Prop :=
  0 < L ∧ a < b ∧ ENNReal.ofReal (L : ℝ)⁻¹ • volume.restrict (Icc a b) ≤ F ∧
    F ≤ (L : ℝ≥0∞) • volume.restrict (Icc a b)

end Stdz

/-! ### Empirical distribution and quantile functions -/

section Empirical

/-- The empirical distribution function `F_n(t) = #{i : x_i ≤ t}/n`. -/
def empCdf {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ := ((Finset.univ.filter fun i => x i ≤ t).card : ℝ) / n

/-- The order statistic `X_{(j+1)}` (`j < n`), through Mathlib's `Tuple.sort`; `0` for `j ≥ n` (never used). -/
def ordStat {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then x (Tuple.sort x ⟨j, h⟩) else 0

/-- Clamp to `[0, 1]`. -/
def clamp01 (u : ℝ) : ℝ := max 0 (min u 1)

/-- The ramp from `a` to `b` (`a ≤ b`): `0` up to `a`, linear on `[a, b]`, `1` from `b` on; a step at `b` if `a = b`. -/
def ramp (a b t : ℝ) : ℝ := if a < b then clamp01 ((t - a) / (b - a)) else if b ≤ t then 1 else 0

/-- `F̃_n`: the linear interpolation of `F_n` between consecutive order statistics (`0` below `X_{(1)}`, `1` from
`X_{(n)}` on, through the values `F_n(X_{(k)}) = k/n`). -/
def interpCdf {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((if ordStat x 0 ≤ t then (1 : ℝ) else 0) +
    ∑ j ∈ Finset.range (n - 1), ramp (ordStat x j) (ordStat x (j + 1)) t) / n

/-- `Q̃_n`: the linear interpolation of the points `((k − ½)/n, X_{(k)})`, `k = 1, …, n`, extended by constants
outside `[1/(2n), 1 − 1/(2n)]`. -/
def interpQuant {n : ℕ} (x : Fin n → ℝ) (u : ℝ) : ℝ :=
  ordStat x 0 + ∑ j ∈ Finset.range (n - 1),
    (ordStat x (j + 1) - ordStat x j) * clamp01 (n * u - (j + 1 / 2))

/-- The clipping `c_n(u) = min{max{u, 1/(2n)}, 1 − 1/(2n)}` of `lem:scores`. -/
def clipN (n : ℕ) (u : ℝ) : ℝ := min (max u (1 / (2 * n))) (1 - 1 / (2 * n))

end Empirical

/-! ### `lem:compose` -/

/-- `chain f k = f_{k−1} ∘ ⋯ ∘ f_0` (`chain f 0 = id`). -/
def chain {X : Type*} (f : ℕ → X → X) : ℕ → X → X
  | 0 => id
  | k + 1 => f k ∘ chain f k

/-! ### Estimators of the corollaries -/

section Estimators
variable {d : ℕ}
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- `cor:field-cop`: `Ŝ_μ(x) = (F̃_{n,i}(x_i))_i`, the interpolated empirical marginal cdfs of the sample. -/
def copStdHat {n : ℕ} (X : Fin n → Euc d) (x : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => interpCdf (fun j => X j i) (x i)

/-- `cor:field-cop`: `Ŝ_ν⁻¹(u) = (Q̃_{n,i}(u_i))_i`, the interpolated empirical marginal quantiles of the sample. -/
def copInvHat {n : ℕ} (Z : Fin n → Euc d) (u : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => interpQuant (fun j => Z j i) (u i)

/-- The sample mean `m̂ = n⁻¹ Σ_j X_j`. -/
def sMean {n : ℕ} (X : Fin n → Euc d) : Euc d := (n : ℝ)⁻¹ • ∑ j, X j

/-- The sample covariance `Σ̂_{ik} = n⁻¹ Σ_j (X_{j,i} − m̂_i)(X_{j,k} − m̂_k)`. -/
def sCov {n : ℕ} (X : Fin n → Euc d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i k => (n : ℝ)⁻¹ * ∑ j, (X j i - sMean X i) * (X j k - sMean X k)

/-- `cor:field-ell`: `S_μ(x) = Cov(μ)^{-1/2}(x − Eμ)`. -/
def ellStd (μ : Measure (Euc d)) (x : Euc d) : Euc d := mvec (invSqrt (covMat μ)) (x - meanVec μ)

/-- `cor:field-ell`: `S_μ⁻¹(z) = Eμ + Cov(μ)^{1/2} z`. -/
def ellInv (μ : Measure (Euc d)) (z : Euc d) : Euc d := meanVec μ + mvec (CFC.sqrt (covMat μ)) z

/-- `cor:field-ell`: `Ŝ_μ(x) = Σ̂^{-1/2}(x − m̂)` from the sample. -/
def ellStdHat {n : ℕ} (X : Fin n → Euc d) (x : Euc d) : Euc d := mvec (invSqrt (sCov X)) (x - sMean X)

/-- `cor:field-ell`: `Ŝ_ν⁻¹(z) = m̂ + Σ̂^{1/2} z` from the sample. -/
def ellInvHat {n : ℕ} (X : Fin n → Euc d) (z : Euc d) : Euc d := sMean X + mvec (CFC.sqrt (sCov X)) z

/-- `cor:field-npn`: `S_μ⁻¹(z) = (F_{μ,i}^{-1}(Φ([R^{1/2}z]_i)))_i`. -/
def npnInv (μ : Measure (Euc d)) (R : Matrix (Fin d) (Fin d) ℝ) (z : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => (marg μ i).quantile (stdPhi (mvec (CFC.sqrt R) z i))

/-- `cor:field-npn`: the clipped normal scores `Ẑ(x) = (Φ^{-1}(c_n(F̃_{n,i}(x_i))))_i`. -/
def zScoreHat {n : ℕ} (X : Fin n → Euc d) (x : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => stdPhiInv (clipN n (interpCdf (fun j => X j i) (x i)))

/-- `cor:field-npn`: `Ŝ_μ = R̂^{-1/2} Ẑ`. -/
def npnStdHat {n : ℕ} (X : Fin n → Euc d) (Rh : Matrix (Fin d) (Fin d) ℝ) (x : Euc d) : Euc d :=
  mvec (invSqrt Rh) (zScoreHat X x)

/-- `cor:field-npn`: `Ŝ_ν⁻¹(z) = (Q̃_{n,i}(Φ([R̂^{1/2}z]_i)))_i`. -/
def npnInvHat {n : ℕ} (Z : Fin n → Euc d) (Rh : Matrix (Fin d) (Fin d) ℝ) (z : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => interpQuant (fun j => Z j i) (stdPhi (mvec (CFC.sqrt Rh) z i))

/-- `eq:copulatransport`: `T_s(x) = (G_i^{-1}(H_{s,i}([M_s(W_s(x))]_i)))_i`, `W_s = zScore R_s` the normal scores,
`H_{s,i}` the marginal cdfs of `V_s = M_s(W_s)`, `G_i` those of `ν`. -/
def copTrans (R ν : Measure (Euc d)) (M : Euc d → Euc d) (x : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => (marg ν i).quantile (cdf (marg (R.map (M ∘ zScore R)) i) (M (zScore R x) i))

/-- The correlation matrix `diag(P)^{-1/2} P diag(P)^{-1/2}`. -/
def corrMat (P : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => P i j / Real.sqrt (P i i * P j j)

end Estimators

namespace Claims

open scoped MatrixOrder Matrix.Norms.L2Operator

/-! #### `def:standardisable`: the new definition generalises the old one -/

/-- The author's decision on `def:standardisable`: if `S_ν⁻¹` is `L`-Lipschitz on a set `A` of full `γ`-measure (old
(iii); the support of `γ` is one), `‖Ŝ_ν⁻¹ − S_ν⁻¹‖_{L²(γ)} = O_P(r_n)` (old (ii)) and `Ŝ_ν⁻¹` is `L`-Lipschitz on all
of `ℝ^d` with probability tending to one (old (iii)), then the NEW (iii) holds for some Lipschitz constant `L'`
(with `h_n = 0`). Stated for the target law only (the only law whose (iii) `thm:field` uses; the old (iii) names only
`ν`); the old forward condition (ii) plays no role. `L'` is existential: a Lipschitz EXTENSION of `S_ν⁻¹` from `A` to
`ℝ^d` is needed (coordinatewise McShane gives `√d·L`; Kirszbraun, not in Mathlib, would keep `L`). -/
def stdz_old_to_new : Prop :=
  ∀ (d : ℕ) (γ : Measure (Euc d)) [IsProbabilityMeasure γ] (Sinv : Euc d → Euc d) (A : Set (Euc d))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Sinvhat : ℕ → Ω → Euc d → Euc d) (r : ℕ → ℝ) (L : ℝ≥0),
    (∀ n, 0 ≤ r n) → γ Aᶜ = 0 → LipschitzOnWith L Sinv A → (∀ n ω, Measurable (Sinvhat n ω)) →
    BigOP P r (fun n ω => eLpNorm (fun z => Sinvhat n ω z - Sinv z) 2 γ) → LipschitzWhp P L Sinvhat →
      ∃ L' : ℝ≥0, InvStdzJ P r L' γ Sinv Sinvhat

/-! #### `lem:transfer` -/

/-- `lem:transfer`: for probability laws `η`, `γ` and a `K`-Lipschitz `k`,
`‖k‖_{L²(η)} ≤ ‖k‖_{L²(γ)} + K·W₂(η, γ)` (no moment assumption: both sides live in `[0, ∞]`). -/
def transfer_lip : Prop :=
  ∀ (d m : ℕ) (η γ : Measure (Euc d)) [IsProbabilityMeasure η] [IsProbabilityMeasure γ] (K : ℝ≥0)
    (k : Euc d → Euc m), LipschitzWith K k →
      eLpNorm k 2 η ≤ eLpNorm k 2 γ + K * wassersteinEDist 2 η γ

/-! #### `lem:quantiles` -/

/-- `lem:quantiles`, distribution functions: if `|F_n − F| ≤ ε` everywhere, then `|F̃_n − F| ≤ ε + 1/n`
everywhere (any law `F`, any sample, `n ≥ 1`). -/
def quantiles_cdf : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) (x : Fin n → ℝ) (ε : ℝ), 1 ≤ n →
    (∀ t, |empCdf x t - cdf F t| ≤ ε) → ∀ t, |interpCdf x t - cdf F t| ≤ ε + 1 / n

/-- `lem:quantiles`, quantile functions: under `ass:marg` (`F` carried by `[a, b]` with density in `[1/L, L]`), for a
sample in `[a, b]` with `|F_n − F| ≤ ε` everywhere, `|Q̃_n(u) − F⁻¹(u)| ≤ L(ε + 2/n)` for every `u ∈ (0, 1)`. -/
def quantiles_quant : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (L : ℝ≥0) (a b : ℝ) (n : ℕ) (x : Fin n → ℝ) (ε : ℝ),
    AssMarg L a b F → 1 ≤ n → (∀ i, x i ∈ Icc a b) → (∀ t, |empCdf x t - cdf F t| ≤ ε) →
      ∀ u ∈ Ioo (0 : ℝ) 1, |interpQuant x u - F.quantile u| ≤ L * (ε + 2 / n)

/-- `lem:quantiles`, Dvoretzky–Kiefer–Wolfowitz–Massart: for an i.i.d. sequence with any law `F`,
`ε_n = sup_t |F_n(t) − F(t)| = O_P(n^{-1/2})`. -/
def quantiles_dkw : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ),
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = F) →
      BigOP P (fun n => 1 / Real.sqrt n)
        (fun n ω => ⨆ t : ℝ, ENNReal.ofReal |empCdf (fun j : Fin n => X j ω) t - cdf F t|)

/-! #### `lem:reldev` -/

/-- `lem:reldev`: for `n ≥ 3` i.i.d. uniform variables on `[0, 1]`, with probability at least `1 − 4/n` (a measurable
event), for all `t ∈ [0, 1]`, `|G_n(t) − t| ≤ 2√(t(1 − t) log n / n) + 5 log n / n`. -/
def reldev_bound : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ E : Set (Fin n → ℝ), MeasurableSet E ∧
    ENNReal.ofReal (1 - 4 / n) ≤ (Measure.pi fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)) E ∧
    ∀ u ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      |empCdf u t - t| ≤ 2 * Real.sqrt (t * (1 - t) * Real.log n / n) + 5 * Real.log n / n

/-! #### `lem:scores` -/

/-- `lem:scores`: for an i.i.d. sequence with an atomless law `F` and `X ∼ F` independent of the sample,
`E[(Φ⁻¹(c_n(F̃_n(X))) − Φ⁻¹(F(X)))² | X₁, …, X_n] = O_P(n^{-1}(log n)²)`. -/
def scores_mse : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ),
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = F) →
      BigOP P (fun n => Real.log n ^ 2 / n)
        (fun n ω => ∫⁻ x, ENNReal.ofReal
          ((stdPhiInv (clipN n (interpCdf (fun j : Fin n => X j ω) x)) - stdPhiInv (cdf F x)) ^ 2) ∂F)

/-! #### `lem:compose` -/

/-- `lem:compose`: if each `f_k` is `K`-Lipschitz on `A_k`, `dist(f̂_k, f_k) ≤ ε` on `A_k`, and all intermediate
values of both chains lie in the corresponding `A_k`, then
`dist(f̂(x'), f(x)) ≤ K^m dist(x', x) + ε Σ_{j<m} K^j`. -/
def compose_perturbed : Prop :=
  ∀ (X : Type) [PseudoMetricSpace X] (m : ℕ) (f fh : ℕ → X → X) (A : ℕ → Set X) (K : ℝ≥0) (ε : ℝ) (x x' : X),
    (∀ k < m, LipschitzOnWith K (f k) (A k)) → (∀ k < m, ∀ y ∈ A k, dist (fh k y) (f k y) ≤ ε) →
    (∀ k < m, chain f k x ∈ A k) → (∀ k < m, chain fh k x' ∈ A k) →
      dist (chain fh m x') (chain f m x) ≤ (K : ℝ) ^ m * dist x' x + ε * ∑ j ∈ Finset.range m, (K : ℝ) ^ j

/-! #### `thm:field`, journal version -/

/-- `thm:field` (journal), the deterministic chain of the proof for one realisation of the estimators: `S'` an
`L`-Lipschitz extension of `S_ν⁻¹`, `Ŝ_ν⁻¹ − S' = h + k` with `k` `K`-Lipschitz. For each group
`‖T̂_s − T_s‖_{L²(R_s)} ≤ ‖h‖_∞ + ‖k‖_{L²(γ)} + K‖Ŝ_s − S_s‖_{L²(R_s)} + L‖Ŝ_s − S_s‖_{L²(R_s)}`
(`T_s = S_ν⁻¹ ∘ S_s`, `T̂_s = Ŝ_ν⁻¹ ∘ Ŝ_s`), the same bounds `W₂((T̂_s)_#R_s, ν)`, and the parity gap is at most the
sum over the two groups. -/
def fieldJ_bound : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (Euc d)) (ν γ : Measure (Euc d)) (S Sinv Shat : Fin 2 → Euc d → Euc d)
    (Sν Sνinv S' Sνinvhat h k : Euc d → Euc d) (L K : ℝ≥0),
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → IsProbabilityMeasure γ →
    (∀ s, Standardises (R s) γ (S s) (Sinv s)) → Standardises ν γ Sν Sνinv →
    LipschitzWith L S' → S' =ᵐ[γ] Sνinv → (∀ s, Measurable (Shat s)) → Measurable Sνinvhat →
    LipschitzWith K k → (∀ z, Sνinvhat z - S' z = h z + k z) →
      (∀ s, eLpNorm (fun x => Sνinvhat (Shat s x) - Sνinv (S s x)) 2 (R s) ≤
          supNorm h + eLpNorm k 2 γ + K * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
            L * eLpNorm (fun x => Shat s x - S s x) 2 (R s)) ∧
      (∀ s, wassersteinEDist 2 ((R s).map (Sνinvhat ∘ Shat s)) ν ≤
          supNorm h + eLpNorm k 2 γ + K * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
            L * eLpNorm (fun x => Shat s x - S s x) 2 (R s)) ∧
      wassersteinEDist 2 ((R 0).map (Sνinvhat ∘ Shat 0)) ((R 1).map (Sνinvhat ∘ Shat 1)) ≤
        ∑ s, (supNorm h + eLpNorm k 2 γ + K * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
            L * eLpNorm (fun x => Shat s x - S s x) 2 (R s))

/-- `thm:field` (journal), the rate: `R₀, R₁, ν` standardisable onto `γ` (`def:standardisable`(i)), forward errors
`‖Ŝ_{R_s} − S_{R_s}‖_{L²(R_s)} = O_P(r_n)` ((ii)) and the NEW (iii) for `ν` (`InvStdzJ`). Then
`W₂((T̂₀)_#R₀, (T̂₁)_#R₁) = O_P(r_n)`. -/
def fieldJ_rate : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (Euc d)) (ν γ : Measure (Euc d)) (S Sinv : Fin 2 → Euc d → Euc d)
    (Sν Sνinv : Euc d → Euc d) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Shat : ℕ → Ω → Fin 2 → Euc d → Euc d) (Sνinvhat : ℕ → Ω → Euc d → Euc d) (r : ℕ → ℝ) (L : ℝ≥0),
    IsProbabilityMeasure P → (∀ n, 0 ≤ r n) →
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → IsProbabilityMeasure γ →
    (∀ s, Standardises (R s) γ (S s) (Sinv s)) → Standardises ν γ Sν Sνinv →
    (∀ n ω s, Measurable (Shat n ω s)) → (∀ n ω, Measurable (Sνinvhat n ω)) →
    (∀ s, BigOP P r fun n ω => eLpNorm (fun x => Shat n ω s x - S s x) 2 (R s)) →
    InvStdzJ P r L γ Sνinv Sνinvhat →
      BigOP P r fun n ω => wassersteinEDist 2 ((R 0).map (Sνinvhat n ω ∘ Shat n ω 0))
        ((R 1).map (Sνinvhat n ω ∘ Shat n ω 1))

/-! #### `cor:field-ell` -/

/-- `cor:field-ell`, (ii): for an affine image `μ = (z ↦ Az + b)_#γ` of the generator (`A` invertible, `γ` with mean
`0`, covariance `I`, `∫‖y‖⁴ dγ < ∞`; elliptical when `γ` is spherical, which (ii) does not need) and an i.i.d. sample
of `μ`, the plug-in standardisation with the sample mean and the `1/n` sample covariance satisfies
`‖Ŝ_μ − S_μ‖_{L²(μ)} = O_P(n^{-1/2})`. -/
def fieldell_fwd : Prop :=
  ∀ (d : ℕ) (γ : Measure (Euc d)) [IsProbabilityMeasure γ] (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Euc d),
    ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ < ⊤ → meanVec γ = 0 → covMat γ = 1 → A.det ≠ 0 →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = γ.map fun z => mvec A z + b) →
      BigOP P (fun n => 1 / Real.sqrt n) fun n ω =>
        eLpNorm (fun x => ellStdHat (fun j : Fin n => X j ω) x - ellStd (γ.map fun z => mvec A z + b) x) 2
          (γ.map fun z => mvec A z + b)

/-- `cor:field-ell`, (iii): for a target `ν = (z ↦ Az + b)_#γ` as above (no sphericity needed),
`S_ν⁻¹(z) = Eν + Cov(ν)^{1/2}z` is Lipschitz and the plug-in inverse `m̂ + Σ̂^{1/2}z` satisfies the new (iii) at rate
`n^{-1/2}` (reference `γ`). -/
def fieldell_inv : Prop :=
  ∀ (d : ℕ) (γ : Measure (Euc d)) [IsProbabilityMeasure γ] (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → Euc d),
    ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ < ⊤ → meanVec γ = 0 → covMat γ = 1 → A.det ≠ 0 →
    (∀ j, Measurable (Z j)) → iIndepFun Z P → (∀ j, P.map (Z j) = γ.map fun z => mvec A z + b) →
      ∃ L : ℝ≥0, InvStdzJ P (fun n => 1 / Real.sqrt n) L γ (ellInv (γ.map fun z => mvec A z + b))
        (fun n ω => ellInvHat (fun j : Fin n => Z j ω))

/-- `cor:field-ell`, the rate: groups `R_s = (z ↦ A_s z + b_s)_#γ` and target `ν = (z ↦ A z + b)_#γ` with a common
spherical generator `γ` (mean `0`, covariance `I`, finite fourth moment), i.i.d. samples of each; the plug-in repair
`T̂_s = Ŝ_ν⁻¹ ∘ Ŝ_{R_s}` from sample means and covariances has parity gap `O_P(n^{-1/2})`. -/
def fieldell_rate : Prop :=
  ∀ (d : ℕ) (γ : Measure (Euc d)) [IsProbabilityMeasure γ] (A₀ : Fin 2 → Matrix (Fin d) (Fin d) ℝ)
    (b₀ : Fin 2 → Euc d) (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin 2 → ℕ → Ω → Euc d) (Z : ℕ → Ω → Euc d),
    IsSpherical γ → ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ < ⊤ → meanVec γ = 0 → covMat γ = 1 → (∀ s, (A₀ s).det ≠ 0) → A.det ≠ 0 →
    (∀ s j, Measurable (X s j)) → (∀ s, iIndepFun (X s) P) →
    (∀ s j, P.map (X s j) = γ.map fun z => mvec (A₀ s) z + b₀ s) →
    (∀ j, Measurable (Z j)) → iIndepFun Z P → (∀ j, P.map (Z j) = γ.map fun z => mvec A z + b) →
      BigOP P (fun n => 1 / Real.sqrt n) fun n ω =>
        wassersteinEDist 2
          ((γ.map fun z => mvec (A₀ 0) z + b₀ 0).map
            (ellInvHat (fun j : Fin n => Z j ω) ∘ ellStdHat (fun j : Fin n => X 0 j ω)))
          ((γ.map fun z => mvec (A₀ 1) z + b₀ 1).map
            (ellInvHat (fun j : Fin n => Z j ω) ∘ ellStdHat (fun j : Fin n => X 1 j ω)))

/-! #### `cor:field-cop` -/

/-- `cor:field-cop`, (ii): for a law `μ` with continuous marginals and an i.i.d. sample, the interpolated empirical
marginal cdfs satisfy `‖Ŝ_μ − S_μ‖_{L²(μ)} = O_P(√(d/n))` (`d` fixed, so the constant absorbs `√d`). The continuity
hypothesis is printed but not needed (`F_n ≤ F̃_n ≤ F_n + 1/n` and DKW hold for every law). -/
def fieldcop_fwd : Prop :=
  ∀ (d : ℕ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → Euc d),
    (∀ i, NullSingletonClass (marg μ i)) → (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = μ) →
      BigOP P (fun n => Real.sqrt (d / n)) fun n ω =>
        eLpNorm (fun x => copStdHat (fun j : Fin n => X j ω) x - copStd μ x) 2 μ

/-- `cor:field-cop`, (iii): if every marginal of `ν` satisfies `ass:marg` (constant `L`), then `S_ν⁻¹ = copInv ν`
extends to an `L`-Lipschitz map of `ℝ^d`, and the interpolated empirical marginal quantiles satisfy the new (iii) at
rate `√(d/n)` onto the copula law `γ = (S_ν)_#ν` (the statement leaves the extension and the split `h_n + k_n`
existential; the proof takes the constant extension outside `[0,1]^d` and `k_n = 0`). -/
def fieldcop_inv : Prop :=
  ∀ (d : ℕ) (ν : Measure (Euc d)) [IsProbabilityMeasure ν] (L : ℝ≥0) (a b : Fin d → ℝ) (Ω : Type)
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → Euc d),
    (∀ i, AssMarg L (a i) (b i) (marg ν i)) → (∀ j, Measurable (Z j)) → iIndepFun Z P → (∀ j, P.map (Z j) = ν) →
      InvStdzJ P (fun n => Real.sqrt (d / n)) L (ν.map (copStd ν)) (copInv ν)
        (fun n ω => copInvHat (fun j : Fin n => Z j ω))

/-- `cor:field-cop`, the rate: groups `R_s` and target `ν` with continuous marginals and a common copula
(`(S_{R_s})_#R_s = (S_ν)_#ν`), the target marginals under `ass:marg`, i.i.d. samples of each. The plug-in coordinatewise
quantile repair `T̂_s = (Q̃_{n,i} ∘ F̃_{s,n,i})_i` has parity gap `O_P(√(d/n))`. -/
def fieldcop_rate : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (Euc d)) (ν : Measure (Euc d)) (L : ℝ≥0) (a b : Fin d → ℝ) (Ω : Type)
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin 2 → ℕ → Ω → Euc d) (Z : ℕ → Ω → Euc d),
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → (∀ s i, NullSingletonClass (marg (R s) i)) →
    (∀ i, AssMarg L (a i) (b i) (marg ν i)) → (∀ s, (R s).map (copStd (R s)) = ν.map (copStd ν)) →
    (∀ s j, Measurable (X s j)) → (∀ s, iIndepFun (X s) P) → (∀ s j, P.map (X s j) = R s) →
    (∀ j, Measurable (Z j)) → iIndepFun Z P → (∀ j, P.map (Z j) = ν) →
      BigOP P (fun n => Real.sqrt (d / n)) fun n ω =>
        wassersteinEDist 2 ((R 0).map (copInvHat (fun j : Fin n => Z j ω) ∘ copStdHat (fun j : Fin n => X 0 j ω)))
          ((R 1).map (copInvHat (fun j : Fin n => Z j ω) ∘ copStdHat (fun j : Fin n => X 1 j ω)))

/-! #### `cor:field-npn` -/

/-- `cor:field-npn`, (ii): for `μ` nonparanormal with correlation `R` (`λ_min(R) ≥ λ > 0`), continuous marginals, an
i.i.d. sample and symmetric correlation estimates with `‖R̂ − R‖_op = O_P(n^{-1/2})`, the clipped normal-score
standardisation satisfies `‖Ŝ_μ − S_μ‖_{L²(μ)} = O_P(n^{-1/2} log n)`. -/
def fieldnpn_fwd : Prop :=
  ∀ (d : ℕ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (R : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (Ω : Type)
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Euc d)
    (Rh : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
    R.PosDef → 0 < lam → lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ R → InNPN μ R → (∀ i, NullSingletonClass (marg μ i)) →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = μ) → (∀ n ω, (Rh n ω).IsHermitian) →
    BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖Rh n ω - R‖ₑ) →
      BigOP P (fun n => Real.log n / Real.sqrt n) fun n ω =>
        eLpNorm (fun x => npnStdHat (fun j : Fin n => X j ω) (Rh n ω) x - npnStd μ R x) 2 μ

/-- `cor:field-npn`, (iii): for a nonparanormal target `ν` with correlation `B` (`λ_min(B) ≥ λ > 0`) whose marginals
satisfy `ass:marg`, an i.i.d. sample and symmetric `B̂` with `‖B̂ − B‖_op = O_P(n^{-1/2})`, `S_ν⁻¹ = npnInv ν B` is
Lipschitz and `Ŝ_ν⁻¹ = (Q̃_{n,i}(Φ([B̂^{1/2}z]_i)))_i` satisfies the new (iii) onto `N(0, I)` at rate `n^{-1/2}`. -/
def fieldnpn_inv : Prop :=
  ∀ (d : ℕ) (ν : Measure (Euc d)) [IsProbabilityMeasure ν] (B : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (L : ℝ≥0)
    (a b : Fin d → ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → Euc d) (Bh : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
    B.PosDef → 0 < lam → lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ B → InNPN ν B →
    (∀ i, AssMarg L (a i) (b i) (marg ν i)) →
    (∀ j, Measurable (Z j)) → iIndepFun Z P → (∀ j, P.map (Z j) = ν) → (∀ n ω, (Bh n ω).IsHermitian) →
    BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖Bh n ω - B‖ₑ) →
      ∃ L' : ℝ≥0, InvStdzJ P (fun n => 1 / Real.sqrt n) L' (multivariateGaussian 0 1) (npnInv ν B)
        (fun n ω => npnInvHat (fun j : Fin n => Z j ω) (Bh n ω))

/-- `cor:field-npn`, the rate: nonparanormal groups `R_s` (correlations `A_s`) and target `ν` (correlation `B`), all
with smallest eigenvalue `≥ λ > 0` and continuous marginals, the target marginals under `ass:marg`, i.i.d. samples,
symmetric correlation estimates at rate `n^{-1/2}` in operator norm. The plug-in nonparanormal repair has parity gap
`O_P(n^{-1/2} log n)`. -/
def fieldnpn_rate : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (Euc d)) (ν : Measure (Euc d)) (A : Fin 2 → Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (L : ℝ≥0) (a b : Fin d → ℝ) (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin 2 → ℕ → Ω → Euc d) (Z : ℕ → Ω → Euc d)
    (Ah : ℕ → Ω → Fin 2 → Matrix (Fin d) (Fin d) ℝ) (Bh : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → 0 < lam →
    (∀ s, (A s).PosDef) → (∀ s, lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ A s) → (∀ s, InNPN (R s) (A s)) →
    (∀ s i, NullSingletonClass (marg (R s) i)) →
    B.PosDef → lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ B → InNPN ν B → (∀ i, AssMarg L (a i) (b i) (marg ν i)) →
    (∀ s j, Measurable (X s j)) → (∀ s, iIndepFun (X s) P) → (∀ s j, P.map (X s j) = R s) →
    (∀ j, Measurable (Z j)) → iIndepFun Z P → (∀ j, P.map (Z j) = ν) →
    (∀ n ω s, (Ah n ω s).IsHermitian) → (∀ n ω, (Bh n ω).IsHermitian) →
    (∀ s, BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖Ah n ω s - A s‖ₑ)) →
    BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖Bh n ω - B‖ₑ) →
      BigOP P (fun n => Real.log n / Real.sqrt n) fun n ω =>
        wassersteinEDist 2
          ((R 0).map (npnInvHat (fun j : Fin n => Z j ω) (Bh n ω) ∘
            npnStdHat (fun j : Fin n => X 0 j ω) (Ah n ω 0)))
          ((R 1).map (npnInvHat (fun j : Fin n => Z j ω) (Bh n ω) ∘
            npnStdHat (fun j : Fin n => X 1 j ω) (Ah n ω 1)))

/-! #### `cor:field-local`, journal version -/

/-- `cor:field-local` (journal), deterministic: `ν ∈ 𝔐` with `L`-Lipschitz extension `S'` of `S_ν⁻¹` and
`Ŝ_ν⁻¹ − S' = h + k`, `k` `K`-Lipschitz; for each group a measurable `S̃_s` (the standardiser of the approximating
member `μ̃_s`) with misspecification `δ_s = W₂((S̃_s)_#R_s, γ)` measured after standardisation. Then the parity gap of
`T̂_s = Ŝ_ν⁻¹ ∘ Ŝ_s` is at most
`Σ_s (Lδ_s + ‖h‖_∞ + ‖k‖_{L²(γ)} + K(‖Ŝ_s − S̃_s‖_{L²(R_s)} + δ_s) + L‖Ŝ_s − S̃_s‖_{L²(R_s)})`. -/
def fieldlocal_bound : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (Euc d)) (ν γ : Measure (Euc d)) (St Shat : Fin 2 → Euc d → Euc d)
    (Sν Sνinv S' Sνinvhat h k : Euc d → Euc d) (L K : ℝ≥0),
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → IsProbabilityMeasure γ →
    Standardises ν γ Sν Sνinv → LipschitzWith L S' → S' =ᵐ[γ] Sνinv →
    (∀ s, Measurable (St s)) → (∀ s, Measurable (Shat s)) → Measurable Sνinvhat →
    LipschitzWith K k → (∀ z, Sνinvhat z - S' z = h z + k z) →
      wassersteinEDist 2 ((R 0).map (Sνinvhat ∘ Shat 0)) ((R 1).map (Sνinvhat ∘ Shat 1)) ≤
        ∑ s, (L * wassersteinEDist 2 ((R s).map (St s)) γ + supNorm h + eLpNorm k 2 γ +
          K * (eLpNorm (fun x => Shat s x - St s x) 2 (R s) + wassersteinEDist 2 ((R s).map (St s)) γ) +
          L * eLpNorm (fun x => Shat s x - St s x) 2 (R s))

/-- `cor:field-local` (journal), the rate: `ν ∈ 𝔐` with the new (iii); for each group (laws `R_{n,s}` possibly
depending on `n`) approximating standardisers `S̃_{n,s}` with `W₂((S̃_{n,s})_#R_{n,s}, γ) ≤ δ_n` and estimators with
`‖Ŝ_s − S̃_{n,s}‖_{L²(R_{n,s})} = O_P(r_n)`. Then the parity gap of the plug-in repair is `O_P(r_n + δ_n)`. -/
def fieldlocal_rate : Prop :=
  ∀ (d : ℕ) (R : ℕ → Fin 2 → Measure (Euc d)) (ν γ : Measure (Euc d)) (St : ℕ → Fin 2 → Euc d → Euc d)
    (Sν Sνinv : Euc d → Euc d) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Shat : ℕ → Ω → Fin 2 → Euc d → Euc d) (Sνinvhat : ℕ → Ω → Euc d → Euc d) (r δ : ℕ → ℝ) (L : ℝ≥0),
    IsProbabilityMeasure P → (∀ n, 0 ≤ r n) → (∀ n, 0 ≤ δ n) →
    (∀ n s, IsProbabilityMeasure (R n s)) → IsProbabilityMeasure ν → IsProbabilityMeasure γ →
    Standardises ν γ Sν Sνinv → (∀ n s, Measurable (St n s)) →
    (∀ n s, wassersteinEDist 2 ((R n s).map (St n s)) γ ≤ ENNReal.ofReal (δ n)) →
    (∀ n ω s, Measurable (Shat n ω s)) → (∀ n ω, Measurable (Sνinvhat n ω)) →
    (∀ s, BigOP P r fun n ω => eLpNorm (fun x => Shat n ω s x - St n s x) 2 (R n s)) →
    InvStdzJ P r L γ Sνinv Sνinvhat →
      BigOP P (fun n => r n + δ n) fun n ω =>
        wassersteinEDist 2 ((R n 0).map (Sνinvhat n ω ∘ Shat n ω 0)) ((R n 1).map (Sνinvhat n ω ∘ Shat n ω 1))

/-! #### `prop:copulatransport` -/

/-- `prop:copulatransport`(i): for every measurable `M_s` such that the marginals `H_{s,i}` of `V_s = M_s(W_s)` are
continuous, `(T_s)_#R_s` has marginals `G_1, …, G_d` (those of `ν`); continuity of the `F_{s,i}` and `G_i` is not
needed. -/
def coptransport_marginals : Prop :=
  ∀ (d : ℕ) (R ν : Measure (Euc d)) [IsProbabilityMeasure R] [IsProbabilityMeasure ν] (M : Euc d → Euc d),
    Measurable M → (∀ i, NullSingletonClass (marg (R.map (M ∘ zScore R)) i)) →
      ∀ i, marg (R.map (copTrans R ν M)) i = marg ν i

/-- `prop:copulatransport`(ii), first part: if moreover the `G_i` are continuous, the copula of `(T_s)_#R_s` is the
copula of `V_s = M_s(W_s)`. (Since `(T_s)_#R_s = Q_#(V_s)_#R_s` with `Q = (G_i^{-1} ∘ H_{s,i})_i`, this is the
certified Wave 30g `prop:iff` claim `iff_marginals_copula` at the law of `V_s`, as the paper's proof says.) -/
def coptransport_copula : Prop :=
  ∀ (d : ℕ) (R ν : Measure (Euc d)) [IsProbabilityMeasure R] [IsProbabilityMeasure ν] (M : Euc d → Euc d),
    Measurable M → (∀ i, NullSingletonClass (marg (R.map (M ∘ zScore R)) i)) → (∀ i, NullSingletonClass (marg ν i)) →
      (R.map (copTrans R ν M)).map (copStd (R.map (copTrans R ν M))) =
        (R.map (M ∘ zScore R)).map (copStd (R.map (M ∘ zScore R)))

/-- `prop:copulatransport`(ii), second part: with continuous `G_i` and `H_{s,i}`, the copula-space transport is an
exact repair, `(T₀)_#R₀ = (T₁)_#R₁`, if and only if `M₀(W₀)` and `M₁(W₁)` have the same copula (the certified
Wave 30g `iff_parity` at the laws of `V₀`, `V₁`). -/
def coptransport_exact_iff : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (Euc d)) (ν : Measure (Euc d)) (M : Fin 2 → Euc d → Euc d),
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → (∀ s, Measurable (M s)) →
    (∀ s i, NullSingletonClass (marg ((R s).map (M s ∘ zScore (R s))) i)) → (∀ i, NullSingletonClass (marg ν i)) →
      ((R 0).map (copTrans (R 0) ν (M 0)) = (R 1).map (copTrans (R 1) ν (M 1)) ↔
        ((R 0).map (M 0 ∘ zScore (R 0))).map (copStd ((R 0).map (M 0 ∘ zScore (R 0)))) =
          ((R 1).map (M 1 ∘ zScore (R 1))).map (copStd ((R 1).map (M 1 ∘ zScore (R 1)))))

/-- `prop:copulatransport`(iii), corrected map: if `R_s` and `ν` have Gaussian copulas with positive definite
correlation matrices `A_s`, `B` (`InNPN`), `ν` has continuous marginals, and `M_s` is the moment-corrected map (frozen
`corrMap`) of an affine map `x ↦ M x + c` from `N(0, A_s)` to `N(0, B)` (the barycentric projection of the entropic
plan, for any `ε > 0`; square-root hypotheses as in the frozen `corrected_gaussian`), the repair is exact:
`(T_s)_#R_s = ν`. (`A ≻ 0` is printed but redundant for `d ≥ 1`: the hypothesis on `Ph` forces
`Cov(M W + c) = M A Mᵀ` to be invertible.) -/
def coptransport_corrected : Prop :=
  ∀ (d : ℕ) (R ν : Measure (Euc d)) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (A B : Matrix (Fin d) (Fin d) ℝ) (M : Euc d →L[ℝ] Euc d) (c : Euc d) (Vh Ph : Matrix (Fin d) (Fin d) ℝ),
    A.PosDef → B.PosDef → (∀ i, B i i = 1) → InNPN R A → InNPN ν B → (∀ i, NullSingletonClass (marg ν i)) →
    Vh.transpose = Vh → Vh * Vh = covM (multivariateGaussian 0 B) id → Ph.transpose = Ph →
    Ph * covM (multivariateGaussian 0 A) (fun x => M x + c) * Ph = 1 →
      R.map (copTrans R ν (corrMap (multivariateGaussian 0 A) (fun x => M x + c)
        (meanV (multivariateGaussian 0 B) id) (Vh * Ph))) = ν

/-- `prop:copulatransport`(iii), uncorrected map: if `R_s` has a Gaussian copula with positive definite correlation
`A_s`, `ν` has continuous marginals and `M_s = G` is linear with `P_s = G A_s Gᵀ` positive definite (the barycentric
projection `CᵀA_s⁻¹` of the entropic plan gives `P_s = CᵀA_s⁻¹C`, `eq:Ps`), then `(T_s)_#R_s` has marginals `G_i`
and a Gaussian copula with the correlation matrix `diag(P_s)^{-1/2} P_s diag(P_s)^{-1/2}` of `P_s`. -/
def coptransport_uncorrected : Prop :=
  ∀ (d : ℕ) (R ν : Measure (Euc d)) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (A G : Matrix (Fin d) (Fin d) ℝ),
    A.PosDef → InNPN R A → (G * A * Gᵀ).PosDef → (∀ i, NullSingletonClass (marg ν i)) →
      (∀ i, marg (R.map (copTrans R ν (mvec G))) i = marg ν i) ∧
        InNPN (R.map (copTrans R ν (mvec G))) (corrMat (G * A * Gᵀ))

end Claims

end StatFormal.Wave30h
