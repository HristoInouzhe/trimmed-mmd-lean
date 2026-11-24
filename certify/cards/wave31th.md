# Fidelity card — wave 31th: trimmed-mmd (JMLR **v3**, `jmlr/v3/`), `rem:qdens` in every dimension `d` (the Gaussian kernel on `ℝ^d`)

Lean: `StatFormal/Wave31th/Statements.lean` (5 claims, no new definitions; frozen 2026-11-12 before any proof, commit `298622e`, sha256
`21bdf3570952406288a84c9498016000843b37ce4878e5bafc421a02f1368b28`, locked with its 22 imports). Routes `RouteChart`, `RouteDensity`,
`RouteCorePi`, `RouteCore`, `RouteGauss` (the proofs) and `RouteSpec` (the `d = 1` specialisation check) (untrusted); `Proofs.lean` imports
them; the gate checks `example : Claims.c := c` and `#print axioms` for each (`[propext, Classical.choice, Quot.sound]`). Paper id
`trimmed-mmd (jmlr)`; label `rem:qdens (v3, every d)` (+ a short description). Branch `tmmd-jmlr-v3gap-h`, based on `merge-tmmd-jmlr` at
`226e886` (every earlier tmmd wave, v2 and v3, among them wave 31tc); proofs commit `2717672`.
Critic (independent AI reviewer, before the freeze, 2026-11-12): 5 claims, 4 ACCEPT and 1 ACCEPT-WITH-NOTE (`gaussian_regular`: `C¹` not
`C^∞`, to be said on this card), none false, verdict READY TO FREEZE after docstring-only edits (applied before hashing: the source
wording, the `d = 1` equivalence wording, the encoding notes, the non-vacuity bullet, the "intended route" wording of the coarea bullet).
It back-translated blind, re-derived the truth of each claim and found no counterexample (attacks tried: `p` negative, non-measurable or
non-integrable off `U`, `p` unbounded away from `L`, `d = 0`, `d = 1`, unbounded level sets, critical points near the level, only `C¹`),
proved in Lean (scratch) a non-vacuity witness of `qdens_euclid` (`d = 2`, `f(x) = exp(−‖x‖²)`, `t = ½`, `p` the standard normal density,
`U = ℝ²`), that the three Gaussian claims follow from `qdens_euclid` and `gaussian_regular`, that `φ` is `1/σ`-Lipschitz, that `d = 0` is
vacuous and that `qdens_euclid` at `d = 1` and `Wave31tc.Claims.qdens_univariate` imply each other, and checked numerically (a quadratic
program, `d = 1`, `σ = 1`, `P = N(−2,1)`, `Q = N(2,1)`, `α = 0.2`: `D_α ≈ 0.968`, `t_α = −u_α ≈ 0.613`, level set `{−2.32, −1.81}` with
`d⋆′ ≈ +0.061, −0.066`) that the hypotheses of the Gaussian claims are met. It also noted that in this Mathlib `ContDiff ℝ ⊤` is
analyticity (`C^∞` is `ContDiff ℝ ∞`): the claims use `ContDiff ℝ 1`.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-12 — PASS with notes (5 claims back-translated blind from the Lean
code and compared with NEW_STATEMENTS.md at `d356058` (G2, lines 184–210) and `jmlr/v3/sections/05_trimming.tex` / `appendix/D_trimming.tex` as of `78c4665`, all
faithful, no hypothesis stronger than printed; the printed remark re-derived and found true; hashes, line numbers, lock (22 imports), freeze commit `298622e` before the
proofs `2717672`, only the new `Statements.lean` added and the lock gaining exactly one entry, labels, targets and the coverage note checked; the five `example : Claims.c := c`
and the axioms re-checked in a scratch file; the Gaussian numerics independently replicated; the `d = 1` converse re-proved in scratch; notes at the end of this card, applied).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md` at trimmed-mmd commit `d356058` (the binding specification: lines 1–210, sha256
`311b3b79b12704db129665550b6137172bf8d6d3552e071d0123422157c37cad`; section "v3 gap closure (2026-11-12)", subsection "Wave 31th", G2
`rem:qdens` in dimension `d ≥ 2`, lines 184–210, with its "Formal target" at `:194-201`, the admissible inputs `:203-208` and the fallback
`:209-210`). The working-tree file carries, after line 210 (commit `6fe8200`, sha256 `b266ef5b…6395`), an independent second write-up of the
same claim (G2, "`rem:qdens` for every `d`", lines 249–269); it agrees with lines 184–210 (same target, same two admissible bridges, same
"not allowed as a bridge") and was not used as a specification. The remark is printed in `jmlr/v3/sections/05_trimming.tex:65-71` at trimmed-mmd
`78c4665` (file sha256 `f787aecc1a51fe078b1b7ebaa354c518c63c46ccda1e0fb4b2ae21a434e800db`; (Q), (Q′) at `:54-61`), its proof in
`jmlr/v3/appendix/D_trimming.tex:312-335` (sha256 `9962dc6bc571298bbcf410b3f9adf604f1c6f8ac61f17478d5d9efe5cdd6000f`); both files unchanged
since `78c4665` (checked at the critic's review). Read-only, read 2026-11-12.
Printed text: "Let `𝒳 = ℝ^d` with the Gaussian kernel, so that `d⋆` is infinitely differentiable and vanishes at infinity. If `t_α ≠ 0`, the level
set `{d⋆ = t_α}` is nonempty, the gradient of `d⋆` does not vanish on it, and `P` has a Lebesgue density `p` that is continuous near the level
set and positive on it, then (Q) holds, by the coarea formula (Evans–Gariepy 2015). The same conditions at `u_α` under `Q` give (Q′)." (Q) and
(Q′) as in `05_trimming.tex:54-61`.

## Decision on the route (recorded at the start of the wave)
The target allowed two declared inputs, the Gaussian-RKHS facts `[SC]` and the coarea formula `[CA]`, and said that a proof by local
straightening (implicit function theorem, change of variables, finitely many charts covering the compact level set) needs no coarea bridge.
Mathlib has no coarea formula and no Hausdorff-measure area formula, but it has the change of variables
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`, the inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`) and
the matrix determinant API, so the route was local straightening, and neither bridge is used: `[CA]` is avoided and `[SC]` is proved (at the
level the argument uses, `C¹` and decay). The continuity and positivity of the level-set density `h(t) = ∫_{d⋆=t} p/|∇d⋆| dℋ^{d−1}` are not
assumed anywhere; (Q) is proved without introducing `h` (see "Proof route": an upper bound from the finite cover of charts, a lower bound from
one chart, then Radon–Nikodym), so no step restates (Q) or the printed flow argument.
The specification's sentence (`NEW_STATEMENTS.md` at `d356058`, lines 206–208) reads: "The continuity and positivity of h near t_α (the printed flow argument) are part of the claim and
must be proved, not assumed; if the whole statement can be proved without [CA] by local straightening (implicit function theorem and change of variables, finitely many charts covering the
compact set L), do that and drop the bridge." The reading adopted here: it forbids assuming the continuity or positivity of `h` (as a hypothesis or a bridge); the formal target's conclusion
(lines 197–198) is "a Lebesgue density with values in `[c_f, C_f]`", i.e. `QDensity`, and says nothing about continuity of `h`; the local-straightening route never introduces `h`. The phrase "nor
anything that restates (Q)" quoted in the `Statements.lean` docstring is from the independent second write-up in the working-tree file (commit `6fe8200`, lines 266–267), not from lines 1–210;
the author may overrule this reading, the frozen file needing then a new wave.

## Targets (5, all in `certify/targets.toml`, module `StatFormal.Wave31th.Proofs`)
| label | claim / theorem `StatFormal.Wave31th.(Claims.)…` |
|---|---|
| `rem:qdens (v3, every d)`, geometric core with no kernel, every `d` | `qdens_euclid` |
| `rem:qdens (v3, every d)`, the Gaussian-RKHS facts of the printed proof at the `C¹` level | `gaussian_regular` |
| `rem:qdens (v3, every d)`, "(Q) holds" | `qdens_gauss_Q` |
| `rem:qdens (v3, every d)`, "the same conditions at `u_α` under `Q` give (Q′)" | `qdens_gauss_Qprime` |
| `rem:qdens (v3, every d)`, (Q) and (Q′) with one common `r_Q` | `qdens_gauss_Q_Qprime` |

## Encodings (declared)
* `𝒳 = ℝ^d` is `EuclideanSpace ℝ (Fin d)` with its Borel σ-algebra and `volume`; `d` is arbitrary (`d = 0` is vacuous: `fderiv` of a function on
  a point is `0`, so `∇f ≠ 0` on a nonempty level set fails; checked by the critic).
* The Gaussian kernel: `φ : ℝ^d → ℋ` into a complete separable real Hilbert space with `⟨φ x, φ y⟩ = exp(−‖x−y‖²/(2σ²))`, `σ > 0` (the encoding of
  `Wave30tx.nearcontact_b`; `ℋ` is any Hilbert space carrying such a feature map, the paper's RKHS being the closed span of `φ(ℝ^d)`; a
  generalisation). `d⋆(x) = ⟨d⋆, φ x⟩` is `Wave12c.witFn dstar φ x`. (A1)–(A2): `φ` strongly measurable with `‖φ x‖ ≤ κ` (some `κ`; `‖φ x‖ = 1`),
  `ℋ` complete and separable. (A3) (`Characteristic φ`) is NOT assumed (the remark does not use it; generalisation; the Gaussian kernel is
  characteristic anyway). `gaussian_regular` needs only completeness of `ℋ` (no separability, measurability or bound on `φ`).
* `D_α(P,Q)` is `Dpop φ P Q α`; `d⋆` is any `dstar` with `IsMinNorm (region φ α P − region φ α Q) dstar` (the printed definition); "`t_α` is a
  `(1−α)`-quantile of `d⋆(X)` under `P`" is `Wave30tx.IsQuantile P (witFn dstar φ) (1−α) tα` (`R(f < t) ≤ p ≤ R(f ≤ t)`), and likewise `u_α` for
  `Q` at level `α`. (Q), (Q′) are `Wave12c.QDensity` and `Wave12c.QDensityLower` (the forms consumed by the frozen `Wave30tx` and
  `Wave31ta.cor_trimrate_v2` claims; (Q′) has only the lower bound).
* "`P` has a Lebesgue density `p`": `P = volume.withDensity (fun x => ENNReal.ofReal (p x))` with `p : ℝ^d → ℝ` arbitrary off `U` (negative values count as `0`).
  "continuous on a neighbourhood of `L`": an open `U ⊇ L` with `ContinuousOn p U` (the claims quantify over `U`).
* "the gradient of `d⋆` does not vanish": `fderiv ℝ d⋆ x ≠ 0`; `d⋆` is `C¹` (`gaussian_regular`), so `fderiv` is the genuine derivative. "vanishes at
  infinity": `Tendsto f (comap (‖·‖) atTop) (𝓝 0)`. "continuously differentiable": `ContDiff ℝ 1`.
* "the law of `d⋆(X)` has on `[t_α − r_Q, t_α + r_Q]` a density with values in `[c_f, C_f]`" is `QDensity P d⋆ t_α r_Q c_f C_f` (a measurable `g` with
  `c_f ≤ g ≤ C_f` on the window and `P(d⋆⁻¹A) = ∫⁻_A g` for every Borel `A` in the window). "for some `r_Q > 0`" is `∃ rQ, 0 < rQ ∧ …` after the
  data and the quantiles, one `r_Q` for (Q) and (Q′) as printed.

## Covered — back-translations and deviations
* **`qdens_euclid`** (the geometric core, every dimension; the part of the remark that is about the level set). For every `d`, `f, p : ℝ^d → ℝ`
  and open `U`: if `f` is `C¹` with `f(x) → 0` as `‖x‖ → ∞`, `t ≠ 0`, `{f = t} ≠ ∅`, `∇f ≠ 0` on `{f = t}`, `{f = t} ⊆ U`, `p` continuous on `U` and
  positive on `{f = t}`, then there are `r > 0` and `0 < c ≤ C` with `QDensity (p·λ) f t r c C`. Generalisations: `P = p·λ` need not be a probability
  measure; `p` is arbitrary off `U`; no kernel and no quantile. At `d = 1` it is equivalent to `Wave31tc.Claims.qdens_univariate` through
  `x ↦ x 0 : ℝ^1 ≃ ℝ` (proof-file lemma `qdens_univariate_of_euclid`, and the `example` in `RouteSpec`: the `d = 1` instance of this claim reproves the
  certified `Wave31tc` claim; the critic proved the converse in scratch).
* **`gaussian_regular`** (the printed "`d⋆` is infinitely differentiable and vanishes at infinity", `D_trimming.tex:314-316`). For a real Hilbert space `ℋ`
  (complete), `φ : ℝ^d → ℋ` with the Gaussian Gram function and `σ > 0`, every `f ∈ ℋ` gives `x ↦ ⟨f, φ x⟩` of class `C¹` that tends to `0` as `‖x‖ → ∞`.
  **Deviation, declared: `C¹` instead of `C^∞`.** The printed fact is Steinwart–Christmann 2008 Cor. 4.36 (every RKHS function of a smooth kernel is
  smooth) and Thm 4.21 / Lemma 4.23 (decay); only `C¹` and the decay are used by the argument and certified here; `C^∞` is neither proved nor assumed.
* **`qdens_gauss_Q`** ("(Q) holds", `05_trimming.tex:68-70`). In the Gaussian setting (feature map `φ`, `P`, `Q` probability measures, `α ∈ (0,1)`,
  `D_α(P,Q) > 0`, `d⋆` of minimal norm in `𝒞_α(P) − 𝒞_α(Q)`, `t_α` a `(1−α)`-quantile of `d⋆(X)`): if `t_α ≠ 0`, `{d⋆ = t_α} ≠ ∅`, `∇d⋆ ≠ 0` on it, `P = p·λ` with `p`
  continuous on an open `U ⊇ {d⋆ = t_α}` and positive on it, then `∃ r_Q > 0, 0 < c_f ≤ C_f` with `QDensity P d⋆ t_α r_Q c_f C_f`. No smoothness
  hypothesis (it is `gaussian_regular`). The setting hypotheses (`IsQuantile`, `0 < D_α`, `IsMinNorm`, (A1)–(A2), probability measures) are as printed and
  unused by the proof (declared; harmless).
* **`qdens_gauss_Qprime`** ("The same conditions at `u_α` under `Q` give (Q′)", `05_trimming.tex:70`). The same with `u_α` an `α`-quantile of `d⋆(Y)` under `Q`,
  `Q = q·λ`: `∃ r_Q > 0, c′_f > 0` with `QDensityLower Q d⋆ u_α r_Q c′_f`.
* **`qdens_gauss_Q_Qprime`** (the printed conclusion with the common radius: (Q′) is printed with the `r_Q` of (Q), and the proof says "taking `r_Q` below both
  values of `η` makes the radius common", `D_trimming.tex:333-335`). Both sets of conditions together give one `r_Q`, `0 < c_f ≤ C_f` and `c′_f > 0` with
  `QDensity P d⋆ t_α r_Q c_f C_f` and `QDensityLower Q d⋆ u_α r_Q c′_f`. It is the conjunction of the two single claims with one common radius: it follows from
  them by taking the smaller of the two radii (`QDensity` and `QDensityLower` are monotone in the radius), which is how the route proves it; the single claims
  do not follow from it (it needs the conditions on both measures).

**Composition with `cor:trimrate`** (not a separate claim): `qdens_gauss_Q_Qprime` gives (Q), (Q′) with one `r_Q` in the forms (`QDensity`,
`QDensityLower`) that the frozen `Wave31ta.cor_trimrate_v2` consumes; that claim fixes `ρ` before `N`, so `ρ := r_Q` works; its other hypotheses
(probability measures, `0 < α < 1`, `0 < D_α`, `IsMinNorm`, (A1), the quantile hypotheses) are among the hypotheses of `qdens_gauss_Q_Qprime`, so the
rates of `cor:trimrate` apply to every Gaussian-kernel problem satisfying the level-set conditions.

**Proof route** (untrusted; the printed proof `D_trimming.tex:312-335` with the coarea formula and the flow replaced by local straightening).
1. `RouteChart`: for `f : (ι → ℝ) → ℝ` of class `C¹` and a coordinate `i` with `∂_i f(x₀) ≠ 0`, the map `Φ(x) = update x i (f x)` has derivative the identity with
   row `i` replaced by `∇f`, so `det Φ′(x) = ∂_i f(x)` (`det_Φ′`, via `Matrix.det_updateRow_sum`), and is a `C¹` diffeomorphism near `x₀` (inverse function
   theorem, `exists_chart`); `f` is the `i`-th coordinate of `Φ`. `chart_bounds`: if `m|∂_i f| ≤ p ≤ M|∂_i f|` near `x₀`, then for the chart region `R = Φ⁻¹(box)`
   (a sup-norm box of half-width `ε` around `Φ x₀`) and every Borel `A`, `m B λ(A ∩ (t−ε,t+ε)) ≤ P(f⁻¹A ∩ R) ≤ M B λ(A ∩ (t−ε,t+ε))`, `B = (2ε)^{|ι|−1}`: the change of
   variables formula with `g = 1` gives `λ(Φ(f⁻¹A ∩ R)) = ∫_{f⁻¹A ∩ R} |∂_i f|`, and `Φ(f⁻¹A ∩ R) = box ∩ {y_i ∈ A}` has volume `B λ(A ∩ (t−ε,t+ε))` (`volume_box`).
2. `RouteCorePi`: at each point of the level set `L` a chart (`local_chart`: `∂_i f ≠ 0`, `p` continuous and positive, so `|∂_i f|` and `p` are within a factor 2 of their
   values near the point, hence the ratio bounds); `L` is closed in the compact band, so finitely many chart regions `R_x` cover it; the band `{|f − t| ≤ r}`
   lies in `⋃ R_x` for small `r` (`exists_band_subset`: the minimum of `|f − t|` on the compact band minus `⋃ R_x`; this is the printed "some band `B_η` lies in `U`");
   for Borel `A ⊆ [t−r, t+r]`: `P(f⁻¹A) ≤ Σ_x P(f⁻¹A ∩ R_x) ≤ (Σ_x M_x B_x) λ(A)` and `P(f⁻¹A) ≥ P(f⁻¹A ∩ R_{x₁}) ≥ m_{x₁} B_{x₁} λ(A)` for one point `x₁ ∈ L`.
3. `RouteDensity`: Radon–Nikodym: two-sided bounds `c λ ≤ P∘f⁻¹ ≤ C λ` on the window give a density, the derivative of the restriction of the image measure with
   respect to Lebesgue measure on the window (`Measure.withDensity_rnDeriv_eq`, `ae_le_of_forall_setLIntegral_le_of_sigmaFinite`), clamped to `[c, max c C]`.
4. `RouteCore`: transfer from `Fin d → ℝ` to `EuclideanSpace ℝ (Fin d)` by `EuclideanSpace.equiv` (`PiLp.volume_preserving_ofLp`, `MeasurePreserving.setLIntegral_comp_preimage_emb`);
   the band `{|f − t| ≤ |t|/2}` is compact (closed, and bounded because `f → 0`; the printed "the band is compact"); `∇f ≠ 0` gives a coordinate with `∂_i ≠ 0`. The three
   Gaussian claims: `qdens_euclid` and `gaussian_regular`, one half-width the minimum of the two (`QDensity_mono'`).
5. `RouteGauss`: `‖φ x − φ y‖² = 2 − 2exp(−‖x−y‖²/(2σ²)) ≤ ‖x−y‖²/σ²`, so `φ` is `1/σ`-Lipschitz and `F_f = ⟨f, φ ·⟩` is `‖f‖/σ`-Lipschitz, hence `‖F_f′‖ ≤ ‖f‖/σ` whenever `F_f` is `C¹`.
   `{f | F_f is C¹}` is a closed submodule: if `f_n → f` with `F_{f_n}` of class `C¹`, then `F_{f_n} → F_f` pointwise and `F_{f_n}′` is uniformly Cauchy
   (`F_{f_n} − F_{f_m} = F_{f_n − f_m}`), so converges uniformly to a continuous `g′` and `hasFDerivAt_of_tendstoUniformly` gives `F_f′ = g′`. It contains every `φ y`
   (`F_{φ y}(x) = exp(−‖y−x‖²/(2σ²))`) and every `f` orthogonal to the span of the `φ y` (`F_f = 0`), and the span together with its orthogonal complement is dense in the complete
   `ℋ` (`Submodule.topologicalClosure_eq_top_iff`), so the submodule is everything. The decay is the same argument with the closed submodule `{f | F_f → 0}`.

## Junk-value audit
* `fderiv ℝ f x ≠ 0` is a hypothesis; at a point where `f` is not differentiable `fderiv = 0`, so the hypothesis can only exclude such `f`; `qdens_euclid` assumes `f` is `C¹` and the Gaussian
  claims get it from `gaussian_regular`.
* `volume.withDensity (ofReal ∘ p)` with `p` possibly non-measurable and negative off `U`: `withDensity_apply` needs only a measurable set, and the proof reads `P` only on
  `f⁻¹[t−r,t+r] ⊆ U` (a measurable set inside `U`, where `p` is continuous). `ofReal` of a negative number is `0` (declared encoding).
* `QDensity` is the frozen predicate; `Measure.map` is not used in the statements; in the proof `Measure.map f P` is taken for the continuous (hence measurable) `f`, genuine.
* `IsQuantile` uses `Measure.real` of probability measures (no `toReal ⊤`); `Dpop` is a `sInf` of a nonempty set bounded below by `0` for `α ∈ (0,1)` (`0 < Dpop` also rules out `sInf ∅`).
* `ENNReal` constants in the proof: `B = ∏_{j≠i} ofReal(2ε)` is finite and positive; every `toReal` is of a finite quantity.
* Vacuity: `qdens_euclid` at `d = 2`, `f(x) = exp(−‖x‖²)`, `t = ½`, `p` the standard normal density, `U = ℝ²` satisfies every hypothesis (`L` the circle `‖x‖² = log 2`; proved in
  Lean by the critic, in scratch); at `d = 1` the Wave 31tc witness `h = e^{−x²}`. The Gaussian claims: `d = 1`, `σ = 1`, `P = N(−2,1)`, `Q = N(2,1)`, `α = 0.2` (numerical, above). `gaussian_regular`: the canonical
  feature map `φ(x) = k(·, x)` of the Gaussian RKHS.

## Defects in the printed text
None: the remark is true as printed (and the proof of `D_trimming.tex:312-335` is correct; the critic and this wave re-derived it). Remarks for the author (wording, not formal):
1. The remark says `d⋆` is infinitely differentiable; the argument needs only `C¹`, which is what is certified (`gaussian_regular`).
2. Positivity of `p` on the whole level set is not needed for (Q): `p > 0` at a single point of `L`, with `p` continuous near `L`, suffices (the lower bound `c_f > 0` comes from one chart at that
   point; the upper bound needs only the boundedness of `p/|∇d⋆|` near the compact `L`). The formal proof takes two-sided chart bounds at every point of `L`, using `p > 0` there for
   convenience; only the upper bounds at all points and the lower bound at one point enter. The printed proof uses positivity on all of `L` to make `h` positive. The statement as printed is
   certified (the hypothesis is stronger than necessary).
3. The proof can avoid the coarea formula and the flow: near `x ∈ L` with `∂_i d⋆(x) ≠ 0`, `y ↦ (y with the i-th coordinate replaced by d⋆(y))` is a `C¹` diffeomorphism in which `d⋆` is a
   coordinate, so `P(d⋆(X) ∈ A ∩ chart)` lies between multiples of `λ(A)`; finitely many charts cover the compact `L` (upper bound), one chart gives the lower bound; this gives
   (Q) directly. The formula `h(t) = ∫_{d⋆=t} p/|∇d⋆| dℋ^{d−1}` and its continuity are then not needed for (Q).
4. The proof's last sentence ("taking `r_Q` below both values of `η`") is the common radius, certified as `qdens_gauss_Q_Qprime`.

## Certified results reused (not re-proved)
Definitions only: `Wave12c.QDensity`, `QDensityLower`, `witFn`, `Wave30tx.IsQuantile`, `TrimmedMMD.Projection.IsMinNorm`, `Concentration.region`, `Unconditional.Dpop`; and, in `RouteSpec` only, the claim
`Wave31tc.Claims.qdens_univariate` (the target of the specialisation lemma). Mathlib: `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, `HasStrictFDerivAt.toOpenPartialHomeomorph`,
`ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`, `Matrix.det_updateRow_sum`, `LinearMap.det_toMatrix'`, `volume_pi_pi`, `Measure.withDensity_rnDeriv_eq`,
`ae_le_of_forall_setLIntegral_le_of_sigmaFinite`, `hasFDerivAt_of_tendstoUniformly`, `contDiff_one_iff_hasFDerivAt`, `norm_fderiv_le_of_lipschitz`,
`Submodule.topologicalClosure_eq_top_iff`, `PiLp.volume_preserving_ofLp`, `IsCompact.elim_nhds_subcover`. **No textbook bridge is declared**: neither the coarea formula nor the
Steinwart–Christmann facts are assumed.

## Not covered (declared)
* The infinite differentiability of `d⋆` (Steinwart–Christmann Cor. 4.36): only `C¹` is proved and used.
* The coarea formula and the Hausdorff-measure expression `h(t) = ∫_{d⋆=t} p/|∇d⋆| dℋ^{d−1}` for the density of `d⋆(X)`, its continuity (the printed flow argument) and positivity:
  not claimed; (Q) is certified as the existence of a density in `[c_f, C_f]` (`QDensity`), which is what the remark states ("then (Q) holds") and what the specification asks. For `d = 1`
  the explicit continuous density `Σ_{x : d⋆(x) = t} p(x)/|d⋆′(x)|` is certified in Wave 31tc (`qdens_formula`); there is no `d ≥ 2` counterpart.
* "`L` is compact" in every dimension: certified in Wave 31tc (`level_compact`); the compact band is re-proved inside the route (`band_compact_euclid`) but not stated as a claim here.
* The quantile hypotheses, `0 < D_α` and the minimal-norm property are hypotheses of the Gaussian claims (as printed) but are not used by the proofs.
* `α = 0` is outside the claims (`0 < α` as in the specification).

## Coverage note (COVERAGE.md row)
`rem:qdens`: "certified in every dimension d (Waves 31tc, 31th): for the Gaussian kernel on R^d (feature map with Gram function exp(-|x-y|^2/(2 sigma^2))), t_alpha != 0, {d* = t_alpha} nonempty, grad d* != 0 on it, P with a density
continuous near it and positive on it give (Q) (QDensity, a density in [c_f, C_f] on [t_alpha - r_Q, t_alpha + r_Q]), the same at u_alpha under Q gives (Q'), with one common r_Q; no coarea bridge (local straightening: inverse function
theorem, change of variables, finite cover of the compact level set, Radon-Nikodym); the Gaussian-RKHS facts are proved at the C^1 level (C^infty is not claimed); the Hausdorff-measure density formula and the continuity of h are not
claimed; d = 1 also with the explicit density (Wave31tc)".

## AI audit notes (2026-11-12, PASS with notes; applied)
1. The `qdens_gauss_Q_Qprime` bullet said it does not follow from the two single claims; it does, by taking the smaller radius (`QDensity`, `QDensityLower` are monotone in the radius), as `RouteCore`
   proves it; only the converse fails. Reworded.
2. Remark 2 for the author: the formal proof takes two-sided chart bounds at every point of `L`, using `p > 0` there for convenience; only the upper bounds at all points and the lower bound at one
   point enter (the remark itself, that positivity at a single point suffices for (Q), is right). Reworded.
3. Specification attribution: the verbatim sentence of `NEW_STATEMENTS.md:206-208` and the adopted reading are now on this card (Decision on the route); the phrase "nor anything that restates (Q)" in
   the frozen docstring comes from the second write-up (`6fe8200`, lines 266–267), recorded.
4. Recorded: the audit independently replicated the Gaussian numerics (a projected-gradient quadratic program, `d = 1`, `σ = 1`, `P = N(−2,1)`, `Q = N(2,1)`, `α = 0.2`: `D_α = 0.9683`, `t_α = −u_α = 0.6132`,
   level set `{−2.320, −1.805}`, slopes `+0.0619, −0.0672`; also `α = 0.35`: `{−2.55, −1.60}`, slopes `+0.054, −0.075`; at `α = 0.5` the level set is near-degenerate, so the nondegeneracy hypothesis is a real
   restriction), re-proved the `d = 1` converse (the `d = 1` instance of `qdens_euclid` and `Wave31tc.Claims.qdens_univariate` imply each other, so "equivalent" is exact), and checked that excluding `α = 0`
   loses nothing (there a `1`-quantile forces `P(d⋆ > t_α) = 0`, while `∇d⋆ ≠ 0` and `p > 0` on `L` force `P(d⋆ > t_α) > 0`: the hypotheses are contradictory).
