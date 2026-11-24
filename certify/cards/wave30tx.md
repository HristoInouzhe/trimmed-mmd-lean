# Fidelity card — wave 30tx: trimmed-mmd (JMLR v2), a parametric rate for the witness and the kept set (`sec:trimrate`), the contact level and the data-driven level (`sec:nearcontact`, `supp:trimrate`)

Lean: `StatFormal/Wave30tx/Statements.lean` (14 claims; frozen 2026-11-08, sha256
`bf8de00fe22d3ea2d9f6c2dff99727800412869d3ec3ba30d32553dbe979182c`, locked with its 21 imports: the frozen `TrimmedMMD` files
(`Statements`, `Concentration`, `Unconditional`, `BangBang`, `Projection`, `ZeroSet`), `Wave4b`, `Wave8a`, `Wave12c` (and through it the ICL,
NN and RobustEquality statement files it imports), `Wave30tl`, `Wave30tp`, `Wave30tr`, `Wave30tu`, `Lib/Distances/TV.lean`). Routes
`RouteBasic`, `RouteSep`, `RouteBasicIneq`, `RouteLocal`, `RouteRate`, `RouteCor`, `RouteContact`, `RouteAlpha`, `RouteNearA`, `RouteNearB`
(untrusted); `Proofs.lean` checks all 14 claims. Paper id `trimmed-mmd (jmlr)`; labels are the paper's with " (v2)".
Branch `tmmd-jmlr-trimrate`, based on `tmmd-jmlr-cont` at `4a5339d` (waves 30tl, 30tp, 30tr, 30ts, 30tu, 30tw), with `tmmd-jmlr-split`
(wave 30tn, for `lem:popthreshold`) merged at `953422e`.
Critic (independent AI reviewer, before the freeze, 2026-11-08): 14 claims ACCEPT (two with notes), none false, no counterexample; it
re-derived every constant of `thm:trimrate`, `lem:localmod`, `cor:trimrate` and the proofs' steps. Applied: line references, the
declaration of the σ-finite base measure, the source-drift note.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes (14 claims back-translated
blind and compared with the printed text at `c3ba305`; deviations are declared generalisations, one declared specialisation and declared
additions; notes at the end of this card).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
Frozen from `trimmed-mmd/jmlr/` at master `c3ba305` ("JMLR v2: localized rate for the witness and the kept set (author decision Q8)").
Read-only, read 2026-11-08. sha256 at `c3ba305`:

| file | sha256 |
|---|---|
| `sections/08_trimming.tex` | `ffd387786fba48547d2272de7031d8998de54f43cee0b9bd0788a7b5a2fd0f9f` |
| `appendix/C_recover.tex` | `3488f8e8921ae4ef743104783e77793b6140902b8c701d59d4801558dd01f107` |
| `sections/03_regions.tex` (context) | `b9673cf0c477f8c1272c6866130075938e875cd35175716c17cb757b3a17798b` |
| `sections/04_test.tex` (context) | `bbd28b351d253f1ec3ad801ab38f9061d7e00a6fc2239f501e736ec433107a3e` |
| `sections/05_estimator.tex` (context) | `20507b945964920aad419c22f34011af12ca0bcaaaa827917f2e16d4580fcf83` |
| `sections/01_introduction.tex` (context) | `b425c1539c2b544a1d81281d62b3fe860d10a846e58b4324543e672bd48acb17` |
| `sections/06_splitting.tex` (context) | `f734a7fb3b8451f399d2c9841b1e1ca35e524e6dc3f19f03dd0a766849e318bf` |
| research note `explore/trimming_rate/NOTE.md` (comparison only) | `a687385d76b1fd7236df06c84e8e1ce88b0172e7b14a918c6e9bae920c515757` |

The paper's master moved to `c339b9d` during the wave; `08_trimming.tex`, `C_recover.tex`, `03_regions.tex` and `05_estimator.tex` are
byte-identical there; `04_test.tex` changed only in prose at `:214-218`, and `01_introduction.tex` and `06_splitting.tex` only in prose
outside the cited passages (`eq:trimset` at `01:12-19` and `eq:sep` at `06:19-30` are byte-identical).
Later in the day (commits `7b6983e`, `2dc9777`, `8e3b6ac`, and uncommitted edits of a length-reduction pass in the paper's working tree)
the committed `08_trimming.tex` and `C_recover.tex` were still the `c3ba305` files; in the working tree the frozen statements had changed
only in wording (`thm:trimrate`: "with `β` there equal to `(1−α)⁻¹`", which is the frozen `τ^A`; `cor:trimrate`: `c` inlined as
`min(c_f,c'_f)`; `rem:nearcontact`(a): "neighborhood"), and the proofs' prose was being shortened. Line numbers below are at `c3ba305`.

Target passages: `08_trimming.tex:232-319` (`sec:trimrate`: `thm:trimrate` `:254-291` with (Q) = `eq:qdens` `:196-201` and (Q′) =
`eq:qdensY` `:258-263`, `cor:trimrate` `:307-319`), `:321-394` (`sec:nearcontact`: lead-in `:331-335`, `rem:nearcontact` `:336-350`, `ω_c`
`:364-368`, `prop:alphahat` `:370-385`); `C_recover.tex:333-789` (`supp:trimrate`: notation and `eq:twotail` `:345-366`, `lem:sepmargin`
`:367-379`, `lem:basicineq` `:395-411`, `lem:localmod` `:454-478`, the proofs with `eq:basicZ` `:569-573`, the lead-in of `lem:contact`
`:659-660`, `lem:contact` `:662-668`, the remark's proof with `C_α` at `:712-714` and Step 4 at `:729-730`).

## Certified results reused (not re-proved)
* **Theorem A** (`thm:twosided`, `τ^A`, events `E^±`; wave 30tr): `Wave30tr.thmA`, `thmA_twosided` (events at `δ/5`, resp. the
  corollary's split), `ek_le` (`e_k ≤ k^{−1/2}`).
* **Concentration library** (`Lib/Concentration`, wave 30tr/30tp): two-sample symmetrisation for a joint supremum
  (`integral_iSup_empDev2_le`), coordinatewise contraction with sample-dependent 1-Lipschitz maps (`signE_iSup_contraction`),
  `signE_norm_sum_le`, the marginals `signE_comp_inl/inr`, and `Wave30tp.mcdiarmid_two_sample`.
* **thm:trimconsist** (trimmed-mmd, `Wave12c.trimconsist`, certified with `[MeasurableSingletonClass 𝒳]`): its route lemmas
  (`hoeffding_cdf`, `empCdf`, `margins`, `tHat_bounds`, `band_incl`, `density_upper`, `quantile_*`) are reused; its event is rebuilt
  (`RRate.consist_event`) on **prop:witnessstab** in the form `Wave30az.witnessstab_gen` (no measurable singletons), so that the tie set
  `{d̂ = t̂_n}` lies in the band (needed for the `min` band of `trimrate_inter`, and not among the printed conclusions).
* **prop:bangbang (i)** / **prop:georep**: `Wave30az.witness_isMinNorm_gen` and `Wave8a.georep_empirical` (the QP witness is the
  minimum-norm element of `𝒞_α(P_n) − 𝒞_α(Q_m)`, so `D̂ = ‖d̂‖`); **lem:projstab** is not needed (the localisation replaces it).
* **lem:popthreshold** (wave 30tn, merged): `Wave30tn.popthreshold` (rem. (a), Step 2) and its route lemmas `foc`, `trimDensity_bound`.
* **eq:zeroeq** (`ZeroSet.zeroeq`, `zero_of_tv_le`), **lem:continuity** (`Wave18b.continuity_lip`), **lem:attainment**
  (`Wave11b.attain_closed`, `attain_convex`, `attain_bounded`, `attain_common`), **cor:uniform** (`TrimmedMMD.Concentration.uniform_alpha`),
  `Distances.tvDist_eq_one_sub_integral_min`, `tvDist_le_one`.
* **Estimator side** (wave 30tu): `consistency_i` (`thm:consistency`(i)), `crossing`, `crossing_meas` (`lem:crossing`), `tauRight_spec`,
  `tau_sched` (the schedule bound of `cor:consistency`).

## Covered (14 claims), with back-translation
Notation: `β̄ = (1−α)⁻¹`; `𝒞_α(R) = region φ α R`; `D = D_{α,k}(P,Q) = Dpop`; `D̂ = D̂_{α,k} = Demp`; `d*` any minimum-norm element of
`𝒞_α(P) − 𝒞_α(Q)`; `d̂ = Σw_iφ(X_i) − Σv_jφ(Y_j)` at any minimiser `(w,v)` of `eq:qp` over `Δ_α(n) × Δ_α(m)`; `f(x) = ⟨f, φ(x)⟩`;
`t_α = quantileAt` (lower `(1−α)`-quantile of `d*(X)`); `t̂_n = tHat` (the `(⌊n(1−α)⌋+1)`-th smallest `d̂(X_i)`); `Â_n = {d̂ < t̂_n}`,
`A* = {d* < t_α}`; `ĝ_n`, `g*` the plug-in densities with arbitrary tie functions `ϑ̂, ϑ : 𝒳 → [0, β̄]`. Samples `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}`
(`sampleLaw`).

* `sepmargin` (`lem:sepmargin`). For `K ⊆ 𝓗` convex with minimum-norm element `d*`, `D = ‖d*‖ > 0`, `f* = d*/D`, and
  `sep_K(f) = inf_{z∈K}⟨f,z⟩ ∈ [−∞,∞)`: `sep_K(f) ≤ ⟨f,d*⟩` for all `f`; `sep_K(f*) = D`, and `D` is the greatest value of `sep_K` on the
  closed unit ball; `sep_K(f*) − sep_K(u) ≥ (D/2)‖u − f*‖²` for every unit `u`; `‖d' − d*‖² = (‖d'‖−D)² + ‖d'‖D‖d'/‖d'‖ − f*‖²` for
  every `d' ≠ 0`.
* `basicineq` (`lem:basicineq`). Under (A1)–(A2), `α ∈ (0,1)`, `n, m ≥ 1`, `D > 0`, `t*` a `(1−α)`-quantile of `f*(X)` and `u*` an
  `α`-quantile of `f*(Y)` (`f* = d*/D`): for every realisation and minimiser with `D̂ > 0`, with `f̂ = d̂/D̂`, `t̂` the `(n_α+1)`-th smallest
  `f̂(X_i)`, `û` the `(m_α+1)`-th largest `f̂(Y_j)` and `ξ(f) = sep(f; 𝒞_α(P_n), 𝒞_α(Q_m)) − sep(f; 𝒞_α(P), 𝒞_α(Q))`:
  `(D/2)‖f̂−f*‖² ≤ ξ(f̂) − ξ(f*) ≤ β̄[(P−P_n){(t̂−f̂)₊ − (t*−f*)₊} + (Q−Q_m){(f̂−û)₊ − (f*−u*)₊}]`.
* `localmod` (`lem:localmod`). Under (A1)–(A2), for `f* ∈ 𝓗`, `t*, u* ∈ ℝ`, `r, λ₁, λ₂ ≥ 0`, `n, m ≥ 1`, with
  `Z(r) = sup{(P−P_n)h₁ + (Q−Q_m)h₂ : ‖f−f*‖ ≤ r, |t−t*| ≤ κr+λ₁, |u−u*| ≤ κr+λ₂}`, `h₁ = (t−f)₊ − (t*−f*)₊`, `h₂ = (f−u)₊ − (f*−u*)₊`:
  `Z(r)` is a measurable function of the samples, `≥ 0`, an upper bound of every bracket of the class, nondecreasing in `r ≥ 0`, integrable,
  `E Z(r) ≤ 2[κr√s + (κr+λ₁)e_n + (κr+λ₂)e_m]`, and for every `χ > 0`, `P(Z(r) ≤ κrL(χ) + M(χ)) ≥ 1 − e^{−χ}` with
  `L(χ) = 2√s + 2(e_n+e_m) + 2√(2χs)`, `M(χ) = 2(λ₁e_n + λ₂e_m) + √(2χ(λ₁²/n + λ₂²/m))`.
* `trimrate` (`thm:trimrate` (i)–(iii)). Under (A1)–(A2), `α ∈ (0,1)`, `D > 0`, (Q) at `t_α` with `ρ, c_f, C_f`, (Q′) at an `α`-quantile
  `u_α` of `d*(Y)` with `c'_f` (same `ρ`), `n, m ≥ 1`, `δ ∈ (0,1)`, `θ > 1`, any bound `D_φ` on `‖φ(x)−φ(x')‖`, and the printed
  `τ^A = τ^A_{n,m}(α,δ/5)`, `λ_X`, `λ_Y`, `J`, `χ`, `L_{n,m}`, `M_{n,m}`, `ζ^loc`, `ℓ^loc`: if `τ^A < D` and `max(λ_X,λ_Y) ≤ ρ`, there is a
  measurable event of probability `≥ 1−δ` on which, at every minimiser: (i) `D̂ > 0` and `‖d̂/D̂ − d*/D‖ ≤ ζ^loc/D`; (ii)
  `‖d̂ − d*‖ ≤ τ^A + √(1+τ^A/D) ζ^loc`; (iii) `|t̂_n/D̂ − t_α/D| ≤ (κζ^loc + λ_X)/D`, `Â_n △ A* ⊆ {|d* − t_α| ≤ ℓ^loc}`, and if `ℓ^loc ≤ ρ`,
  `P(Â_n △ A*) ≤ 2C_fℓ^loc` and `∫|ĝ_n − g*| dP ≤ 2C_fℓ^loc/(1−α)` for all tie functions.
* `trimrate_inter` (last sentence). Same hypotheses: there are measurable events `E₁`, `E₂` with `P(E₁), P(E₂) ≥ 1−δ`, `P(E₁∩E₂) ≥ 1−2δ`;
  (i)–(iii) on `E₁`; if `η < D` and `ℓ_{n,m} ≤ ρ` (`η`, `ζ_{n,m}`, `ℓ_{n,m}` of `thm:trimconsist`), the conclusions of `thm:trimconsist`
  (`|t̂_n − t_α| ≤ ℓ_{n,m}`, inclusion, mass, density) on `E₂`, and on `E₁∩E₂` the inclusion, mass and density bounds with
  `min(ℓ_{n,m}, ℓ^loc)`.
* `trimrate_A3` (the parenthetical). Under (A1)–(A3), `D_{α,k}(P,Q) > 0` for every `α ∈ [0, TV(P,Q))`.
* `cor_trimrate` (`cor:trimrate`). For every `ε ∈ (0,1)` there is `Λ > 0` such that for every `(𝒳, 𝓗, φ, κ, P, Q, α)` and constants
  `ρ, c_f, C_f, c'_f` satisfying the hypotheses of `thm:trimrate` there is `N` with: for `n, m ≥ N` there is a measurable event of
  probability `≥ 1−ε` on which, at every minimiser, `D̂ > 0`, `‖d̂/D̂ − d*/D‖ ≤ ΛV_α/(Dq)`, `‖d̂ − d*‖ ≤ ΛV_α/q`,
  `P(Â_n △ A*) ≤ ΛC_f(κV_α + c_f⁻¹)/q` and `(1−α)∫|ĝ_n − g*| dP ≤ ΛC_f(κV_α + c_f⁻¹)/q` for all tie functions; `q = √(n∧m)`,
  `V_α = κ/(1−α) + [(1−α)min(c_f,c'_f)]^{−1/2}`.
* `contact_compact` (`lem:contact`, first sentence). Under (A1)–(A2), `𝒞_α(P)` is norm-compact for every `α ∈ [0,1)`.
* `contact` (`lem:contact` with its lead-in). Under (A1)–(A3) and `α* = TV(P,Q) < 1`: `P ⊓ Q` is the greatest measure below `P` and
  `Q` and has mass `1 − TV(P,Q)`; `R* = (1−α*)⁻¹(P ⊓ Q)` lies in `R_{α*}(P) ∩ R_{α*}(Q)` and is its only element;
  `𝒞_{α*}(P) ∩ 𝒞_{α*}(Q) = {μ_{R*}}`; `ω_c(ε) → 0` as `ε ↓ 0`.
* `nearcontact_densities` (lead-in of the remark). For `P = p·μ`, `Q = q·μ` probability laws (`μ` σ-finite, `p, q ≥ 0` measurable) with
  `TV < 1`: `P`-a.e., `dR*/dP = β*min(p,q)/p`, `0 < dR*/dP < β* ⇔ 0 < q < p`, and `q ≥ p > 0 ⇒ dR*/dP = β*`.
* `nearcontact_a` (`rem:nearcontact`(a)). Under (A1)–(A3), `0 < α* < 1`, `P(0 < dR*/dP < β*) > 0`, population witnesses `d*_α` for
  `α ∈ [0,α*)`, `f*_α = d*_α/D_α`, `(1−α)`-quantiles `s_α` of `f*_α(X)`: if `P(f*_α = s_α) = 0` for all `α` in a left neighbourhood of
  `α*`, then along no sequence `α_j ↑ α*` (`α_j < α*`) do the indicators of `A*_{α_j} = {f*_{α_j} < s_{α_j}}` converge in `L¹(P)` to an
  integrable `h`, and for every `ρ > 0`, `inf{C ∈ [0,∞] : P(f*_α ∈ B) ≤ C·Leb(B) ∀ Borel B ⊆ [s_α−ρ, s_α+ρ]} → ∞` as `α ↑ α*`.
* `nearcontact_b` (`rem:nearcontact`(b)). Under the same lead-in hypotheses, `𝒳 = ℝ^d`, `⟨φx, φy⟩ = exp(−‖x−y‖²/(2σ²))`, `P, Q` with
  continuous densities `p, q` (Lebesgue) and `{0 < q < p} ≠ ∅`: `‖f*_α‖ = 1`; `⟨f*_α, h⟩ → 0` for every `h ∈ 𝓗` as `α ↑ α*`;
  `P(|f*_α(X)| ≥ η) → 0` for every `η > 0`; `s_α → 0`; for every `ρ > 0` the best lower density bound (`densLower`) on
  `[s_α−ρ, s_α+ρ]` tends to `0` and the smallest upper bound (`densUpper`) to `∞`.
* `alphahat` (`prop:alphahat`, finite-sample part). Under (A1)–(A3), `0 < α* < 1`, `δ, δ' ∈ (0,1)`, `n, m ≥ 1`, a threshold `τ` valid at
  level `δ`, nondecreasing, continuous on `(0,1)`, with nonempty crossing set for every realisation, `r_n = r_n(α*,δ')`, `r_m = r_m(α*,δ')`:
  `ω_c → 0`; there is a measurable `E` of probability `≥ 1−2δ'`, contained in the two `cor:uniform` events at `δ'`, on which for every
  `α̃ ∈ [0, α*]` and every minimiser `(w,v)` of `eq:qp` at `α̃`: `‖μ_{Σw_iδ_{X_i}} − μ_{R*}‖ ≤ r_n + ω_c(D̂_{α̃} + r_n + r_m)` and
  `‖μ_{Σv_jδ_{Y_j}} − μ_{R*}‖ ≤ r_m + ω_c^{Q,P}(D̂_{α̃} + r_n + r_m)`; `{α̂ ≤ α*}` is measurable, `P(E ∩ {α̂ ≤ α*}) ≥ 1−δ−2δ'`, and on it
  `D̂_{α̂} ≤ τ(α*)` and both bounds hold at `α̃ = α̂`.
* `alphahat_schedule` (`prop:alphahat`, schedule sentence). Same kernel hypotheses; along any filter of indices with `δ_i → 0` and
  `log(1/δ_i)/min(n_i,m_i) → 0`, thresholds `τ_{n,m,d}` valid at level `d`, continuous on `(0,1)`, with nonempty crossing sets and
  `≤ r_n(·,d/2) + r_m(·,d/2)`: for every `e > 0` there are measurable events `E_i`, of probability `→ 1`, on which both MMDs at `α̂_i` are
  `≤ e` for every minimiser.

## Deviations (declared)
* **Generalisations.** No `[MeasurableSingletonClass 𝒳]` (the earlier `Wave12c`/`Wave4b` claims assume it; `Wave8a.region_empirical`
  needs none). `D_φ` any bound on `‖φ(x)−φ(x')‖` (as in `Wave30tr`); `d*` any minimum-norm element; `u_α`, `t*`, `u*` any quantile of the
  printed level; tie functions arbitrary (printed: "a function fixing `E_P[g*] = 1`", resp. "any tie function"; the earlier
  `thm:trimconsist` claim used constants), the normalisation not used. `sepmargin`: `K` need not be closed, `𝓗` need not be complete.
  `trimrate_A3` includes `α = 0`. `contact_compact`: (A3) not assumed. `alphahat`: any valid, nondecreasing threshold, continuous on
  `(0,1)`, with nonempty crossing sets (the paper's `τ_{n,m}` has these properties: `Wave30tu` `tauFull*` valid and `≤ τ^A`, `Wave30tw`
  continuity and `CrossingFacts`); `alphahat_schedule`: in addition `≤ r_n(·,d/2)+r_m(·,d/2)` (as in `Wave30tu.cor_consistency`; the paper's
  `τ_{n,m} ≤ τ^A ≤` that bound by `eq:tauA`). `nearcontact_b`: `𝓗` any separable Hilbert space carrying the Gaussian Gram matrix (the
  printed RKHS is the instance; `f*_α` lies in the closed span of `φ(ℝ^d)`, isometric to the RKHS).
* **Specialisations.** `nearcontact_densities` takes the densities with respect to a σ-finite `μ` (any pair of laws has densities with
  respect to `μ = P + Q`, which is finite, so nothing is lost). The lead-in facts of `lem:contact` (`P ⊓ Q` greatest below both, mass
  `1 − TV(P,Q)`; printed unconditionally at `C_recover.tex:659-660`) are certified inside `contact`, i.e. under the lemma's hypotheses
  ((A1)–(A3), `α* < 1`); the route lemma `RContact.inf_univ` proves the mass identity for any two probability laws.
* **Additions** (true, not printed): `localmod` also states that `Z(r)` bounds every bracket of `𝓗(r)` (so the real supremum is not a
  junk value) and that `Z(r)` is integrable; `contact` states the lead-in sentence (`P ⊓ Q` greatest below both — true by the definition
  of `⊓` in Mathlib's lattice of measures, an encoding check — and of mass `1 − TV`); `cor_trimrate` uses one event and one factor for
  all four statements (equivalent to four separate `O_P` statements).
* **Lead-in hypotheses kept.** `nearcontact_b` keeps the remark's lead-in hypotheses (`0 < α* < 1`, (A1)–(A3), `P(0 < dR*/dP < β*) > 0`)
  as printed; the proof does not use the last one (or `σ > 0`).

## Encodings and junk-value audit
* `sepK` is an `EReal` infimum: `−∞` when `K` is unbounded below in the direction, so `sep_K(f) ≤ ⟨f,d*⟩` and the margin are meaningful
  (`D − (−∞) = +∞`); `K ∋ d*` is nonempty, so `sepK ≠ +∞`.
* `sepAB` (`eq:sep`) is a real `sInf − sSup`, used only on the regions, which are nonempty (`g ≡ 1`; `n, m ≥ 1`) and norm-bounded by `κ`.
* `Zloc` is a real `⨆` over `rampPar`, nonempty (`(f*,t*,u*)`, `κ ≥ 0`) and with brackets bounded by `2(2κr+λ₁) + 2(2κr+λ₂)`; the
  claim also states the upper-bound property explicitly. Monotonicity is on `r ≥ 0` only.
* `popDev` integrands are bounded and measurable; the expectation bound is accompanied by integrability of `Z(r)`.
* `ord`/`kfloor`/`ordTop`: for `α ∈ (0,1)` and `n, m ≥ 1`, `kfloor n α < n`, so `ord` is evaluated in range and `m − kfloor m α − 1` has
  no ℕ-truncation; `(n_α+1)`-th smallest = `ord _ (kfloor n α)` (0-indexed), `(m_α+1)`-th largest = `ord _ (m − m_α − 1)`.
* `Jpeel` uses `⌈·⌉₊` of a positive real (`log(2√(n∧m)) > 0`, `log θ > 0`), equal to the printed ceiling; `θ^{−J}` is `(θ^J)⁻¹`.
* Divisions by `D` and `D̂`: `D > 0` is a hypothesis; `D̂ > 0` is a conclusion ((i)) and a hypothesis of `basicineq`.
* Tie functions are unrestricted; for a non-measurable choice the Bochner integral is `0` and the bound holds trivially (the
  right-hand side is `≥ 0`), for measurable ones it is the printed bound.
* `P ⊓ Q` is Mathlib's lattice infimum; `R* = ENNReal.ofReal((1−α*)⁻¹) • (P ⊓ Q)`, with `α* < 1`. `trimSet` = `eq:trimset` (probability,
  `≪ P`, `dR/dP ≤ (1−α)⁻¹` a.e.). `ω_c` is a real `sSup`, evaluated only at `ε ≥ 0` (nonempty: `μ_{R*}`; bounded by `κ + ‖μ_{R*}‖`).
* `dR*/dP` is `rnDeriv`, used through `toReal` only in a.e. statements or inside a positive-mass set; `p x = 0` in `β*min(p,q)/p` occurs
  only on a `P`-null set.
* `densUpper` = `sInf` in `[0,∞]` (`sInf ∅ = ∞` = "no finite bound", the printed reading of the smallest constant `C_α ∈ [0,∞]`);
  `densLower` = `sSup` in `[0,∞]` (`0` always admissible).
* "No limit point in `L¹(P)`": no integrable `h` and no sequence `α_j → α*`, `α_j < α*`, with `∫|1_{A*_{α_j}} − h| dP → 0`
  (integrability of `h` is required, otherwise the Bochner integral would be the junk `0`). Equivalent to "no cluster point" in the metric
  space `L¹(P)`.
* `wEmp w x = Σ ofReal(w_i)•δ_{x_i}`, for `w ≥ 0` on the capped simplex; `∫φ d(wEmp w x) = Σw_iφ(x_i)` (route lemma `integral_wEmp`).
* `hausdorffDist` of nonempty bounded regions (no junk).
* Convergence in probability (`alphahat_schedule`): measurable inner events of probability `→ 1` (encoding of `Wave30tu.cor_consistency`).

## Non-vacuity
`trimrate`/`cor_trimrate`: `𝒳 = [0,3]`, `φ(x) = x ∈ ℝ`, `P = U[0,1]`, `Q = U[2,3]`, `α ∈ (0,1)`: `d* = −(2−α)`, both laws uniform near
their quantiles (critic's example). `nearcontact_*`: e.g. Gaussian kernel on `ℝ`, `P = N(0,1)`, `Q = N(1,1)`: continuous densities, `{0<q<p}`
open nonempty, `0 < TV < 1`, the contact trimming fractional where `0<q<p`. `contact`/`alphahat`: any pair with `TV < 1` and a
characteristic kernel.

## Proof route (untrusted)
* `RouteSep`: first-order condition of the projection, Cauchy–Schwarz on the unit sphere, polarisation.
* `RouteBasicIneq`: CVaR duality on any probability measure (weak duality for every cut, attainment by the bathtub density at a quantile,
  both tails), lifted to the regions through `⟨f, ∫gφ⟩ = ∫g⟨f,φ⟩`; the empirical order statistics are quantiles of `P_n`, `Q_m`
  (counting); the margin from the population side and the maximality of `f̂` on the empirical side.
* `RouteLocal`: countable dense parameter set (`rampDev` is `4(1+κ)`-Lipschitz in the parameters), two-sample symmetrisation,
  coordinatewise contraction, the linear bound, Khintchine-type `E‖S_σ‖ ≤ κ√s`, McDiarmid and Minkowski in `ℝ²`.
* `RouteRate`: events `E^±` (Theorem A at `δ/5`), four one-sided Hoeffding events for the empirical cdfs of `d*(X)` at `t_α ± λ_X` and of
  `d*(Y)` at `u_α ± λ_Y` (each `δ/10`, which is the printed DKW radius), the peeling events of `localmod` at `r_j = 2θ^{−j}`
  (`e^{−χ} = δ/(5(J+1))`, union bound), then Steps 0–5 as printed (`quad_solve`, `witness_bound`, `kept_of_band`); the trimconsist event
  rebuilt (`consist_event`) for the last sentence.
* `RouteCor`: Markov on shells applied to the measurable sets `{Z(2^{i+1}b) ≥ c_i}` (no measurability of `r̂` needed; the first shell
  containing `r̂` is found with `Nat.find`), constants depending on `ε` only, `N` from the large-sample conditions; kept set on the band of
  half-width `2κ‖d̂ − d*‖ + λ_X`.
* `RouteContact`: total boundedness via bounded simple approximations of `φ` in `L¹(P)` plus closedness; `(μ·f) ⊓ (μ·g) = μ·min(f,g)`;
  mass via `tvDist_eq_one_sub_integral_min`; uniqueness of the common trimming by mass comparison; `ω_c → 0` by minimising
  `infDist(·, 𝒞_{α*}(Q))` on a compact set.
* `RouteAlpha`: the two `uniform_alpha` events, exact nearest points in the closed convex regions (Hilbert projection), nested regions,
  `consistency_i`, `crossing`, `crossing_meas`, `tauRight_spec`, `tau_sched`.
* `RouteNearA`: Step 1 (`a_α → μ_{R*}` from `ω_c` and `D_α → 0`), Step 2 via `popthreshold` and (A3) (no subsequence needed:
  `L¹`-convergence forces `h ∈ {0,1}` a.e.), Step 3 via sequential Banach–Alaoglu (`WeakDual.isSeqCompact_closedBall` through
  `toDual`) and dominated convergence.
* `RouteNearB`: real-analyticity along lines of `x ↦ ⟨g, φ(x)⟩` for the Gaussian Gram matrix (an `ℓ²` model with the same Gram matrix
  `e^{2ast}`, a Hahn–Banach extension of the induced functional, a power series of infinite radius, the identity theorem); Step 4 without
  weak-∗ compactness in `L^∞` (`∫g_jf_j dP = ⟨a_j, f_j⟩ → ⟨μ_{R*}, f̄⟩`, mixtures `(1−ε_j)g + ε_j`), a generic bathtub uniqueness lemma,
  the density form from `nearcontact_densities`; `f̄` constant on `ℝ^d` gives `⟨f_j, f̄⟩ = 0` hence `f̄ = 0`; Step 5 by dominated
  convergence along sequences.

## Paper notes (printed text at `c3ba305`)
No printed statement is false. Remarks on the proofs (none affects a statement):
1. `C_recover.tex:775-776` (proof of `prop:alphahat`): "The regions increase with the level and are closed, so there are `a ∈ 𝒞_{α*,k}(P)`
   with `‖â − a‖ ≤ r_n`": in infinite dimensions closedness alone does not give a nearest point; convexity (Hilbert projection) or
   compactness (`lem:contact`) does. Suggested wording: "are closed and convex".
2. `C_recover.tex:622-626` (proof of `cor:trimrate`): Markov's inequality is applied to `P(S_j ∩ E)`, where `S_j` is defined through `r̂`,
   whose measurability is not addressed; the bound is really for the measurable superset `{Z(2^j/q) ≥ D4^j/(8β̄q²)}`, which is what the
   formal proof uses. Suggested wording: "`S_j ∩ E ⊆ {Z(2^j/q) ≥ D4^j/(8β̄q²)}`, so by Markov's inequality …".
3. `C_recover.tex:732-742` and `:755-756` (Step 4): the weak-∗ compactness of `(g_{α_j})` in `L^∞(P)` is not needed: `∫g_jf_j dP = ⟨a_j,f_j⟩ →
   ⟨μ_{R*},f̄⟩` follows from Step 1 and the weak convergence of `f_j`. Likewise the appeal to "no nonzero constant function in the Gaussian
   RKHS" can be replaced by `⟨f_j, f̄⟩ = D_j⁻¹(⟨a_j,f̄⟩ − ⟨b_j,f̄⟩) = 0` once `f̄ ≡ t̄`. Simplifications only.
4. `C_recover.tex:707` (Step 2 of the remark's proof): the subsequence is not needed (an `L¹` limit of indicators is itself an
   indicator a.e.). Simplification only.

## Not covered (declared)
`eq:twotail` as a separate display (its content is proved inside `RouteBasicIneq`); the prose after `thm:trimrate`
(`08_trimming.tex:292-306`: orders of magnitude `√(log log(n∧m)/(n∧m))`, the factor `√2`, numerical crossovers) and after
`rem:nearcontact` and `prop:alphahat` (`:351-362`, `:386-394`); the sketch remarks of the research note; every numerical claim.

## Fidelity review notes (2026-11-08, method v1; none affects fidelity)
1. Scope of the lead-in in `contact`: certified under the lemma's hypotheses (declared above as a specialisation; the COVERAGE row says so).
2. Line ranges: the frozen header cites `lem:sepmargin` as `C_recover.tex:367-380` and `lem:contact` as `:662-667`; the environments are
   `:367-379` and `:662-668` (cosmetic; the header is frozen).
3. Source drift: completed above (`01_introduction.tex`, `06_splitting.tex` changed in prose only at `c339b9d`).
4. The `prop:alphahat` coverage row mentions that the schedule part also uses `τ ≤ r_n(·,δ/2) + r_m(·,δ/2)` (true for the paper's
   `τ_{n,m}`: `Wave30tu.Full.tauFull_threshold`, since `D_φ ≤ 2κ`). The auditor verified that the paper's `τ_{n,m}` meets every threshold
   hypothesis of `alphahat` through certified targets (`Wave30tu.Full.tauFull_threshold`, `Wave30tw.tauFull_continuous`,
   `Wave30tw.crossing_full_cont`).

## Sign-off
Gate (2026-11-08, branch `tmmd-jmlr-trimrate`): `CERTIFIED: 3651 targets; statements frozen; axioms within ['Classical.choice', 'Quot.sound', 'propext']`;
`tools/check_aliases.py`: `ALIASES OK: 3594 aliases in 15 paper files; each is literally a certified theorem under its frozen claim; all
3583 targets of the 15 paper pages covered (68 targets have no page)`. The 14 targets have aliases on `Papers/TrimmedMMDJMLR` (regenerated;
the page now also carries the jmlr targets of waves 30tl–30tw, which had no page before the merge of `tmmd-jmlr-split`).
