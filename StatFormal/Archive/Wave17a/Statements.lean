import StatFormal.Archive.OTFD.Wave8c.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import StatFormal.Archive.RobustEquality.Quick.Statements
import StatFormal.Archive.NNFibers.Wave1.Statements
import TauCeti.Analysis.Convex.Subdifferential
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# FROZEN STATEMENTS — wave 17a (QUEUE rows 167–175): otfd A `lem:rt-visible`; B `prop:rk-transfer-cocycle`,
# `lem:interior-levels`; C `prop:conditional-pop-content`, `prop:net-inner-band`; robust equality paper2
# `prop:predline`; TM `lem:separation`, `thm:rffjoint`; NN `prop:noncentral-tube`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`, `otfd-B_bands.md`,
`otfd-C_conditional.md`, `robust-equality-paper2.md`, `trimmed-mmd.md`, `proliferation-nns.md`; current text after the
2026-10-13/14 corrections; otfd paths under `otfd/papers/`):
* A `lem:rt-visible` (`A_sieves/supplement.tex:4181-4185`, proof `:4187-4195`), with `Π_K`, `ι_K` of the sieve
  (`Π_K x = (⟨x,e_k⟩)_{k≤K}`, `ι_KΠ_K x = Σ_{k≤K}⟨x,e_k⟩e_k`).
* B `prop:rk-transfer-cocycle` (`B_bands/supplement.tex:5533-5544`, proof `:5546-5566`), with the maps `F_•`, `Q_•` of
  `thm:prob-content`(c) (a.e. inverses) and `T_{A→B} = Q_B∘F_A` of `prop:rk-transfer`.
* B `lem:interior-levels` (`B_bands/supplement.tex:929-937`), with condition (a) of `thm:band-consistency`
  (`:851-857`: `A_{K,1−δ} ⊂ int 𝒰_K`), the cubic law and `c_K`, `τ_{K,p} = c_K^{-1}(p)`, `ρ_box` (frozen `Wave8c`), and
  the naive law's `‖·‖_{M_K}` (frozen `Wave8c.mnorm`).
* C `prop:conditional-pop-content` (`C_conditional/main.tex:641-645`), with the population band `eq:conditional-pop-band`
  (`main.tex:629-639`), `A_{K,p}` with `μ_K(A_{K,p}) = p` (`main.tex:275`) and the reconstruction
  `𝔪(t) + ⟨𝐞_K(t), Z⟩` (`main.tex:260-265`).
* C `prop:net-inner-band` (`C_conditional/supplement.tex:1581-1606`, proof `:1645-1690`).
* paper2 `prop:predline` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:385-406`, proof
  `app_proofs.tex:118-131`), with the certificate `thm:certificate` (`main.tex:255-260`), `(P_η)`, `(C_δ)`
  (`eq:problems`, `main.tex:278-283`) and the anisotropic sets (`main.tex:229-232`).
* TM `lem:separation` (`trimmed-mmd/paper.tex:1081-1094`).
* TM `thm:rffjoint` (`trimmed-mmd/paper.tex:1709-1724`, proof `supplement.tex:1145-1157`), with `lem:rffkernel`
  (`paper.tex:1694-1707`), `thm:concentration` (`paper.tex:767-780`), `lem:qpstability` (`supplement.tex:1129-1143`).
* NN `prop:noncentral-tube` (`proliferation-and-geometry-in-nns/paper_revised.tex:906-916`), with `Γ̄_s`,
  `eq:codim-s`, `eq:lambda-s` (`:883-904`).
Imports the frozen `OTFD/Wave8c` (`IsRankPair`, `cubicLaw`, `cK`, `tauKp`, `rhoBox`, `mnorm`),
`TrimmedMMD/Unconditional` (`setDist`, `Dpop`, `Demp`, `region`, `empirical`, `TrimmedMMD.rn`), `RobustEquality/Quick`
(`InAniso`) and `NNFibers/Wave1` (`Neuron`, `closureSet`) statements, not copied; Mathlib and Tau Ceti
(`TauCeti.subdifferential`, `TauCeti.wassersteinEDist`, `TauCeti.IsCoupling`) otherwise. No `Foundations` file.

Covered:
* A `lem:rt-visible`: `rt_visible` (`P ≠ Q` ⇒ `Π_K#P ≠ Π_K#Q` for all `K ≥ K₀`); `rt_visible_initial` (equality at `K`
  is inherited by every `K' ≤ K`, the proof's first step).
* B `prop:rk-transfer-cocycle`: `rk_transfer_cocycle` (the three identities, `P_{A,K}`-a.e.); `rk_transfer_version`
  (every composite is unchanged `P_{A,K}`-a.e. when each map is replaced by an a.e.-equal version, measurable or
  not); `rk_transfer_cocycle_version` (the three identities for arbitrary versions).
* B `lem:interior-levels`: `interior_levels_naive` (naive law: `{‖u‖_M ≤ p} ⊂ int{‖u‖_M ≤ 1}` for `p < 1`);
  `interior_levels_cubic` (cubic law: `A_{K,p} ⊂ int 𝒰_K ⇔ τ_{K,p}D_∞ < λ_K/2 ⇔ p < c_K(λ_K/(2D_∞))`, `λ_K/2` the
  smallest half-width); `interior_levels_vanish` (`c_K(λ_{(K)}/(2D_∞)) → 0` as `K → ∞`, any widths, any `D_∞`).
* C `prop:conditional-pop-content`: `conditional_pop_content` (measurable event, probability `≥ p`, all `t` at once).
* C `prop:net-inner-band`: `net_inner_band_attained` (Step 1: `M_p(v)` is a maximum attained on `∂A_{K,p}`);
  `net_inner_band_i`, `_ii`, `_iii`, `_iv`; `net_inner_band_edges` (the "Consequently" sentence, per level and `t`).
* paper2 `prop:predline`: (i) `predline_certificate` (prediction-line budgets give `F(h) ≤ (sup_θ Δ_θ(h) + √β₀ +
  √β₁)²` for every rule), `predline_constant` (constant rules: realised disparity `0` under every shift, nominal `0`,
  so the certificate is `(√β₀+√β₁)²`), `predline_constrained` (`(C_δ)` becomes `Δ ≤ √δ − √β₀ − √β₁`),
  `predline_penalised_not_shift` (the proof's "adds a constant to `(P_η)`" is false: counterexample); (iii)
  `predline_lookback` (`W₂²(w#P^past, w#P^now) ≤ wᵀM_sw`), `predline_budget_one_excludes` ("need not contain the
  look-back law": an explicit `d = 2` case outside the budget-`1` set).
* TM `lem:separation`: `separation` (the inequality, `EReal`), `separation_nearest_exists` (nearest points exist for
  nonempty weakly compact sets), `separation_attained` (`sep(f*;A,B) = dist(A,B)`).
* TM `thm:rffjoint`: `rffjoint` (one measurable event of probability `≥ 1 − δ` carrying both displays).
* NN `prop:noncentral-tube`: `noncentral_tube_affine` (the Gaussian–affine core in any finite-dimensional space);
  `lambda_s` (`eq:lambda-s`); `noncentral_tube` (the proposition for `Γ̄_s` with `c_s` and `λ_s` of the paper).

Not covered (declared):
* A: the use of the lemma in `thm:rt-fixedK` (`main.tex:1474`, the rank test is eventually consistent along `K`).
* B cocycle: the existence of the McCann maps (`thm:prob-content`(c) is a hypothesis: `IsRankPair`); the `\ext{}`
  paragraph after the proof (fitted transfers, `Lip(Q̂_C) ≤ ‖M_K‖ D_C²/(2ε)`).
* B interior levels: the ball reference (needs the Hilbert Gaussian law, B `lem:refs-ac`, L3); "`τ_{K,1−δ} < 1`" for
  the naive law is the certified `Wave8c` `naive_calibration` (`c_K(τ) = τ`), so only the inclusion is stated; that
  `𝒰_K = supp μ_K` is the closed box (resp. `{‖u‖_M ≤ 1}`, certified in `naive_calibration`) enters as the definition.
* C content: the link from "the reconstruction given `C = x`" to a kernel/`condDistrib` (a fixed conditional law
  `P_{K,x}` is used, see Encodings); Brenier's theorem (any measurable `Q` with `Q#μ_K = P_{K,x}` is allowed).
* C net band: the uniformity "for every `p ≤ 1 − δ`" is the per-level statement quantified over all compact
  `A ⊆ S` (the constants do not depend on `p`); `lem:convex-continuous-gradient` and `cor:net-inner-band-neural`.
* paper2: (ii) (a selection effect, "not a theorem" by the paper's own remark; the identity `β_s(h) = W₂²(h#·,h#·)`
  is `lem:delta-inf`); the tightness clause "attained by shifting the two quantile functions apart whenever they stay
  nondecreasing" (companion paper); in (iii) "is a set of populations … holds for every rule at once" (definitional;
  `prop:uniform`), the groupwise term `|M_s^{1/2}w|` (certified `thm:seminorm`(iv)(c)) and "with budget `d` it does"
  (certified `RobustEquality.Quick.Claims.aniso_ii_iii`).
* TM `thm:rffjoint`: `lem:rffkernel` itself (Sriperumbudur–Szabó; a hypothesis with an abstract `ε = ε_r(δ/3)`), the
  rates `O(min(n,m)^{-1/2}) + O(r^{-1/4})` and `O(r^{-1/2})`, and the random-feature construction (`z_r` is any
  feature family).
* NN: the small-tube expansion `eq:smalltube-noncentral` (stated after the proposition, not part of it) and the
  remark that `Γ̃_s` is dense in `Γ̄_s` (`dist(X,Γ̃_s) = dist(X,Γ̄_s)`).

Encodings (to be checked by the critic):
* A: `H` a real Hilbert space with a Hilbert basis `b : HilbertBasis ℕ ℝ H` (the complete orthonormal basis `(e_k)`;
  `H` is then separable and infinite-dimensional), Borel; `Π_K x = (⟨b_k, x⟩)_{k<K} ∈ EuclideanSpace ℝ (Fin K)`
  (`projK`, continuous, so `Measure.map` is genuine); `P, Q` Borel probability measures (`𝒫(H)`).
* B cocycle: the frozen `IsRankPair μ P F Q` (`Q#μ = P`, `F#P = μ`, `F∘Q = id` `μ`-a.e., `Q∘F = id` `P`-a.e., `F, Q`
  measurable) is `thm:prob-content`(c) for the pair `(F_•, Q_•)`; one common reference `μ` on `ℝ^K`
  (`EuclideanSpace ℝ (Fin K)`). The reference need not be boundedly supported or absolutely continuous, nor the
  `P_{•,K}` in `𝒫^ℓ`: generalisation. `T_{A→A} = Q_A∘F_A`, `T_{B→C}∘T_{A→B} = Q_C∘F_B∘Q_B∘F_A`, `T_{B→A}∘T_{A→B} =
  Q_A∘F_B∘Q_B∘F_A`. "Versions" are arbitrary functions equal `P_{•,K}`-a.e. to `F_•` and `μ`-a.e. to `Q_•` (no
  measurability required of them).
* B interior levels: the cubic law is the frozen `cubicLaw a` (`⊗_k Unif[−a_k, a_k]`, half-widths `a_k = λ_k/2 > 0`,
  `N ≥ 1` coordinates), `𝒰_K = ∏_k [−a_k, a_k]` (`cubeBox`), `A_{K,p} = {u ∈ 𝒰_K : ρ_box(u) ≤ τ_{K,p}}` (`cubicRegion`,
  `ρ_box` and `τ_{K,p} = sInf{t : p ≤ c_K(t)}` frozen; nonempty and bounded below for `0 < p ≤ 1`: no junk).
  "`λ_1 ≥ λ_2 ≥ ⋯`, `λ_K`" and "unordered: `min_k λ_k`" are both the index `k₀` of a smallest half-width. `D_∞ > 0` is
  arbitrary (the paper's `D_∞ ≥ D_K` is not needed). `δ ∈ (0,1)` is `p = 1 − δ ∈ (0,1)`. In `interior_levels_vanish`
  the widths are a sequence `λ : ℕ → ℝ`, `λ_k > 0`, `K + 1` coordinates (so `K + 1 ≥ 1`), `λ_{(K)}/2` is
  `Finset.inf'` of the half-widths, and `D_∞` may depend on `K`. Naive law: `‖u‖_M` is the frozen `mnorm` (`M` any
  real matrix; `PosDef` is not needed for the inclusion), `A_{K,p} = {‖u‖_M ≤ τ_{K,p}}` with `τ_{K,p} = p`.
* C content: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `μ_K` a probability measure, `Q` measurable with `Q#μ_K = P_{K,x}`
  (Brenier map, generalised); `A_{K,p}` any measurable set with `μ_K(A) ≥ p` (the paper: `= p`); the band edges are
  `𝔪(t) ± h^pop(±𝐞_K(t))` with `h^pop(v) = essSup_{μ_K|_A} ⟨v, Q(·)⟩` in `EReal` (`hPop`: no `ℝ`-junk for unbounded
  essential ranges; `⊥` only if `μ_K(A) = 0`, where the claim is trivial); `𝒯` any index type, `𝔪 : 𝒯 → ℝ`,
  `𝐞_K : 𝒯 → ℝ^K` arbitrary; "the reconstruction of a new response lies in the band" is `InPopBand` of its
  coefficient vector `z`, whose law is `P_{K,x}`; the event is proved measurable (it is closed).
* C net band: `ℝ^K` as above; `A = A_{K,p}` any compact set with `A ⊆ S ⊆ O`, `O` open; "`χ_{K,x}` differentiable on
  `O`, `Q = ∇χ_{K,x}`" is replaced by the weaker `Q(u) ∈ ∂χ(u)` for `u ∈ O` (Tau Ceti's `EReal`-valued
  subdifferential; a convex `χ` differentiable at `u` has `∇χ(u) ∈ ∂χ(u)`), plus `Q` continuous on `O`; `ω_S(h)` is a
  number `ω` with `‖Q(u) − Q(u')‖ ≤ ω` for `u, u' ∈ S`, `‖u − u'‖ ≤ h` (the modulus evaluated at `h`); `η` is any
  bound `‖T − Q‖ ≤ η` on `S` (the paper's `η` is the smallest one: generalisation); `𝒩_p` a nonempty `Finset` inside
  `A` with every point of `frontier A` within `h`; `Q_{K,x}` is a function `Qb` with `Qb = Q` `μ_K`-a.e. on `O`;
  `max_𝒩` is `Finset.sup'`; `sup_A ⟨v,T⟩` and `M_p(v)` are real `sSup`s of images (bounded and nonempty under the
  hypotheses, so genuine; `net_inner_band_attained` proves `M_p(v)` is a maximum); the support condition is
  `(μ_K.restrict A).support = A` (Mathlib's `Measure.support`); `E_K` is any bound `‖𝐞_K(t)‖ ≤ E_K`.
* paper2: rules `h : ℝ^d → ℝ` measurable (`ℝ^d = EuclideanSpace ℝ (Fin d)`, `K = ℝ^d`); laws are probability
  measures; `W₂` is Tau Ceti's `wassersteinEDist 2` on `ℝ` (`ℝ≥0∞`-valued: no junk); the structured model is
  `𝒮_Θ = ∪_θ B₀(θ) × B₁(θ)` with `B_s(θ) = {Q : W₂²(h#C_s(θ), h#Q) ≤ β_s}`, `C_s(θ)` the transported centres
  `𝔗_θ P̂_s` (any probability laws: generalisation); `Δ_θ(h) = W₂(h#C₀(θ), h#C₁(θ))`; `sup_θ` is `⨆` in `ℝ≥0∞`.
  `(C_δ)` for a rule set: `(Δ + c)² ≤ δ ⇔ Δ ≤ √δ − c`, `c = √β₀ + √β₁`, stated for reals `Δ ≥ 0`. (iii): a coupling
  `π` of `(P^past, P^now)` (its marginals) with integrable second moments, `M = E_π(X'−X)(X'−X)ᵀ` entrywise; `M ≻ 0`
  is not needed for the inequality (generalisation). The excluded look-back law uses the frozen `InAniso`.
* TM separation: `ℋ` any real inner product space (complete where nearest points are used); `B_ℋ = {‖f‖ ≤ 1}`;
  `dist(A,B)` is the frozen `setDist` (an `sInf` of a nonempty set bounded below by `0`: genuine); `sep(f;A,B)` is
  `inf_A ⟨f,·⟩ − sup_B ⟨f,·⟩` in `EReal` (`sepVal`: `±∞` allowed, never `⊤ − ⊤`); "weakly compact" is
  `IsCompact (toWeakSpace ℝ ℋ '' A)`; "the nearest points" are any `a* ∈ A`, `b* ∈ B` with `‖a* − b*‖ = dist(A,B)`.
* TM rffjoint: the frozen setting of `TrimmedMMD/Unconditional` (`φ : 𝒳 → ℋ` strongly measurable, `‖φ‖ ≤ κ`, `ℋ`
  separable Hilbert, `k(x,y) = ⟨φ x, φ y⟩`); the feature draw is a probability space `(Ω_f, ν)` and `z : Ω_f → 𝒳 → ℋ'`
  any feature family into a real Hilbert space (`ℝ^r` with `z_r`: generalisation), each `z ω` strongly measurable;
  `lem:rffkernel` is the hypothesis: a measurable `E_f` with `ν(E_f) ≥ 1 − δ/3` on which `|⟨z(x), z(y)⟩ − k(x,y)| ≤ ε`
  for all `x, y ∈ 𝒳` (`𝒳` the compact domain, here the sample space itself); `D̂^{(r)} = Demp (z ω)`, `D̂ = Demp φ`,
  `D = Dpop φ` (frozen); `r_n = TrimmedMMD.rn`; the joint law is `P^{⊗n} ⊗ (Q^{⊗m} ⊗ ν)`; the second display is
  stated under `D̂^{(r)} + D̂ > 0` (at `0` both sides vanish).
* NN: `N(0, σ²I)` on a finite-dimensional real inner product space `E` is `stdGaussian E` scaled by `σ > 0`
  (`isoGauss`); `χ²_c(λ)` is the law of `Σ_{i<c} (Z_i + μ_i)²`, `Z_i` iid `N(0,1)`, `μ = (√λ, 0, …, 0)` (`ncChiSq`;
  `λ ≥ 0` where used), and `F` its CDF `ncChiSq c λ (Iic ·)` (`Measure.real`); `dist(X, V)` is `Metric.infDist`; the
  codimension `finrank E − finrank V.direction` is a genuine `ℕ` difference (`≤`). For `Γ̄_s`, `Θ_m` carries the
  Euclidean norm of all `m(d_in + d_out)` coordinates: the frozen `closureSet θs g` (on `Fin m → Neuron`) is moved
  by the coordinate map `eucPar` into `EuclideanSpace ℝ (Fin m × (Fin d_in ⊕ Fin d_out))`; `n_i = #g⁻¹(inl i) ≥ 1`
  (`g` surjective), `‖·‖²` coordinatewise; `c_s = (m − j)d_in + (q + j)d_out` in `ℕ` (`m ≥ q + j` by surjectivity).

Critic notes:
* All 28 claims are proved in `Wave17a/Route{RtVisible,Cocycle,Interior,CondBand,Predline,Separation,Rff,Noncentral,
  NoncentralNN}.lean` (axioms: propext, Classical.choice, Quot.sound). The routes reuse the untrusted
  `OTFD/Wave8c/RouteCubic` (`tau_props`, `unifSym_prob`), `TrimmedMMD/Unconditional/Proofs` (certified
  `concentration`, `abs_Demp_sub_Dpop_le`, `region_nonempty`) and `NNFibers/Wave1/RouteCodim` (certified
  `dim_closure`, `codim_blockcount`) — routes only.
* No statement of the nine results was found false. One proof-level slip: paper2 `prop:predline`(i), proof
  (`app_proofs.tex:118-124`): "the budget term does not depend on `h`, so it adds a constant to `(P_η)`" is false —
  `(Δ + c)² = Δ² + 2cΔ + c²` has an `h`-dependent cross term; `predline_penalised_not_shift` gives two rules whose
  ranking under `R + η(Δ + c)²` and `R + ηΔ²` differs (`η = c = 1`, `R = (0, 3/2)`, `Δ = (1, 0)`). The statement's
  reduction is true for `(C_δ)` (`predline_constrained`); for `(P_η)` it holds only in the weak sense that the
  penalty depends on `h` through `Δ` alone. Suggested fix: "(P_η) penalises `(Δ_Θ(h) + √β₀ + √β₁)²`, a function of
  the nominal disparity alone; (C_δ) is the nominal constraint with target `√δ − √β₀ − √β₁`".
* paper2 (iii): the inequality `W₂²(w#P^past, w#P^now) ≤ wᵀM_sw` needs neither `M_s ≻ 0` nor the anisotropic set;
  `M_s ≻ 0` (the I6 repair) is needed only for the set and its certificate (certified `aniso_i`, `aniso_ii_iii`).
  "Need not contain" is witnessed with `P^past = δ₀` (every coupling is then the product, cost `2 > 1`).
* A: the proof's "dominated convergence for bounded continuous `f`" plus `ext_of_forall_integral_eq` (Borel measures
  on a metric space) is exactly what is formalised; no π-system argument is needed.
* B interior levels: `c_K(t) = κt^N` for `tD_∞ ≤ λ_K/2` (the Euclidean ball lies in the box), which gives both the
  strict monotonicity and the continuity used in the level equivalence; the vanishing holds for every positive
  width sequence and every `D_∞ > 0`, with the bound `c_K(λ_{(K)}/(2D_∞)) ≤ (√π/2)^N`.
* C content: simultaneity over uncountably many `t` goes through the support of `Q#(μ_K|_A)` (QUEUE note), on which
  every half-space bound `⟨v,·⟩ ≤ h^pop(v)` holds for all `v` at once; neither Brenier nor absolute continuity of
  `μ_K` is used.
* C net band: Step 1 needs only `Q(u) ∈ ∂χ(u)` at the two endpoints (monotonicity), so differentiability and
  convexity of `A` are not used; `h ≥ 0` (a covering radius) is needed — with `h < 0` and `K = 0` the frontier is empty
  and `ω` is unconstrained.
* TM separation: nearest points exist for any nonempty weakly compact `A, B` (lower semicontinuity of `‖a − b‖` in the
  weak topology); convexity is used only for attainment.
* TM rffjoint: `|D̂^{(r)2} − D̂²| ≤ 4ε` is proved directly on the regions (the same trimming function on both feature
  maps; signed weights of `ℓ¹`-mass `2`), i.e. `lem:qpstability` in region form; the event is the product
  `A_P × A_Q × E_f`, of mass `≥ (1 − δ/3)³ ≥ 1 − δ` (independence of the feature draw is used, as in the paper).
* NN: `L x = (⟨b_i, x⟩)_i` (orthonormal basis of `(dir V)ᗮ`) pushes `stdGaussian` to `stdGaussian ℝ^c`
  (characteristic functionals, `L` a coisometry); a reflection moves the shift to `(√λ, 0, …, 0)`. `eq:lambda-s` is
  attained at copies `(ω_i, a_i/n_i)` and zero-type units `0` (Cauchy–Schwarz per group for the lower bound).
* Critic (2026-10-15): ACCEPT / ACCEPT-WITH-NOTE, all 28 TRUE. Tau Ceti's `∂χ` requires `χ(u)` finite, so the
  net-band hypothesis is not vacuous; `h ≥ 0` is the paper's covering radius. TM `rffjoint` is CONDITIONAL on
  `lem:rffkernel` (not certified; rated L3; the cited theorem covers a phase-free estimator while the paper uses phased
  features). B interior-levels: the ball reference is declared (needs the Hilbert Gaussian law). paper2 `predline`(i)
  proof step (`app_proofs.tex:118-124`) "the budget term does not depend on `h`, so it adds a constant to `(P_η)`" is
  FALSE (`η = c = 1`, `R = (0, 3/2)`, `Δ = (1,0)`: minimisers differ) — paper S2 (DEFECTS #60); the statement holds
  in the reading where the penalty depends on `h` through `Δ` alone.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave17a

/-! ### A `lem:rt-visible` -/

/-- `Π_K x = (⟨e_1, x⟩, …, ⟨e_K, x⟩) ∈ ℝ^K` for the Hilbert basis `b = (e_k)`. -/
def projK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (b : HilbertBasis ℕ ℝ H) (K : ℕ) (x : H) :
    EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 fun k : Fin K => ⟪b k, x⟫

/-! ### B `lem:interior-levels` -/

/-- The cubic reference support `𝒰_K = ∏_k [−a_k, a_k]`. -/
def cubeBox {N : ℕ} (a : Fin N → ℝ) : Set (Fin N → ℝ) := Set.pi univ fun k => Icc (-a k) (a k)

/-- The cubic level region `A = {u ∈ 𝒰_K : ρ_box(u) ≤ τ}`. -/
def cubicRegion {N : ℕ} (a : Fin N → ℝ) (Dinf τ : ℝ) : Set (Fin N → ℝ) :=
  cubeBox a ∩ {u | StatFormal.OTFD.Wave8c.rhoBox Dinf u ≤ τ}

/-! ### C `prop:conditional-pop-content`, `prop:net-inner-band` -/

section CondBand
variable {K : ℕ}

/-- `h^pop(v) = μ_K-ess sup_{u ∈ A} ⟨v, Q(u)⟩`, in `EReal`. -/
def hPop (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (v : EuclideanSpace ℝ (Fin K)) : EReal :=
  essSup (fun u => ((⟪v, Q u⟫ : ℝ) : EReal)) (μ.restrict A)

/-- The reconstruction `𝔪(t) + ⟨𝐞_K(t), z⟩` lies in `[𝔪(t) − h^pop(−𝐞_K(t)), 𝔪(t) + h^pop(𝐞_K(t))]` for every `t`. -/
def InPopBand {T : Type*} (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (m : T → ℝ) (e : T → EuclideanSpace ℝ (Fin K))
    (z : EuclideanSpace ℝ (Fin K)) : Prop :=
  ∀ t, (m t : EReal) - hPop μ A Q (-e t) ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧
    ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ (m t : EReal) + hPop μ A Q (e t)

/-- `max_{u ∈ 𝒩} ⟨v, T(u)⟩`. -/
def netMax (N : Finset (EuclideanSpace ℝ (Fin K))) (hN : N.Nonempty)
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (v : EuclideanSpace ℝ (Fin K)) : ℝ :=
  N.sup' hN fun u => ⟪v, T u⟫

/-- `sup_{u ∈ A} ⟨v, F(u)⟩` (used for `sup_A ⟨v,T⟩` and `M_p(v) = max_A ⟨v,Q⟩`). -/
def supOn (A : Set (EuclideanSpace ℝ (Fin K))) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (v : EuclideanSpace ℝ (Fin K)) : ℝ :=
  sSup ((fun u => ⟪v, F u⟫) '' A)

/-- The hypotheses of `prop:net-inner-band` at one level `A = A_{K,p} ⊆ S ⊆ O`. -/
structure NetSetting (μ : Measure (EuclideanSpace ℝ (Fin K))) (A S O : Set (EuclideanSpace ℝ (Fin K)))
    (χ : EuclideanSpace ℝ (Fin K) → EReal) (Q Qb T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (ω η h : ℝ) (N : Finset (EuclideanSpace ℝ (Fin K))) : Prop where
  isOpen_O : IsOpen O
  subset_AS : A ⊆ S
  subset_SO : S ⊆ O
  compact_A : IsCompact A
  cont_Q : ContinuousOn Q O
  subgrad : ∀ u ∈ O, Q u ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) χ u
  nonneg_h : 0 ≤ h
  modulus : ∀ u ∈ S, ∀ u' ∈ S, ‖u - u'‖ ≤ h → ‖Q u - Q u'‖ ≤ ω
  approx : ∀ u ∈ S, ‖T u - Q u‖ ≤ η
  net_sub : (N : Set (EuclideanSpace ℝ (Fin K))) ⊆ A
  net_cover : ∀ u ∈ frontier A, ∃ w ∈ N, ‖u - w‖ ≤ h
  version : ∀ᵐ u ∂μ, u ∈ O → Qb u = Q u

end CondBand

/-! ### TM `lem:separation` -/

/-- `sep(f; A, B) = inf_{a ∈ A} ⟨f, a⟩ − sup_{b ∈ B} ⟨f, b⟩`, in `EReal`. -/
def sepVal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H) (A B : Set H) : EReal :=
  (⨅ a ∈ A, ((⟪f, a⟫ : ℝ) : EReal)) - ⨆ b ∈ B, ((⟪f, b⟫ : ℝ) : EReal)

/-! ### NN `prop:noncentral-tube` -/

/-- The noncentral `χ²_c(λ)` law: `Σ_{i<c} (Z_i + μ_i)²` with `Z_i` iid `N(0,1)` and `μ = (√λ, 0, …, 0)`. -/
def ncChiSq (c : ℕ) (lam : ℝ) : Measure ℝ :=
  (Measure.pi fun _ : Fin c => gaussianReal 0 1).map
    fun z => ∑ i : Fin c, (z i + if (i : ℕ) = 0 then Real.sqrt lam else 0) ^ 2

/-- `N(0, σ² I)` on a finite-dimensional real inner product space. -/
def isoGauss (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] (σ : ℝ) : Measure E :=
  (stdGaussian E).map fun x => σ • x

open StatFormal.NNFibers.Wave1 in
/-- Euclidean coordinates of a parameter `θ ∈ Θ_m`: `(u, inl k) ↦ (ω_u)_k`, `(u, inr k) ↦ (a_u)_k`. -/
def eucPar {din dout m : ℕ} (θ : Fin m → Neuron din dout) :
    EuclideanSpace ℝ (Fin m × (Fin din ⊕ Fin dout)) :=
  WithLp.toLp 2 fun p => Sum.elim (θ p.1).1 (θ p.1).2 p.2

open StatFormal.NNFibers.Wave1 in
/-- `σ² λ_s = Σ_i (n_i ‖ω_i‖² + ‖a_i‖²/n_i)` (`eq:lambda-s`), `n_i = #g⁻¹(inl i)`. -/
def lamS {din dout q m j : ℕ} (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j) : ℝ :=
  ∑ i, ((Finset.univ.filter fun u => g u = Sum.inl i).card * ∑ k, (θs i).1 k ^ 2 +
    (∑ k, (θs i).2 k ^ 2) / (Finset.univ.filter fun u => g u = Sum.inl i).card)

namespace Claims

open StatFormal.OTFD.Wave8c (IsRankPair cubicLaw cK tauKp rhoBox mnorm)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)

/-! #### A `lem:rt-visible` -/

/-- `lem:rt-visible`: for `P ≠ Q` there is `K₀` with `Π_K#P ≠ Π_K#Q` for every `K ≥ K₀`. -/
def rt_visible : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ℕ ℝ H) (P Q : Measure H), IsProbabilityMeasure P → IsProbabilityMeasure Q → P ≠ Q →
      ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → P.map (projK b K) ≠ Q.map (projK b K)

/-- The proof's first step: equality of the projections at `K` is inherited by every `K' ≤ K`. -/
def rt_visible_initial : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ℕ ℝ H) (P Q : Measure H) (K K' : ℕ), K' ≤ K →
      P.map (projK b K) = Q.map (projK b K) → P.map (projK b K') = Q.map (projK b K')

/-! #### B `prop:rk-transfer-cocycle` -/

/-- `prop:rk-transfer-cocycle`: `T_{A→A} = Id`, `T_{B→C}∘T_{A→B} = T_{A→C}`, `T_{B→A}∘T_{A→B} = Id`, `P_{A,K}`-a.e. -/
def rk_transfer_cocycle : Prop :=
  ∀ (K : ℕ) (μ PA PB PC : Measure (EuclideanSpace ℝ (Fin K)))
    (FA QA FB QB FC QC : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsRankPair μ PA FA QA → IsRankPair μ PB FB QB → IsRankPair μ PC FC QC →
      (∀ᵐ z ∂PA, QA (FA z) = z) ∧ (∀ᵐ z ∂PA, QC (FB (QB (FA z))) = QC (FA z)) ∧
        ∀ᵐ z ∂PA, QA (FB (QB (FA z))) = z

/-- Version independence: replacing each map by a version equal to it a.e. (for its source measure) changes the
composites `T_{A→A}`, `T_{A→B}`, `T_{A→C}`, `T_{B→C}∘T_{A→B}`, `T_{B→A}∘T_{A→B}` only on a `P_{A,K}`-null set. -/
def rk_transfer_version : Prop :=
  ∀ (K : ℕ) (μ PA PB PC : Measure (EuclideanSpace ℝ (Fin K)))
    (FA QA FB QB FC QC FA' QA' FB' QB' QC' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsRankPair μ PA FA QA → IsRankPair μ PB FB QB → IsRankPair μ PC FC QC →
    FA' =ᵐ[PA] FA → QA' =ᵐ[μ] QA → FB' =ᵐ[PB] FB → QB' =ᵐ[μ] QB → QC' =ᵐ[μ] QC →
      (∀ᵐ z ∂PA, QA' (FA' z) = QA (FA z)) ∧ (∀ᵐ z ∂PA, QB' (FA' z) = QB (FA z)) ∧
      (∀ᵐ z ∂PA, QC' (FA' z) = QC (FA z)) ∧
      (∀ᵐ z ∂PA, QC' (FB' (QB' (FA' z))) = QC (FB (QB (FA z)))) ∧
      ∀ᵐ z ∂PA, QA' (FB' (QB' (FA' z))) = QA (FB (QB (FA z)))

/-- The three cocycle identities hold for arbitrary versions of the maps. -/
def rk_transfer_cocycle_version : Prop :=
  ∀ (K : ℕ) (μ PA PB PC : Measure (EuclideanSpace ℝ (Fin K)))
    (FA QA FB QB FC QC FA' QA' FB' QB' QC' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsRankPair μ PA FA QA → IsRankPair μ PB FB QB → IsRankPair μ PC FC QC →
    FA' =ᵐ[PA] FA → QA' =ᵐ[μ] QA → FB' =ᵐ[PB] FB → QB' =ᵐ[μ] QB → QC' =ᵐ[μ] QC →
      (∀ᵐ z ∂PA, QA' (FA' z) = z) ∧ (∀ᵐ z ∂PA, QC' (FB' (QB' (FA' z))) = QC' (FA' z)) ∧
        ∀ᵐ z ∂PA, QA' (FB' (QB' (FA' z))) = z

/-! #### B `lem:interior-levels` -/

/-- Naive reference: `A_{K,p} = {‖u‖_M ≤ p}` lies strictly inside `𝒰_K = {‖u‖_M ≤ 1}` for every `p < 1`. -/
def interior_levels_naive : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (p : ℝ), p < 1 →
    {u | mnorm M u ≤ p} ⊆ interior {u | mnorm M u ≤ 1}

/-- Cubic reference, `a_{k₀} = λ_K/2` the smallest half-width, `p = 1 − δ ∈ (0,1)`:
`A_{K,p} ⊂ int 𝒰_K ⇔ τ_{K,p} D_∞ < λ_K/2 ⇔ p < c_K(λ_K/(2D_∞))`. -/
def interior_levels_cubic : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf p : ℝ) (k₀ : Fin N), (∀ k, 0 < a k) → (∀ k, a k₀ ≤ a k) → 0 < Dinf →
    0 < p → p < 1 →
      (cubicRegion a Dinf (tauKp a Dinf p) ⊆ interior (cubeBox a) ↔ tauKp a Dinf p * Dinf < a k₀) ∧
        (tauKp a Dinf p * Dinf < a k₀ ↔ p < cK a Dinf (a k₀ / Dinf))

/-- "The right-hand side tends to `0` as `K → ∞`": `c_K(λ_{(K)}/(2D_∞)) → 0` for any positive widths `λ_k`
(`K + 1` coordinates) and any `D_∞ > 0` (possibly depending on `K`). -/
def interior_levels_vanish : Prop :=
  ∀ (lam Dinf : ℕ → ℝ), (∀ k, 0 < lam k) → (∀ K, 0 < Dinf K) →
    Tendsto (fun K : ℕ => cK (fun k : Fin (K + 1) => lam (k : ℕ) / 2) (Dinf K)
      ((Finset.univ.inf' Finset.univ_nonempty fun k : Fin (K + 1) => lam (k : ℕ) / 2) / Dinf K)) atTop (𝓝 0)

/-! #### C `prop:conditional-pop-content` -/

/-- `prop:conditional-pop-content`: if `Z ∼ P_{K,x} = Q#μ_K` and `μ_K(A_{K,p}) ≥ p`, the reconstruction lies in the
population band for every `t` simultaneously, on a measurable event of probability `≥ p`. -/
def conditional_pop_content : Prop :=
  ∀ (K : ℕ) (T : Type) (μ Px : Measure (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : Set (EuclideanSpace ℝ (Fin K))) (p : ℝ)
    (m : T → ℝ) (e : T → EuclideanSpace ℝ (Fin K)),
    IsProbabilityMeasure μ → Measurable Q → μ.map Q = Px → MeasurableSet A → ENNReal.ofReal p ≤ μ A →
      MeasurableSet {z | InPopBand μ A Q m e z} ∧ ENNReal.ofReal p ≤ Px {z | InPopBand μ A Q m e z}

/-! #### C `prop:net-inner-band` -/

/-- Step 1: `M_p(v) = max_A ⟨v, Q⟩` is attained, and attained on `∂A`. -/
def net_inner_band_attained : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A S O : Set (EuclideanSpace ℝ (Fin K)))
    (χ : EuclideanSpace ℝ (Fin K) → EReal) (Q Qb T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (ω η h : ℝ) (N : Finset (EuclideanSpace ℝ (Fin K))) (v : EuclideanSpace ℝ (Fin K)),
    NetSetting μ A S O χ Q Qb T ω η h N → A.Nonempty → v ≠ 0 →
      ∃ u ∈ A ∩ frontier A, ⟪v, Q u⟫ = supOn A Q v ∧ ∀ u' ∈ A, ⟪v, Q u'⟫ ≤ supOn A Q v

/-- (i) `max_𝒩 ⟨v,T⟩ ≤ sup_A ⟨v,T⟩ ≤ M_p(v) + ‖v‖η`. -/
def net_inner_band_i : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A S O : Set (EuclideanSpace ℝ (Fin K)))
    (χ : EuclideanSpace ℝ (Fin K) → EReal) (Q Qb T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (ω η h : ℝ) (N : Finset (EuclideanSpace ℝ (Fin K))) (hN : N.Nonempty) (v : EuclideanSpace ℝ (Fin K)),
    NetSetting μ A S O χ Q Qb T ω η h N →
      netMax N hN T v ≤ supOn A T v ∧ supOn A T v ≤ supOn A Q v + ‖v‖ * η

/-- (ii) `max_𝒩 ⟨v,T⟩ ≥ M_p(v) − ‖v‖{ω_S(h) + η}` and `M_p(v) ≥ h^pop(v)`. -/
def net_inner_band_ii : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A S O : Set (EuclideanSpace ℝ (Fin K)))
    (χ : EuclideanSpace ℝ (Fin K) → EReal) (Q Qb T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (ω η h : ℝ) (N : Finset (EuclideanSpace ℝ (Fin K))) (hN : N.Nonempty) (v : EuclideanSpace ℝ (Fin K)),
    NetSetting μ A S O χ Q Qb T ω η h N →
      supOn A Q v - ‖v‖ * (ω + η) ≤ netMax N hN T v ∧ hPop μ A Qb v ≤ (supOn A Q v : EReal)

/-- (iii) `0 ≤ sup_A ⟨v,T⟩ − max_𝒩 ⟨v,T⟩ ≤ ‖v‖{ω_S(h) + 2η}`. -/
def net_inner_band_iii : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A S O : Set (EuclideanSpace ℝ (Fin K)))
    (χ : EuclideanSpace ℝ (Fin K) → EReal) (Q Qb T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (ω η h : ℝ) (N : Finset (EuclideanSpace ℝ (Fin K))) (hN : N.Nonempty) (v : EuclideanSpace ℝ (Fin K)),
    NetSetting μ A S O χ Q Qb T ω η h N →
      0 ≤ supOn A T v - netMax N hN T v ∧ supOn A T v - netMax N hN T v ≤ ‖v‖ * (ω + 2 * η)

/-- (iv) Under `supp(μ_K|_A) = A`: `M_p(v) = h^pop(v)` and `|max_𝒩 ⟨v,T⟩ − h^pop(v)| ≤ ‖v‖{ω_S(h) + η}`. -/
def net_inner_band_iv : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A S O : Set (EuclideanSpace ℝ (Fin K)))
    (χ : EuclideanSpace ℝ (Fin K) → EReal) (Q Qb T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (ω η h : ℝ) (N : Finset (EuclideanSpace ℝ (Fin K))) (hN : N.Nonempty) (v : EuclideanSpace ℝ (Fin K)),
    NetSetting μ A S O χ Q Qb T ω η h N → (μ.restrict A).support = A →
      hPop μ A Qb v = (supOn A Q v : EReal) ∧ |netMax N hN T v - supOn A Q v| ≤ ‖v‖ * (ω + η)

/-- "Consequently": the net band `𝔪 ± max_𝒩 ⟨±𝐞_K, T⟩` lies inside the band of `T`, its edge deficit against the
population band is at most `E_K{ω_S(h) + η}`, and under the support condition it is two-sided. -/
def net_inner_band_edges : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A S O : Set (EuclideanSpace ℝ (Fin K)))
    (χ : EuclideanSpace ℝ (Fin K) → EReal) (Q Qb T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (ω η h : ℝ) (N : Finset (EuclideanSpace ℝ (Fin K))) (hN : N.Nonempty) (𝒯 : Type) (m : 𝒯 → ℝ)
    (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (EK : ℝ),
    NetSetting μ A S O χ Q Qb T ω η h N → (∀ t, ‖e t‖ ≤ EK) →
      (∀ t, m t + netMax N hN T (e t) ≤ m t + supOn A T (e t) ∧
        m t - supOn A T (-e t) ≤ m t - netMax N hN T (-e t)) ∧
      (∀ t, (m t : EReal) + hPop μ A Qb (e t) ≤ ((m t + netMax N hN T (e t) + EK * (ω + η) : ℝ) : EReal) ∧
        ((m t - netMax N hN T (-e t) - EK * (ω + η) : ℝ) : EReal) ≤ (m t : EReal) - hPop μ A Qb (-e t)) ∧
      ((μ.restrict A).support = A → ∀ t,
        |(m t + netMax N hN T (e t)) - (m t + supOn A Q (e t))| ≤ EK * (ω + η) ∧
        |(m t - netMax N hN T (-e t)) - (m t - supOn A Q (-e t))| ≤ EK * (ω + η) ∧
        hPop μ A Qb (e t) = (supOn A Q (e t) : EReal) ∧ hPop μ A Qb (-e t) = (supOn A Q (-e t) : EReal))

/-! #### paper2 `prop:predline` -/

/-- (i) Budgets on the prediction line: for every rule `h`, every `(Q₀,Q₁) ∈ 𝒮_Θ` has
`W₂²(h#Q₀, h#Q₁) ≤ (sup_θ Δ_θ(h) + √β₀ + √β₁)²`. -/
def predline_certificate : Prop :=
  ∀ (d : ℕ) (Θ : Type) (C₀ C₁ : Θ → Measure (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (β₀ β₁ : ℝ) (Q₀ Q₁ : Measure (EuclideanSpace ℝ (Fin d))),
    Measurable h → (∀ θ, IsProbabilityMeasure (C₀ θ)) → (∀ θ, IsProbabilityMeasure (C₁ θ)) →
    IsProbabilityMeasure Q₀ → IsProbabilityMeasure Q₁ → 0 ≤ β₀ → 0 ≤ β₁ →
    (∃ θ, TauCeti.wassersteinEDist 2 ((C₀ θ).map h) (Q₀.map h) ^ 2 ≤ ENNReal.ofReal β₀ ∧
      TauCeti.wassersteinEDist 2 ((C₁ θ).map h) (Q₁.map h) ^ 2 ≤ ENNReal.ofReal β₁) →
      TauCeti.wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ^ 2 ≤
        ((⨆ θ, TauCeti.wassersteinEDist 2 ((C₀ θ).map h) ((C₁ θ).map h)) +
          ENNReal.ofReal (Real.sqrt β₀) + ENNReal.ofReal (Real.sqrt β₁)) ^ 2

/-- (i) Constant rules: no shift moves their predictions (realised disparity `0` for every pair of laws) and their
nominal disparity is `0` on every slice, so the certificate is `(√β₀ + √β₁)²`. -/
def predline_constant : Prop :=
  ∀ (d : ℕ) (Θ : Type) (C₀ C₁ : Θ → Measure (EuclideanSpace ℝ (Fin d))) (c : ℝ)
    (Q₀ Q₁ : Measure (EuclideanSpace ℝ (Fin d))),
    (∀ θ, IsProbabilityMeasure (C₀ θ)) → (∀ θ, IsProbabilityMeasure (C₁ θ)) →
    IsProbabilityMeasure Q₀ → IsProbabilityMeasure Q₁ →
      TauCeti.wassersteinEDist 2 (Q₀.map fun _ => c) (Q₁.map fun _ => c) = 0 ∧
      (⨆ θ, TauCeti.wassersteinEDist 2 ((C₀ θ).map fun _ => c) ((C₁ θ).map fun _ => c)) = 0

/-- (i) `(C_δ)` reduces to the nominal disparity with a shifted target: `(Δ + √β₀ + √β₁)² ≤ δ ⇔ Δ ≤ √δ − √β₀ − √β₁`. -/
def predline_constrained : Prop :=
  ∀ (Δ β₀ β₁ δ : ℝ), 0 ≤ Δ → 0 ≤ β₀ → 0 ≤ β₁ → 0 ≤ δ →
    ((Δ + Real.sqrt β₀ + Real.sqrt β₁) ^ 2 ≤ δ ↔ Δ ≤ Real.sqrt δ - Real.sqrt β₀ - Real.sqrt β₁)

/-- The proof's "the budget term … adds a constant to `(P_η)`" is false: with `c = √β₀ + √β₁ > 0` the penalised
objective `R(h) + η(Δ(h) + c)²` is not `R(h) + ηΔ(h)² + const`, and the two objectives have different minimisers
(two rules, `η = c = 1`, `R = (0, 3/2)`, `Δ = (1, 0)`). -/
def predline_penalised_not_shift : Prop :=
  ∃ (R Δ : Fin 2 → ℝ) (η c : ℝ), 0 < η ∧ 0 < c ∧ (∀ i, 0 ≤ R i ∧ 0 ≤ Δ i) ∧
    (∀ k : ℝ, ∃ i, R i + η * (Δ i + c) ^ 2 ≠ R i + η * Δ i ^ 2 + k) ∧
    (∀ i, R 0 + η * Δ 0 ^ 2 ≤ R i + η * Δ i ^ 2) ∧ R 1 + η * (Δ 1 + c) ^ 2 < R 0 + η * (Δ 0 + c) ^ 2

/-- (iii) For a coupling `π_s` of the two look-back laws and `M_s = E_π(X'−X)(X'−X)ᵀ`:
`W₂²(w#P^past, w#P^now) ≤ wᵀM_sw` for every `w`. -/
def predline_lookback : Prop :=
  ∀ (d : ℕ) (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) (M : Matrix (Fin d) (Fin d) ℝ),
    IsProbabilityMeasure π → (∀ i j, Integrable (fun z => (z.2 - z.1) i * (z.2 - z.1) j) π) →
    (∀ i j, M i j = ∫ z, (z.2 - z.1) i * (z.2 - z.1) j ∂π) →
      ∀ w : EuclideanSpace ℝ (Fin d),
        TauCeti.wassersteinEDist 2 ((π.map Prod.fst).map fun x => ⟪w, x⟫)
            ((π.map Prod.snd).map fun x => ⟪w, x⟫) ^ 2 ≤
          ENNReal.ofReal (dotProduct (WithLp.ofLp w) (Matrix.mulVec M (WithLp.ofLp w)))

/-- (iii) "The set with budget `1` need not contain the look-back law": `P^past = δ₀`, `P^now = ½(δ_{e₁} + δ_{e₂})`
on `ℝ²`, `π` their (only) coupling, `M = ½I ≻ 0`, and `P^now` is not in the anisotropic set of budget `1`. -/
def predline_budget_one_excludes : Prop :=
  ∃ (π : Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) (M : Matrix (Fin 2) (Fin 2) ℝ),
    IsProbabilityMeasure π ∧ M.PosDef ∧ (∀ i j, Integrable (fun z => (z.2 - z.1) i * (z.2 - z.1) j) π) ∧
    (∀ i j, M i j = ∫ z, (z.2 - z.1) i * (z.2 - z.1) j ∂π) ∧
    ¬ StatFormal.RobustEquality.Quick.InAniso M 1 (π.map Prod.fst) (π.map Prod.snd)

/-! #### TM `lem:separation` -/

/-- `eq:sep`: for nonempty `A, B` and `‖f‖ ≤ 1`, `dist(A,B) ≥ inf_A ⟨f,·⟩ − sup_B ⟨f,·⟩`. -/
def separation : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A B : Set H) (f : H),
    A.Nonempty → B.Nonempty → ‖f‖ ≤ 1 → sepVal f A B ≤ (setDist A B : EReal)

/-- Nearest points exist for nonempty weakly compact `A, B`. -/
def separation_nearest_exists : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A B : Set H),
    A.Nonempty → B.Nonempty → IsCompact (toWeakSpace ℝ H '' A) → IsCompact (toWeakSpace ℝ H '' B) →
      ∃ a ∈ A, ∃ b ∈ B, ‖a - b‖ = setDist A B

/-- Attainment: for convex weakly compact `A, B` with `dist(A,B) > 0` and nearest points `a*, b*`,
`f* = (a* − b*)/‖a* − b*‖` has `‖f*‖ = 1` and `sep(f*; A, B) = dist(A,B)`. -/
def separation_attained : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (A B : Set H) (a b : H),
    Convex ℝ A → Convex ℝ B → IsCompact (toWeakSpace ℝ H '' A) → IsCompact (toWeakSpace ℝ H '' B) →
    0 < setDist A B → a ∈ A → b ∈ B → ‖a - b‖ = setDist A B →
      ‖(‖a - b‖⁻¹) • (a - b)‖ = 1 ∧ sepVal ((‖a - b‖⁻¹) • (a - b)) A B = (setDist A B : EReal)

/-! #### TM `thm:rffjoint` -/

/-- `thm:rffjoint`: given the feature event of `lem:rffkernel` at level `δ/3`, one measurable event of probability
`≥ 1 − δ` jointly over the two samples and the feature draw on which `|D̂^{(r)} − D| ≤ r_n(α,δ/3) + r_m(α,δ/3) +
2√ε` and `|D̂^{(r)} − D̂| ≤ 4ε/(D̂^{(r)} + D̂)`. -/
def rffjoint : Prop :=
  ∀ (𝒳 H H' Ω : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [MeasurableSpace Ω] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (φ : 𝒳 → H) (z : Ω → 𝒳 → H') (κ α δ ε : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → (∀ ω, StronglyMeasurable (z ω)) → 0 ≤ α → α < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → 0 ≤ ε →
    (∃ Ef : Set Ω, MeasurableSet Ef ∧ ENNReal.ofReal (1 - δ / 3) ≤ ν Ef ∧
      ∀ ω ∈ Ef, ∀ x y : 𝒳, |⟪z ω x, z ω y⟫ - ⟪φ x, φ y⟫| ≤ ε) →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳) × Ω), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod
          ((Measure.pi fun _ : Fin m => Q).prod ν)) E ∧
        ∀ s ∈ E,
          |Demp (z s.2.2) s.1 s.2.1 α - Dpop φ P Q α| ≤
              StatFormal.TrimmedMMD.rn κ α (δ / 3) n + StatFormal.TrimmedMMD.rn κ α (δ / 3) m + 2 * Real.sqrt ε ∧
          (0 < Demp (z s.2.2) s.1 s.2.1 α + Demp φ s.1 s.2.1 α →
            |Demp (z s.2.2) s.1 s.2.1 α - Demp φ s.1 s.2.1 α| ≤
              4 * ε / (Demp (z s.2.2) s.1 s.2.1 α + Demp φ s.1 s.2.1 α))

/-! #### NN `prop:noncentral-tube` -/

/-- The Gaussian–affine core: for `X ∼ N(0, σ²I)` on `E` and a nonempty affine subspace `V` of codimension `c`,
`Pr{dist(X, V) ≤ δ} = F_{χ²_c(λ)}(δ²/σ²)` with `λ = dist(0, V)²/σ²`. -/
def noncentral_tube_affine : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (V : AffineSubspace ℝ E) (σ δ : ℝ), (V : Set E).Nonempty → 0 < σ → 0 < δ →
      (isoGauss E σ).real {x | Metric.infDist x V ≤ δ} =
        (ncChiSq (Module.finrank ℝ E - Module.finrank ℝ V.direction)
          (Metric.infDist 0 (V : Set E) ^ 2 / σ ^ 2)).real (Iic (δ ^ 2 / σ ^ 2))

open StatFormal.NNFibers.Wave1 in
/-- `eq:lambda-s`: `dist(0, Γ̄_s)² = Σ_i (n_i ‖ω_i‖² + ‖a_i‖²/n_i)` (Euclidean norm on `Θ_m`). -/
def lambda_s : Prop :=
  ∀ (din dout q m j : ℕ) (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j),
    Function.Surjective g → Metric.infDist 0 (eucPar '' closureSet θs g) ^ 2 = lamS θs g

open StatFormal.NNFibers.Wave1 in
/-- `prop:noncentral-tube`: for `X ∼ N(0, σ²I)` on `Θ_m` and `δ > 0`,
`Pr{dist(X, Γ̄_s) ≤ δ} = F_{χ²_{c_s}(λ_s)}(δ²/σ²)`, `c_s = (m − j)d_in + (q + j)d_out`, `λ_s = σ⁻² Σ_i (…)`. -/
def noncentral_tube : Prop :=
  ∀ (din dout q m j : ℕ) (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j) (σ δ : ℝ),
    Function.Surjective g → 0 < σ → 0 < δ →
      (isoGauss (EuclideanSpace ℝ (Fin m × (Fin din ⊕ Fin dout))) σ).real
          {x | Metric.infDist x (eucPar '' closureSet θs g) ≤ δ} =
        (ncChiSq ((m - j) * din + (q + j) * dout) (lamS θs g / σ ^ 2)).real (Iic (δ ^ 2 / σ ^ 2))

end Claims

end StatFormal.Wave17a
