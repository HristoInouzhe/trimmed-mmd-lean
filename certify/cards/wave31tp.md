# Fidelity card — wave 31tp: the classical Fourier/RKHS library behind trimmed-mmd (**Annals of Statistics version**, Section 5.2 and Section S4), with two composed paper claims (`prose:ex-separated-matern` without the bridge, the C^∞ clause of `rem:qdens`)

Lean: `StatFormal/Wave31tp/Statements.lean` (45 claim definitions for the drafted items L1–L30; new definitions `ft2`, `specDens`,
`nativeN`, `sobolevS`, `dilate`, `dilateR`, `mollify`, `specMeas`, `fourierFeature`, `kSpec`, `besselPot`, `maternK`, `ftMeas`,
`IsPosDefFun`, `jBall`, `gaussMixDens`, `gaussMix`; frozen 2026-11-21 before any proof, commit `5baeb23`, sha256 `501e5051…7f16`,
locked with its 100 local imports). Routes `RouteF`, `RouteK`, `RouteG`, `RouteE`, `RouteM`, `RouteS`, `RouteV`, `RouteN`, `RouteMat`,
`RouteR`, `RouteC` (untrusted) on the library folders `StatFormal/Lib/{FourierL2, TIKernel, FourierTaylor, FourierOps, JBall,
GaussMix, GaussMoments, MomentPoly, SobolevFin, NativeChar, Matern, RKHSReg}`; `Proofs.lean` defines the 45 theorems, each of type
literally `Claims.X`; all proved, `#print axioms` propext, Classical.choice, Quot.sound for each.
Paper id `trimmed-mmd (jmlr)` (face `Papers/TrimmedMMDJMLR`; the AoS version is tracked on this page, as for Waves 31tn/31to). Branch
`tmmd-aos-fullstack` (worktree `~/projects/StatFormal-tmmd-aos`), on top of `4015890`.
Scope (author decision, 2026-11-21, full-stack campaign `~/projects/tmmd-aos-brief/fullstack/CAMPAIGN.md`): every classical fact used by
the Fourier-analytic results of the AoS version is proved in the library, with no textbook bridge. This wave is the library (general
statements on any finite-dimensional real inner-product space, Mathlib's Fourier convention) and two composed claims; the paper's
Fourier results themselves (angular convention) are composed on it in Wave 31tq (`PLAN.md` §4.2).
Critic (independent AI reviewer, before the freeze, 2026-11-21, `tmmd-aos-brief/fullstack/CRITIC_31tp.md`): v1 NOT READY TO FREEZE
(5 blocking items: L15 even part ψ_e and the real structure of L²(ψ·vol; ℂ); S1 general V; L12(d) form; S2 total definitions; L22
Matérn family with amplitude and length-scale), all applied (`DIFF_31tp.md`); re-check of v2 READY TO FREEZE with notes n1–n4, applied
before the freeze.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-21 — PASS with notes. Scope: all 45 claims,
back-translated from the frozen `Statements.lean` and its definitions before the paper was opened; the reviewer had read this card's own
back-translation while locating files, so the step was blind to the paper but not to the card. Hashes: `Statements.lean` matches the
lock, and no frozen file, lock entry, source copy or target row changed after `5baeb23`. Printed text: compared with trimmed-mmd `aos/`
at `6ac0ca7`, where the formalised passages are unchanged since `c8058c0`. Findings: 32 claims faithful and 13 faithful with a note.
The notes cover Mathlib's Fourier convention for eq:newnative, eq:newbochner, eq:newbandlim and eq:newmomentdecay (the angular form is
left to Wave 31tq), Matérn kernels defined by their spectral density, and unused or weaker hypotheses (generalisations). There is no
undeclared stronger hypothesis, unguarded junk value, vacuous hypothesis set or restated conclusion. Instance probes: the `Laplacian`
is `InnerProductSpace.instLaplacian`, `𝓕` on L² is the unitary `Lp.fourierTransformₗᵢ`, and the real inner product on L²(ψ·vol; ℂ) is
∫Re(G·conj F). Bridges: B1 `ContainsSmoothCompact` is proved (L19b) and composed into the sentence after Example 5.2 (L29); C4, the C^∞
clause of Remark S5.6, is closed for every element of ℋ, the witness included (L30). The gate was re-run: CERTIFIED 4033, ALIASES OK
3976. Full audit: `tmmd-aos-brief/fullstack/AUDIT_31tp.md`. Non-blocking notes there: docstrings in `Lib/TIKernel` (44 of 122), one
duplicate helper (`innerₗ_flip'`), the stale `docs/trimmed-mmd-aos.md`, the README link and the alias grouping in
`gen_papers_face.py`, and main-text line numbers that refer to `c8058c0`.
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tp.md` at freeze (v2 + n1–n4): whole file sha256
`1f73ccaa14c4f37d12b30c3986f5713c90f1efb19c29d04552b13233d40a2964` (411 lines; copy committed as
`certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tp.md`, same hash); the claims block (line 14 to the end) sha256
`9ca257e3e5ece16b43ccc2cd8acedd09b5d539e33b11fed73edb0494be97cad1`. v1 kept as `fullstack/work/NEW_STATEMENTS_31tp.v1.md`.
Printed source: trimmed-mmd `aos/` at `c8058c0` (sha256 prefixes `sections/05_rates.tex` `d4b6fe12293f`, `supplement/S4_rates.tex`
`1632f5261e36`, `supplement/S5_trimming.tex` `6bb834eb323c`). Line numbers below: `main` = `05_rates.tex`, `S4` = `S4_rates.tex`,
`S5` = `S5_trimming.tex`. Gap inventory `fullstack/GAPS.md` (closed here: A13 the Fourier setting eq:newnative, eq:newbochner; B1 the
bridge `Wave31tg.ContainsSmoothCompact`; C4 the C^∞ clause of Remark S5.6; E3 characteristic kernels; the library halves of A5, A8, A10,
A11, A12).

## Targets (45 claims in `StatFormal.Wave31tp.Proofs`; all in `certify/targets.toml`, theorem = `StatFormal.Wave31tp.<name>`)
| item | label (abridged) | claim |
|---|---|---|
| L1 | `lib:plancherel` | `plancherel` |
| L2 | `lib:ft2-agree` | `ft2_ae` |
| L3 | `lib:ftmeas` | `ftMeas_facts` |
| L4 | `lib:taylor-cexp` | `taylor_cexp` |
| L5 | `eq:newmomentdecay` (S4 :850-857) | `moment_decay` |
| L6 | `lib:dilate` | `dilate_facts` |
| L7 | `lib:laplacian-fourier` | `laplacian_fourier` |
| L8 | `lib:mollify`, `lib:mollify-cont` | `mollify_smooth`, `mollify_cont` |
| L9 | `lib:sobolev-finite` | `sobolev_smooth_finite` |
| L10 | `lib:translation`, `lib:translation-indicator` | `translation_plancherel`, `translation_indicator` |
| L11 | `lib:jball`, `lib:jball-one` | `jball_facts`, `jball_one` |
| L12 | `lib:gram-iso`, `lib:gram-rep`, `lib:gram-mmd`, `lib:rkhs-canonical` | `gram_iso`, `gram_rep`, `gram_mmd`, `rkhs_canonical` |
| L13 | `lib:bochner-integrable` | `bochner_integrable` |
| L14 | `lib:gram-profile` | `gram_profile` |
| L15 | `lib:fourier-feature`, `lib:feature-exists` | `fourier_feature`, `feature_exists` |
| L16 | `eq:newbochner` (S4 :442-447) | `mmd_fourier` |
| L17 | `eq:newnative` inclusion (S4 :436-441) | `native_incl` |
| L18 | `eq:newnative` equality (S4 :436-441) | `native_char` |
| L19 | `lib:sobolev-incl`; `prose:ex-separated-matern` (the bridge proved) | `sobolev_incl`, `containsSmoothCompact_of_spec` |
| L20 | `lib:bandlimited`; `eq:newbandlim` (S4 :760-766) | `bandlimited`, `bandlimited_gauss` |
| L21 | `lib:gauss-spec`, `lib:laplace-spec` | `gauss_spec`, `laplace_spec` |
| L22 | `lib:matern`, `lib:matern-one` | `matern_facts`, `matern_one` |
| L23 | `lib:gauss-moments` | `gauss_moments` |
| L24 | `lib:rkhs-smooth`, `lib:gauss-smooth` | `rkhs_smooth`, `gauss_smooth` |
| L25 | `lib:characteristic-spec` | `characteristic_spec` |
| L26 | `lib:rkhs-vanish` | `rkhs_vanish` |
| L27 | `lib:support-density`, `lib:gauss-mixture`, `lib:gauss-mixture-distinct` | `support_density`, `gaussMix_facts`, `gaussMix_distinct` |
| L28 | `lib:moment-poly`, `lib:moment-poly-scale` | `moment_poly`, `moment_poly_scale` |
| L29 | `prose:ex-separated-matern` (main :54-56, S4 :27-32; no bridge) | `matern_interpolation_free` |
| L30 | `rem:qdens`, the C^∞ clause (S5 :331-336) | `gauss_regular_smooth` |

## Encodings (declared; full list in the Lean header and `NEW_STATEMENTS_31tp.md` "Common setting")
* Domain: any finite-dimensional real inner-product space `V` with Borel σ-algebra and `volume`, `d = finrank ℝ V`; `EuclideanSpace ℝ
  (Fin d)` only where a frozen definition needs coordinates (`jBall`, `gaussMixDens`) or the shape of an earlier frozen claim
  (L19(b), L27(b,c), L29, L30). Feature spaces `H : Type`.
* Fourier convention: Mathlib's, `𝐞 t = e^{2πit}`, `𝓕f(ξ) = ∫ 𝐞(−⟪x,ξ⟫) f x`; the paper's `ĝ(ω) = 𝓕g(ω/2π)`; its weight `(1+|ω|²)^s`
  is `(1 + 4π²‖ξ‖²)^s` here. The dictionary is proof-level in Wave 31tq.
* `ft2`: a representative of Mathlib's unitary L² transform, junk `0` off L², used only under `MemLp f 2`, inside `∫⁻` or a.e.;
  `specDens k₀ = Re 𝓕k₀` (L14 proves `𝓕k₀` real, ≥ 0 and even, nothing lost); `nativeN`, `sobolevS` lower integrals in `[0,∞]`
  (`0/0 = 0`, `x/0 = ⊤` are the right readings); `ftMeas μ ξ = ∫ 𝐞(−⟪x,ξ⟫) dμ`.
* `IsPosDefFun`: Bochner–Rudin "positive definite" (Wendland's "positive semi-definite"), re/im explicit; Wendland's strict notion is
  `Wave31tg.StrictlyPDOn`.
* "f ∈ ℋ" is the house encoding: `g : H` represents `f` when `∀ x, ⟪g, φ x⟫_ℝ = f x`; `‖f‖_ℋ` is the minimal `‖g‖` (attained: L12(d),
  L18). Translation-invariant feature map: `⟪φ x, φ y⟫ = k₀ (x − y)`.
* Matérn kernels by their spectral density (Bessel potentials by Gaussian subordination, `besselPot`; family `maternK s a ℓ = a·G_s(·/ℓ)`,
  `ν = s − d/2`; M. L. Stein 1999 §2.7, Rasmussen–Williams eq. 4.15). The closed form with the Bessel function `K_ν` is not formalised
  (Mathlib has no `K_ν`); `ν = 1/2` is proved (L22(b)).
* Gaussian mixtures: Mathlib's `multivariateGaussian` laws with nondegenerate covariances; the explicit density is proved (L27(b)).

## Covered — back-translation and deviations
* L1 `plancherel`: for `f, g ∈ L¹ ∩ L²(V; ℂ)`: `𝓕f ∈ L²`, `∫|𝓕f|² = ∫|f|²`, `∫ 𝓕f · conj 𝓕g = ∫ f · conj g`. Faithful (Rudin RCA 9.13).
* L2 `ft2_ae`: on `L¹ ∩ L²`, `ft2 f = 𝓕f` a.e. and the L² inverse transform `= 𝓕⁻f` a.e. Faithful.
* L3 `ftMeas_facts`: finite μ, ν: `ftMeas μ` continuous, `‖ftMeas μ‖ ≤ μ(V)`, `ftMeas μ 0 = μ(V)`, equals `𝓕f` when `μ = f·vol` with
  `f ≥ 0` integrable, and `ftMeas μ = ftMeas ν ⇒ μ = ν`. Faithful.
* L4 `taylor_cexp`: `|e^{it} − Σ_{j<N} (it)^j/j!| ≤ |t|^N/N!` for all real `t`, `N ∈ ℕ`. Faithful (sharp form).
* L5 `moment_decay` (eq:newmomentdecay in Mathlib's convention): finite ρ₁, ρ₂ carried by `[x₀ − W, x₀ + W]`, `W ≥ 0`, `N ≥ 1`, equal
  moments of `(x − x₀)^j`, `j < N`: `|ftMeas ρ₁ ξ − ftMeas ρ₂ ξ| ≤ (ρ₁(ℝ) + ρ₂(ℝ)) min(1, (2π|ξ|W)^N/N!)`. Faithful (the proof needs
  neither `N ≥ 1` nor `W ≥ 0`; harmless).
* L6 `dilate_facts`: `b ∈ L¹`, `w > 0`: `b_w = w^{−d} b(·/w)` integrable with the same integral, `𝓕b_w(ξ) = 𝓕b(wξ)`, `‖𝓕b‖ ≤ ‖b‖₁`. Faithful.
* L7 `laplacian_fourier`: `b ∈ C_c^∞(V; ℂ)`, `m ∈ ℕ`: `𝓕(Δ^m b)(ξ) = (−4π²‖ξ‖²)^m 𝓕b(ξ)` (Mathlib's `Laplacian.laplacian`) and, for
  `ξ ≠ 0`, `‖𝓕b(ξ)‖ ≤ ‖Δ^m b‖₁ (4π²‖ξ‖²)^{−m}`. Faithful.
* L8 `mollify_smooth`: `E` measurable bounded, `b ∈ C^∞`, `b ≥ 0`, `∫b = 1`, `supp b ⊆ B̄(0,1)`, `w > 0`: `1_E ⋆ b_w` is `C^∞`, compactly
  supported, in `[0,1]`, `= 1` where `B̄(x,w) ⊆ E`, `= 0` where `B̄(x,w) ∩ E = ∅`, in `L¹ ∩ L²`, with `𝓕 = 𝓕1_E · 𝓕b(w·)`.
  `mollify_cont`: `vol(E) < ∞`, `b` bounded continuous integrable probability density: `1_E ⋆ b` continuous, in `L¹ ∩ L²`, in `[0,1]`,
  `𝓕 = 𝓕1_E · 𝓕b`. Faithful.
* L9 `sobolev_smooth_finite`: `g ∈ C_c^∞(V; ℂ)`, every real `s`: `sobolevS s g < ∞`. Faithful.
* L10 `translation_plancherel`: `f ∈ L¹ ∩ L²`: `∫|𝓕f|²|𝐞(⟪h,ξ⟫) − 1|² = ∫|f(x+h) − f(x)|²`. `translation_indicator`: `vol(E) < ∞`:
  `‖1_E(·+h) − 1_E‖₂² = vol(E Δ (E − h))` and `= vol(E Δ (E + h))`. Faithful.
* L11 `jball_facts`: `j_d(y) = vol(B)⁻¹ ∫_B cos(y v₁)`: continuous, even, `j_d(0) = 1`, `|j_d| ≤ 1`, `j_d(y) < 1` for `y ≠ 0`, `→ 0` at
  infinity, `j_d([1,∞))` bounded above with `sup < 1`, and the rotation identity `vol(B_r)⁻¹ ∫_{B_r} cos⟪h,ξ⟫ dh = j_d(r‖ξ‖)` on every
  `V` of dimension `d`, `r > 0`. `jball_one`: `j₁(y) = sin y / y` (`y ≠ 0`) and `1 − sup_{y≥1} j₁ = 1 − sin 1` (the paper's `c₁`, S4 :674). Faithful.
* L12 `gram_iso`, `gram_rep`: equal Gram functions give a linear isometry of the closed span of `φ(𝒳)` carrying `φ` to `φ′`, and every
  representer for φ has one for φ′ of no larger norm. `gram_mmd`: under (A1) (strongly measurable, `‖φ‖ ≤ κ`) the norms of differences
  of weighted mean embeddings, `Wave30tj.mmd`, `Wave8a.dTrim`, `Dpop` (D_α) and `Demp` (D̂_α) agree for φ and φ′, and φ′ satisfies (A1).
  `rkhs_canonical`: for any Mathlib `RKHS ℝ H 𝒳 ℝ`, `x ↦ kerFun H x 1` reproduces, has Gram `kernel H y x 1`, dense span; any φ′ with that
  Gram represents exactly the functions of `H`, with a minimal representer of norm `‖f‖_H`. Faithful (the paper's "the RKHS depends only
  on k", S4 :433).
* L13 `bochner_integrable`: `k₀ : V → ℂ` continuous, integrable, positive definite: `k₀(−z) = conj k₀(z)`, `k₀(0)` real, `|k₀| ≤ k₀(0)`,
  `𝓕k₀` real and ≥ 0, integrable, `∫𝓕k₀ = k₀(0)`, `𝓕⁻𝓕k₀ = k₀` everywhere. Faithful (Rudin, Fourier Analysis on Groups §1.4–1.5).
* L14 `gram_profile`: `⟪φx, φy⟫ = k₀(x − y)` (real `k₀`, any real inner-product `H`): evenness, `|k₀| ≤ k₀(0)`, `‖φx − φy‖² = 2(k₀(0) −
  k₀(x − y))`, positive definiteness, continuity of φ ⇔ of `k₀` at 0 ⇔ of `k₀`; integrable: `𝓕k₀` is the cosine transform and `specDens`
  is even; continuous integrable: `specDens ≥ 0`, integrable, `∫ = k₀(0)`, cosine inversion. Faithful.
* L15 `fourier_feature`: `ψ ≥ 0` measurable integrable: `L²(ψ·vol; ℂ)` (real structure `L2.innerProductSpace`) complete and separable,
  the feature map continuous, a.e. `𝐞(−⟪x,·⟫)`, Gram `kSpec ψ (x − y)`, `kSpec ψ` continuous, even, `|kSpec ψ| ≤ kSpec ψ 0 = ∫ψ`,
  `kSpec ψ = 𝓕ψ_e = 𝓕⁻ψ_e` (`ψ_e` the even part), and if `kSpec ψ` is integrable, `𝓕 kSpec ψ = ψ_e` a.e. (everywhere for continuous ψ).
  `feature_exists`: for continuous integrable PD real `k₀`, `specDens k₀` is continuous, even, ≥ 0, integrable, `kSpec (specDens k₀) =
  k₀`, and its Fourier feature map has Gram `k₀`. Faithful (generalisation: any ψ; the even part is the critic's correction).
* L16 `mmd_fourier` (eq:newbochner in Mathlib's convention): continuous integrable `k₀`, `H` complete: φ continuous, strongly measurable,
  `‖φx‖ = √k₀(0)`; for finite μ₁, μ₂: `specDens·|ftMeas μ₁ − ftMeas μ₂|²` integrable, `‖∫φdμ₁ − ∫φdμ₂‖² = ∫ specDens |ftMeas μ₁ −
  ftMeas μ₂|²`, and the double-integral formula. Faithful (finite measures: a generalisation of the printed probability measures).
* L17 `native_incl`: continuous `f ∈ L²` with `nativeN k₀ f < ∞` is represented with `‖g‖² ≤ nativeN`; on `L¹ ∩ L²`, `nativeN` is the
  integral of `|𝓕f|²/specDens`. L18 `native_char`: every `g` gives a continuous L² function with `nativeN ≤ ‖g‖²`, with equality on the
  closed span of `φ(V)`; a continuous `f` is represented iff `f ∈ L²` and `nativeN f < ∞`, and then a minimal representer has
  `‖g₀‖² = nativeN f`. Together: eq:newnative with "=" (Wendland Thm 10.12) in Mathlib's convention. Faithful.
* L19 `sobolev_incl`: `specDens k₀ ≥ c(1+4π²‖ξ‖²)^{−s}`, `c > 0`: continuous L² `f` with `sobolevS s f < ∞` is represented with `‖g‖² ≤
  sobolevS/c` (Wendland Cor 10.13). `containsSmoothCompact_of_spec`: under the same lower bound on `ℝ^d`, `Wave31tg.ContainsSmoothCompact
  φ` holds — the bridge declared in Wave 31tg is now a theorem. Faithful.
* L20 `bandlimited`: `specDens ≥ m > 0` on `‖ξ‖ ≤ Ω`, `ft2 f = 0` a.e. off the band: `f` represented with `‖g‖² ≤ ‖f‖₂²/m`.
  `bandlimited_gauss` (eq:newbandlim in Mathlib's convention): Gaussian kernel `e^{−‖x−y‖²/(2σ²)}` on V: `‖g‖² ≤ (2πσ²)^{−d/2}
  e^{2π²σ²Ω²} ‖f‖₂²`. Faithful (`0 ≤ Ω` not needed by the proof; harmless).
* L21 `gauss_spec`: the Gaussian profile is continuous, integrable, `𝓕 = (2πσ²)^{d/2} e^{−2π²σ²‖ξ‖²}`. `laplace_spec`: `e^{−|x|}` on ℝ is
  continuous, integrable, `𝓕 = 2/(1 + 4π²ξ²)`. Faithful.
* L22 `matern_facts`: `s > d/2`: the subordination integrand is integrable on `(0,∞)` for every x; `G_s` continuous, positive, maximal at
  0, integrable, `∫G_s = 1`, `𝓕G_s = (1+4π²‖ξ‖²)^{−s}`; for `a, ℓ > 0`, `a·G_s(·/ℓ)` continuous, positive, integrable, `𝓕 = aℓ^d(1 +
  4π²ℓ²‖ξ‖²)^{−s}`, and `aℓ^d max(1,ℓ²)^{−s}(1+4π²‖ξ‖²)^{−s} ≤ specDens ≤ aℓ^d max(1,ℓ^{−2})^s (1+4π²‖ξ‖²)^{−s}`. `matern_one`: on ℝ,
  `G₁(x) = e^{−|x|}/2` (ν = ½, the Laplace kernel). Faithful (main :116-117, S4 :500-501).
* L23 `gauss_moments`: on ℝ, `∫(2πξ)^{2N} specDens(e^{−x²/(2σ²)}) = (2N−1)‼ σ^{−2N}` (integrable). Faithful (S4 :896, :935).
* L24 `rkhs_smooth`: `∫‖ξ‖^{2m} specDens < ∞` ⇒ every `x ↦ ⟪g, φx⟫` is `C^m`. `gauss_smooth`: Gaussian kernel ⇒ `C^∞`
  (Steinwart–Christmann Cor 4.36). Faithful.
* L25 `characteristic_spec`: `specDens > 0` a.e. ⇒ the mean embedding is injective on finite measures, `ZeroSet.Characteristic φ` (A3)
  and `Wave31tg.StrictlyPDOn φ univ`. Faithful (S4 :644, main :269).
* L26 `rkhs_vanish`: every `x ↦ ⟪g, φx⟫` tends to 0 as `‖x‖ → ∞` (Riemann–Lebesgue). Faithful.
* L27 `support_density`: `U` open, `p` continuous and ≥ 0 on U: for `x ∈ U`, `x ∈ supp((1_U p)·vol) ⇔ x ∈ closure{y ∈ U : p(y) > 0}`.
  `gaussMix_facts`: weights > 0 summing to 1, covariances ≻ 0: the mixture law equals `gaussMixDens·vol`, the density is real-analytic on
  ℝ^d and positive. `gaussMix_distinct`: two distinct such mixtures have densities differing somewhere in every nonempty open set.
  Faithful (S4 :485-493, main :73-74; `support_density` does not use `p ≥ 0`).
* L28 `moment_poly`: `T > 0`, `N ≥ 1`: every `M ∈ ℝ^N` has exactly one polynomial `G`, `deg G < N`, with `∫_{−T}^{T} t^j G = M_j` for
  `j < N`. `moment_poly_scale`: the scaling identities between `[−T,T]` and `[−1,1]`. Faithful (S4 :905-911).
* L29 `matern_interpolation_free`: on ℝ^d, `H` complete, Gram `k₀(x−y)` with either `k₀ = a·G_s(·/ℓ)` (`s > d/2`, `a, ℓ > 0`) or `k₀`
  continuous integrable with a spectral lower bound `c(1+4π²‖ξ‖²)^{−s}`: for `S_R`, `S_P`, `S_Q` pairwise `ε`-apart with `S_P`, `S_Q`
  bounded, some `g` is `0`, `1`, `−1` on them. This is `prose:ex-separated-matern` (main :54-56, S4 :27-32) with **no bridge**
  (generalisation: any kernel with a Sobolev-type spectral lower bound). Completeness of H is a genuine hypothesis (the paper's RKHS).
* L30 `gauss_regular_smooth`: Gaussian kernel on ℝ^d: every `Wave12c.witFn f φ` is `C^∞` and vanishes at infinity. The C^∞ clause of
  `rem:qdens` (S5 :331-336), strengthening the certified `Wave31th.gaussian_regular` (C¹).

## Proof route (untrusted)
* F: `Lib/FourierL2/Agree.lean` identifies the L² and integral transforms on L¹∩L² through tempered distributions (L2), then Plancherel
  with polarization from Mathlib's unitary `Lp.fourierTransformₗᵢ` (L1). `Lib/FourierTaylor`: L4 by the boundary comparison
  `image_norm_le_of_norm_deriv_right_le_deriv_boundary` with `R_{N+1}' = iR_N` (t < 0 by conjugation); L5 by expanding
  `𝐞(−(x−x₀)ξ)` and cancelling matched moments. `Lib/FourierOps`: L6 change of variables; L7 Mathlib's Laplacian as a Schwartz Fourier
  multiplier (`laplacian_eq_fourierMultiplierCLM`) transferred by `toSchwartzMap`; L8 `contDiff_convolution_right`, dominated convergence,
  `Real.fourier_mul_convolution_eq`; L10 `fourierIntegral_comp_add_right` and L1. `Lib/SobolevFin`: L9 via Schwartz decay
  (`integrable_pow_mul`) and L2; L19(b) from L9 and L19(a); L20 from Plancherel in ℝ≥0∞ form and L17. `Lib/JBall`: continuity, strict
  bound by positivity of `1 − cos`, Riemann–Lebesgue on the ball indicator, compactness for the sup, an orthonormal basis through ξ/‖ξ‖
  for the rotation identity; `j₁` by `EuclideanSpace ℝ (Fin 1) ≃ ℝ` and concavity of sin on `[0, π]`.
* K: `Lib/TIKernel/{PosDef, Window, Bochner}` — L13 by ball windows and integral positive definiteness (averaging over i.i.d. points)
  for `𝓕k₀ ≥ 0`, Gaussian regularisation and monotone convergence for `∫𝓕k₀ = k₀(0)`, inversion; `Profile` (L14), `Feature` (L15: the
  Fourier feature map, a.e. inversion, cosine inversion), `Gram` (L12: the Gram isometry of the closed span, projections, Bochner
  integrals; Mathlib's `RKHS` link), `MMD` (L3, L16: `ftMeas = charFun`, Fubini), `Native` (L17: `G = 𝓕₂f/𝓕k₀` represents f in the
  Fourier feature map, transferred by the Gram isometry; L19(a)), `Spectra` (L21: `fourier_gaussian_innerProductSpace`; the Laplace
  transform as a cosine transform). `Lib/NativeChar` (L18): the reflection `G ↦ conj G(−·)` fixes the closed real span of the Fourier
  features; the Gram isometry maps `spanCl φ` into `spanCl Ψ`; for a symmetric G, `⟪G, Ψ·⟫ = 𝓕⁻(sG)` and its native functional is
  `‖G‖²`; minimal representer = projection. `Lib/Matern` (L22): domination of the subordination integrand by its value at 0, dominated
  convergence, Tonelli on `V × (0,∞)` with the heat-kernel integral, Fubini with the Gaussian transform, `fourier_dilate`; `G₁` by
  Fourier inversion against L21(b). `Lib/GaussMoments` (L23): `fourier_gaussian_pi`, `Γ(n + ½) = (2n−1)‼√π/2ⁿ`. `Lib/RKHSReg` (L24–L26,
  L30): every `⟪g, φ·⟫` is `Re 𝓕(specDens·conj G)` (Gram transfer to the Fourier feature map), spectral moments and
  `Real.contDiff_fourier`, Gaussian moments on V, Riemann–Lebesgue; L25 by L16 and `ftMeas_inj`, strict PD through atomic measures.
* S, P: `Lib/GaussMix` (L27: the support lemma for measures charging open sets; mixture density from the certified library
  `Lib/GaussianDensityD.multivariateGaussian_eq_withDensity`, analyticity, identity theorem on connected ℝ^d); `Lib/MomentPoly` (L28:
  vanishing moments give `∫G² = 0`, so the Hankel moment map is injective, hence bijective; substitution).
* Composed: L29 (`RouteC`) = Matérn spectral lower bound (L22) + L19(b) + the certified `Wave31tg.matern_interpolation`; L30 = L24(b) +
  L26 + L21(a).

## Junk-value audit
`ft2` (junk 0 off L²) is applied only under `MemLp f 2` and only inside `∫⁻` or a.e. statements; `𝓕` only to integrable functions;
`specDens` (Re of `𝓕k₀`) is the full transform where it matters (L14: real); `nativeN`, `sobolevS` in ℝ≥0∞: `x/0 = ⊤` for `x ≠ 0` and
`0/0 = 0` are the intended readings (L17 shows `ft2 f = 0` a.e. on `{specDens = 0}` when `nativeN < ∞`); every `Real.rpow` base is
positive (`1 + 4π²‖ξ‖²`, `4πt` on `t > 0`, `2πσ²`, `ℓ`, `max(1, ℓ^{±2})`); `besselPot` divides by `Γ(s) > 0` (`s > d/2 ≥ 0` in every claim
using it); `sSup (j_d '' Ici 1)` is of a nonempty set and L11 asserts `BddAbove`; `jBall` divides by `vol(B) ∈ (0,∞)`; `dilate` uses
`(w^d)⁻¹` with `w > 0`; `gaussMixDens` uses `√((2π)^d det B)⁻¹` and `B⁻¹` only under `B ≻ 0`; `gaussMix` uses `ofReal w` with `w > 0`;
`(2N − 1).doubleFactorial` at `N = 0` is `0‼ = 1 = (−1)‼` (correct); no other ℕ subtraction; Bochner integrals in `H` only of bounded
strongly measurable maps (hypotheses or proved conjuncts); `Measure.map` does not occur; `ftMeas` only of finite measures. Vacuity: every
hypothesis set has a witness (Gaussian kernel and its Fourier feature map, which L15 provides on every V; Matérn with `s = d/2 + 1`;
`f = 0`; finite mixtures with one component).

## Defects / wording in the printed text
None found in this wave (library statements; the printed sentences of L5, L16–L18, L20(b), L29, L30 were re-derived by the drafter and
the critic, constants included).

## Certified results reused (not re-proved)
`Wave31tg.matern_interpolation` (L29), `Lib/GaussianDensityD` (L27(b)); frozen definitions `Wave30tj.mmd`, `Wave8a.dTrim`,
`TrimmedMMD.Unconditional.Dpop`/`Demp`, `TrimmedMMD.Concentration.region`, `TrimmedMMD.ZeroSet.Characteristic`,
`Wave31tg.ContainsSmoothCompact`, `Wave31tg.StrictlyPDOn`, `Wave12c.witFn`.

## Not covered (declared)
* The paper's Fourier results in its angular convention (`prop:newsobolev`, `prop:newgauss`, `prop:newrates` (iii), `prop:newgammaone`,
  `lem:newsobnorm`, `thm:newsobolev`, `cor:newsobolev`, `lem:newgaussstep`, `thm:newgauss`, `prop:newupperone`, `prop:newmoments`, the last
  sentence of `prop:newslope`): Wave 31tq, composed on this library. The equations eq:newnative, eq:newbochner, eq:newbandlim,
  eq:newmomentdecay are certified here in Mathlib's convention (`ĝ(ω) = 𝓕g(ω/2π)`); their angular restatement is a change of variables
  done in Wave 31tq.
* The closed form of the Matérn kernels with the Bessel function `K_ν` (only `ν = ½` is proved; the family is defined by its spectral
  density, which is what every printed use needs).
* The non-Fourier rest of the AoS gap inventory (the paper's run, `GAPS.md` C1–C7, B2): Wave 31tr.

## Coverage note (COVERAGE.md rows)
`docs/planning/inventory/COVERAGE.md` (section trimmed-mmd-jmlr): `prose:ex-separated-matern` now "certified, no bridge (Wave31tp L29)",
the earlier bridged row kept for the JMLR v3 text; `rem:qdens` note extended by the C^∞ clause (Wave31tp L30); new rows for the AoS
equations `eq:newnative`, `eq:newbochner`, `eq:newbandlim`, `eq:newmomentdecay` ("certified in Mathlib's convention; angular form in
Wave31tq"), with extracted-inventory rows. The `lib:` targets are library results with no printed counterpart (shown on the paper face
as certified library targets). Paper face `Papers/TrimmedMMDJMLR` regenerated (414 targets, 414 aliases). The generator groups a target
under the first label token that has an inventory row, so `plancherel` (label "serves … via eq:newnative") is listed under `eq:newnative`
and `taylor_cexp` under `eq:newmomentdecay`; both are library inputs of those equations, and the alias docstrings carry the full labels.
`README.md`: the hand-added link to `docs/trimmed-mmd-aos.md` (commit `4015890`), which the generator does not emit, was restored after
regeneration (so `gen_papers_face.py --check` reports README.md, as it already did at `4015890`).

## Gate
`python3 tools/certify.py check` (2026-11-21, branch `tmmd-aos-fullstack`, run under `flock` + `systemd-run -p MemoryMax=7G`):
`CERTIFIED: 4033 targets; statements frozen; axioms within ['Classical.choice', 'Quot.sound', 'propext']`
`python3 tools/check_aliases.py`:
`ALIASES OK: 3976 aliases in 16 paper files; each is literally a certified theorem under its frozen claim; all 3965 targets of the 16 paper pages covered (68 targets have no page)`
