import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.Probability.Quantile
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# FROZEN STATEMENTS — otfd wave 8c: B `lem:naive-law`, B `lem:ext-cubic-bracket`, C `prop:cond-transfer`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-B_bands.md`, `otfd-C_conditional.md`; current text
of 2026-10-14, paths below are under `otfd/papers/`):
* B `lem:naive-law` (`B_bands/supplement.tex:364-382`, proof `:384-410`), with the naive spherical law, `M_K`, `L_K`,
  `‖·‖_{M_K}`, `B_{K,M_K}(τ)` of `subsec:geometry` (`B_bands/main.tex:406-428`) and the calibration functional of
  `def:depth-family` (`main.tex:502-517`).
* B `lem:ext-cubic-bracket` (`B_bands/supplement.tex:1576-1605`, proof `:1607-1633`), with the set-up paragraph "A verified
  bracket for the cubic calibration" (`supplement.tex:1556-1574`: `N`, `ω_k`, `T_k`, `S`, `F_k`, `c_K = F_S∘s`, `h`,
  `ν_k = ⌊T_k/h⌋`, `F_L`, `i_p`, `δ_G`), `ρ^{(K)}_box` of `prop:calibrations`(c) (`main.tex:530-537`) and
  `c_K^{-1}(p) = inf{t : c_K(t) ≥ p}` of `def:depth-family`.
* C `prop:cond-transfer` (`C_conditional/main.tex:959-984`), with `def:cond-transfer` (`main.tex:950-957`), the population
  maps of `sec:cond-ranks` (`main.tex:926-931`: `Q_{K,x}`, `F_{K,x}`, `F∘Q = Id` `μ_K`-a.e., `Q∘F = Id` `P_{K,x}`-a.e.);
  proof `C_conditional/supplement.tex:2011-2045` and the `K = 2` example after it (`:2047-2054`).
Self-contained: imports Mathlib and Tau Ceti only (`TauCeti.subdifferential`, `TauCeti.IsKantorovichOptimalTransportMap`,
`MeasureTheory.Measure.quantile`); no frozen StatFormal file is needed.

Covered:
* B `lem:naive-law`: (a) `naive_indep`; (b) `naive_norm` (`‖L_K^{-1}(rθ)‖_{M_K} = r` for `r ≥ 0`, `‖θ‖ = 1`),
  `naive_norm_law` (`‖U‖_{M_K}` has the law of `R`), `naive_calibration` (`ρ = ‖·‖_{M_K}` maps `supp μ_K` into
  `[0,1]`, `μ_K(B_{K,M_K}(τ)) = τ` on `[0,1]`, and `supp μ_K = B_{K,M_K}`; `c_K(τ) = τ` is then continuous with
  `c_K(0) = 0`, `c_K(1) = 1`); (c) `naive_invariant` (`G#μ_K = μ_K` and `ρ∘G = ρ`), `naive_orth_iff` ("exactly the
  maps `L_K^{-1}OL_K`"); (d) `naive_density` (`μ_K ≪ Leb` with the displayed density), `omega_sphere` (`ω_{K−1}` is
  the surface area of `S^{K−1}`, Mathlib's `volume.toSphere univ`), `naive_one_dim` (for `K = 1` the uniform law on
  `[−M_1^{-1/2}, M_1^{-1/2}]`).
* B `lem:ext-cubic-bracket`: set-up: `cubic_term_cdf` (`T_k ∈ [0, ω_k²]` with CDF `F_k`), `cubic_bin_law` (the law of
  `ν_k` is the bin-probability vector and the `ν_k` are independent, so the law of `ν` is their convolution),
  `cubic_ck_eq` (`c_K = F_S ∘ s` on `τ ≥ 0`); first sentence: `cubic_coupling`; (i) `cubic_bracket_cdf`; (ii)
  `cubic_bracket_threshold`; (iii) `cubic_bracket_content`; (iv) `cubic_bracket_width`, `cubic_width_density` (the
  middle inequality `≤ 2Nh·sup f_S` for any density bound `C`) and `cubic_density`.
* C `prop:cond-transfer`: (i) `transfer_push_rank` (`T#P_x = P_{x'}`, `F_{x'}∘T = F_x` a.e.), `transfer_unique`;
  (ii) `transfer_cocycle`; (iii) `affine_formula`, `affine_spectrum`, `affine_optimal_iff`, `affine_symm_iff_comm`,
  `affine_symm_posdef`; (iv) `locscale_formula`, `reference_free_1d`, `reference_dependent_2d`,
  `reference_dependent` (every `K ≥ 2`).

Not covered (declared):
* B (b): "`c_K` is continuous" etc. are immediate for `c_K(τ) = τ` and are not stated separately.
* B cubic: "`F_S` is continuous and strictly increasing on `[0,1]`, so `s(τ_{K,p}) = F_S^{-1}(p)`" (a step of the
  set-up; (ii) is stated for `τ_{K,p} = c_K^{-1}(p)` directly and does not need it); "a single convolution gives both"
  and "The bracket is informative only when `G ≫ N`" (interpretive); the multichannel remark (covered by allowing any
  number `N` of terms); the FFT/floating-point remark `rem:ext-cubic-bracket-use`.
* C: the interpretive clause of (i) "the conditional depth and sign of `T(z)` at `x'` equal those of `z` at `x`" is the
  identity `F_{x'}∘T = F_x` composed with `1 − c_K∘ρ` and `𝗌` (not restated); the citations; the existence of the
  McCann maps (McCann's theorem is not formalised: `Q_{K,x}`, `F_{K,x}` are hypotheses with their defining
  properties).

Encodings (see card):
* Naive law: `ℝ^K = EuclideanSpace ℝ (Fin K)`, matrices act by `Matrix.toEuclideanLin` (`mvec`). `M_K` is a real
  `PosDef` matrix (symmetric by definition), `L_K` any matrix with `L_Kᵀ L_K = M_K` (hence invertible; `L_K^{-1}` is
  the matrix inverse), `‖u‖_{M_K} = √(uᵀM_Ku)` (`mnorm`, radicand `≥ 0`: no junk). `θ ~ Unif(S^{K−1})` is Mathlib's
  `volume.toSphere` pushed to `ℝ^K` and normalised (`sphereUnif`), `R ~ Unif(0,1)` is `volume` on `(0,1]`
  (`unifRadius`), independence is the product measure, `μ_K = (Unif(0,1) ⊗ Unif(S^{K−1})).map((r,θ) ↦
  L_K^{-1}(rθ))` (`naiveLaw`). `supp` is Mathlib's `Measure.support`. "Orthogonal" is `Matrix.orthogonalGroup`.
  `ω_{K−1} = 2π^{K/2}/Γ(K/2)` with `Real.rpow`, `Real.Gamma` (`omega K`); the density is an `ℝ≥0∞`-valued indicator
  (`naiveDensity`; at `‖u‖_{M_K} = 0` the indicator is `0`, so the division is never evaluated there). `K ≥ 1`
  where the sphere is used (`K = 0` gives the zero measure). `K = 1`: `ℝ^1 → ℝ`, `u ↦ u 0`, and `M_1 = M 0 0`.
* Cubic law: `N ≥ 1` independent terms (`N = K`, or `N = dK` flattened: any `N`), half-widths `a_k = λ_k/2 > 0`,
  `μ_K = ⊗_k Unif[−a_k, a_k]` on `Fin N → ℝ` (`cubicLaw`), `D_K = (Σ a_k²)^{1/2}` (`dK`), `ω_k = a_k/D_K` (`om`),
  `ρ_box(u) = ‖u‖₂/D_∞` with any `D_∞ > 0` (`rhoBox`; the paper's `D_∞ ≥ D_K` is not needed: generalisation).
  `T_k(u) = (u_k/D_K)² = ω_k²W_k²` with `W_k = |u_k|/a_k` iid `Unif(0,1)` under `μ_K` (`termT`), `S = Σ_k T_k`
  (`sumS`), so `(D_∞ρ_box/D_K)² = S` identically. Bin width `h > 0` (the paper's `h = 1/G`: generalisation);
  `ν_k = ⌊T_k/h⌋ ∈ ℤ` (`nuK`), `ν = Σ ν_k` (`nuSum`), `F_L(x) = μ_K(ν ≤ ⌊x/h⌋)` (`cdfL`), `F_S(x) = μ_K(S ≤ x)`
  (`cdfS`), `i_p = min{i ∈ ℕ : μ_K(ν ≤ i) ≥ p}` (`ip`; for `0 < p ≤ 1` the set is nonempty: no junk),
  `δ_G = Σ_k min(h, ω_k²)` (`deltaG`), `c_K(τ) = μ_K(ρ_box ≤ τ)` (`cK`), `τ_{K,p} = c_K^{-1}(p) = sInf{t : c_K(t) ≥ p}`
  (`tauKp`; for `0 < p ≤ 1` nonempty and bounded below by `0`: no junk), `s(τ) = (τD_∞/D_K)²` (`sOf`). Probabilities
  are `Measure.real` (finite measure). "`f_S ≤ C`" is `μ_K.map S ≤ C • Leb` (equivalent to a density bounded by `C`);
  it is claimed for **every** pair of distinct indices `i ≠ j` (the two largest `ω_k` give the printed, best bound:
  generalisation). In (iii) the threshold `τ̂ ≥ 0` is arbitrary (any computed value); `A = {ρ_box ≤ τ̂} ∩ supp μ_K`.
* Counterfactuals: `ℝ^K = EuclideanSpace ℝ (Fin K)` (and `ℝ` itself for `K = 1`). `Q_{K,x}`, `F_{K,x}`: for (i)–(ii)
  any measurable pair with the four defining properties of `sec:cond-ranks` (`IsRankPair`: `Q#μ = P`, `F#P = μ`,
  `F∘Q = id` `μ`-a.e., `Q∘F = id` `P`-a.e.; generalisation: McCann is not used there, nor absolute continuity). For
  (iii)–(iv), where the maps are identified, "the McCann map from `α` to `β`" is `IsGradMap α β T`: `T` measurable,
  `T#α = β`, and `T(x) ∈ ∂φ(x)` for `α`-a.e. `x` for some `φ : E → EReal` (Tau Ceti's `subdifferential (innerₗ E)`);
  by Rockafellar's theorem this is the same as being `α`-a.e. the gradient of a convex function. The reference `μ` is
  a probability measure, `μ ≪ Leb`; **finite second moments** of `μ` and of the conditional laws are assumed where the
  maps are identified (Tau Ceti's Brenier uniqueness needs finite cost; in the paper's standing setting `μ_K` has
  compact support and the responses are bounded — a declared conditionalisation for (iv)). "Optimal transport map"
  is `IsKantorovichOptimalTransportMap` for the cost `‖x − y‖²/2` (Tau Ceti's normalisation; the same maps as for
  `‖x − y‖²`). In `affine_optimal_iff` the standing assumption that `supp μ_K` is convex is a hypothesis (used for
  an open set inside `supp P_{K,x}`). Eigenvalues of `A'A⁻¹` are its complex spectrum (`spectrum ℂ` of the
  complexified matrix). `G_x = cdf P_x`, `G^{-1} = quantile` (Tau Ceti; `sInf{z : t ≤ G(z)}`, evaluated only at
  `G_x(z) ∈ (0,1)` for `P_x`-a.e. `z`). "For `K ≥ 2` it does in general" is an explicit `K = 2` witness: references
  `μ`, `ν` with compact convex support, all four laws absolutely continuous with finite second moments, McCann maps
  that exist, and for **every** choice of McCann maps the two counterfactuals differ on a set of positive
  `P_x`-mass.

Critic notes:
* All 31 claims are proved in `Wave8c/Route{Naive,Cubic,Transfer,Refs}.lean` (only propext, choice, Quot.sound). No statement of
  the three results was found false.
* B naive law: (a) and (c) are derived from (d) — the density depends on `M_K` only and is `G`-invariant
  (`|det G| = 1`); `naive_indep`, `naive_invariant`, `naive_norm`, `naive_orth_iff` also hold for `K = 0` (the law is
  the zero measure there). (b)'s `supp μ_K = B_{K,M_K}` uses the density lower bound `√det M_K/ω_{K−1}` on
  `{0 < ‖u‖_{M_K} < 1}`.
* B cubic: (ii) holds for every `D_∞ > 0`; with `τ_{K,p}` the generalised inverse it needs only right-continuity of
  `c_K` (no continuity or strict monotonicity of `F_S`); (iv)'s density bound holds for any two distinct terms, by
  `law(T_i + T_j) = law(T_i) ∗ law(T_j)`, the arcsine integral `∫_0^x dy/√(y(x−y)) = π`, and convolution with the
  law of the remaining terms (a probability law) not increasing the bound.
* C (i)–(ii) are pure measure theory and hold for any pairs with the stated a.e. inverse properties; uniqueness in
  (i) is among **measurable** maps `S` (the paper says "map"). (iii)–(iv) use Tau Ceti's Brenier uniqueness
  (subgradient selections are optimal; the optimal plan from an absolutely continuous source is unique), which needs
  finite second moments: a declared conditionalisation (automatic in (iii), where `μ_K` has finite second moment and
  `P_{K,x}` is its affine image). `affine_optimal_iff`'s "only if" follows the paper: the support of the optimal
  graph plan lies in `∂u` for a convex `u`, an open set inside `supp P_{K,x}` comes from convexity of `supp μ_K`, `u`
  is differentiable there with gradient `T`, and Schwarz gives symmetry.
* C `reference_dependent_2d`: the paper's `K = 2` example made concrete. `μ = Unif(closed unit disk)`, `P_x = μ`,
  `P_{x'} = A#μ`, second reference `ν = B#μ`, `A = [[1,−2],[−2,9]]`, `B = [[7,4],[4,3]]`, `M = [[1,−2],[−2,5]]`,
  `R` the rotation with `cos = 3/5`, `sin = 4/5`, and `MB = AR` (`M = B^{-1}(BA²B)^{1/2}B^{-1}` of the paper). With
  reference `μ` the counterfactual is `A`; with `ν` it is `MB = AR`; they differ off `{0}`. Both references satisfy
  the standing setting (absolutely continuous, compact convex support, finite second moments); `AB ≠ BA`.
* Non-vacuity and conventions: `IsGradMap` is not vacuous, since Tau Ceti's `subdifferential` requires `φ x` finite
  (`≠ ⊥`, `≠ ⊤`), so `φ ≡ ⊤` gives no subgradients; the convexity of `supp μ_K` assumed in `affine_optimal_iff` is the
  standing assumption of C `main.tex:630` (compact convex topological support `𝒰_K`); `μ.map S ≤ C • Leb` is
  equivalent to `S` having a Lebesgue density `≤ C` a.e. (Radon–Nikodym), so it encodes `sup f_S ≤ C`; the
  thresholds `τ̂ ≥ 0` in (iii)–(iv) match the domain `[0,1] ⊆ [0,∞)` of `c_K` (for `τ < 0`, `c_K(τ) = 0` while
  `F_S(s(τ)) > 0`, so `c_K = F_S∘s` holds only for `τ ≥ 0`).
* `reference_dependent` (every `K = 2 + n`): reference `Unif(unit ball of ℝ^K)`, block-diagonal `diag(A, I)`,
  `diag(B, I)`, `diag(M, I)`, `diag(R, I)` of the `K = 2` witness; the two counterfactuals differ off the
  hyperplane `{z_0 = 0}`, which is Lebesgue-null.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped InnerProductSpace ENNReal RealInnerProductSpace

namespace StatFormal.OTFD.Wave8c

/-! ### B `lem:naive-law` -/

section Naive
variable {K : ℕ}

/-- A `K × K` matrix acting on `ℝ^K`. -/
abbrev mvec (A : Matrix (Fin K) (Fin K) ℝ) : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) :=
  Matrix.toEuclideanLin A

/-- `‖u‖_{M} = √(uᵀ M u)`. -/
def mnorm (M : Matrix (Fin K) (Fin K) ℝ) (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  Real.sqrt ((WithLp.ofLp u) ⬝ᵥ (M *ᵥ WithLp.ofLp u))

/-- `Unif(S^{K−1})`: Mathlib's sphere measure `volume.toSphere`, pushed to `ℝ^K` and normalised. -/
def sphereUnif (K : ℕ) : Measure (EuclideanSpace ℝ (Fin K)) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere univ)⁻¹ •
    ((volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere.map Subtype.val)

/-- `Unif(0,1)` for the radius. -/
def unifRadius : Measure ℝ := volume.restrict (Ioc 0 1)

/-- The naive spherical law `μ_K = L(L_K^{-1}(Rθ))`, `R ~ Unif(0,1)` independent of `θ ~ Unif(S^{K−1})`. -/
def naiveLaw (L : Matrix (Fin K) (Fin K) ℝ) : Measure (EuclideanSpace ℝ (Fin K)) :=
  (unifRadius.prod (sphereUnif K)).map fun p => mvec L⁻¹ (p.1 • p.2)

/-- `ω_{K−1} = 2π^{K/2}/Γ(K/2)`. -/
def omega (K : ℕ) : ℝ := 2 * Real.pi ^ ((K : ℝ) / 2) / Real.Gamma ((K : ℝ) / 2)

/-- The density `u ↦ √det M / (ω_{K−1} ‖u‖_M^{K−1}) · 1{0 < ‖u‖_M ≤ 1}`. -/
def naiveDensity (M : Matrix (Fin K) (Fin K) ℝ) (u : EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  Set.indicator {v | 0 < mnorm M v ∧ mnorm M v ≤ 1}
    (fun v => ENNReal.ofReal (Real.sqrt M.det / (omega K * mnorm M v ^ (K - 1)))) u

end Naive

/-! ### B `lem:ext-cubic-bracket` -/

section Cubic
variable {N : ℕ}

/-- `Unif[−a, a]`. -/
def unifSym (a : ℝ) : Measure ℝ := ENNReal.ofReal (1 / (2 * a)) • volume.restrict (Icc (-a) a)

/-- The cubic law `⊗_k Unif[−a_k, a_k]` on `ℝ^N`. -/
def cubicLaw (a : Fin N → ℝ) : Measure (Fin N → ℝ) := Measure.pi fun k => unifSym (a k)

/-- `D_K = (Σ_k a_k²)^{1/2}`. -/
def dK (a : Fin N → ℝ) : ℝ := Real.sqrt (∑ k, a k ^ 2)

/-- `ω_k = a_k / D_K`. -/
def om (a : Fin N → ℝ) (k : Fin N) : ℝ := a k / dK a

/-- `ρ_box(u) = ‖u‖₂ / D_∞`. -/
def rhoBox (Dinf : ℝ) (u : Fin N → ℝ) : ℝ := Real.sqrt (∑ k, u k ^ 2) / Dinf

/-- `T_k(u) = (u_k/D_K)² = ω_k² W_k²`. -/
def termT (a : Fin N → ℝ) (k : Fin N) (u : Fin N → ℝ) : ℝ := (u k / dK a) ^ 2

/-- `S = Σ_k T_k`. -/
def sumS (a : Fin N → ℝ) (u : Fin N → ℝ) : ℝ := ∑ k, termT a k u

/-- `F_k(y) = min(√y/ω_k, 1)`. -/
def cdfK (a : Fin N → ℝ) (k : Fin N) (y : ℝ) : ℝ := min (Real.sqrt y / om a k) 1

/-- `ν_k = ⌊T_k/h⌋`. -/
def nuK (a : Fin N → ℝ) (h : ℝ) (k : Fin N) (u : Fin N → ℝ) : ℤ := ⌊termT a k u / h⌋

/-- `ν = Σ_k ν_k`. -/
def nuSum (a : Fin N → ℝ) (h : ℝ) (u : Fin N → ℝ) : ℤ := ∑ k, nuK a h k u

/-- `F_L(x) = P(ν ≤ ⌊x/h⌋)`. -/
def cdfL (a : Fin N → ℝ) (h x : ℝ) : ℝ := (cubicLaw a).real {u | nuSum a h u ≤ ⌊x / h⌋}

/-- `F_S(x) = P(S ≤ x)`. -/
def cdfS (a : Fin N → ℝ) (x : ℝ) : ℝ := (cubicLaw a).real {u | sumS a u ≤ x}

/-- `i_p = min{i : P(ν ≤ i) ≥ p}`. -/
def ip (a : Fin N → ℝ) (h p : ℝ) : ℕ := sInf {i : ℕ | p ≤ (cubicLaw a).real {u | nuSum a h u ≤ i}}

/-- `δ_G = Σ_k min(h, ω_k²)`. -/
def deltaG (a : Fin N → ℝ) (h : ℝ) : ℝ := ∑ k, min h (om a k ^ 2)

/-- `c_K(τ) = μ_K(ρ_box ≤ τ)`. -/
def cK (a : Fin N → ℝ) (Dinf τ : ℝ) : ℝ := (cubicLaw a).real {u | rhoBox Dinf u ≤ τ}

/-- `τ_{K,p} = c_K^{-1}(p) = inf{t : c_K(t) ≥ p}`. -/
def tauKp (a : Fin N → ℝ) (Dinf p : ℝ) : ℝ := sInf {t : ℝ | p ≤ cK a Dinf t}

/-- `s(τ) = (τ D_∞ / D_K)²`. -/
def sOf (a : Fin N → ℝ) (Dinf τ : ℝ) : ℝ := (τ * Dinf / dK a) ^ 2

/-- The standing parameters: `N ≥ 1` terms with positive half-widths, `h > 0`, `D_∞ > 0`. -/
def CubicSetting (a : Fin N → ℝ) (h Dinf : ℝ) : Prop :=
  0 < N ∧ (∀ k, 0 < a k) ∧ 0 < h ∧ 0 < Dinf

end Cubic

/-! ### C `prop:cond-transfer` -/

section Transfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- `(F, Q)` are the population rank and quantile maps between the reference `μ` and the law `P`: `Q#μ = P`,
`F#P = μ`, `F∘Q = Id` `μ`-a.e. and `Q∘F = Id` `P`-a.e. -/
def IsRankPair (μ P : Measure E) (F Q : E → E) : Prop :=
  Measurable F ∧ Measurable Q ∧ μ.map Q = P ∧ P.map F = μ ∧ (∀ᵐ u ∂μ, F (Q u) = u) ∧ ∀ᵐ z ∂P, Q (F z) = z

/-- `T` is the McCann map from `α` to `β`: measurable, `T#α = β`, and `α`-a.e. a subgradient of one function. -/
def IsGradMap (α β : Measure E) (T : E → E) : Prop :=
  Measurable T ∧ α.map T = β ∧
    ∃ φ : E → EReal, ∀ᵐ x ∂α, T x ∈ TauCeti.subdifferential (innerₗ E) φ x

end Transfer

/-- The affine map `u ↦ b + A u` on `ℝ^K`. -/
def affineMap {K : ℕ} (b : EuclideanSpace ℝ (Fin K)) (A : Matrix (Fin K) (Fin K) ℝ)
    (u : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K) :=
  b + mvec A u

/-- The quadratic cost `‖x − y‖²/2`. -/
def quadCost {E : Type*} [NormedAddCommGroup E] (z : E × E) : ℝ≥0∞ := ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)

namespace Claims

/-! ### B `lem:naive-law` -/

/-- (a) `μ_K` does not depend on the choice of `L_K`. -/
def naive_indep : Prop :=
  ∀ (K : ℕ) (M L L' : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M → L'ᵀ * L' = M →
    naiveLaw L = naiveLaw L'

/-- (b) `‖U‖_{M_K} = R`: `‖L_K^{-1}(rθ)‖_{M_K} = r` for every `r ≥ 0` and unit `θ`. -/
def naive_norm : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (r : ℝ) (θ : EuclideanSpace ℝ (Fin K)), 0 ≤ r → ‖θ‖ = 1 → mnorm M (mvec L⁻¹ (r • θ)) = r

/-- (b) `‖U‖_{M_K}` has the law of `R`. -/
def naive_norm_law : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), 1 ≤ K → M.PosDef → Lᵀ * L = M →
    (naiveLaw L).map (mnorm M) = unifRadius

/-- (b) `ρ = ‖·‖_{M_K}` is a calibration functional with `c_K(τ) = τ`: it maps `supp μ_K` into `[0,1]`,
`μ_K(B_{K,M_K}(τ)) = τ` for `τ ∈ [0,1]`, and `supp μ_K = B_{K,M_K}`. -/
def naive_calibration : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), 1 ≤ K → M.PosDef → Lᵀ * L = M →
    (∀ u ∈ (naiveLaw L).support, mnorm M u ∈ Icc (0 : ℝ) 1) ∧
      (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → naiveLaw L {u | mnorm M u ≤ τ} = ENNReal.ofReal τ) ∧
      (naiveLaw L).support = {u | mnorm M u ≤ 1}

/-- (c) Every `G` with `GᵀM_KG = M_K` satisfies `G#μ_K = μ_K` and `ρ∘G = ρ` on `ℝ^K`. -/
def naive_invariant : Prop :=
  ∀ (K : ℕ) (M L G : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M → Gᵀ * M * G = M →
    (naiveLaw L).map (mvec G) = naiveLaw L ∧ ∀ u, mnorm M (mvec G u) = mnorm M u

/-- (c) The `G` with `GᵀM_KG = M_K` are exactly the `L_K^{-1}OL_K` with `O` orthogonal. -/
def naive_orth_iff : Prop :=
  ∀ (K : ℕ) (M L G : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    (Gᵀ * M * G = M ↔ ∃ O ∈ Matrix.orthogonalGroup (Fin K) ℝ, G = L⁻¹ * O * L)

/-- (d) `μ_K ≪ Leb`, with density `√det M_K / (ω_{K−1}‖u‖_{M_K}^{K−1}) · 1{0 < ‖u‖_{M_K} ≤ 1}`. -/
def naive_density : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), 1 ≤ K → M.PosDef → Lᵀ * L = M →
    naiveLaw L ≪ volume ∧ naiveLaw L = volume.withDensity (naiveDensity M)

/-- (d) `ω_{K−1} = 2π^{K/2}/Γ(K/2)` is the surface area of `S^{K−1}`. -/
def omega_sphere : Prop :=
  ∀ K : ℕ, 1 ≤ K →
    (volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere univ = ENNReal.ofReal (omega K)

/-- (d) For `K = 1`: `μ_1` is the uniform law on `[−M_1^{-1/2}, M_1^{-1/2}]`. -/
def naive_one_dim : Prop :=
  ∀ M L : Matrix (Fin 1) (Fin 1) ℝ, M.PosDef → Lᵀ * L = M →
    (naiveLaw L).map (fun u => u 0) =
      ENNReal.ofReal (Real.sqrt (M 0 0) / 2) •
        volume.restrict (Icc (-(1 / Real.sqrt (M 0 0))) (1 / Real.sqrt (M 0 0)))

/-! ### B `lem:ext-cubic-bracket` -/

/-- Set-up: `T_k ∈ [0, ω_k²]` almost surely, with the CDF `F_k(y) = min(√y/ω_k, 1)` on `y ≥ 0`. -/
def cubic_term_cdf : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf → ∀ k,
    (∀ᵐ u ∂cubicLaw a, termT a k u ∈ Icc 0 (om a k ^ 2)) ∧
      ∀ y : ℝ, 0 ≤ y → (cubicLaw a).real {u | termT a k u ≤ y} = cdfK a k y

/-- Set-up: the law of `ν_k` is the vector of bin probabilities `F_k((i+1)h) − F_k(ih)`, and the `ν_k` are
independent, so the law of `ν` is their convolution. -/
def cubic_bin_law : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf →
    (∀ k (i : ℕ), (cubicLaw a).real {u | nuK a h k u = i} = cdfK a k ((i + 1) * h) - cdfK a k (i * h)) ∧
      iIndepFun (fun k u => nuK a h k u) (cubicLaw a)

/-- Set-up: `c_K(τ) = F_S(s(τ))` for `τ ≥ 0`. -/
def cubic_ck_eq : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf →
    ∀ τ : ℝ, 0 ≤ τ → cK a Dinf τ = cdfS a (sOf a Dinf τ)

/-- Almost surely `hν ≤ S ≤ hν + δ_G ≤ h(ν + N)`, and the right-edge rounded sum `Σ_k h⌈T_k/h⌉` is `h(ν + N)`. -/
def cubic_coupling : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf →
    ∀ᵐ u ∂cubicLaw a,
      h * nuSum a h u ≤ sumS a u ∧ sumS a u ≤ h * nuSum a h u + deltaG a h ∧
        h * nuSum a h u + deltaG a h ≤ h * (nuSum a h u + N) ∧
        ∑ k, h * ⌈termT a k u / h⌉ = h * (nuSum a h u + N)

/-- (i) `F_L(x − Nh) ≤ F_L(x − δ_G) ≤ F_S(x) ≤ F_L(x)` for every `x`. -/
def cubic_bracket_cdf : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf → ∀ x : ℝ,
    cdfL a h (x - N * h) ≤ cdfL a h (x - deltaG a h) ∧ cdfL a h (x - deltaG a h) ≤ cdfS a x ∧
      cdfS a x ≤ cdfL a h x

/-- (ii) `h i_p ≤ s(τ_{K,p}) ≤ h i_p + δ_G ≤ h(i_p + N)`, i.e. `τ_lo ≤ τ_{K,p} ≤ τ_hi`, for `0 < p ≤ 1`. -/
def cubic_bracket_threshold : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf → ∀ p : ℝ, 0 < p → p ≤ 1 →
    h * ip a h p ≤ sOf a Dinf (tauKp a Dinf p) ∧
      sOf a Dinf (tauKp a Dinf p) ≤ h * ip a h p + deltaG a h ∧
      h * ip a h p + deltaG a h ≤ h * (ip a h p + N) ∧
      dK a / Dinf * Real.sqrt (h * ip a h p) ≤ tauKp a Dinf p ∧
      tauKp a Dinf p ≤ dK a / Dinf * Real.sqrt (h * ip a h p + deltaG a h)

/-- (iii) For every threshold `τ̂ ≥ 0`, the region `A = {ρ_box ≤ τ̂} ∩ supp μ_K` has content
`c_K(τ̂) ∈ [F_L(s(τ̂) − δ_G), F_L(s(τ̂))]`, `F_L(s(τ̂) − δ_G) ≥ F_L(s(τ̂) − Nh)`; and `τ̂ = τ_hi` has content `≥ p`. -/
def cubic_bracket_content : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf →
    (∀ τh : ℝ, 0 ≤ τh →
      (cubicLaw a).real ({u | rhoBox Dinf u ≤ τh} ∩ (cubicLaw a).support) = cK a Dinf τh ∧
        cdfL a h (sOf a Dinf τh - deltaG a h) ≤ cK a Dinf τh ∧ cK a Dinf τh ≤ cdfL a h (sOf a Dinf τh) ∧
        cdfL a h (sOf a Dinf τh - N * h) ≤ cdfL a h (sOf a Dinf τh - deltaG a h)) ∧
      ∀ p : ℝ, 0 < p → p ≤ 1 →
        p ≤ cK a Dinf (dK a / Dinf * Real.sqrt (h * ip a h p + deltaG a h))

/-- (iv) `p_hi − p_lo ≤ P(s − δ_G < S ≤ s + δ_G) ≤ 2Nh sup f_S`, with `sup f_S ≤ π/(4ω_iω_j)` for any two distinct
terms (`N ≥ 2`). -/
def cubic_bracket_width : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf → ∀ τh : ℝ, 0 ≤ τh →
    cdfL a h (sOf a Dinf τh) - cdfL a h (sOf a Dinf τh - deltaG a h) ≤
        (cubicLaw a).real {u | sOf a Dinf τh - deltaG a h < sumS a u ∧
          sumS a u ≤ sOf a Dinf τh + deltaG a h} ∧
      ∀ i j : Fin N, i ≠ j →
        (cubicLaw a).real {u | sOf a Dinf τh - deltaG a h < sumS a u ∧
          sumS a u ≤ sOf a Dinf τh + deltaG a h} ≤ 2 * N * h * (Real.pi / (4 * om a i * om a j))

/-- (iv), general form: `P(s − δ_G < S ≤ s + δ_G) ≤ 2Nh · sup f_S` for every bound `C` on the density of `S`
(`law(S) ≤ C • Leb`). -/
def cubic_width_density : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf → ∀ τh : ℝ, 0 ≤ τh →
    ∀ C : ℝ≥0∞, (cubicLaw a).map (sumS a) ≤ C • volume →
      ENNReal.ofReal ((cubicLaw a).real {u | sOf a Dinf τh - deltaG a h < sumS a u ∧
          sumS a u ≤ sOf a Dinf τh + deltaG a h}) ≤ ENNReal.ofReal (2 * N * h) * C

/-- (iv) For `N ≥ 2`, `S` has a density bounded by `π/(4ω_iω_j)` for any two distinct terms `i ≠ j`. -/
def cubic_density : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (h Dinf : ℝ), CubicSetting a h Dinf → ∀ i j : Fin N, i ≠ j →
    (cubicLaw a).map (sumS a) ≤ ENNReal.ofReal (Real.pi / (4 * om a i * om a j)) • volume

/-! ### C `prop:cond-transfer` -/

/-- (i) `T_{x→x'}#P_x = P_{x'}` and `F_{x'}∘T_{x→x'} = F_x` `P_x`-a.e. -/
def transfer_push_rank : Prop :=
  ∀ (K : ℕ) (μ Px Px' : Measure (EuclideanSpace ℝ (Fin K))) (Fx Qx Fx' Qx' : EuclideanSpace ℝ (Fin K) →
      EuclideanSpace ℝ (Fin K)),
    IsRankPair μ Px Fx Qx → IsRankPair μ Px' Fx' Qx' →
      Px.map (fun z => Qx' (Fx z)) = Px' ∧ ∀ᵐ z ∂Px, Fx' (Qx' (Fx z)) = Fx z

/-- (i) `T_{x→x'}` is the `P_x`-a.e. unique (measurable) map with both properties. -/
def transfer_unique : Prop :=
  ∀ (K : ℕ) (μ Px Px' : Measure (EuclideanSpace ℝ (Fin K))) (Fx Qx Fx' Qx' S : EuclideanSpace ℝ (Fin K) →
      EuclideanSpace ℝ (Fin K)),
    IsRankPair μ Px Fx Qx → IsRankPair μ Px' Fx' Qx' → Measurable S →
      Px.map S = Px' → (∀ᵐ z ∂Px, Fx' (S z) = Fx z) → S =ᵐ[Px] fun z => Qx' (Fx z)

/-- (ii) Cocycle: `T_{x→x} = Id` and `T_{x'→x''}∘T_{x→x'} = T_{x→x''}`, `P_x`-a.e. -/
def transfer_cocycle : Prop :=
  ∀ (K : ℕ) (μ Px Px' Px'' : Measure (EuclideanSpace ℝ (Fin K)))
    (Fx Qx Fx' Qx' Fx'' Qx'' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsRankPair μ Px Fx Qx → IsRankPair μ Px' Fx' Qx' → IsRankPair μ Px'' Fx'' Qx'' →
      (∀ᵐ z ∂Px, Qx (Fx z) = z) ∧ ∀ᵐ z ∂Px, Qx'' (Fx' (Qx' (Fx z))) = Qx'' (Fx z)

/-- (iii) Affine models: `T_{x→x'}(z) = b' + A'A⁻¹(z − b)`, `P_x`-a.e. -/
def affine_formula : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ] (b b' : EuclideanSpace ℝ (Fin K))
    (A A' : Matrix (Fin K) (Fin K) ℝ) (Fx Qx' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    μ ≪ volume → MemLp id 2 μ → A.PosDef → A'.PosDef →
      IsGradMap (μ.map (affineMap b A)) μ Fx → IsGradMap μ (μ.map (affineMap b' A')) Qx' →
        (fun z => Qx' (Fx z)) =ᵐ[μ.map (affineMap b A)] fun z => b' + mvec (A' * A⁻¹) (z - b)

/-- (iii) `A'A⁻¹` has positive real eigenvalues. -/
def affine_spectrum : Prop :=
  ∀ (K : ℕ) (A A' : Matrix (Fin K) (Fin K) ℝ), A.PosDef → A'.PosDef →
    ∀ c ∈ spectrum ℂ ((A' * A⁻¹).map (algebraMap ℝ ℂ)), c.im = 0 ∧ 0 < c.re

/-- (iii) `T_{x→x'}` is the optimal transport map from `P_x` to `P_{x'}` iff `A'A⁻¹` is symmetric. -/
def affine_optimal_iff : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ] (b b' : EuclideanSpace ℝ (Fin K))
    (A A' : Matrix (Fin K) (Fin K) ℝ) (Fx Qx' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    μ ≪ volume → MemLp id 2 μ → Convex ℝ μ.support → A.PosDef → A'.PosDef →
      IsGradMap (μ.map (affineMap b A)) μ Fx → IsGradMap μ (μ.map (affineMap b' A')) Qx' →
        (TauCeti.IsKantorovichOptimalTransportMap quadCost (μ.map (affineMap b A))
            (μ.map (affineMap b' A')) (fun z => Qx' (Fx z)) ↔ (A' * A⁻¹)ᵀ = A' * A⁻¹)

/-- (iii) `A'A⁻¹` is symmetric iff `A` and `A'` commute. -/
def affine_symm_iff_comm : Prop :=
  ∀ (K : ℕ) (A A' : Matrix (Fin K) (Fin K) ℝ), A.PosDef → A'.PosDef →
    ((A' * A⁻¹)ᵀ = A' * A⁻¹ ↔ A * A' = A' * A)

/-- (iii) A symmetric `A'A⁻¹` is positive definite. -/
def affine_symm_posdef : Prop :=
  ∀ (K : ℕ) (A A' : Matrix (Fin K) (Fin K) ℝ), A.PosDef → A'.PosDef → (A' * A⁻¹)ᵀ = A' * A⁻¹ →
    (A' * A⁻¹).PosDef

/-- (iv) If `P_{x'} = L(b + cZ)`, `c > 0`, `Z ~ P_x`, then `T_{x→x'}(z) = b + cz` (`P_x`-a.e.) for every reference. -/
def locscale_formula : Prop :=
  ∀ (K : ℕ) (μ Px : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ] [IsProbabilityMeasure Px]
    (b : EuclideanSpace ℝ (Fin K)) (c : ℝ) (Fx Qx Qx' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    μ ≪ volume → Px ≪ volume → MemLp id 2 μ → MemLp id 2 Px → 0 < c →
      IsGradMap Px μ Fx → IsGradMap μ Px Qx → IsRankPair μ Px Fx Qx →
        IsGradMap μ (Px.map fun z => b + c • z) Qx' →
          (fun z => Qx' (Fx z)) =ᵐ[Px] fun z => b + c • z

/-- (iv) `K = 1`: for every absolutely continuous reference, `T_{x→x'} = G_{x'}^{-1}∘G_x`, `P_x`-a.e. -/
def reference_free_1d : Prop :=
  ∀ (μ Px Px' : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure Px] [IsProbabilityMeasure Px']
    (Fx Qx' : ℝ → ℝ),
    μ ≪ volume → Px ≪ volume → Px' ≪ volume → MemLp id 2 μ → MemLp id 2 Px → MemLp id 2 Px' →
      IsGradMap Px μ Fx → IsGradMap μ Px' Qx' →
        (fun z => Qx' (Fx z)) =ᵐ[Px] fun z => Px'.quantile (cdf Px z)

/-- (iv) For `K ≥ 2` the counterfactual depends on the reference in general: a `K = 2` witness. -/
def reference_dependent_2d : Prop :=
  ∃ μ ν Px Px' : Measure (EuclideanSpace ℝ (Fin 2)),
    IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ IsProbabilityMeasure Px ∧ IsProbabilityMeasure Px' ∧
    μ ≪ volume ∧ ν ≪ volume ∧ Px ≪ volume ∧ Px' ≪ volume ∧
    MemLp id 2 μ ∧ MemLp id 2 ν ∧ MemLp id 2 Px ∧ MemLp id 2 Px' ∧
    IsCompact μ.support ∧ Convex ℝ μ.support ∧ IsCompact ν.support ∧ Convex ℝ ν.support ∧
    (∃ Fx Qx' Gx Rx' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsGradMap Px μ Fx ∧ IsGradMap μ Px' Qx' ∧ IsGradMap Px ν Gx ∧ IsGradMap ν Px' Rx') ∧
    ∀ Fx Qx' Gx Rx' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsGradMap Px μ Fx → IsGradMap μ Px' Qx' → IsGradMap Px ν Gx → IsGradMap ν Px' Rx' →
        ¬ ((fun z => Qx' (Fx z)) =ᵐ[Px] fun z => Rx' (Gx z))

/-- (iv) For every `K ≥ 2` the counterfactual depends on the reference in general: a witness in each dimension. -/
def reference_dependent : Prop :=
  ∀ K : ℕ, 2 ≤ K → ∃ μ ν Px Px' : Measure (EuclideanSpace ℝ (Fin K)),
    IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ IsProbabilityMeasure Px ∧ IsProbabilityMeasure Px' ∧
    μ ≪ volume ∧ ν ≪ volume ∧ Px ≪ volume ∧ Px' ≪ volume ∧
    MemLp id 2 μ ∧ MemLp id 2 ν ∧ MemLp id 2 Px ∧ MemLp id 2 Px' ∧
    IsCompact μ.support ∧ Convex ℝ μ.support ∧ IsCompact ν.support ∧ Convex ℝ ν.support ∧
    (∃ Fx Qx' Gx Rx' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
      IsGradMap Px μ Fx ∧ IsGradMap μ Px' Qx' ∧ IsGradMap Px ν Gx ∧ IsGradMap ν Px' Rx') ∧
    ∀ Fx Qx' Gx Rx' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
      IsGradMap Px μ Fx → IsGradMap μ Px' Qx' → IsGradMap Px ν Gx → IsGradMap ν Px' Rx' →
        ¬ ((fun z => Qx' (Fx z)) =ᵐ[Px] fun z => Rx' (Gx z))

end Claims

end StatFormal.OTFD.Wave8c
