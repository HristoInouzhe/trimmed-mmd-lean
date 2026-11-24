import StatFormal.Archive.OTFD.Wave10a.Statements
import StatFormal.Archive.OTFD.Wave2.Statements
import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.Defects2.Statements
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# FROZEN STATEMENTS — wave 18a (QUEUE rows 181–188): otfd B `prop:rk-band-overstates`, `prop:entropy-zero`;
# C `lem:convex-continuous-gradient`, `prop:neural-potential-approximation`; robust equality JASA `lem:fl-price`,
# `thm:cs-certificate` (extension), `cor:cs-translation`, `prop:cs-monotone` (extension)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-B_bands.md`, `otfd-C_conditional.md`,
`robust-equality-jasa.md`; current text after the 2026-10-13/14/15 corrections; otfd paths under `otfd/papers/`):
* B `prop:rk-band-overstates` (`B_bands/supplement.tex:5684-5703`, proof `:5705-5714`), with the reconstruction
  `x_u = 𝔪 + ⟨𝐞(·), Q̂(u)⟩` and `‖·‖_{M_K}`, `‖·‖_{M_K⁻¹}` of `prop:rk-linear-certificate` (`:5664-5682`).
* B `prop:entropy-zero` (`B_bands/supplement.tex:6228-6245`, proof `:1733-1749`), with `π_θ`, `Ω_ε`, `Ω_γ`,
  `R^bar_{i,K,θ}`, `D^{soft,geom}_{i,K,θ}` of `subsec:soft-coupling` (`:6394-6425`).
* C `lem:convex-continuous-gradient` (`C_conditional/supplement.tex:1562-1568`, proof `:1570-1580`).
* C `prop:neural-potential-approximation` (`C_conditional/supplement.tex:1386-1400`, proof `:1401-1409`), with the
  conditional potential limit (`main.tex:667-671`, `thm:conditional-band-limits`: normalized potentials converge to
  `χ_{K,x}` uniformly on compact subsets of `int 𝒰_K`).
* JASA `lem:fl-price` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_calibration.tex:84-91`, proof
  `:93-96`).
* JASA `thm:cs-certificate` (`jasa/supp_common_shift.tex:141-151`, proof `:153-165`), `def:cs-set` (`:95-112`), the
  transported floor (`:131-134`); `cor:cs-translation` (`:169-178`, proof `:180-187`); `prop:cs-monotone`
  (`:284-290`, proof `:292-296`) with the corrected prediction-line pairs (`:276-281`).
Imports the frozen `OTFD/Wave10a` (`mInvNorm`, `ballM`), `OTFD/Wave2` (`mnorm`), `Wave4b` (`InBall`, `Findep`,
`Fstruct`, `nominal`, `sqrtT`, `TrefPull`, `sqrtTPull`, `RefClass`; through it `RobustEquality.Certificate`:
`centre`, `KernelWitness`, `Tref1`) and `Defects2` (`lineMonoSup`, `ThetaL`, `ThetaMono`) statements, not copied;
Mathlib and Tau Ceti (`TauCeti.wassersteinEDist`) otherwise. No `Foundations` file.

Covered:
* B `prop:rk-band-overstates`: (i) `rk_band_overstates_i` (the band maximum is `∫(a⁺x↑ − a⁻x↓)`, attained, and it
  dominates `L` on the region); (ii) `rk_band_overstates_ii` (affine-reference laws: the band edges, both maxima,
  the ratio formula and `ratio ≥ 1`); (iii) `rk_band_overstates_iii` (trigonometric basis, `S = σI`, `M_K = I`,
  `L` the mean on `[0,1]`: the ratio is `√(2J+1) = √K`).
* B `prop:entropy-zero`: `entropy_zero` (any regularizer vanishing uniformly on the polytope: `π_θ → π_0`, the
  barycentric ranks and mean-radius soft depths converge to those of `π_0`); `entropy_zero_entropic`,
  `entropy_zero_quadratic` (the two instances satisfy the hypothesis, so their minimizers converge);
  `entropy_zero_permutation` (`m = n`, uniform marginals, `π_0 = P_σ/n`: the limits are `u_{σ(i)}` and
  `1 − g_K(u_{σ(i)})`).
* C `lem:convex-continuous-gradient`: `convex_continuous_gradient` (first sentence);
  `convex_continuous_gradient_density` ("in particular", positive density, continuous version of `Q_{K,x}`).
* C `prop:neural-potential-approximation`: `neural_potential_rate` (`sup_S ‖∇φ_n − Q_{K,x}‖ ≤ 2d_n/r + Lr/2` for
  every permissible `r`), `neural_potential_rate_opt` (at `r = 2√(d_n/L)` the bound is `2√(Ld_n)`);
  `neural_potential_consistency` (uniform convergence of the maps on `S` from the teacher limit plus
  `sup_{S'} |φ_n − g^OT_n| → 0`), `neural_potential_edges` (exact band edges over levels `A ⊆ S`, uniformly in
  `‖v‖ ≤ E`).
* JASA `lem:fl-price`: `fl_price_bound` (`W₂(h#P, h#(P∗U)) ≤ π_h(U)`); `fl_price_linear` (`π_h(U) =
  (wᵀ E[UUᵀ] w)^{1/2}` for `h = ⟨w,·⟩`); `fl_price_ellipsoid` (`= |w| s_w/√(d+2)` for `U` uniform on the ellipsoid).
* JASA `thm:cs-certificate` (extends the certified `Wave4b` `cs_slice_T`, `cs_certificate`): `cs_certificate_pair`
  (the displayed per-pair inequality at each `θ`); `cs_floor_pull` (the transported floor in original
  coordinates).
* JASA `cor:cs-translation`: `cs_translation_nominal`, `cs_translation_T`, `cs_translation_floor`,
  `cs_translation_slice` (`Δ_θ`, `T^θ_s`, the floors and the slice worst case depend on `θ = (A_θ, b_θ)` only through
  `A_θ`); `cs_translation_pure` (pure translations: structured worst case = product worst case, and the same for the
  certificate); `cs_translation_fixed_ge` (a class containing the translated references at some slice gives
  "at least").
* JASA `prop:cs-monotone` (extends the certified `Defects2` `cs_monotone_line_lower`): `cs_monotone_upper`
  (`≤ LΔ + √β₀ + √β₁`), `cs_monotone_zero_budget` (`= LΔ` at `β = 0`), `cs_monotone_line_infinite` (`+∞` without a
  slope bound when `Δ > 0`, prediction-line reading).

Not covered (declared):
* B overstate: compactness of `A` and the specific region `{x_u : u ∈ A}` in (i) (any family of curves with pointwise
  sup/inf is allowed: generalisation); `M_KS` positive definite is used only for the invertibility of `S`.
* B entropy-zero: existence and uniqueness of `π_θ` (strict convexity, stated in `subsec:soft-coupling`, not in the
  proposition: every minimizer selection is covered); the barycentric-*depth* convergence of the proof's last
  sentence (needs continuity of the gauge; not part of the statement); `rem:entropy-zero-bijective`; the
  quantitative rates cited after the proof.
* C gradient: nothing of the lemma; that `O ⊂ int 𝒰_K` is not needed.
* C neural: the "fixed common additive gauge" enters only through
  the hypothesis on `φ_n − g^OT_n`; the sentence after the proof (net matching, `d^net_n + (L^NN + L^OT)h_n`).
* JASA fl-price: none of the lemma; `U` uniform on the ellipsoid is the normalised Lebesgue measure of the set.
* JASA cs-certificate: the reweighting family (b) and the composition (c) (the frozen certificate is for uniform
  empirical centres; a reweighted centre is a weighted atomic law); compactness of `Θ` and continuity in `θ` (not used).
* JASA cs-translation: the free end `𝒫(T_θK)` and the identification of the scenario radius
  `R^{𝒩_θ}_min + β_s` with a constant radius (the floor is proved invariant, `cs_translation_floor`, and the radii are
  then taken constant in `cs_translation_pure`); the remark after the proof.
* JASA cs-monotone: the printed populations reading (refuted, certified `Defects2`), `η_s ∈ 𝒫₂` (all probability laws
  are allowed for the upper bound; the witnesses `T#μ_s` are in `𝒫₂` when `μ_s` is).

Encodings (to be checked by the critic):
* B overstate: `𝒯` any measure space `(T, μ)` (paper: `[0,1]`, Lebesgue); curves `T → ℝ`; `L(x) = ∫ a x` (`linL`);
  the band `B = [x↓, x↑]` is the set of a.e.-strongly measurable curves between the edges (`bandSet`; without the
  measurability clause a non-measurable `y` would have junk integral `0`); "`x↓, x↑` is the band of `𝒳`" is
  `IsBandOf` (pointwise `IsGLB`/`IsLUB`: no `sSup` junk); `sup_{y∈B} L(y)` is an `IsGreatest` value. Hypotheses: the
  curves of `𝒳` and the edges are a.e.-strongly measurable and `a·x↑`, `a·x↓` integrable (implicit in the paper: the
  integrals must exist). (ii): `ℝ^K = Fin K → ℝ`, `x_u(t) = 𝐞(t) ⬝ᵥ (m + S u)` (`𝔪 = 0`), `A = {mnorm M u ≤ τ}`,
  `‖S^⊤𝐞(t)‖_{M⁻¹} = mInvNorm M (Sᵀ *ᵥ 𝐞 t)`, `∫ a𝐞` the Bochner integral in `Fin K → ℝ`; `M_KS` symmetric positive
  definite is `(M * S).PosDef`; `τ > 0` (at `τ = 0` the ratio is `0/0`); `a` integrable, `𝐞` a.e.-strongly measurable
  and `a𝐞` integrable. The ratio claim `ExcessRatio` packs: the band edges of the region, both maxima, a positive
  denominator and the quotient. (iii): `K = 1 + 2J` coordinates indexed through `Fin 1 ⊕ (Fin J × Fin 2)`
  (`trigBasis`: `1`, `√2 cos 2π(j+1)t`, `√2 sin 2π(j+1)t`), `μ = Lebesgue on [0,1]`, `a = 1`, `S = σ • 1`, `σ > 0`,
  `M = 1`, any `m`, `τ > 0`.
* B entropy-zero: couplings are `Fin n → Fin m → ℝ`; `Π(a,b)` (`transportPolytope`) with nonnegative entries and
  the two marginal constraints (any `a, b`); `⟨C,π⟩ = Σ C_ij π_ij`; "`π_θ` minimizes `⟨C,π⟩ + Ω_θ(π)` over `Π(a,b)`"
  is `IsRegMin`, for every `θ > 0`, any selection; "unique minimizer `π_0`" is `IsUniqueMin`; "`Ω_θ` vanishes
  uniformly on the polytope as `θ ↓ 0`" is `∀ δ > 0, ∀ᶠ θ in 𝓝[>] 0, ∀ π ∈ Π, |Ω_θ π| ≤ δ`; the limit is along
  `𝓝[>] 0`. `Ω_ε = ε Σ π_ij log(π_ij/(a_ib_j))` (`entReg`, `a_i, b_j > 0`; `0 log 0 = 0` is Mathlib's convention
  and the paper's), `Ω_γ = (γ/2) Σ_j Σ_i π_ij²` (`quadReg`). `R^bar_i = Σ_j (π_ij/a_i) u_j` (`baryRank`, `u_j` in any
  real normed space), `D^soft_i = 1 − Σ_j (π_ij/a_i) g(u_j)` (`softDepth`, `g` any function, paper: `g_K`); `a_i > 0`.
  Permutation: `m = n`, `a = b = 1/n`, `π_0 i j = if σ i = j then 1/n else 0`, hard rank `u_{σ(i)}`.
* C gradient: `ℝ^K = EuclideanSpace ℝ (Fin K)` with `volume`; "`χ` convex and finite on `O`" is a real `χ` convex on
  a convex `C ⊇ O` (the effective domain of an extended convex function finite on `O`); "`∇χ = G` a.e. on `O`" is
  `∀ᵐ u, u ∈ O → HasGradientAt χ (G u) u`; conclusion `∀ u ∈ O, HasGradientAt χ (G u) u`. Second part: `μ_K =
  volume.withDensity ρ`, `ρ` measurable, `ρ > 0` a.e. on `O`; Brenier `Q_{K,x} = ∇χ_{K,x}` `μ_K`-a.e. is
  `∀ᵐ u ∂μ_K, HasGradientAt χ (Qb u) u`; "`Q_{K,x}` has a continuous version on `O`" is `G` continuous on `O` with
  `G = Qb` `μ_K`-a.e. on `O`.
* C neural: `ℝ^K` as above; `φ_n` real, convex on `ℝ^K`, with gradient `T_n(u)` at each `u ∈ S`; `d_n` is any bound
  `|φ_n − χ| ≤ d_n` on `S'` (the paper's `d_n` is the sup, the smallest such bound: generalisation); "`L`-Lipschitz
  gradient nearby" is `∇χ = Q` on `S'` with `‖Q v − Q w‖ ≤ L‖v − w‖` for `v, w ∈ S'`, `L ≥ 0`; "permissible `r`" is
  `closedBall u r ⊆ S'` for every `u ∈ S`. Consistency: `n : ℕ`, `atTop`; `S` compact, `S'` compact with a uniform
  thickening `closedBall u r₀ ⊆ S'` (`u ∈ S`), `χ` convex on a convex `C` with `S' ⊆ int C`, gradient `Q` on `S'`
  (its continuity on `S'` is proved, Rockafellar 25.5);
  teacher limit `g_n → χ` uniformly on `S'`; `sup_{S'}|φ_n − g_n| → 0`; conclusion `TendstoUniformlyOn T Q atTop S`.
  Edges: `sup_A ⟨v, F⟩` is `supOver A F v` (real `sSup` of a set proved bounded and nonempty for the large `n`
  quantified).
* JASA fl-price: `ℝ^d = EuclideanSpace ℝ (Fin d)`; `X ∼ P`, `U ∼ ρ` probability measures, `P(Kᶜ) = 0`; `P ∗ U` is
  Mathlib's `Measure.conv` (the law of `X + U`, `U` independent); `π_h(U)` (`jitterPrice`) in `ℝ≥0∞` with
  `∫⁻` (no integrability junk); `W₂` is Tau Ceti's `wassersteinEDist 2`; `h` measurable (`Measure.map` genuine, `ℝ`
  Borel). Linear case: `K` nonempty, `E‖U‖² < ∞`, `wᵀE[UUᵀ]w = Σ_ij w_i w_j ∫ u_i u_j dρ`. Ellipsoid: `w ≠ 0`,
  `s_w, s_p > 0`, `ŵ = w/|w|`, the set `{s_w t ŵ + s_p y : ⟨y, ŵ⟩ = 0, t² + |y|² ≤ 1}` (`ellipsoid`), `U ∼
  volume[|ellipsoid]` (`ProbabilityTheory.cond`).
* JASA cs-certificate: the frozen `Wave4b` setting (`InBall`, transported classes `{𝔗_θ#ν}`, `sqrtTPull`,
  `nominal` at the transported centres). Floor: `R^{ν}_min(P̂) = −ε n⁻¹ Σ_i log E_ν e^{−c(x_i,·)/ε}` (`floorRef`),
  `R^𝒩_min = inf_{ν∈𝒩}` in `EReal` (`floorSet`; no `ℝ`-junk).
* JASA cs-translation: `ℝ^d = EuclideanSpace ℝ (Fin d)`, `c(x,y) = ‖x − y‖²` (`sqCost`), `h(x) = ⟨w,x⟩ + b`
  (`linRule`), `T_θ x = A x + b_θ` (`affT A b`, `A` a continuous linear map); "depends on `θ` only through `A_θ`" is
  "the value at `(A, b)` equals the value at `(A, 0)`"; the slice worst case (`sliceWorst`) is the frozen `Findep` at
  the transported centres and classes; pure translations `𝔗_θ = (· + b_θ)`, `Θ` nonempty, constant radii.
* JASA cs-monotone: the frozen `lineMonoSup` (pairs of probability laws on `ℝ` around `T#μ_s`, `μ_s` any probability
  laws, paper `h#P̂_s`); `β_s ∈ ℝ≥0`, `√β_s` is `NNReal.sqrt`.

Critic notes:
* All 27 claims are proved in `Wave18a/Route{Overstate,OverstateTrig,EntropyZero,Gradient,Neural,Jitter,Ellipsoid,
  CsCertificate,CsTranslation,CsMonotone}.lean` (axioms: propext, Classical.choice, Quot.sound). Routes reuse the
  untrusted `OTFD/Wave10a/RouteKarp` (certified `ballM_support`, `dot_le_of_ball`, `ballM_compact`), `Wave4b/
  RouteCertificate` (certified `certificate`, `sqrtT_map`, `refClass_map`) and `Defects2/RouteCsMonotone`
  (certified `cs_monotone_line_lower`) — routes only.
* Partly certified before: `thm:cs-certificate` (`Wave4b.cs_slice_T`, `cs_certificate`: the "Consequently" bound)
  and `prop:cs-monotone` (`Defects2`: printed reading refuted, lower bound `≥ LΔ` on the prediction line). This
  wave adds the per-pair display, the transported floor, the upper bound, the `β = 0` equality and the corrected
  `+∞` clause; nothing is restated.
* No statement of the eight results was found false. Hypotheses made explicit: `0 ≤ L` in `neural_potential_rate`
  (with `K = 0` and `L < 0` the bound `2d/r + Lr/2` can be negative while the left side is `0`; "L-Lipschitz"
  presupposes it); `RefClass` (finite references) in `cs_translation_slice`/`_pure` (σ-finiteness for the
  invariance of `KL` under a translation, `MeasurableEmbedding.rnDeriv_map`); `w ≠ 0` and `s_w, s_p > 0` for the
  ellipsoid (`ŵ = w/|w|`).
* `neural_potential_consistency` proves continuity of `Q = ∇χ` on `S' ⊆ int C` (Rockafellar 25.5: one-sided
  secants plus uniform continuity of `χ` on a compact ball in `int C`) and then uses Heine–Cantor; the rate claim
  needs no convexity of `χ` (descent lemma only). `neural_potential_rate_opt` is arithmetic only: it does not check
  that `r = 2√(d/L)` is admissible (`closedBall u r ⊆ S'`).
* `sqCost` is unbounded, so the frozen `InBall` cost integral is a junk `0` for witnesses `Γ_i` with non-integrable
  cost (heavy tails). The invariance claims transport this identically on both sides, so they remain meaningful for
  compactly supported references (the paper's setting; with `ε > 0` the witnesses live on the references' supports).
* `cs_translation_fixed_ge` (revised after the critic): the paper's `K_Θ` need not contain `K`, so the claim no
  longer assumes an identity slice; any slice `θ₀` whose class contains the translated references works.
* Paper S4: B `prop:rk-band-overstates`(iii) should read "`1 ≤ j ≤ J`" (at `j = 0` the sine term vanishes and
  `K ≠ 2J+1`); the formalisation indexes `j + 1`, `j < J`.
* C gradient: the route avoids Rademacher and subdifferential existence: a.e. gradients are dense in `O`; the
  gradient inequality at those points passes to the limit (continuity of `χ` on `int C`, of `G` on `O`), so
  `G(u) ∈ ∂χ(u)` for every `u ∈ O`, and `0 ≤ χ(u+h) − χ(u) − ⟨G(u),h⟩ ≤ ⟨G(u+h) − G(u),h⟩ = o(‖h‖)`.
* B overstate (ii): `M_KS ≻ 0` enters only through `det S ≠ 0` (positive denominator); `a ∈ L¹` is not used
  beyond `a𝐞 ∈ L¹`. (iii): `‖𝐞(t)‖² = 1 + 2J` and `∫₀¹ 𝐞 = (1,0,…,0)`, so the ratio is `σ√K/σ` exactly.
* JASA fl-price: `E[UUᵀ] = I/(d+2)` for the unit ball is proved by polar coordinates (`∫_B‖x‖² = d|B|/(d+2)`) and
  reflection invariance of `a ↦ ∫_B⟨a,x⟩²`; the ellipsoid is `A(B)`, `A = s_wP_ŵ + s_p(I − P_ŵ)`, `A⁻¹` explicit,
  and the Jacobian change of variables gives `Unif(A B) = A#Unif(B)` in integrals.
* JASA cs-translation: with `ε > 0` a finite `KL` forces `Γ_i ≪ ν`, so the frozen `InBall` cost integrals are taken
  over the references' supports (compact in the paper); the invariance statements hold for any references, and
  `floorRef`'s possible `log 0` junk (a reference null near an anchor) is transported identically on both sides.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave18a

/-! ### B `prop:rk-band-overstates` -/

section Overstate
variable {T : Type*} [MeasurableSpace T]

/-- `L(x) = ∫_𝒯 a x`. -/
def linL (μ : Measure T) (a x : T → ℝ) : ℝ := ∫ t, a t * x t ∂μ

/-- The band `B = [x↓, x↑]`: a.e.-strongly measurable curves between the edges. -/
def bandSet (μ : Measure T) (xlo xup : T → ℝ) : Set (T → ℝ) :=
  {y | AEStronglyMeasurable y μ ∧ ∀ t, xlo t ≤ y t ∧ y t ≤ xup t}

/-- `x↓`, `x↑` are the pointwise infimum and supremum of the region `𝒳`. -/
def IsBandOf (X : Set (T → ℝ)) (xlo xup : T → ℝ) : Prop :=
  ∀ t, IsGLB ((fun x => x t) '' X) (xlo t) ∧ IsLUB ((fun x => x t) '' X) (xup t)

/-- The affine-reference region `{x_u : ‖u‖_{M_K} ≤ τ}`, `x_u(t) = 𝐞(t) ⬝ᵥ (m + S u)` (`𝔪 = 0`). -/
def affRegion {K : ℕ} (e : T → Fin K → ℝ) (M S : Matrix (Fin K) (Fin K) ℝ) (m : Fin K → ℝ) (τ : ℝ) :
    Set (T → ℝ) :=
  {x | ∃ u, StatFormal.OTFD.Wave2.mnorm M u ≤ τ ∧ x = fun t => e t ⬝ᵥ (m + S *ᵥ u)}

/-- The ratio `∫|a| ‖S^⊤𝐞‖_{M⁻¹} / ‖S^⊤ ∫ a𝐞‖_{M⁻¹}`. -/
def overstateRatio {K : ℕ} (μ : Measure T) (a : T → ℝ) (e : T → Fin K → ℝ) (M S : Matrix (Fin K) (Fin K) ℝ) :
    ℝ :=
  (∫ t, |a t| * StatFormal.OTFD.Wave10a.mInvNorm M (Sᵀ *ᵥ e t) ∂μ) /
    StatFormal.OTFD.Wave10a.mInvNorm M (Sᵀ *ᵥ ∫ t, a t • e t ∂μ)

/-- `(sup_B L − L(x_[m])) / (sup_𝒳 L − L(x_[m])) = r`, with `B` the band of `𝒳`, both suprema attained and a
positive denominator. -/
def ExcessRatio (μ : Measure T) (a : T → ℝ) (X : Set (T → ℝ)) (xm : T → ℝ) (r : ℝ) : Prop :=
  ∃ xlo xup sB sX, IsBandOf X xlo xup ∧ IsGreatest (linL μ a '' bandSet μ xlo xup) sB ∧
    IsGreatest (linL μ a '' X) sX ∧ 0 < sX - linL μ a xm ∧ (sB - linL μ a xm) / (sX - linL μ a xm) = r

end Overstate

/-- The trigonometric basis `1, √2 cos 2π(j+1)t, √2 sin 2π(j+1)t` (`j < J`) on `K = 1 + 2J` coordinates. -/
def trigBasis (J : ℕ) (t : ℝ) : Fin (1 + J * 2) → ℝ := fun k =>
  match finSumFinEquiv.symm k with
  | Sum.inl _ => 1
  | Sum.inr k' =>
    if (finProdFinEquiv.symm k').2 = 0 then
      Real.sqrt 2 * Real.cos (2 * Real.pi * ((finProdFinEquiv.symm k').1 + 1 : ℕ) * t)
    else Real.sqrt 2 * Real.sin (2 * Real.pi * ((finProdFinEquiv.symm k').1 + 1 : ℕ) * t)

/-! ### B `prop:entropy-zero` -/

section EntropyZero
variable {n m : ℕ}

/-- The transport polytope `Π(a,b)`. -/
def transportPolytope (a : Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → Fin m → ℝ) :=
  {π | (∀ i j, 0 ≤ π i j) ∧ (∀ i, ∑ j, π i j = a i) ∧ ∀ j, ∑ i, π i j = b j}

/-- `⟨C, π⟩`. -/
def frob (C π : Fin n → Fin m → ℝ) : ℝ := ∑ i, ∑ j, C i j * π i j

/-- `π` minimizes `⟨C,·⟩ + Ω` over `P`. -/
def IsRegMin (P : Set (Fin n → Fin m → ℝ)) (C : Fin n → Fin m → ℝ) (Ω : (Fin n → Fin m → ℝ) → ℝ)
    (π : Fin n → Fin m → ℝ) : Prop :=
  π ∈ P ∧ ∀ π' ∈ P, frob C π + Ω π ≤ frob C π' + Ω π'

/-- `π₀` is the unique minimizer of `⟨C,·⟩` over `P`. -/
def IsUniqueMin (P : Set (Fin n → Fin m → ℝ)) (C π₀ : Fin n → Fin m → ℝ) : Prop :=
  π₀ ∈ P ∧ (∀ π ∈ P, frob C π₀ ≤ frob C π) ∧ ∀ π ∈ P, frob C π = frob C π₀ → π = π₀

/-- The entropic penalty `Ω_ε(π) = ε Σ π_ij log(π_ij/(a_i b_j))`. -/
def entReg (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) (π : Fin n → Fin m → ℝ) : ℝ :=
  ε * ∑ i, ∑ j, π i j * Real.log (π i j / (a i * b j))

/-- The quadratic penalty `Ω_γ(π) = (γ/2) Σ_j ‖π_{·,j}‖²`. -/
def quadReg (γ : ℝ) (π : Fin n → Fin m → ℝ) : ℝ := γ / 2 * ∑ j, ∑ i, π i j ^ 2

/-- Barycentric rank `R^bar_i = Σ_j (π_ij/a_i) u_j`. -/
def baryRank {E : Type*} [AddCommGroup E] [Module ℝ E] (a : Fin n → ℝ) (u : Fin m → E)
    (π : Fin n → Fin m → ℝ) (i : Fin n) : E :=
  ∑ j, (π i j / a i) • u j

/-- Mean-radius soft depth `D^soft_i = 1 − Σ_j (π_ij/a_i) g(u_j)`. -/
def softDepth {E : Type*} (a : Fin n → ℝ) (g : E → ℝ) (u : Fin m → E) (π : Fin n → Fin m → ℝ)
    (i : Fin n) : ℝ :=
  1 - ∑ j, π i j / a i * g (u j)

end EntropyZero

/-! ### C `prop:neural-potential-approximation` -/

/-- `sup_{u ∈ A} ⟨v, F(u)⟩` (a real `sSup`). -/
def supOver {K : ℕ} (A : Set (EuclideanSpace ℝ (Fin K)))
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (v : EuclideanSpace ℝ (Fin K)) : ℝ :=
  sSup ((fun u => ⟪v, F u⟫) '' A)

/-! ### JASA `lem:fl-price` -/

section Jitter
variable {d : ℕ}

/-- `π_h(U) = sup_{x∈K} (E|h(x+U) − h(x)|²)^{1/2}`, in `ℝ≥0∞`. -/
def jitterPrice (K : Set (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨆ x ∈ K, (∫⁻ u, ‖h (x + u) - h x‖ₑ ^ 2 ∂ρ) ^ (1 / 2 : ℝ)

/-- The ellipsoid `{s_w t ŵ + s_p y : y ⊥ ŵ, t² + |y|² ≤ 1}`, `ŵ = w/|w|`. -/
def ellipsoid (w : EuclideanSpace ℝ (Fin d)) (sw sp : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {v | ∃ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ⟪y, w⟫ = 0 ∧ t ^ 2 + ‖y‖ ^ 2 ≤ 1 ∧
    v = (sw * t) • (‖w‖⁻¹ • w) + sp • y}

end Jitter

/-! ### JASA `thm:cs-certificate`, `cor:cs-translation` -/

section CommonShift
variable {K : Type} [MeasurableSpace K]

/-- The floor term at one reference: `R^{ν}_min(P̂) = −ε n⁻¹ Σ_i log E_ν e^{−c(x_i,·)/ε}`. -/
def floorRef {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (ν : Measure K) : ℝ :=
  -ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-c (x i) z / ε) ∂ν))

/-- The pulled-back floor term `−ε n⁻¹ Σ_i log E_ν e^{−c^θ(x_i,·)/ε}`, `c^θ(x₀,x) = c(𝔗x₀, 𝔗x)`. -/
def floorPull {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (𝔗 : K → K) (ε : ℝ) (ν : Measure K) : ℝ :=
  -ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-c (𝔗 (x i)) (𝔗 z) / ε) ∂ν))

/-- `R^𝒩_min(P̂) = inf_{ν∈𝒩} R^{ν}_min(P̂)` (`= −ε sup_ν …`), in `EReal`. -/
def floorSet {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (N : Set (Measure K)) : EReal :=
  ⨅ ν ∈ N, ((floorRef x c ε ν : ℝ) : EReal)

/-- The slice worst case `sup_{B₀(θ)×B₁(θ)} W₂²(h#Q₀, h#Q₁)` at the transported centres and classes. -/
def sliceWorst {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (ε r₀ r₁ : ℝ) (𝔗 : K → K)
    (N₀ N₁ : Set (Measure K)) (h : K → ℝ) : ℝ≥0∞ :=
  StatFormal.Wave4b.Findep (fun i => 𝔗 (x₀ i)) (fun i => 𝔗 (x₁ i)) c ε r₀ r₁
    ((fun ν => ν.map 𝔗) '' N₀) ((fun ν => ν.map 𝔗) '' N₁) h

end CommonShift

/-- `c(x,y) = ‖x − y‖²`. -/
def sqCost {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) : ℝ := ‖x - y‖ ^ 2

/-- The linear rule `h(x) = ⟨w,x⟩ + b`. -/
def linRule {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (b : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ⟪w, x⟫ + b

/-- The affine map `T(x) = A x + b`. -/
def affT {d : ℕ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := A x + b

namespace Claims

open StatFormal.OTFD.Wave10a (mInvNorm)
open StatFormal.Wave4b (InBall Findep Fstruct nominal sqrtT TrefPull sqrtTPull RefClass)
open StatFormal.Defects2 (lineMonoSup ThetaL ThetaMono)
open StatFormal.RobustEquality.Certificate (centre KernelWitness Tref1)

/-! #### B `prop:rk-band-overstates` -/

/-- (i) `sup_{y∈B} L(y) = ∫(a⁺x↑ − a⁻x↓)` (attained) `≥ L(x)` for every `x ∈ 𝒳`. -/
def rk_band_overstates_i : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) (a : T → ℝ) (X : Set (T → ℝ)) (xlo xup : T → ℝ),
    IsBandOf X xlo xup → (∀ x ∈ X, AEStronglyMeasurable x μ) → AEStronglyMeasurable a μ →
    AEStronglyMeasurable xlo μ → AEStronglyMeasurable xup μ →
    Integrable (fun t => a t * xup t) μ → Integrable (fun t => a t * xlo t) μ →
      IsGreatest (linL μ a '' bandSet μ xlo xup) (∫ t, (max (a t) 0 * xup t - max (-a t) 0 * xlo t) ∂μ) ∧
        ∀ x ∈ X, linL μ a x ≤ ∫ t, (max (a t) 0 * xup t - max (-a t) 0 * xlo t) ∂μ

/-- (ii) Affine-reference laws: the excess ratio equals `∫|a| ‖S^⊤𝐞‖_{M⁻¹} / ‖S^⊤∫a𝐞‖_{M⁻¹}`, which is `≥ 1`. -/
def rk_band_overstates_ii : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) (K : ℕ) (a : T → ℝ) (e : T → Fin K → ℝ)
    (M S : Matrix (Fin K) (Fin K) ℝ) (m : Fin K → ℝ) (τ : ℝ),
    M.PosDef → (M * S).PosDef → 0 < τ → Integrable a μ → AEStronglyMeasurable e μ →
    Integrable (fun t => a t • e t) μ → (∫ t, a t • e t ∂μ) ≠ 0 →
      ExcessRatio μ a (affRegion e M S m τ) (fun t => e t ⬝ᵥ m) (overstateRatio μ a e M S) ∧
        1 ≤ overstateRatio μ a e M S

/-- (iii) Trigonometric basis, `S = σI`, `M_K = I`, `L` the mean on `[0,1]`: the ratio is `√K = √(2J+1)`. -/
def rk_band_overstates_iii : Prop :=
  ∀ (J : ℕ) (σ τ : ℝ) (m : Fin (1 + J * 2) → ℝ), 0 < σ → 0 < τ →
    ExcessRatio (volume.restrict (Icc (0 : ℝ) 1)) (fun _ => 1)
      (affRegion (trigBasis J) 1 (σ • 1) m τ) (fun t => trigBasis J t ⬝ᵥ m) (Real.sqrt (2 * J + 1))

/-! #### B `prop:entropy-zero` -/

/-- General regularizer vanishing uniformly on `Π(a,b)`: `π_θ → π₀`, and the barycentric ranks and mean-radius
soft depths converge to those of `π₀`. -/
def entropy_zero : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ)
    (Ω : ℝ → (Fin n → Fin m → ℝ) → ℝ) (πθ : ℝ → Fin n → Fin m → ℝ) (π₀ : Fin n → Fin m → ℝ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Fin m → E) (g : E → ℝ),
    (∀ i, 0 < a i) → IsUniqueMin (transportPolytope a b) C π₀ →
    (∀ δ > 0, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ π ∈ transportPolytope a b, |Ω θ π| ≤ δ) →
    (∀ θ > 0, IsRegMin (transportPolytope a b) C (Ω θ) (πθ θ)) →
      Tendsto πθ (𝓝[>] 0) (𝓝 π₀) ∧
        (∀ i, Tendsto (fun θ => baryRank a u (πθ θ) i) (𝓝[>] 0) (𝓝 (baryRank a u π₀ i))) ∧
        ∀ i, Tendsto (fun θ => softDepth a g u (πθ θ) i) (𝓝[>] 0) (𝓝 (softDepth a g u π₀ i))

/-- The entropic instance: `Ω_ε` vanishes uniformly on `Π(a,b)`, so entropic minimizers converge to `π₀`. -/
def entropy_zero_entropic : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (πθ : ℝ → Fin n → Fin m → ℝ)
    (π₀ : Fin n → Fin m → ℝ), (∀ i, 0 < a i) → (∀ j, 0 < b j) →
    (∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ π ∈ transportPolytope a b, |entReg a b ε π| ≤ δ) ∧
      (IsUniqueMin (transportPolytope a b) C π₀ →
        (∀ ε > 0, IsRegMin (transportPolytope a b) C (entReg a b ε) (πθ ε)) →
          Tendsto πθ (𝓝[>] 0) (𝓝 π₀))

/-- The quadratic instance: `Ω_γ` vanishes uniformly on `Π(a,b)`, so quadratic minimizers converge to `π₀`. -/
def entropy_zero_quadratic : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (πθ : ℝ → Fin n → Fin m → ℝ)
    (π₀ : Fin n → Fin m → ℝ), (∀ i, 0 < a i) →
    (∀ δ > 0, ∀ᶠ γ in 𝓝[>] (0 : ℝ), ∀ π ∈ transportPolytope a b, |quadReg γ π| ≤ δ) ∧
      (IsUniqueMin (transportPolytope a b) C π₀ →
        (∀ γ > 0, IsRegMin (transportPolytope a b) C (quadReg γ) (πθ γ)) →
          Tendsto πθ (𝓝[>] 0) (𝓝 π₀))

/-- `m = n`, uniform marginals and a permutation optimum `π₀ = P_σ/n`: the limits are the hard assigned rank
`u_{σ(i)}` and depth `1 − g(u_{σ(i)})`. -/
def entropy_zero_permutation : Prop :=
  ∀ (n : ℕ) (C : Fin n → Fin n → ℝ) (Ω : ℝ → (Fin n → Fin n → ℝ) → ℝ) (πθ : ℝ → Fin n → Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Fin n → E) (g : E → ℝ),
    let un : Fin n → ℝ := fun _ => 1 / n
    IsUniqueMin (transportPolytope un un) C (fun i j => if σ i = j then 1 / n else 0) →
    (∀ δ > 0, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ π ∈ transportPolytope un un, |Ω θ π| ≤ δ) →
    (∀ θ > 0, IsRegMin (transportPolytope un un) C (Ω θ) (πθ θ)) →
      ∀ i, Tendsto (fun θ => baryRank un u (πθ θ) i) (𝓝[>] 0) (𝓝 (u (σ i))) ∧
        Tendsto (fun θ => softDepth un g u (πθ θ) i) (𝓝[>] 0) (𝓝 (1 - g (u (σ i))))

/-! #### C `lem:convex-continuous-gradient` -/

/-- `χ` convex and finite on `O` open, `∇χ = G` a.e. on `O`, `G` continuous on `O`: `χ` is differentiable on `O`
with `∇χ = G`. -/
def convex_continuous_gradient : Prop :=
  ∀ (K : ℕ) (C O : Set (EuclideanSpace ℝ (Fin K))) (χ : EuclideanSpace ℝ (Fin K) → ℝ)
    (G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    Convex ℝ C → ConvexOn ℝ C χ → IsOpen O → O ⊆ C → ContinuousOn G O →
    (∀ᵐ u ∂volume, u ∈ O → HasGradientAt χ (G u) u) →
      ∀ u ∈ O, HasGradientAt χ (G u) u

/-- "In particular": `μ_K` with a density positive a.e. on `O`, `Q_{K,x} = ∇χ_{K,x}` `μ_K`-a.e., and a continuous
version of `Q_{K,x}` on `O`: `χ_{K,x}` is differentiable on `O` with gradient that version. -/
def convex_continuous_gradient_density : Prop :=
  ∀ (K : ℕ) (C O : Set (EuclideanSpace ℝ (Fin K))) (χ : EuclideanSpace ℝ (Fin K) → ℝ)
    (ρ : EuclideanSpace ℝ (Fin K) → ℝ≥0∞) (Qb G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    Convex ℝ C → ConvexOn ℝ C χ → IsOpen O → O ⊆ C → Measurable ρ →
    (∀ᵐ u ∂volume, u ∈ O → 0 < ρ u) →
    (∀ᵐ u ∂(volume.withDensity ρ), HasGradientAt χ (Qb u) u) →
    ContinuousOn G O → (∀ᵐ u ∂(volume.withDensity ρ), u ∈ O → G u = Qb u) →
      ∀ u ∈ O, HasGradientAt χ (G u) u

/-! #### C `prop:neural-potential-approximation` -/

/-- The rate: `sup_S ‖∇φ_n − Q_{K,x}‖ ≤ 2d_n/r + Lr/2` for every permissible `r > 0`. -/
def neural_potential_rate : Prop :=
  ∀ (K : ℕ) (S S' : Set (EuclideanSpace ℝ (Fin K))) (φ χ : EuclideanSpace ℝ (Fin K) → ℝ)
    (Tφ Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (dn L r : ℝ),
    ConvexOn ℝ univ φ → (∀ u ∈ S, HasGradientAt φ (Tφ u) u) →
    (∀ v ∈ S', HasGradientAt χ (Q v) v) → (∀ v ∈ S', ∀ w ∈ S', ‖Q v - Q w‖ ≤ L * ‖v - w‖) →
    (∀ v ∈ S', |φ v - χ v| ≤ dn) → 0 ≤ L → 0 < r → (∀ u ∈ S, Metric.closedBall u r ⊆ S') →
      ∀ u ∈ S, ‖Tφ u - Q u‖ ≤ 2 * dn / r + L * r / 2

/-- The optimised rate: at `r = 2√(d_n/L)` the bound `2d_n/r + Lr/2` equals `2√(L d_n)`. -/
def neural_potential_rate_opt : Prop :=
  ∀ dn L : ℝ, 0 < dn → 0 < L →
    2 * dn / (2 * Real.sqrt (dn / L)) + L * (2 * Real.sqrt (dn / L)) / 2 = 2 * Real.sqrt (L * dn)

/-- Consistency: teacher limit `g_n → χ` uniformly on `S'` and `sup_{S'}|φ_n − g_n| → 0` give uniform convergence of
the maps `∇φ_n → Q_{K,x}` on `S`. -/
def neural_potential_consistency : Prop :=
  ∀ (K : ℕ) (S S' C : Set (EuclideanSpace ℝ (Fin K))) (χ : EuclideanSpace ℝ (Fin K) → ℝ)
    (g φ : ℕ → EuclideanSpace ℝ (Fin K) → ℝ) (Tφ : ℕ → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (r₀ : ℝ),
    IsCompact S' → 0 < r₀ → (∀ u ∈ S, Metric.closedBall u r₀ ⊆ S') →
    Convex ℝ C → S' ⊆ interior C → ConvexOn ℝ C χ → (∀ v ∈ S', HasGradientAt χ (Q v) v) →
    (∀ k, ConvexOn ℝ univ (φ k)) → (∀ k, ∀ u ∈ S, HasGradientAt (φ k) (Tφ k u) u) →
    TendstoUniformlyOn g χ atTop S' → TendstoUniformlyOn (fun k v => φ k v - g k v) 0 atTop S' →
      TendstoUniformlyOn Tφ Q atTop S

/-- Exact band edges: eventually in `n`, for every nonempty level region `A ⊆ S` and `‖v‖ ≤ E`,
`|sup_A ⟨v, ∇φ_n⟩ − sup_A ⟨v, Q_{K,x}⟩| ≤ η` (here `S` compact and `Q` continuous on `S`). -/
def neural_potential_edges : Prop :=
  ∀ (K : ℕ) (S : Set (EuclideanSpace ℝ (Fin K))) (Tφ : ℕ → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (E : ℝ),
    IsCompact S → ContinuousOn Q S → TendstoUniformlyOn Tφ Q atTop S →
      ∀ η > 0, ∀ᶠ k in atTop, ∀ A ⊆ S, A.Nonempty → ∀ v : EuclideanSpace ℝ (Fin K), ‖v‖ ≤ E →
        |supOver A (Tφ k) v - supOver A Q v| ≤ η

/-! #### JASA `lem:fl-price` -/

/-- `W₂(h#P, h#(P∗U)) ≤ π_h(U)` for `supp P ⊆ K`. -/
def fl_price_bound : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (P ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] [IsProbabilityMeasure ρ],
    Measurable h → P Kᶜ = 0 →
      wassersteinEDist 2 (P.map h) ((P ∗ ρ).map h) ≤ jitterPrice K h ρ

/-- `h = ⟨w,·⟩`: `π_h(U) = (wᵀ E[UUᵀ] w)^{1/2}`. -/
def fl_price_linear : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ],
    K.Nonempty → Integrable (fun u => ‖u‖ ^ 2) ρ →
      jitterPrice K (fun x => ⟪w, x⟫) ρ =
        ENNReal.ofReal (Real.sqrt (∑ i, ∑ j, w i * w j * ∫ u, u i * u j ∂ρ))

/-- `U` uniform on the ellipsoid: `π_h(U) = |w| s_w / √(d+2)`, whatever `s_p`. -/
def fl_price_ellipsoid : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)) (sw sp : ℝ),
    K.Nonempty → w ≠ 0 → 0 < sw → 0 < sp →
      jitterPrice K (fun x => ⟪w, x⟫) (volume[|ellipsoid w sw sp]) =
        ENNReal.ofReal (‖w‖ * sw / Real.sqrt (d + 2))

/-! #### JASA `thm:cs-certificate` (extension) -/

/-- The displayed inequality: for each `θ` and every `(Q₀,Q₁) ∈ B₀(θ) × B₁(θ)` (transported centres and classes),
every `λ₀, λ₁ > 0`: `W₂(h#Q₀, h#Q₁) ≤ Δ_θ(h) + √T^θ₀(h,λ₀) + √T^θ₁(h,λ₁)`. -/
def cs_certificate_pair : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K)
    (c : K → K → ℝ) (ε r₀ r₁ lam₀ lam₁ : ℝ) (𝔗 : K → K) (h : K → ℝ) (N₀ N₁ : Set (Measure K))
    (Q₀ Q₁ : Measure K),
    0 < n₀ → 0 < n₁ → 0 < ε → 0 < lam₀ → 0 < lam₁ →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → Measurable 𝔗 → RefClass N₀ → RefClass N₁ →
    InBall (fun i => 𝔗 (x₀ i)) c ε r₀ ((fun ν => ν.map 𝔗) '' N₀) Q₀ →
    InBall (fun i => 𝔗 (x₁ i)) c ε r₁ ((fun ν => ν.map 𝔗) '' N₁) Q₁ →
      wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ≤
        nominal (fun i => 𝔗 (x₀ i)) (fun i => 𝔗 (x₁ i)) h + sqrtTPull x₀ c h 𝔗 ε r₀ lam₀ N₀ +
          sqrtTPull x₁ c h 𝔗 ε r₁ lam₁ N₁

/-- The floor of the transported set in original coordinates:
`R^{𝔗#ν}_min(𝔗P̂) = −ε n⁻¹ Σ_i log E_ν e^{−c^θ(x_i,·)/ε}`. -/
def cs_floor_pull : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (𝔗 : K → K) (ε : ℝ)
    (ν : Measure K), Measurable (Function.uncurry c) → Measurable 𝔗 →
      floorRef (fun i => 𝔗 (x i)) c ε (ν.map 𝔗) = floorPull x c 𝔗 ε ν

/-! #### JASA `cor:cs-translation` -/

/-- `Δ_θ` depends on `θ = (A, b)` only through `A` (linear rule). -/
def cs_translation_nominal : Prop :=
  ∀ (d n₀ n₁ : ℕ) (x₀ : Fin n₀ → EuclideanSpace ℝ (Fin d)) (x₁ : Fin n₁ → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d)) (b₀ : ℝ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d)),
    nominal (fun i => affT A b (x₀ i)) (fun i => affT A b (x₁ i)) (linRule w b₀) =
      nominal (fun i => affT A 0 (x₀ i)) (fun i => affT A 0 (x₁ i)) (linRule w b₀)

/-- `T^θ_s` (per reference and over the class) depends on `θ` only through `A`. -/
def cs_translation_T : Prop :=
  ∀ (d n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (w : EuclideanSpace ℝ (Fin d)) (b₀ : ℝ)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d))
    (ε r lam : ℝ) (N : Set (Measure (EuclideanSpace ℝ (Fin d)))),
    (∀ ν : Measure (EuclideanSpace ℝ (Fin d)),
      TrefPull x sqCost (linRule w b₀) (affT A b) ε r lam ν = TrefPull x sqCost (linRule w b₀) (affT A 0) ε r lam ν) ∧
    sqrtTPull x sqCost (linRule w b₀) (affT A b) ε r lam N = sqrtTPull x sqCost (linRule w b₀) (affT A 0) ε r lam N

/-- The floor of the transported set depends on `θ` only through `A`. -/
def cs_translation_floor : Prop :=
  ∀ (d n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (N : Set (Measure (EuclideanSpace ℝ (Fin d)))),
    floorSet (fun i => affT A b (x i)) sqCost ε ((fun ν => ν.map (affT A b)) '' N) =
      floorSet (fun i => affT A 0 (x i)) sqCost ε ((fun ν => ν.map (affT A 0)) '' N)

/-- The worst case over `B₀(θ) × B₁(θ)` depends on `θ` only through `A`. -/
def cs_translation_slice : Prop :=
  ∀ (d n₀ n₁ : ℕ) (x₀ : Fin n₀ → EuclideanSpace ℝ (Fin d)) (x₁ : Fin n₁ → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d)) (b₀ : ℝ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d)) (ε r₀ r₁ : ℝ) (N₀ N₁ : Set (Measure (EuclideanSpace ℝ (Fin d)))),
    RefClass N₀ → RefClass N₁ →
    sliceWorst x₀ x₁ sqCost ε r₀ r₁ (affT A b) N₀ N₁ (linRule w b₀) =
      sliceWorst x₀ x₁ sqCost ε r₀ r₁ (affT A 0) N₀ N₁ (linRule w b₀)

/-- Pure translations: the structured worst case equals the product worst case of the main text, and so does the
certificate `sup_θ inf_λ (Δ_θ + √T^θ₀ + √T^θ₁)²`. -/
def cs_translation_pure : Prop :=
  ∀ (d n₀ n₁ : ℕ) (Θ : Type) (x₀ : Fin n₀ → EuclideanSpace ℝ (Fin d)) (x₁ : Fin n₁ → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d)) (b₀ : ℝ) (bθ : Θ → EuclideanSpace ℝ (Fin d)) (ε r₀ r₁ : ℝ)
    (N₀ N₁ : Set (Measure (EuclideanSpace ℝ (Fin d)))),
    Nonempty Θ → RefClass N₀ → RefClass N₁ →
      Fstruct x₀ x₁ sqCost ε (fun θ z => z + bθ θ) (fun _ => r₀) (fun _ => r₁)
          (fun θ => (fun ν => ν.map (· + bθ θ)) '' N₀) (fun θ => (fun ν => ν.map (· + bθ θ)) '' N₁)
          (linRule w b₀) = Findep x₀ x₁ sqCost ε r₀ r₁ N₀ N₁ (linRule w b₀) ∧
        (⨆ θ, ⨅ (lam₀ : ℝ) (_ : 0 < lam₀) (lam₁ : ℝ) (_ : 0 < lam₁),
          (nominal (fun i => x₀ i + bθ θ) (fun i => x₁ i + bθ θ) (linRule w b₀) +
            sqrtTPull x₀ sqCost (linRule w b₀) (· + bθ θ) ε r₀ lam₀ N₀ +
            sqrtTPull x₁ sqCost (linRule w b₀) (· + bθ θ) ε r₁ lam₁ N₁) ^ 2) =
          ⨅ (lam₀ : ℝ) (_ : 0 < lam₀) (lam₁ : ℝ) (_ : 0 < lam₁),
            (nominal x₀ x₁ (linRule w b₀) + sqrtT x₀ sqCost (linRule w b₀) ε r₀ lam₀ N₀ +
              sqrtT x₁ sqCost (linRule w b₀) ε r₁ lam₁ N₁) ^ 2

/-- Pure translations with larger classes (and radii) at some slice `θ₀`: the structured worst case is at least the
product one (the identity need not be a slice). -/
def cs_translation_fixed_ge : Prop :=
  ∀ (d n₀ n₁ : ℕ) (Θ : Type) (x₀ : Fin n₀ → EuclideanSpace ℝ (Fin d)) (x₁ : Fin n₁ → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d)) (b₀ : ℝ) (bθ : Θ → EuclideanSpace ℝ (Fin d)) (ε r₀ r₁ : ℝ) (r₀' r₁' : Θ → ℝ)
    (N₀ N₁ : Set (Measure (EuclideanSpace ℝ (Fin d)))) (N₀' N₁' : Θ → Set (Measure (EuclideanSpace ℝ (Fin d))))
    (θ₀ : Θ), RefClass N₀ → RefClass N₁ →
    (fun ν => ν.map (· + bθ θ₀)) '' N₀ ⊆ N₀' θ₀ → (fun ν => ν.map (· + bθ θ₀)) '' N₁ ⊆ N₁' θ₀ →
    r₀ ≤ r₀' θ₀ → r₁ ≤ r₁' θ₀ →
      Findep x₀ x₁ sqCost ε r₀ r₁ N₀ N₁ (linRule w b₀) ≤
        Fstruct x₀ x₁ sqCost ε (fun θ z => z + bθ θ) r₀' r₁' N₀' N₁' (linRule w b₀)

/-! #### JASA `prop:cs-monotone` (extension, prediction-line pairs) -/

/-- `sup W₂(η₀,η₁) ≤ LΔ + √β₀ + √β₁` over common `T ∈ Θ_L`. -/
def cs_monotone_upper : Prop :=
  ∀ (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (L β₀ β₁ : ℝ≥0),
    lineMonoSup μ₀ μ₁ β₀ β₁ (ThetaL L) ≤
      (L : ℝ≥0∞) * wassersteinEDist 2 μ₀ μ₁ + (NNReal.sqrt β₀ : ℝ≥0∞) + (NNReal.sqrt β₁ : ℝ≥0∞)

/-- At `β₀ = β₁ = 0` the supremum equals `LΔ`. -/
def cs_monotone_zero_budget : Prop :=
  ∀ (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (L : ℝ≥0),
    lineMonoSup μ₀ μ₁ 0 0 (ThetaL L) = (L : ℝ≥0∞) * wassersteinEDist 2 μ₀ μ₁

/-- Without a slope bound the supremum is `+∞` whenever `Δ > 0` (prediction-line reading). -/
def cs_monotone_line_infinite : Prop :=
  ∀ (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (β₀ β₁ : ℝ≥0∞),
    0 < wassersteinEDist 2 μ₀ μ₁ → lineMonoSup μ₀ μ₁ β₀ β₁ ThetaMono = ⊤

end Claims
end StatFormal.Wave18a
