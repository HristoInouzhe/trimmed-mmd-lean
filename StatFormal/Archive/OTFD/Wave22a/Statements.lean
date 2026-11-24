import StatFormal.Archive.OTFD.Wave10a.Statements
import StatFormal.Archive.OTFD.Scale.Statements
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# FROZEN STATEMENTS — otfd wave 22a (QUEUE rows 244–249, 266–268): A `prop:lift-select`,
# `thm:sieve-convergence`, `cor:app-ghs-lipschitz`, `thm:rt-fixedK`, `thm:rt-coherent`, `prop:rt-lift`,
# `lem:T-stability`, `prop:estimated-basis`, `prop:rt-adaptive`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`; current text of
`otfd/papers/A_sieves/`):
* `prop:lift-select` (`main.tex:1315-1323`), with `def:lift` (`main.tex:1158-1173`) and the paragraph "The dimension,
  through lifts" (`main.tex:1306-1313`: separable, diagonal and full quadratic tails are monotone).
* `thm:sieve-convergence` (`main.tex:741-797`), with `def:ghs-rank` (`main.tex:721-739`).
* `cor:app-ghs-lipschitz` (`supplement.tex:1061-1072`).
* `thm:rt-fixedK` (`main.tex:1461-1471`) and `thm:rt-coherent` (`main.tex:1479-1491`), with the setting paragraph
  (`main.tex:1381-1402`: `Λ = θP + (1−θ)Q`, `ν^P_K = F^Λ_K#P_K`, `𝓔_K = 𝒟(ν^P_K, ν^Q_K)`, `𝓔_∞`, `𝒟`).
* `prop:rt-lift` (`supplement.tex:5558-5570`), with the pooled lifted ranks `R^lift_i = (R_i, t_⊥(X_{i,⊥}))`
  (`supplement.tex:5549-5556`).
* `lem:T-stability` (`main.tex:1229-1235`), with the probability scale `Υ` (`main.tex:1202-1222`, frozen in
  `OTFD/Scale`).
* `prop:estimated-basis` (`main.tex:1029-1095`).
* `prop:rt-adaptive` (`supplement.tex:5743-5755`), with the definition of `p_l`, `m`, `p^ad` (`supplement.tex:
  5734-5741`) and its proof (`:5757-5768`).
Imports the frozen `OTFD/Wave10a` statements (`permPValue`; through them the frozen `OTFD/Wave1` `truncK`,
`PellClass`) and `OTFD/Scale` (`IsGauge`, `ScaleHyp`, `ups`), not copied. Mathlib otherwise.

Covered:
* `cor:app-ghs-lipschitz`: `ghs_lip_finite` (the supremum `ψ̃` is finite everywhere once finite at one point),
  `ghs_lip` (`ψ̃` convex and `L_Q`-Lipschitz), `ghs_lip_subgrad` (every subgradient of `ψ̃` lies in the closed
  convex hull of the slopes), `ghs_lip_grad` (`‖∇ψ̃‖ ≤ L_Q` wherever the gradient exists).
* `thm:sieve-convergence`: `sieve_subdiff_nonempty` (in `ℝ^K` the Lipschitz representative has `∂φ_K(z) ≠ ∅` for
  every `z`), `sieve_subgrad_cube` (cubic law: every subgradient of `ψ_K = φ_K ∘ Π_K` lies in the Hilbert cube
  `C_λ`, the condition licensing the norm upgrade), `cube_interior_empty` (`int C_λ = ∅`, why the cubic quantile
  clause is unavailable).
* `thm:rt-fixedK`: `rt_fixedK_laws` (if the pooled map is injective on a `Λ`-conull set, the two rank laws are equal
  iff `P_K = Q_K`).
* `thm:rt-coherent`: `rt_coherent_pell` (`Λ ∈ 𝒫^ℓ(H)`), `rt_coherent_bound` (the displayed perturbation inequality
  `|𝓔_K − 𝓔_∞| ≤ 4(θ^{−1/2} + (1−θ)^{−1/2}) S_Λ(K)`), `rt_coherent_eventually` ("hence there is `K_1` with
  `𝓔_K ≥ 𝓔_∞/2` for `K ≥ K_1`", given `S_Λ(K) → 0` and `𝓔_∞ > 0`).
* `prop:rt-lift`: (i) `rt_lift_pvalue`; (ii) `rt_lift_laws` (lift injective `Λ_T`-a.e. ⇒ lifted rank laws differ
  iff `P_T ≠ Q_T`).
* `lem:T-stability`: `t_stability_push` (`Υ#ν = Υ#μ_K ⇒ ν = μ_K`), `t_stability_eq` (the "in particular", with
  `ED = 0` replaced by equality of the two laws on the probability scale).
* `prop:lift-select`: `lift_grad_separable` (separable monotone tails), `lift_grad_quadratic` (full quadratic tails).
* `prop:estimated-basis`: (i) `ebasis_reflect` (centred cubic law, coordinate reflections); (iii) `ebasis_cap`
  (`‖η ê − e‖² ≤ 2`), `ebasis_w2` (the two displayed inequalities, Bosq's bound as a hypothesis).
* `prop:rt-adaptive`: (i) `rt_adaptive_valid`; (ii) `rt_adaptive_bound` (`p^ad ≤ L min_l p_l(σ_0)`).

Not covered (declared):
* ghs-lipschitz: that `ψ̃` agrees with the GHS potential `ψ` `P`-a.e. and `P`-a.e. uniqueness of the gradient (GHS,
  L4).
* sieve-convergence: both limits (GHS stability `thm:app-ghs-stability`, L4) and the quantile clauses; existence of
  the Brenier potentials (`thm:app-ghs-existence`); the chain rule for `ψ_K` beyond the cube range (here `ψ_K` is
  written directly as a supremum of affine maps with slopes `ι_K z`).
* rt-fixedK: `𝖤_N → 𝓔_K` in probability and `c_{N,α} → 0` (finite-dimensional weak-convergence stability of hard
  assignments, missing); the a.e. injectivity of `F^Λ_K` (Brenier–McCann inverse, a hypothesis); energy-distance
  identifiability (Székely–Rizzo / Lyons, missing), which turns `rt_fixedK_laws` into `𝓔_K > 0 ⇔ P_K ≠ Q_K`;
  the consistency of the test.
* rt-coherent: `S_Λ(K) → 0` (`prop:integrated-sieve-strong`, L4) and `𝓔_∞ > 0` for `P ≠ Q` (identifiability in `H`
  and a.e. injectivity of `𝔽_Λ`); the test consistency.
* rt-lift: (ii) that population tail maps of laws with positive densities on intervals are injective on those
  intervals, and the head map's a.e. injectivity (both hypotheses); positivity of the energy distance.
* T-stability: the `δ–η` form (compactness and portmanteau in `ℝ^K`, missing); `ED = 0 ⇒` equal laws
  (identifiability, missing); `P_K ∈ 𝒫^ℓ(ℝ^K)` without moments (McCann/GHS uniqueness): the claim assumes `P_K ≪`
  Haar and a finite second moment, under which Brenier uniqueness (Tau Ceti) applies.
* lift-select: "Hence `lem:T-stability`, `prop:selector`, `prop:T-proxy` hold in `ℝ^T`" (instantiation: the claims
  of those results are stated for any dimension, so they apply to lifts once these are gradients); the "in
  particular" consistency (flagged, see critic notes).
* estimated-basis: (i) for the ball law, `Π̂_K#μ̂ = μ_K` (definitional), the calibrations; (ii); the `O_P(n_0^{−1/2})`
  rate and Bosq's perturbation bound (operator perturbation theory, missing); (iv), (v) (L4).
* rt-adaptive: consistency in (ii) (needs `thm:rt-fixedK`'s limits); data-dependent levels/bases beyond what the
  encoding of the statistics absorbs (see encodings).

Encodings (to be checked by the critic):
* `H` a real inner product space (complete where gradients or Hahn–Banach are used). Subgradients of a real
  function: `IsSubgrad f x y :⇔ ∀ z, f x + ⟨y, z − x⟩ ≤ f z`. `ψ̃ = supAff S b`, a real `⨆` over the subtype `S`;
  `S` is the part of `ch(supp Q)` where `ψ* < ∞` (any set with `‖y‖ ≤ L` on it: generalisation), `b = ψ*` restricted
  there (any real function); the `⨆` is genuine because `S ≠ ∅` and it is bounded above at one point (hypothesis,
  `ghs_lip_finite` propagates it; no `sSup ∅`/unbounded junk). `L_Q` is any `L` bounding `‖y‖` on `S`.
* Sieve: `Π_K = truncK e K` (frozen), `e : ℕ → H` orthonormal; `ψ_K(x) = φ_K(Π_K x)` with `φ_K = supAff S b` on
  `ℝ^K = EuclideanSpace ℝ (Fin K)` and slopes `S ⊆ ∏_{k<K}[−λ_k, λ_k]` (`ch supp μ_K` for the cubic law);
  `C_λ = cubeH e λ = {y : ∀ k, |⟨y, e_k⟩| ≤ λ_k}` (equal to the Hilbert cube when `e` is a Hilbert basis);
  `int C_λ = ∅` is claimed for `λ_k → 0` (the paper's `λ ∈ ℓ²` is stronger).
* Rank tests: `Λ = mix θ P Q = θP + (1−θ)Q` (`ENNReal.ofReal` weights), `0 < θ < 1`. `𝒟 = energyD`, iterated
  Bochner integrals `2∫∫‖u−v‖ dν' dν − ∫∫‖u−u'‖ dν dν − ∫∫‖v−v'‖ dν' dν'`; in every claim the laws are images of
  bounded measurable maps, so the integrands are bounded and measurable (no junk). Rank laws are `P.map F`,
  `F` measurable (no `Measure.map` junk). `rt_fixedK_laws` is stated on any standard Borel source and countably
  separated target (`ℝ^K` both); "`F^Λ_K` has a `Λ_K`-a.e. inverse" is weakened to "injective on a measurable
  `Λ`-conull set" (implied by it). `rt_coherent_bound` takes any two bounded measurable maps `f, g : X → F` into a
  separable normed group: `f = ι_K ∘ F^Λ_K ∘ Π_K`, `g = 𝔽_Λ`, `X = H`, so `𝓔_K = energyD (P.map f) (Q.map f)` (`ι_K` is an
  isometry, so the energy distance in `ℝ^K` equals that of the embedded laws) and
  `S_Λ(K) = (∫‖f − g‖² dΛ)^{1/2}` (Bochner; the integrand is bounded). `θ^{−1/2} = 1/√θ`. `𝒫^ℓ(H)` is the frozen
  `PellClass`.
* rt-lift: `ℝ^T = EuclideanSpace ℝ (Fin K ⊕ Fin m)` (head `inl`, tail `inr`, `T = K + m`, every `K ≤ T`), `headT`,
  `liftMap F_K t` (head map on the head, `t_j` on tail coordinate `j`). (i): the pooled lifted ranks are
  `liftRanks R t 𝔛 i = (R(𝔛) i, t(𝔛)(𝔛 i))` with any head rank rule `R` that is permutation-equivariant a.s. (the
  pooled hard ranks under a.s. uniqueness, `prop:rt-df`) and any tail rule `t(𝔛) : X → Z` computed from the pooled
  sample by a reordering-invariant rule (a.s.); exchangeability of the pooled sample is `H_0`; `permPValue` frozen;
  the event is measurable and its probability `≤ α` for every real `α`. (ii): "injective `Λ_T`-a.e." is: `F_K`
  injective on a measurable `S_K` with `Λ{head ∉ S_K} = 0` and each `t_j` injective on a measurable `I_j` with
  `Λ{x_j ∉ I_j} = 0` (the population tail map is strictly increasing on the support interval).
* T-stability: `E` any finite-dimensional real inner product space (`ℝ^K`), `P_K ≪ ρ` for an additive Haar `ρ`;
  "`P_K`-a.e. equal to the gradient of a convex function" is `IsConvGradAE`: some everywhere-finite convex
  `φ : E → ℝ` with `HasGradientAt φ (G x) x` for `P`-a.e. `x` (specialisation: finite potentials; with a bounded
  reference the potentials are finite, `cor:app-ghs-lipschitz`). `F_K` is any such map with `F_K#P_K = μ_K`.
  `ED(Υ#G#P_K, Υ#μ_K) = 0` is replaced by `Υ#(G#P_K) = Υ#μ_K` (identifiability of ED not available).
* lift-select: lifts on `ℝ^T = EuclideanSpace ℝ (Fin K ⊕ Fin m)`; head potential `φ_K` real convex with
  `∇φ_K(x_K) = F_K(x_K)` for `P_T`-a.e. `x` (the head hypothesis pulled back to `P_T`, weaker than `P_K`-a.e.);
  separable tails: monotone `t_j : ℝ → ℝ` (the "nondecreasing map per coordinate"), atomless tail marginals
  `P_T{x_j = s} = 0` (implied by `P_T ∈ 𝒫^ℓ(ℝ^T)`: coordinate hyperplanes are Lipschitz hypersurfaces); quadratic tails:
  `x_⊥ ↦ Λ(x_⊥ − m)` with `Λ` a positive (self-adjoint, `⟨Λv,v⟩ ≥ 0`) operator on `ℝ^m` (PD in the paper:
  generalisation).
* estimated-basis: (i) the centred cubic law is `⊗_k Unif[−λ_k, λ_k]` on `Fin K → ℝ` (`cubeLaw`), reflections
  `x ↦ (η_k x_k)`, `η_k ∈ {±1}`. (iii) a realisation of the basis split is fixed (conditioning on `𝓘_0`): any
  `e, ê : ℕ → H` with unit vectors for `k < K`; `η_k = signCoef ⟨ê_k, e_k⟩` (`sign 0 := 1`); `J Π̂_K X = reflE η (truncK ê K X)`;
  `W_2²` is `w2sq`, the `⨅` over couplings (product-measure marginals) of `∫⁻ ‖z₁ − z₂‖²` in `ℝ≥0∞`; `‖Σ‖_op` is any `s`
  with `E⟨v,X⟩² ≤ s‖v‖²` for all `v` (`Σ = E[X ⊗ X]`); `‖Γ̂ − Γ‖_op = δ ≥ 0`, `sep_k > 0`; Bosq's bound
  `‖η_kê_k − e_k‖ ≤ 2√2 δ / sep_k` is a hypothesis; expectations are lower integrals (no integrability junk).
* rt-adaptive: levels `l : Fin (L+1)` (`L + 1 ≥ 1` levels), statistic of a labelling `σ` at level `l` is `T_l(x ∘ σ)`
  (a level whose basis/grid is a symmetric function of the unordered pooled sample is absorbed into `T_l`, since
  `T_l(x ∘ σ)` is then computed with the same basis for every `σ`); `σ_0 = 1`, `σ_{b} = g_b`; `pLev`, `mMin` (a `⨅` over
  the nonempty finite `Fin (L+1)`: the true minimum), `pAd`. (i): `B` relabellings iid uniform on `S_N`,
  independent of the data, is the average over `g : Fin B → Perm (Fin N)` with weight `(N!)^{−B}` (Fubini), data law
  `μ` exchangeable (`H_0`), every real `α`, every `B`. (ii): the full permutation distribution, `pFull`, `pAdFull`.

Critic notes:
* All 22 claims are proved in `Wave22a/Route{Convex,Laws,Coherent,LiftTest,Adaptive,Basis,Lift,Stability}.lean`
  (axioms: propext, Classical.choice, Quot.sound). Routes use the certified Wave 10a route (`rt_perm_pvalue`), the
  `OTFD/Scale` routes (`g_ups`, `S_ups`, `continuousOn_Sinv`, `measure_ups_ball`), the untrusted Foundations library
  `Exchangeable/Group` (`sum_measure_eq_lintegral_card`) and Tau Ceti (`Brenier`: Knott–Smith optimality of subgradient
  selections, Brenier uniqueness) — routes only.
* No statement was found false. The constant `4(θ^{−1/2} + (1−θ)^{−1/2})` of `thm:rt-coherent` is confirmed.
* Near-definitional or small cores: `rt_lift_pvalue` (the frozen `rt_perm_pvalue` plus equivariance of the lifted
  ranks), `rt_coherent_pell` (additivity of masses, moments and null sets), `ebasis_cap`, `cube_interior_empty`,
  `rt_lift_laws` (`rt_fixedK_laws` applied to the lift). None restates its own hypothesis.
* `prop:lift-select` "in particular": the cited schedule must be a fixed-`T`, out-of-sample consistency result (review
  m16); the current text cites `prop:app-fixed-soft-consistency` (the extract still shows `thm:app-entropic-diagonal`).
  Not covered.
* `prop:lift-select`, first sentence: as a `P_T`-a.e. statement it needs the tail marginals to be atomless at the
  jumps of the tail maps; this holds for `P_T ∈ 𝒫^ℓ(ℝ^T)`, the standing class, so no error, but it is implicit.
* `thm:sieve-convergence`: wording slip m6 — the range of `𝔽_P` lies in `C_λ` (covered by `ghs_lip_subgrad` with
  slopes in `C_λ`), not in `ι_K(ch supp μ_K)`.
* `rt_fixedK_laws`, `rt_lift_laws`, `t_stability_eq` are conditional on hypotheses that the paper derives from
  Brenier–McCann (a.e. inverses) and energy-distance identifiability.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 22 TRUE, none tautological. Coverage is PARTIAL (core only) for every item
  except rt-adaptive (i) and rt-lift (i); sieve-convergence is auxiliary only (no limit clause). `t_stability_eq`
  assumes `MemLp id 2 μ` (rules out heavy-tailed references); `IsConvGradAE` requires finite potentials, which bites
  for unbounded references (`P = Unif[0,1]`, `μ = N(0,1)`: `F_K = Φ⁻¹` is the derivative of no everywhere-finite convex
  function). rt-fixedK's "injective on a conull set" is implied by the a.e. inverse; lift-select's atomless tails follow
  from `𝒫^ℓ`. Paper S4 (DEFECTS #72, "m6"): A main.tex:764 "range of `𝔽_P` lies in `ι_K(ch supp μ_K)`" should be
  "`ch supp μ = C_λ`" (`K = 1`: `⟨𝔽_P(x), e_2⟩ ≠ 0` with positive probability); (⋆) still holds with `𝒞 = C_λ`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.Wave22a

open StatFormal.OTFD.Scale (IsGauge ScaleHyp ups)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave10a (permPValue)

/-! ### Convex analysis: `cor:app-ghs-lipschitz`, `thm:sieve-convergence` -/

section Convex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `y ∈ ∂f(x)` for a real-valued `f`. -/
def IsSubgrad (f : H → ℝ) (x y : H) : Prop := ∀ z, f x + ⟪y, z - x⟫ ≤ f z

/-- `ψ̃(x) = sup_{y ∈ S} {⟨x, y⟩ − b(y)}`, a supremum of affine maps with slopes in `S`. -/
def supAff (S : Set H) (b : H → ℝ) (x : H) : ℝ := ⨆ y : S, (⟪x, (y : H)⟫ - b y)

/-- The Hilbert cube `C_λ = {y : |⟨y, e_k⟩| ≤ λ_k for all k}`. -/
def cubeH (e : ℕ → H) (lam : ℕ → ℝ) : Set H := {y | ∀ k, |⟪y, e k⟫| ≤ lam k}

/-- `P`-a.e. the gradient of an everywhere-finite convex function. -/
def IsConvGradAE [CompleteSpace H] [MeasurableSpace H] (P : Measure H) (G : H → H) : Prop :=
  ∃ φ : H → ℝ, ConvexOn ℝ univ φ ∧ ∀ᵐ x ∂P, HasGradientAt φ (G x) x

end Convex

/-! ### Rank tests: `thm:rt-fixedK`, `thm:rt-coherent`, `prop:rt-lift`, `prop:rt-adaptive` -/

section Rank

/-- The pooled law `Λ = θP + (1−θ)Q`. -/
def mix {X : Type*} [MeasurableSpace X] (θ : ℝ) (P Q : Measure X) : Measure X :=
  ENNReal.ofReal θ • P + ENNReal.ofReal (1 - θ) • Q

/-- The energy distance `𝒟(ν,ν') = 2E‖U−V‖ − E‖U−U'‖ − E‖V−V'‖`. -/
def energyD {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] (ν ν' : Measure F) : ℝ :=
  2 * ∫ u, ∫ v, ‖u - v‖ ∂ν' ∂ν - ∫ u, ∫ u', ‖u - u'‖ ∂ν ∂ν - ∫ v, ∫ v', ‖v - v'‖ ∂ν' ∂ν'

/-- The head `x_K` of `x ∈ ℝ^T = ℝ^{K ⊕ m}`. -/
def headT {K m : ℕ} (x : EuclideanSpace ℝ (Fin K ⊕ Fin m)) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 fun k => x (Sum.inl k)

/-- The tail `x_⊥` of `x ∈ ℝ^T = ℝ^{K ⊕ m}`. -/
def tailT {K m : ℕ} (x : EuclideanSpace ℝ (Fin K ⊕ Fin m)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j => x (Sum.inr j)

/-- The lifted map with separable tails: `x ↦ (F_K(x_K), (t_j(x_j))_j)`. -/
def liftMap {K m : ℕ} (FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (t : Fin m → ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin K ⊕ Fin m)) : EuclideanSpace ℝ (Fin K ⊕ Fin m) :=
  WithLp.toLp 2 fun i => Sum.elim (fun k => FK (headT x) k) (fun j => t j (x (Sum.inr j))) i

/-- The lifted map with full quadratic tail: `x ↦ (F_K(x_K), Λ(x_⊥ − m))`. -/
def liftQuad {K m : ℕ} (FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin K ⊕ Fin m)) : EuclideanSpace ℝ (Fin K ⊕ Fin m) :=
  WithLp.toLp 2 fun i => Sum.elim (fun k => FK (headT x) k) (fun j => A (tailT x - c) j) i

/-- Pooled lifted ranks `R^lift_i = (R_i, t_⊥(X_i))`, with the tail rule computed from the pooled sample. -/
def liftRanks {X Y Z : Type*} {N : ℕ} (R : (Fin N → X) → Fin N → Y) (t : (Fin N → X) → X → Z)
    (x : Fin N → X) : Fin N → Y × Z :=
  fun i => (R x i, t x (x i))

/-- The labellings `σ_0 = 1, σ_1, …, σ_B`. -/
def labs {N B : ℕ} (g : Fin B → Equiv.Perm (Fin N)) : Fin (B + 1) → Equiv.Perm (Fin N) :=
  Fin.cons 1 g

/-- `p_l(σ_c) = (B+1)⁻¹ #{d : 𝖤^{(l)}(σ_d) ≥ 𝖤^{(l)}(σ_c)}`. -/
def pLev {X : Type*} {N B L : ℕ} (T : Fin (L + 1) → (Fin N → X) → ℝ) (x : Fin N → X)
    (g : Fin B → Equiv.Perm (Fin N)) (l : Fin (L + 1)) (c : Fin (B + 1)) : ℝ :=
  ((Finset.univ.filter fun d : Fin (B + 1) =>
      T l (x ∘ ⇑(labs g c)) ≤ T l (x ∘ ⇑(labs g d))).card : ℝ) / (B + 1)

/-- `m(σ_c) = min_l p_l(σ_c)`. -/
def mMin {X : Type*} {N B L : ℕ} (T : Fin (L + 1) → (Fin N → X) → ℝ) (x : Fin N → X)
    (g : Fin B → Equiv.Perm (Fin N)) (c : Fin (B + 1)) : ℝ :=
  ⨅ l, pLev T x g l c

/-- The adaptive `p`-value `p^ad = (B+1)⁻¹ #{b : m(σ_b) ≤ m(σ_0)}`. -/
def pAd {X : Type*} {N B L : ℕ} (T : Fin (L + 1) → (Fin N → X) → ℝ) (x : Fin N → X)
    (g : Fin B → Equiv.Perm (Fin N)) : ℝ :=
  ((Finset.univ.filter fun c : Fin (B + 1) => mMin T x g c ≤ mMin T x g 0).card : ℝ) / (B + 1)

/-- Full permutation distribution: `p_l(σ) = #{τ : 𝖤^{(l)}(τ) ≥ 𝖤^{(l)}(σ)} / N!`. -/
def pFull {X : Type*} {N L : ℕ} (T : Fin (L + 1) → (Fin N → X) → ℝ) (x : Fin N → X)
    (l : Fin (L + 1)) (σ : Equiv.Perm (Fin N)) : ℝ :=
  ((Finset.univ.filter fun τ : Equiv.Perm (Fin N) => T l (x ∘ ⇑σ) ≤ T l (x ∘ ⇑τ)).card : ℝ) /
    (Nat.factorial N : ℝ)

/-- Full permutation distribution: `p^ad = #{τ : m(τ) ≤ m(σ_0)} / N!`, `m = min_l p_l`. -/
def pAdFull {X : Type*} {N L : ℕ} (T : Fin (L + 1) → (Fin N → X) → ℝ) (x : Fin N → X) : ℝ :=
  ((Finset.univ.filter fun τ : Equiv.Perm (Fin N) =>
      (⨅ l, pFull T x l τ) ≤ ⨅ l, pFull T x l 1).card : ℝ) / (Nat.factorial N : ℝ)

end Rank

/-! ### `prop:estimated-basis` -/

section Basis

/-- `Unif[−a, a]`. -/
def unifSym (a : ℝ) : Measure ℝ := (volume (Icc (-a) a))⁻¹ • volume.restrict (Icc (-a) a)

/-- The centred cubic law `⊗_k Unif[−λ_k, λ_k]` on coefficient vectors. -/
def cubeLaw {K : ℕ} (lam : Fin K → ℝ) : Measure (Fin K → ℝ) := Measure.pi fun k => unifSym (lam k)

/-- `sign a` with `sign 0 := 1`. -/
def signCoef (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

/-- `J z = diag(η) z`. -/
def reflE {K : ℕ} (η : Fin K → ℝ) (z : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 fun k => η k * z k

/-- `W_2(ν, ν')²`, the infimum over couplings of `∫ ‖z₁ − z₂‖²`. -/
def w2sq {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] (ν ν' : Measure F) : ℝ≥0∞ :=
  ⨅ (π : Measure (F × F)) (_ : π.map Prod.fst = ν ∧ π.map Prod.snd = ν'), ∫⁻ z, ‖z.1 - z.2‖ₑ ^ 2 ∂π

end Basis

namespace Claims

/-! #### `cor:app-ghs-lipschitz` -/

/-- `ψ̃ = sup_{y∈S}{⟨·,y⟩ − b(y)}` with bounded slopes is finite everywhere once it is finite at one point. -/
def ghs_lip_finite : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S : Set H) (b : H → ℝ) (L : ℝ) (x₀ : H),
    S.Nonempty → (∀ y ∈ S, ‖y‖ ≤ L) → BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
      ∀ x, BddAbove (range fun y : S => ⟪x, (y : H)⟫ - b y)

/-- `ψ̃` is convex and globally `L_Q`-Lipschitz. -/
def ghs_lip : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S : Set H) (b : H → ℝ) (L : ℝ) (x₀ : H),
    S.Nonempty → (∀ y ∈ S, ‖y‖ ≤ L) → BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
      ConvexOn ℝ univ (supAff S b) ∧ ∀ x x', |supAff S b x - supAff S b x'| ≤ L * ‖x - x'‖

/-- Every subgradient of `ψ̃` lies in the closed convex hull of the slopes. -/
def ghs_lip_subgrad : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (S : Set H) (b : H → ℝ)
    (L : ℝ) (x₀ : H),
    S.Nonempty → (∀ y ∈ S, ‖y‖ ≤ L) → BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
      ∀ x y, IsSubgrad (supAff S b) x y → y ∈ closure (convexHull ℝ S)

/-- The gradient of `ψ̃` is bounded by `L_Q` wherever it exists. -/
def ghs_lip_grad : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (S : Set H) (b : H → ℝ)
    (L : ℝ) (x₀ : H),
    S.Nonempty → (∀ y ∈ S, ‖y‖ ≤ L) → BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
      ∀ x g, HasGradientAt (supAff S b) g x → ‖g‖ ≤ L

/-! #### `thm:sieve-convergence` -/

/-- In `ℝ^K`, the Lipschitz representative has a subgradient at every point. -/
def sieve_subdiff_nonempty : Prop :=
  ∀ (K : ℕ) (S : Set (EuclideanSpace ℝ (Fin K))) (b : EuclideanSpace ℝ (Fin K) → ℝ) (L : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin K)),
    S.Nonempty → (∀ y ∈ S, ‖y‖ ≤ L) → BddAbove (range fun y : S => ⟪x₀, (y : EuclideanSpace ℝ (Fin K))⟫ - b y) →
      ∀ z, ∃ y, IsSubgrad (supAff S b) z y

/-- Cubic law: every subgradient of the embedded sieve potential `ψ_K = φ_K ∘ Π_K`, `φ_K` a supremum of affine
maps with slopes in the box `∏_{k<K}[−λ_k, λ_k]`, lies in the Hilbert cube `C_λ`. -/
def sieve_subgrad_cube : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (lam : ℕ → ℝ) (K : ℕ)
    (S : Set (EuclideanSpace ℝ (Fin K))) (b : EuclideanSpace ℝ (Fin K) → ℝ) (x₀ : EuclideanSpace ℝ (Fin K)),
    Orthonormal ℝ e → (∀ k, 0 ≤ lam k) → S.Nonempty → (∀ z ∈ S, ∀ k : Fin K, |z k| ≤ lam k) →
    BddAbove (range fun z : S => ⟪x₀, (z : EuclideanSpace ℝ (Fin K))⟫ - b z) →
      ∀ x y, IsSubgrad (fun x => supAff S b (truncK e K x)) x y → y ∈ cubeH e lam

/-- The Hilbert cube has empty interior (`λ_k → 0`). -/
def cube_interior_empty : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (lam : ℕ → ℝ),
    Orthonormal ℝ e → Tendsto lam atTop (𝓝 0) → interior (cubeH e lam) = ∅

/-! #### `thm:rt-fixedK` -/

/-- If the pooled map `F` is injective on a measurable `Λ`-conull set, the rank laws `F#P`, `F#Q` agree iff
`P = Q`. -/
def rt_fixedK_laws : Prop :=
  ∀ (E Y : Type) [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y] (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (θ : ℝ) (F : E → Y) (S : Set E),
    0 < θ → θ < 1 → Measurable F → MeasurableSet S → mix θ P Q Sᶜ = 0 → InjOn F S →
      (P.map F = Q.map F ↔ P = Q)

/-! #### `thm:rt-coherent` -/

/-- `Λ ∈ 𝒫^ℓ(H)`. -/
def rt_coherent_pell : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] (P Q : Measure H) (θ : ℝ),
    0 < θ → θ < 1 → PellClass P → PellClass Q →
      PellClass (mix θ P Q)

/-- The perturbation inequality `|𝓔_K − 𝓔_∞| ≤ 4(θ^{−1/2} + (1−θ)^{−1/2}) S_Λ(K)`, for any two bounded measurable
rank maps `f` (sieve) and `g` (Hilbert). -/
def rt_coherent_bound : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (F : Type) [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (θ M : ℝ) (f g : X → F),
    0 < θ → θ < 1 → Measurable f → Measurable g → (∀ x, ‖f x‖ ≤ M) → (∀ x, ‖g x‖ ≤ M) →
      |energyD (P.map f) (Q.map f) - energyD (P.map g) (Q.map g)| ≤
        4 * (1 / √θ + 1 / √(1 - θ)) * √(∫ x, ‖f x - g x‖ ^ 2 ∂(mix θ P Q))

/-- If `S_Λ(K) → 0` and `𝓔_∞ > 0`, then `𝓔_K ≥ 𝓔_∞/2` for all large `K`. -/
def rt_coherent_eventually : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (F : Type) [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (θ M : ℝ) (f : ℕ → X → F) (g : X → F),
    0 < θ → θ < 1 → (∀ K, Measurable (f K)) → Measurable g → (∀ K x, ‖f K x‖ ≤ M) → (∀ x, ‖g x‖ ≤ M) →
    Tendsto (fun K => ∫ x, ‖f K x - g x‖ ^ 2 ∂(mix θ P Q)) atTop (𝓝 0) →
    0 < energyD (P.map g) (Q.map g) →
      ∀ᶠ K in atTop, energyD (P.map g) (Q.map g) / 2 ≤ energyD (P.map (f K)) (Q.map (f K))

/-! #### `prop:rt-lift` -/

/-- (i) Under `H_0` the permutation `p`-value of any statistic of the pooled lifted ranks is super-uniform. -/
def rt_lift_pvalue : Prop :=
  ∀ (X Y Z : Type) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (𝔛 : Ω → Fin N → X)
    (R : (Fin N → X) → Fin N → Y) (t : (Fin N → X) → X → Z) (T : (Fin N → Y × Z) → ℝ) (α : ℝ),
    Measurable 𝔛 → Measurable R → Measurable (Function.uncurry t) → Measurable T →
    (∀ τ : Equiv.Perm (Fin N), P.map (fun ω => 𝔛 ω ∘ ⇑τ) = P.map 𝔛) →
    (∀ τ : Equiv.Perm (Fin N), ∀ᵐ ω ∂P, R (𝔛 ω ∘ ⇑τ) = R (𝔛 ω) ∘ ⇑τ) →
    (∀ τ : Equiv.Perm (Fin N), ∀ᵐ ω ∂P, t (𝔛 ω ∘ ⇑τ) = t (𝔛 ω)) →
      MeasurableSet {ω | permPValue T (liftRanks R t (𝔛 ω)) ≤ α} ∧
      P {ω | permPValue T (liftRanks R t (𝔛 ω)) ≤ α} ≤ ENNReal.ofReal α

/-- (ii) If the head map is injective on a `Λ_K`-conull set and each tail map is injective on a set carrying its
`Λ`-marginal, the lifted rank laws of the two groups agree iff `P_T = Q_T`, whatever `K`. -/
def rt_lift_laws : Prop :=
  ∀ (K m : ℕ) (P Q : Measure (EuclideanSpace ℝ (Fin K ⊕ Fin m))) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (θ : ℝ) (FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (SK : Set (EuclideanSpace ℝ (Fin K)))
    (t : Fin m → ℝ → ℝ) (I : Fin m → Set ℝ),
    0 < θ → θ < 1 → Measurable FK → MeasurableSet SK → InjOn FK SK →
    mix θ P Q {x | headT x ∉ SK} = 0 →
    (∀ j, Measurable (t j)) → (∀ j, MeasurableSet (I j)) → (∀ j, InjOn (t j) (I j)) →
    (∀ j, mix θ P Q {x | x (Sum.inr j) ∉ I j} = 0) →
      (P.map (liftMap FK t) = Q.map (liftMap FK t) ↔ P = Q)

/-! #### `lem:T-stability` -/

/-- On the probability scale, `Υ#ν = Υ#μ_K` forces `ν = μ_K`. -/
def t_stability_push : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ),
    IsGauge g → ScaleHyp μ g → ∀ (ν : Measure E) [IsProbabilityMeasure ν],
      ν.map (ups μ g) = μ.map (ups μ g) → ν = μ

/-- "In particular": a gradient `G` whose law on the probability scale is that of the reference equals `F_K`
`P_K`-a.e. (`P_K ≪` Haar with finite second moment, bounded-moment reference). -/
def t_stability_eq : Prop :=
  ∀ (K : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin K))) [ρ.IsAddHaarMeasure]
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ] (g : EuclideanSpace ℝ (Fin K) → ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure P]
    (F G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsGauge g → ScaleHyp μ g → MemLp id 2 μ → P ≪ ρ → MemLp id 2 P →
    Measurable F → Measurable G → P.map F = μ → IsConvGradAE P F → IsConvGradAE P G →
    (P.map G).map (ups μ g) = μ.map (ups μ g) →
      G =ᵐ[P] F

/-! #### `prop:lift-select` -/

/-- A lift with monotone separable tails is `P_T`-a.e. the gradient of a convex function on `ℝ^T`. -/
def lift_grad_separable : Prop :=
  ∀ (K m : ℕ) (P : Measure (EuclideanSpace ℝ (Fin K ⊕ Fin m))) [IsProbabilityMeasure P]
    (φK : EuclideanSpace ℝ (Fin K) → ℝ) (FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (t : Fin m → ℝ → ℝ),
    ConvexOn ℝ univ φK → (∀ᵐ x ∂P, HasGradientAt φK (FK (headT x)) (headT x)) →
    (∀ j, Monotone (t j)) → (∀ j s, P {x | x (Sum.inr j) = s} = 0) →
      ∃ Φ : EuclideanSpace ℝ (Fin K ⊕ Fin m) → ℝ, ConvexOn ℝ univ Φ ∧
        ∀ᵐ x ∂P, HasGradientAt Φ (liftMap FK t x) x

/-- A lift with a full quadratic tail `x_⊥ ↦ Λ(x_⊥ − m)`, `Λ` positive, is `P_T`-a.e. the gradient of a convex
function on `ℝ^T`. -/
def lift_grad_quadratic : Prop :=
  ∀ (K m : ℕ) (P : Measure (EuclideanSpace ℝ (Fin K ⊕ Fin m))) [IsProbabilityMeasure P]
    (φK : EuclideanSpace ℝ (Fin K) → ℝ) (FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin m)),
    ConvexOn ℝ univ φK → (∀ᵐ x ∂P, HasGradientAt φK (FK (headT x)) (headT x)) → A.IsPositive →
      ∃ Φ : EuclideanSpace ℝ (Fin K ⊕ Fin m) → ℝ, ConvexOn ℝ univ Φ ∧
        ∀ᵐ x ∂P, HasGradientAt Φ (liftQuad FK A c x) x

/-! #### `prop:estimated-basis` -/

/-- (i) The centred cubic law is invariant under every coordinate reflection `J = diag(±1)`. -/
def ebasis_reflect : Prop :=
  ∀ (K : ℕ) (lam η : Fin K → ℝ), (∀ k, 0 < lam k) → (∀ k, η k = 1 ∨ η k = -1) →
    (cubeLaw lam).map (fun x k => η k * x k) = cubeLaw lam

/-- (iii) The cap: `‖η ê − e‖² ≤ 2` for unit vectors, `η = sign⟨ê, e⟩`. -/
def ebasis_cap : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e ê : H), ‖e‖ = 1 → ‖ê‖ = 1 →
    ‖signCoef ⟪ê, e⟫ • ê - e‖ ^ 2 ≤ 2

/-- (iii) `W_2(J#P̂_K, P_K)² ≤ E‖JΠ̂_KX − Π_KX‖² ≤ ‖Σ‖_op Σ_{k<K} min(2, 8‖Γ̂−Γ‖²/sep_k²)`, given Bosq's bound. -/
def ebasis_w2 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure H) [IsProbabilityMeasure P] (K : ℕ) (e ê : ℕ → H) (s δ : ℝ) (sep : ℕ → ℝ),
    (∀ k < K, ‖e k‖ = 1) → (∀ k < K, ‖ê k‖ = 1) → 0 ≤ s → 0 ≤ δ →
    (∀ v : H, ∫⁻ x, ENNReal.ofReal (⟪v, x⟫ ^ 2) ∂P ≤ ENNReal.ofReal (s * ‖v‖ ^ 2)) →
    (∀ k < K, 0 < sep k) →
    (∀ k < K, ‖signCoef ⟪ê k, e k⟫ • ê k - e k‖ ≤ 2 * √2 * δ / sep k) →
      let J : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) :=
        reflE fun k : Fin K => signCoef ⟪ê k, e k⟫
      w2sq (P.map fun x => J (truncK ê K x)) (P.map (truncK e K)) ≤
          ∫⁻ x, ‖J (truncK ê K x) - truncK e K x‖ₑ ^ 2 ∂P ∧
        ∫⁻ x, ‖J (truncK ê K x) - truncK e K x‖ₑ ^ 2 ∂P ≤
          ENNReal.ofReal (s * ∑ k : Fin K, min 2 (8 * δ ^ 2 / sep k ^ 2))

/-! #### `prop:rt-adaptive` -/

/-- (i) Under `H_0` (exchangeable pooled sample), with `B` iid uniform relabellings shared by all levels,
`P(p^ad ≤ α) ≤ α` for every `α` and every `B`. -/
def rt_adaptive_valid : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (N B L : ℕ) (T : Fin (L + 1) → (Fin N → X) → ℝ)
    (μ : Measure (Fin N → X)) [IsProbabilityMeasure μ] (α : ℝ),
    (∀ l, Measurable (T l)) → (∀ τ : Equiv.Perm (Fin N), μ.map (fun x => x ∘ ⇑τ) = μ) →
      (∀ g : Fin B → Equiv.Perm (Fin N), MeasurableSet {x | pAd T x g ≤ α}) ∧
      ((Nat.factorial N : ℝ≥0∞) ^ B)⁻¹ * ∑ g : Fin B → Equiv.Perm (Fin N), μ {x | pAd T x g ≤ α} ≤
        ENNReal.ofReal α

/-- (ii) With the full permutation distribution, `p^ad ≤ L · min_l p_l(σ_0)` (`L + 1` levels here). -/
def rt_adaptive_bound : Prop :=
  ∀ (X : Type) (N L : ℕ) (T : Fin (L + 1) → (Fin N → X) → ℝ) (x : Fin N → X),
    pAdFull T x ≤ (L + 1 : ℝ) * ⨅ l, pFull T x l 1

end Claims

end StatFormal.OTFD.Wave22a
