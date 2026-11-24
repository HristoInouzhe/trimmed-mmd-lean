import StatFormal.Archive.OTFD.Wave6b.Statements
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# FROZEN STATEMENTS — otfd wave 13a (QUEUE rows 111–112): A `thm:sieve-breakdown`,
# A `prop:ghs-iii-counterexample` (refutation of GHS, Bernoulli 2026, Thm. 3.1(iii), eq. (15))

Sources (current text after the 2026-10-14 corrections; paths under `research-lines/`):
* A `thm:sieve-breakdown` (`otfd/papers/A_sieves/supplement.tex:294-350`), proof `supplement.tex:704-786`;
  the frozen `def:bp` (R `s2_setting.tex:53-58`, as `OTFDR/Lift/Statements.lean` `BP`).
* A `prop:ghs-iii-counterexample` (`otfd/papers/A_sieves/supplement.tex:1114-1162`), proof `:1164-1244`, with
  `thm:app-ghs-stability` (`:1074-1107`, eq. `eq:app-uniform-subgradient`, `(⋆)`) and the remark "Where GHS's
  argument breaks" (`:1246-1250`).
* GHS = González-Sanz, Hallin, Sen, "Monotone measure-transportation maps in Hilbert spaces", Bernoulli 32(2) (2026);
  text `ot-functional-depth-and-quantile/review_work/ghs_source.txt` (PDF
  `ot-functional-depth-and-quantile/important_reference_papers/GonzalezSanz-Hallin-Sen-2026-Bernoulli.pdf`):
  Thm. 3.1 (`ghs_source.txt:599-622`, journal pp. 1224–1225), Def. 2.3(ii) of `𝒫^ℓ(ℋ)` (`:340-346`), "strongly
  compact" (`:594-597`), the uniform subgradient bound used "by assumption" in the proof (`:879-895`, p. 1228).
  **Verbatim GHS Thm. 3.1** (ℋ a separable Hilbert space, `ghs_source.txt:593`): "Let {P_n} and {Q_n} ⊆ 𝒫(ℋ) be two
  sequences of probability measures such that P_n →w P ∈ 𝒫^ℓ(ℋ) and Q_n →w Q ∈ 𝒫(ℋ). Assume that supp(Q) and
  supp(Q_n) both are subsets of the ball ℬ(0, M) for all n ∈ ℕ and some M > 0. Let γ_n ∈ Π(P_n, Q_n) be such that
  supp(γ_n) ⊆ ∂ψ_n for some proper l.s.c. convex function ψ_n, and let ψ be a proper l.s.c. convex function such
  that ∇ψ#P = Q. Then, […] (iii) if supp(Q) is strongly compact or dim(ℋ) is finite,
  sup_{(x,y)∈∂ψ_n, x∈K} ‖y − ∇ψ(x)‖ → 0 (15) for any strongly compact set K ⊆ int(dom(∇ψ)) ∩ int(supp(P))."
Reuses the frozen `OTFDR/Lift/Statements.lean` (`Contam`, `BP`), `OTFD/Wave1/Statements.lean` (`tukeyDepth`,
`truncK`, `IsLipHyp`) and `OTFD/Wave6b/Statements.lean` (`empMeasure`), imported, not copied.

Covered:
* `thm:sieve-breakdown`: `sieve_breakdown` (eq. `pointwise-breakdown`: `BP(q^H_{j,n}) = TD⁻(u_j;Q_n) + 1/n ∈
  [TD − (K_n−1)/n, TD]`, every `n`, under the stated hypotheses); `sieve_bp_exact_general` (the equality alone, for
  **every** grid and sample, `K ≥ 1`, `n ≥ 1`: no general position, distinctness or `K ≤ n`); `sieve_bp_limit`
  ("consequently … `BP → τ`"); `coherent_tukey_limit` (`eq:app-coherent-tukey-limit`,
  `TD(Π_Ku;Π_K#μ) ↓ TD_H(u;μ)`); `sieve_bp_coherent` (`eq:coherent-breakdown-limit`).
* `prop:ghs-iii-counterexample`: `ghs_iii_false` (GHS Thm. 3.1(iii) as published is false); the charitable
  reading `ghs_iii_false_charitable` (also false) and `ghs_literal_imp_charitable` (the literal statement implies
  the charitable one, so the second refutation is the stronger); `ghs_counterexample` (parts (a), (b): for **every**
  probability `P ∈ 𝒫^ℓ(ℓ²)` with full support, the paper's `ψ`, `ψ_n = max{ψ, x_n}` with `P_n = P`, `K₀ = {0}`, `M = 1`
  satisfy every hypothesis of GHS Thm. 3.1 and (iii), plus the uniform subgradient bound and strong compactness of
  every `supp Q_n`, while `(0, e_n) ∈ supp γ_n`, `∇ψ(0) = 0`); `exists_pell_full_support` (such a `P` exists).
  `psi_frechet` (part (a): `0 ≤ ψ(x+h) − ψ(x) − ⟨∇ψ(x),h⟩ ≤ ¼‖h‖²`, so `ψ` is Fréchet differentiable everywhere).
  `ghs_K1_clause` (part (c), last sentence: `ψ_n` is differentiable at `e_n/n` with gradient `e_n`, and
  `‖e_n − ∇ψ(e_n/n)‖ ≥ ½`).

Not covered (declared):
* `thm:sieve-breakdown`: the last sentence (iid reference points from an absolutely continuous law are a.s. in general
  position: affine dependence of `K+1` points is Lebesgue-null); the remark after it.
* `prop:ghs-iii-counterexample`: the **Gaussian** law `P` of the proposition. `ghs_counterexample` takes any full-support
  `P ∈ 𝒫^ℓ(ℓ²)`; the refutation uses the law built in the route (a mixture of scaled translates of a random series
  along a dense sequence of directions), because `P_Gauss ∈ 𝒫^ℓ` is `lem:app-block-Pl` (QUEUE, 5–8 d, not formalised).
  The facts of (a) that are not GHS hypotheses: the tie set `T_n` is `P`-null (Lipschitz hypersurface), `G_n = ∇ψ_n`
  `P`-a.e., `Q_n → Q` in total variation (weak convergence is covered), `∇ψ` is `½`-Lipschitz. Part (c) except the
  `𝒦₁` clause: `∂ψ_n(0) = [0, e_n]`, the directional clause, failure of `(⋆)`, and the norm conclusion on compact
  `𝒦₀' ⊆ ℋ∖{0}`. GHS Thm. 3.1(i), (ii) and A's corrected `thm:app-ghs-stability`(ii) (L4).

Encodings (see card):
* Sieve: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `Π_K = truncK e K` (frozen, `x ↦ (⟨e_k,x⟩)_{k<K}`) with `e : ℕ → H` orthonormal
  ("fixed deterministic orthonormal projection"), `ι_K a = Σ_{k<K} a_k e_k` (`liftK`). General position: every affine
  hyperplane `{z : ⟨v,z⟩ = c}`, `v ≠ 0`, contains at most `K` grid points (`GenPos`). An optimal bijection `T_n` is a
  permutation `σ` minimising `Σ_j ‖u_j − Z_{σ j}‖²` (`IsOptBij`; `T_n(u_j) = Z_{σ j}`). The estimator is
  `X̃ ↦ sup_{σ optimal for Π X̃} ‖ι_K(Π X̃)_{σ j}‖_H` (`liftQNorm`; the paper: "the cited breakdown functional takes the
  supremum over the admissible optimal transports after contamination"), a real `iSup` over a finite nonempty type
  (an optimum always exists): no junk. `BP` is the frozen `def:bp` on samples of curves `X : Fin n → H` (replacement of
  curves, `H`-norm). `Q_n = n⁻¹Σδ_{u_j}` is the frozen `empMeasure`; `TD⁻(u;ν) = inf_{‖v‖=1} ν{⟨v,z−u⟩ < 0}`
  (`tdOpen`), `TD` the frozen `tukeyDepth` (`inf_{v≠0}`, equal to the sphere version by scaling), `ℝ≥0∞`-valued and
  finite (`toReal` exact) since `K ≥ 1`, `n ≥ 1`. Sequences are indexed so that the `n`-th sample has size `n+1`
  (`Fin 0` is empty, so `j : ∀ n, Fin n` would not exist); limits along `atTop`. `K_n/n → 0` is
  `K_n/(n+1) → 0`. The coherent part uses a Hilbert basis `b : HilbertBasis ℕ ℝ H` with `Π_K = truncK b K`, `μ` a
  Borel probability on `H`, `TD_H(u;μ) = inf_{v≠0} μ{⟨v,z−u⟩ ≤ 0}` (`tukeyDepthH`), "every nonzero linear projection of
  `Z − u` is atomless at zero" is `∀ v ≠ 0, μ{⟨v,z−u⟩ = 0} = 0`; `↓` is `Antitone` (from `K = 1`) plus `Tendsto`.
* GHS: ℋ ranges over all real separable (`SeparableSpace`) complete inner product spaces in `Type` with the Borel
  σ-algebra. Functions are `H → EReal`; "proper l.s.c. convex" (`ProperLscConvex`): never `⊥`, somewhere finite,
  `LowerSemicontinuous`, convex epigraph `{(x,t) : f x ≤ t}`. `∂f = {(x,y) : f x < ⊤, ∀ z, f x + ⟨y,z−x⟩ ≤ f z}`
  (`subdiff`, a subset of `H × H`, as GHS write `(x,y) ∈ ∂ψ_n`). `∇ψ` is the Gâteaux gradient (`IsGatGrad`: `f` finite
  near `x` and `(f(x+th)−f(x))/t → ⟨g,h⟩` for every `h`; GHS distinguish differentiability from Fréchet
  differentiability, `ghs_source.txt:681-684`), `dom(∇ψ) = gradDom ψ`. "`∇ψ#P = Q`" (`GradPushes`): some measurable `T`
  with `T(x) = ∇ψ(x)` for `P`-a.e. `x` (in particular `ψ` is `P`-a.e. differentiable) and `T#P = Q`. In (15) `∇ψ(x)` is
  any `g` with `IsGatGrad ψ x (g x)` on `K` (the gradient is unique). `→w` is convergence of `∫f` for every bounded
  continuous `f` (`WeakConv`); `𝒫^ℓ` is GHS's class (`InPell`: null on every frozen `IsLipHyp` set; no moment clause,
  unlike A's `PellClass`); `Π(P,Q)`: both marginals (`IsCoupling`); `supp` is Mathlib's `Measure.support`; `ℬ(0,M)` the
  closed ball; "strongly compact" is `IsCompact` (norm topology); `int` is `interior`. "`sup … → 0`" is
  `∀ ε > 0, eventually ∀ (x,y) ∈ ∂ψ_n with x ∈ K, ‖y − ∇ψ(x)‖ ≤ ε` (no real `sSup`: an unbounded set would give the
  junk `sSup = 0` and make the conclusion vacuous).
  **Literal reading** (`GHSThm31iii`): the hypotheses of Thm. 3.1 (`GHSSetting`) and of (iii) imply (15) for the
  given `ψ_n`. **Charitable reading** (`GHSThm31iiiCharitable`): additionally assume GHS's proof hypothesis
  `⋃_{n≥N₀} ⋃_{x∈K} ∂ψ_n(x) ⊆ ℬ(0,M)` ("which holds by assumption", p. 1228) and that every `supp Q_n` is strongly
  compact, and weaken (15) to the sup over `supp γ_n ⊆ ∂ψ_n` (which also covers the reading in which `ψ_n` is "some"
  function to be chosen: every admissible `ψ_n` has `supp γ_n ⊆ ∂ψ_n`). The counterexample: `ℋ = ℓ²(ℕ,ℝ)`
  (`ell2`, Borel), `e_n = lp.single 2 n 1`, `a_j = 2^{−(j+1)}` (Lean index `j` is the paper's `j+1`; `n` is the paper's
  `n+1`), `ψ(x) = Σ a_j(√(1+x_j²) − 1)` (`psiC`, a `tsum`; summable, see the route), `ψ_n(x) = max{ψ(x), x_n}`
  (`psiNC`); `Q, Q_n, γ_n` are existential in `ghs_counterexample` (determined by `P` and the gradients); `K₀ = {0}`.
  `e_n/n` of the `𝒦₁` clause is `e_n/(n+1)` in Lean indexing.

Critic notes:
* `thm:sieve-breakdown`: true as stated, and the equality `BP = TD⁻ + 1/n` holds for every grid (no general position,
  no distinctness, any `K ≥ 1`): with `m = n·TD⁻` attained at a unit `v`, shifting by `−Rv` the `m+1` sample points that
  a clean optimal `σ₀` matches to `{⟨v,u_k−u_j⟩ < 0} ∪ {j}` keeps `σ₀` optimal (the shift changes the cost of every `τ`
  by `2RΣ_{k∈τ⁻¹(I)}⟨u_k,v⟩` + const, minimised by those `m+1` grid points), so `‖T(u_j)‖ → ∞`; with `≤ m`
  replacements, monotonicity of every optimal `σ` and a uniform-in-direction margin bound `‖T(u_j)‖`. The cited
  equality case of GSAM Thm. 2.7 is not needed. General position is used only for `TD − (K−1)/n ≤ TD⁻ + 1/n`.
  Under a fixed (adversarial) selection of the optimal bijection instead of the supremum, the equality can fail when
  the grid is affinely dependent (`n = K = 3`, collinear grid, clean points with equal projections on the line; an
  informal check, not formalised), so the supremum convention of the paper matters.
* `prop:ghs-iii-counterexample`, route: `P` is built in `RoutePell.lean`; `P ∈ 𝒫^ℓ` uses only that one coordinate of
  the series is independent of the others and atomless, and that some dense direction is transversal to the given
  hypersurface. `Q_n → Q` weakly uses `P{0} = 0` (a hyperplane is a Lipschitz hypersurface), `x_n → 0` and `ψ > 0`
  off `0`.
* `prop:ghs-iii-counterexample`: confirmed — GHS Thm. 3.1(iii) is false as published, in the literal and in the
  charitable reading. The refutation needs `P ∈ 𝒫^ℓ(ℓ²)` with full support (proved for the route's law); the
  Gaussian law of the paper is only one instance. The counterexample does **not** refute the reading "`supp Q` and all
  `supp Q_n` lie in one common strongly compact set": that reading is not refuted, and is close to A's corrected `(⋆)`
  (`thm:app-ghs-stability`(ii)), which asks instead that the subgradients over `K₀` lie in a common compact set.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. The original GHS PDF (`ot-functional-depth-and-quantile/
  important_reference_papers/GonzalezSanz-Hallin-Sen-2026-Bernoulli.pdf`, pp. 1224–1225) was checked: the quoted
  Thm 3.1 matches word for word, and every hypothesis of Thm 3.1 and of (iii) is in `GHSSetting`/the Prop, each at least
  as strong as GHS's (the safe direction for a refutation). `gradDom` ⊆ GHS's `dom(∇ψ)` (their eq. (7): `∂ψ(x)` a
  singleton, `ghs_source.txt:276`), with equal interiors for proper l.s.c. convex `ψ`. GHS's `ℬ(0,M)` is closed in §3.1
  but open in the proof (p. 1228): equivalent since `M` is universally quantified (`M ↦ 2M`). The constructed law is
  in GHS's `𝒫^ℓ` (zero mass on Lipschitz hypersurfaces; no moment or Gaussian requirement). Residual risk: GHS's
  online supplement and any erratum are not available locally; their proof calls (iii) "a direct consequence" of (i)
  with no extra hypothesis. `ghs_K1_clause` shows failure at points of differentiability of `ψ_n`, but no claim refutes
  a reading restricted to such points. Sieve: BP as the sup over all optimal bijections is A's stated convention
  (supplement `:718–719`); the general equality (no general position, no `K ≤ n`) is a proved generalisation.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ENNReal Topology BoundedContinuousFunction

namespace StatFormal.OTFD.Wave13a

open StatFormal.OTFDR.Lift (Contam BP)
open StatFormal.OTFD.Wave1 (tukeyDepth truncK IsLipHyp)
open StatFormal.OTFD.Wave6b (empMeasure)

/-! ### A `thm:sieve-breakdown` -/

section Sieve
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `ι_K a = Σ_{k<K} a_k e_k`. -/
def liftK (e : ℕ → H) (K : ℕ) (a : EuclideanSpace ℝ (Fin K)) : H := ∑ k : Fin K, a k • e k

/-- `σ` is an optimal bijection (grid `u_j ↦ z_{σ j}`) for squared Euclidean cost. -/
def IsOptBij {K n : ℕ} (u z : Fin n → EuclideanSpace ℝ (Fin K)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), ∑ j, ‖u j - z (σ j)‖ ^ 2 ≤ ∑ j, ‖u j - z (τ j)‖ ^ 2

/-- The lifted quantile at `u_j` on a sample of curves `X`, measured in `H`-norm, worst case over the optimal
bijections: `sup_{σ optimal for Π_K X} ‖ι_K (Π_K X_{σ j})‖`. -/
def liftQNorm (e : ℕ → H) (K : ℕ) {n : ℕ} (u : Fin n → EuclideanSpace ℝ (Fin K)) (j : Fin n)
    (X : Fin n → H) : ℝ :=
  ⨆ σ : {σ : Equiv.Perm (Fin n) // IsOptBij u (fun i => truncK e K (X i)) σ},
    ‖liftK e K (truncK e K (X (σ.1 j)))‖

/-- General position: no affine hyperplane `{z : ⟨v,z⟩ = c}` (`v ≠ 0`) contains more than `K` grid points. -/
def GenPos {K n : ℕ} (u : Fin n → EuclideanSpace ℝ (Fin K)) : Prop :=
  ∀ (v : EuclideanSpace ℝ (Fin K)) (c : ℝ), v ≠ 0 → {j | ⟪v, u j⟫_ℝ = c}.ncard ≤ K

/-- Open-halfspace depth `TD⁻(u;ν) = inf_{‖v‖=1} ν{z : ⟨v, z − u⟩ < 0}`. -/
def tdOpen {K : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) (u : EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  ⨅ (v : EuclideanSpace ℝ (Fin K)) (_ : ‖v‖ = 1), ν {z | ⟪v, z - u⟫_ℝ < 0}

/-- Hilbert Tukey depth `TD_H(u;μ) = inf_{v≠0} μ{z : ⟨v, z − u⟩ ≤ 0}`. -/
def tukeyDepthH [MeasurableSpace H] (μ : Measure H) (u : H) : ℝ≥0∞ :=
  ⨅ (v : H) (_ : v ≠ 0), μ {z | ⟪v, z - u⟫_ℝ ≤ 0}

/-- The standing hypotheses of `thm:sieve-breakdown` at one `n`. -/
structure SieveSetting (e : ℕ → H) (K n : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin K)) (X : Fin n → H) :
    Prop where
  ortho : Orthonormal ℝ e
  one_le_K : 1 ≤ K
  K_le_n : K ≤ n
  u_inj : Function.Injective u
  genpos : GenPos u
  z_inj : Function.Injective fun i => truncK e K (X i)

end Sieve

/-! ### GHS Thm. 3.1(iii) and A `prop:ghs-iii-counterexample` -/

section GHS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proper, lower semicontinuous, convex `f : H → (−∞, ∞]`. -/
def ProperLscConvex (f : H → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧ (∀ x, f x ≠ ⊥) ∧ LowerSemicontinuous f ∧ Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}

/-- The subdifferential `∂f ⊆ H × H`: `(x,y) ∈ ∂f` iff `f x < ∞` and `f z ≥ f x + ⟨y, z − x⟩` for all `z`. -/
def subdiff (f : H → EReal) : Set (H × H) :=
  {p | f p.1 ≠ ⊤ ∧ ∀ z, f p.1 + ((⟪p.2, z - p.1⟫_ℝ : ℝ) : EReal) ≤ f z}

/-- `g` is the (Gâteaux) gradient of `f` at `x`: `f` is finite near `x` and
`(f(x+th) − f(x))/t → ⟨g, h⟩` as `t → 0`, for every `h`. -/
def IsGatGrad (f : H → EReal) (x g : H) : Prop :=
  (∀ᶠ y in 𝓝 x, f y ≠ ⊤ ∧ f y ≠ ⊥) ∧
    ∀ h : H, Tendsto (fun t : ℝ => ((f (x + t • h)).toReal - (f x).toReal) / t) (𝓝[≠] 0) (𝓝 ⟪g, h⟫_ℝ)

/-- `dom(∇f)`: the points where `f` has a gradient. -/
def gradDom (f : H → EReal) : Set H := {x | ∃ g, IsGatGrad f x g}

variable [MeasurableSpace H]

/-- Weak convergence `μ_n →w μ`: `∫ f dμ_n → ∫ f dμ` for every bounded continuous `f`. -/
def WeakConv (μs : ℕ → Measure H) (μ : Measure H) : Prop :=
  ∀ f : H →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μs n)) atTop (𝓝 (∫ x, f x ∂μ))

/-- GHS's `𝒫^ℓ(ℋ)` (Def. 2.3(ii)): `P` gives mass zero to every Lipschitz hypersurface. -/
def InPell (P : Measure H) : Prop := ∀ S : Set H, IsLipHyp S → P S = 0

/-- `γ ∈ Π(P, Q)`. -/
def IsCoupling (γ : Measure (H × H)) (P Q : Measure H) : Prop :=
  γ.map Prod.fst = P ∧ γ.map Prod.snd = Q

/-- `∇ψ#P = Q`: a measurable `T` equal to `∇ψ` `P`-almost everywhere pushes `P` to `Q`. -/
def GradPushes (ψ : H → EReal) (P Q : Measure H) : Prop :=
  ∃ T : H → H, Measurable T ∧ (∀ᵐ x ∂P, IsGatGrad ψ x (T x)) ∧ P.map T = Q

/-- The hypotheses of GHS Thm. 3.1 (before (i)–(iii)). -/
structure GHSSetting (P : Measure H) (Pn : ℕ → Measure H) (Q : Measure H) (Qn : ℕ → Measure H) (M : ℝ)
    (γ : ℕ → Measure (H × H)) (ψn : ℕ → H → EReal) (ψ : H → EReal) : Prop where
  prob_P : IsProbabilityMeasure P
  prob_Pn : ∀ n, IsProbabilityMeasure (Pn n)
  prob_Q : IsProbabilityMeasure Q
  prob_Qn : ∀ n, IsProbabilityMeasure (Qn n)
  weak_P : WeakConv Pn P
  pell : InPell P
  weak_Q : WeakConv Qn Q
  M_pos : 0 < M
  supp_Q : Q.support ⊆ Metric.closedBall 0 M
  supp_Qn : ∀ n, (Qn n).support ⊆ Metric.closedBall 0 M
  coupling : ∀ n, IsCoupling (γ n) (Pn n) (Qn n)
  convex_n : ∀ n, ProperLscConvex (ψn n)
  supp_γ : ∀ n, (γ n).support ⊆ subdiff (ψn n)
  convex : ProperLscConvex ψ
  push : GradPushes ψ P Q

/-- Conclusion (15) of GHS Thm. 3.1(iii) at `K`: `sup_{(x,y)∈∂ψ_n, x∈K} ‖y − ∇ψ(x)‖ → 0`. -/
def GHSConcl (ψn : ℕ → H → EReal) (ψ : H → EReal) (K : Set H) : Prop :=
  ∀ g : H → H, (∀ x ∈ K, IsGatGrad ψ x (g x)) →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p ∈ subdiff (ψn n), p.1 ∈ K → ‖p.2 - g p.1‖ ≤ ε

/-- The weaker conclusion over `supp γ_n ⊆ ∂ψ_n`: `sup_{(x,y)∈supp γ_n, x∈K} ‖y − ∇ψ(x)‖ → 0`. -/
def GHSConclSupp (γ : ℕ → Measure (H × H)) (ψ : H → EReal) (K : Set H) : Prop :=
  ∀ g : H → H, (∀ x ∈ K, IsGatGrad ψ x (g x)) →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p ∈ (γ n).support, p.1 ∈ K → ‖p.2 - g p.1‖ ≤ ε

/-- GHS's uniform subgradient bound (proof of Thm. 3.1, p. 1228): `⋃_{n≥N₀} ⋃_{x∈K} ∂ψ_n(x) ⊆ ℬ(0,M)`. -/
def UniformSubgradBound (ψn : ℕ → H → EReal) (K : Set H) (M : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ p ∈ subdiff (ψn n), p.1 ∈ K → ‖p.2‖ ≤ M

end GHS

/-- GHS Thm. 3.1(iii), literal reading. -/
def GHSThm31iii : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure H) (Pn : ℕ → Measure H) (Q : Measure H) (Qn : ℕ → Measure H) (M : ℝ)
    (γ : ℕ → Measure (H × H)) (ψn : ℕ → H → EReal) (ψ : H → EReal),
    GHSSetting P Pn Q Qn M γ ψn ψ → (IsCompact Q.support ∨ FiniteDimensional ℝ H) →
      ∀ K : Set H, IsCompact K → K ⊆ interior (gradDom ψ) ∩ interior P.support → GHSConcl ψn ψ K

/-- GHS Thm. 3.1(iii), charitable reading: with GHS's proof hypothesis (uniform subgradient bound), every `supp Q_n`
strongly compact, and the conclusion only over `supp γ_n`. -/
def GHSThm31iiiCharitable : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure H) (Pn : ℕ → Measure H) (Q : Measure H) (Qn : ℕ → Measure H) (M : ℝ)
    (γ : ℕ → Measure (H × H)) (ψn : ℕ → H → EReal) (ψ : H → EReal),
    GHSSetting P Pn Q Qn M γ ψn ψ → (IsCompact Q.support ∨ FiniteDimensional ℝ H) →
      (∀ n, IsCompact (Qn n).support) →
      ∀ K : Set H, IsCompact K → K ⊆ interior (gradDom ψ) ∩ interior P.support →
        UniformSubgradBound ψn K M → GHSConclSupp γ ψ K

/-! #### The counterexample space `ℓ²` -/

/-- `ℓ²(ℕ, ℝ)`. -/
abbrev ell2 : Type := lp (fun _ : ℕ => ℝ) 2

/-- The Borel σ-algebra on `ℓ²`. -/
instance : MeasurableSpace ell2 := borel ell2

instance : BorelSpace ell2 := ⟨rfl⟩

/-- `e_n`. -/
def basisVec (n : ℕ) : ell2 := lp.single 2 n (1 : ℝ)

/-- `a_j = 2^{−(j+1)}` (the paper's `a_{j+1}`). -/
def aw (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)

/-- `φ(t) = √(1+t²) − 1`. -/
def phi (t : ℝ) : ℝ := Real.sqrt (1 + t ^ 2) - 1

/-- `ψ(x) = Σ_j a_j φ(x_j)`. -/
def psiC (x : ell2) : ℝ := ∑' j, aw j * phi (x j)

/-- `ψ_n(x) = max{ψ(x), x_n}`. -/
def psiNC (n : ℕ) (x : ell2) : ℝ := max (psiC x) (x n)

namespace Claims

/-! ### A `thm:sieve-breakdown` -/

/-- A `thm:sieve-breakdown`, eq. `pointwise-breakdown`: `BP(q^H_{j,n}) = TD⁻(u_j;Q_n) + 1/n` and
`TD(u_j;Q_n) − (K−1)/n ≤ BP(q^H_{j,n}) ≤ TD(u_j;Q_n)`. -/
def sieve_breakdown : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K n : ℕ)
    (u : Fin n → EuclideanSpace ℝ (Fin K)) (X : Fin n → H) (j : Fin n),
    SieveSetting e K n u X →
      BP (liftQNorm e K u j) X = (tdOpen (empMeasure u) (u j)).toReal + 1 / n ∧
      (tukeyDepth (empMeasure u) (u j)).toReal - ((K : ℝ) - 1) / n ≤ BP (liftQNorm e K u j) X ∧
      BP (liftQNorm e K u j) X ≤ (tukeyDepth (empMeasure u) (u j)).toReal

/-- The equality `BP(q^H_{j,n}) = TD⁻(u_j;Q_n) + 1/n` for every grid and sample (generalisation). -/
def sieve_bp_exact_general : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K n : ℕ)
    (u : Fin n → EuclideanSpace ℝ (Fin K)) (X : Fin n → H) (j : Fin n),
    Orthonormal ℝ e → 1 ≤ K →
      BP (liftQNorm e K u j) X = (tdOpen (empMeasure u) (u j)).toReal + 1 / n

/-- A `thm:sieve-breakdown`, "consequently": if `TD(u_{j_n,n};Q_n) → τ` and `K_n/n → 0`, then `BP → τ`
(the `n`-th sample has size `n+1`). -/
def sieve_bp_limit : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → ℕ → H) (Kn : ℕ → ℕ)
    (u : ∀ n, Fin (n + 1) → EuclideanSpace ℝ (Fin (Kn n))) (X : ∀ n, Fin (n + 1) → H)
    (j : ∀ n, Fin (n + 1)) (τ : ℝ),
    (∀ n, SieveSetting (e n) (Kn n) (n + 1) (u n) (X n)) →
    Tendsto (fun n => (tukeyDepth (empMeasure (u n)) (u n (j n))).toReal) atTop (𝓝 τ) →
    Tendsto (fun n => (Kn n : ℝ) / (n + 1)) atTop (𝓝 0) →
      Tendsto (fun n => BP (liftQNorm (e n) (Kn n) (u n) (j n)) (X n)) atTop (𝓝 τ)

/-- A `thm:sieve-breakdown`, proof, eq. `app-coherent-tukey-limit`: `TD(Π_K u; Π_K#μ) ↓ TD_H(u;μ)`. -/
def coherent_tukey_limit : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (μ : Measure H) [IsProbabilityMeasure μ] (u : H),
    (∀ v : H, v ≠ 0 → μ {z | ⟪v, z - u⟫_ℝ = 0} = 0) →
      Antitone (fun K => tukeyDepth (μ.map (truncK b (K + 1))) (truncK b (K + 1) u)) ∧
      Tendsto (fun K => tukeyDepth (μ.map (truncK b K)) (truncK b K u)) atTop (𝓝 (tukeyDepthH μ u))

/-- A `thm:sieve-breakdown`, eq. `coherent-breakdown-limit`: under coherent depth approximation,
`BP(q^H_{j_n,n}) → TD_H(u;μ)`. -/
def sieve_bp_coherent : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (μ : Measure H) [IsProbabilityMeasure μ] (u : H)
    (Kn : ℕ → ℕ) (uu : ∀ n, Fin (n + 1) → EuclideanSpace ℝ (Fin (Kn n))) (X : ∀ n, Fin (n + 1) → H)
    (j : ∀ n, Fin (n + 1)),
    (∀ n, SieveSetting (⇑b) (Kn n) (n + 1) (uu n) (X n)) → Tendsto Kn atTop atTop →
    (∀ v : H, v ≠ 0 → μ {z | ⟪v, z - u⟫_ℝ = 0} = 0) →
    Tendsto (fun n => |(tukeyDepth (empMeasure (uu n)) (uu n (j n))).toReal -
        (tukeyDepth (μ.map (truncK b (Kn n))) (truncK b (Kn n) u)).toReal|) atTop (𝓝 0) →
    Tendsto (fun n => (Kn n : ℝ) / (n + 1)) atTop (𝓝 0) →
      Tendsto (fun n => BP (liftQNorm (⇑b) (Kn n) (uu n) (j n)) (X n)) atTop
        (𝓝 (tukeyDepthH μ u).toReal)

/-! ### GHS Thm. 3.1(iii) -/

/-- GHS Thm. 3.1(iii) (Bernoulli 32(2), 2026, p. 1225, eq. (15)) is false as published. -/
def ghs_iii_false : Prop := ¬ GHSThm31iii

/-- It is false in the charitable reading too. -/
def ghs_iii_false_charitable : Prop := ¬ GHSThm31iiiCharitable

/-- The literal reading implies the charitable one (so `ghs_iii_false_charitable` is the stronger refutation). -/
def ghs_literal_imp_charitable : Prop := GHSThm31iii → GHSThm31iiiCharitable

/-- A `prop:ghs-iii-counterexample` (a), (b) on `ℓ²`, for any full-support `P ∈ 𝒫^ℓ(ℓ²)`: with `P_n = P`, `M = 1`,
`K₀ = {0}`, the paper's `ψ` and `ψ_n`, every hypothesis of GHS Thm. 3.1 and of (iii) holds (with the uniform
subgradient bound and compact `supp Q_n`), `∇ψ(0) = 0`, and `(0, e_n) ∈ supp γ_n` for every `n`. -/
def ghs_counterexample : Prop :=
  ∀ P : Measure ell2, IsProbabilityMeasure P → InPell P → P.support = univ →
    ∃ (Q : Measure ell2) (Qn : ℕ → Measure ell2) (γ : ℕ → Measure (ell2 × ell2)),
      GHSSetting P (fun _ => P) Q Qn 1 γ (fun n x => ((psiNC n x : ℝ) : EReal)) (fun x => ((psiC x : ℝ) : EReal)) ∧
      IsCompact Q.support ∧ (∀ n, IsCompact (Qn n).support) ∧
      ({0} : Set ell2) ⊆ interior (gradDom fun x => ((psiC x : ℝ) : EReal)) ∩ interior P.support ∧
      UniformSubgradBound (fun n x => ((psiNC n x : ℝ) : EReal)) {0} 1 ∧
      IsGatGrad (fun x => ((psiC x : ℝ) : EReal)) 0 0 ∧
      ∀ n, ((0 : ell2), basisVec n) ∈ (γ n).support

/-- A full-support `P ∈ 𝒫^ℓ(ℓ²)` exists. -/
def exists_pell_full_support : Prop :=
  ∃ P : Measure ell2, IsProbabilityMeasure P ∧ InPell P ∧ P.support = univ

/-- A `prop:ghs-iii-counterexample` (a): `ψ` is Fréchet differentiable with
`0 ≤ ψ(x+h) − ψ(x) − ⟨∇ψ(x),h⟩ ≤ ¼‖h‖²`, `∇ψ(x)_j = a_j x_j/√(1+x_j²)`. -/
def psi_frechet : Prop :=
  ∃ D : ell2 → ell2, (∀ x j, D x j = aw j * (x j / Real.sqrt (1 + x j ^ 2))) ∧
    ∀ x h : ell2, 0 ≤ psiC (x + h) - psiC x - ⟪D x, h⟫_ℝ ∧
      psiC (x + h) - psiC x - ⟪D x, h⟫_ℝ ≤ ‖h‖ ^ 2 / 4

/-- A `prop:ghs-iii-counterexample` (c), `𝒦₁` clause: `ψ_n` is differentiable at `e_n/(n+1)` with gradient `e_n`,
and `‖∇ψ_n − ∇ψ‖ ≥ ½` there. -/
def ghs_K1_clause : Prop :=
  ∀ (n : ℕ) (g : ell2), IsGatGrad (fun x => ((psiC x : ℝ) : EReal)) ((1 / (n + 1 : ℝ)) • basisVec n) g →
    IsGatGrad (fun x => ((psiNC n x : ℝ) : EReal)) ((1 / (n + 1 : ℝ)) • basisVec n) (basisVec n) ∧
      1 / 2 ≤ ‖basisVec n - g‖

end Claims
end StatFormal.OTFD.Wave13a
