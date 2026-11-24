import StatFormal.Archive.ICL.Gibbs.Statements
import StatFormal.Archive.Wave12c.Statements
import StatFormal.Archive.Wave6a.Statements
import StatFormal.Archive.OTFD.Wave1.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# FROZEN STATEMENTS — wave 14a (QUEUE rows 116, 117, 120): ICL `prop:fixed-point`; robust equality JASA
# `thm:ep-cert0`; otfd B `lem:cal-blind`

Sources (verbatim in `lean-formalisation/inventory/extracted/context-distribution-icl.md`,
`robust-equality-jasa.md`, `otfd-B_bands.md`; current text after the 2026-10-13/14 corrections):
* ICL `prop:fixed-point` (`context-distribution-ICL/paper/v3/supp/theory.tex:9-19`, with the sentence before it
  `:6-7`: for `μ ≪ P₀`, `P₀` atomless, `Π_μ = μ^{⊗M}`), the risk `G_μ(z) = ∫ L(z; z_{1:M}) dΠ_μ` and the mean risk
  `𝒜(μ) = ∫ G_μ dP₀` (`sections/03_framework.tex:17-41`), `J = 𝒜 + λ_cov Φ + λ_KL KL(μ|P₀)`
  (`sections/04_selector.tex:38-41`), the frozen `prop:gibbs` (`ICL/Gibbs`) and the frozen `lem:cond-curvature`
  (`Wave12c`, `supp/proofs_conditional.tex:161-221`, `κ_M = binom(M,2)^{1/2}`).
* robust equality `thm:ep-cert0` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_eps.tex:64-97`, proof
  `:99-124`), with `def:ep-member` (`:40-55`: `B^ν_0(r) = {Q : Q(S_ν) = 1, W₂²(P̂,Q) ≤ r}`, the frozen `Wave6a`
  `epBall` at `ε = 0`) and the notation block (`:5-15`: `c(x,y) = |x−y|²`, `f_h(x₀,x) = (h(x) − h(x₀))²`,
  `Δ(h) = W₂(h#P̂₀, h#P̂₁)`).
* otfd B `lem:cal-blind` (`otfd/papers/B_bands/main.tex:988-996`, proof `supplement.tex:5875-5879`), with
  `Π_K x = (⟨x,e_1⟩, …, ⟨x,e_K⟩)` (`main.tex:408-413`, the frozen `OTFD/Wave1` `truncK`).
Reuses the frozen `ICL/Gibbs` (`gibbsObj`), `Wave12c` (`kappaM`), `Wave6a` (`epBall`),
`RobustEquality/Certificate` (`centre`, via `Wave6a`) and `OTFD/Wave1` (`truncK`) statements, imported, not copied;
Tau Ceti's `wassersteinEDist`. No `Foundations` library file is imported directly.

Covered:
* `prop:fixed-point`: `fixed_point_foc` (every minimizer `μ⋆` of `J` is a fixed point of the Gibbs map,
  `μ⋆ = P₀` tilted by `−(M/λ) c_{μ⋆}`, and `dμ⋆/dP₀ = e^{−(M/λ)c_{μ⋆}} / ∫ e^{−(M/λ)c_{μ⋆}} dP₀` `P₀`-a.e.);
  `fixed_point_unique` (the threshold of the review's rec. 3: for `0 ≤ L ≤ B_L` and `λ > κ_M B_L =
  B_L √(M(M−1)/2)` there is at most one minimizer).
* `thm:ep-cert0`: `ep_cert0_i` ((i)); `ep_cert0_iii` ((iii), the attained infimum `|w|² r_s`, under the segment
  hypothesis with `t*² ≥ r_s`), `ep_cert0_iii_general` ("in general `inf_λ T⁰_s ≤ |w|² r_s` as soon as
  `P̂_s(S) = 1`", as `T⁰_s(|w|²) = |w|² r_s`); `ep_cert0_iv` ((iv)); `ep_cert0_v_pointwise`, `ep_cert0_v` ((v), the
  per-anchor envelope and the certified value of `T⁰_s(λ)`); `ep_cert0_vi`, `ep_cert0_vi_grad` ((vi), with a
  Lipschitz constant, resp. a gradient bound, on the box); `ep_cert0_vii` ((vii): the finite formula, convexity,
  and "piecewise linear" as a finite maximum of affine functions).
* `lem:cal-blind`: `cal_blind_meas` (`φ ∘ Π_K` is `σ(Π_K)`-measurable for Borel `φ`), `cal_blind_eq` (equal
  values when `Π_K x = Π_K x'`, no hypothesis on `φ`); the hidden hypothesis: `cal_blind_meas_iff` (for an
  orthonormal `e`, `φ ∘ Π_K` is `σ(Π_K)`-measurable iff `φ` is Borel) and `cal_blind_meas_false` (for `K ≥ 1`
  some `[0,1]`-valued `φ` makes `φ ∘ Π_K` not `σ(Π_K)`-measurable).

Not covered (declared):
* `prop:fixed-point`: the **existence** of a minimizer (it needs weak compactness of `𝒫(𝒵)`, weak lower
  semicontinuity of `KL(·|P₀)` and weak continuity of `μ ↦ ∫ L d(P₀ ⊗ μ^{⊗M})`, none available in Mathlib/Tau
  Ceti in usable form; estimated 8–12 agent-days on its own); "for `M ≥ 2` the objective is not convex, and the
  fixed point need not be unique" (existential remarks; the uniqueness threshold is covered instead).
* `thm:ep-cert0`: (ii) (strong duality for finitely supported `P̂_s` and the two-point attaining kernel);
  "refining the cells drives the bound to the supremum" in (vi) (a convergence remark); the Status paragraph.
* `lem:cal-blind`: the identification of `D^geom_K`, `D^prob_K` of `def:depth-family` as functions of `Π_K x`
  (true by their definitions; not re-encoded), "no choice of reference law, … changes this" (a remark).

Encodings (to be checked by the critic):
* `prop:fixed-point`: `M = m + 1 ≥ 1`; the context loss is `L : 𝒵 → (Fin M → 𝒵) → ℝ`, `L z x = L(z; x_{1:M})`,
  jointly measurable for the product σ-algebra and bounded (`|L| ≤ B`); symmetry is `SymmCtx` (invariance under
  every permutation of the `M` context slots). `Π_μ = μ^{⊗M}` (`Measure.pi`) is built in (the sentence before the
  proposition: `μ ≪ P₀`, `P₀` atomless); atomlessness, compactness of `𝒵` and continuity of `L` serve only this
  identification and the existence part, and are dropped for the covered claims (generalisation: `𝒵` any
  measurable space, `P₀` any probability measure). `J(μ) = ∫ (∫ L(z;x) dμ^{⊗M}(x)) dP₀(z) + λ KL(μ|P₀).toReal`
  (`mfObj`), `KL` = Mathlib's `klDiv`; as in the frozen `prop:gibbs`, candidates are probability measures with
  `KL(μ|P₀) < ∞` (the paper's `J = +∞` otherwise; `{μ ≪ P₀}` with `J < ∞` is exactly this set), so `toReal`
  never meets `⊤`. `μ⋆` is a minimizer (`IsMFMinimizer`) if it is such a measure and `J(μ⋆) ≤ J(μ)` for all such
  `μ`. `c_μ(z') = ∫∫ L(z; z', z_{2:M}) dμ^{⊗(M−1)} dP₀(z)` (`cmu`, `z'` in slot `0` via `Fin.cons`).
  "`dμ⋆/dP₀ ∝ exp{−(M/λ)c_{μ⋆}}` `P₀`-a.s." is stated twice: as `μ⋆ = P₀.tilted (−(M/λ)c_{μ⋆})` and as the a.e.
  identity for `(μ⋆.rnDeriv P₀).toReal` with the explicit normaliser (no junk: `c_{μ⋆}` is bounded measurable, so
  `exp` is integrable and the normaliser is positive). Uniqueness: `0 ≤ L ≤ B_L` (the hypothesis of the frozen
  `lem:cond-curvature`; a loss with `|L| ≤ B` is shifted to `[0, 2B]` at the cost of a constant in `J`), `κ_M`
  the frozen `kappaM`, strict `λ > κ_M B_L`; symmetry is not needed.
* `thm:ep-cert0`: the anchors are labelled, `P̂_s = centre x_s` (frozen, ties allowed), `n_s ≥ 1`. In (i) the
  space is any Polish metric space `𝒦` with its Borel σ-algebra and `c = dist²` (the paper's compact
  `K ⊆ ℝ^d` with `c = |x−y|²` is a case — generalisation); `ν_s` any measure, `S_{ν_s} = ν_s.support` (Mathlib),
  and `Q_s ∈ B_s` is the frozen `epBall x_s ν_s 0 r_s` (`Q(S_ν) = 1`, `W₂²(P̂,Q) ≤ r` in `EReal`, Tau Ceti's
  `wassersteinEDist 2`); `B_s ≠ ∅` is witnessed by `Q_s`. `h` bounded measurable, `λ_s ≥ 0`. The squared form
  `sup W₂² ≤ (Δ + √T₀ + √T₁)²` is stated in the equivalent per-`Q` non-squared form in `ℝ≥0∞`, as the frozen
  `thm:certificate`. `T⁰_s(λ) = λ r_s + n_s⁻¹ Σ_i sup_{x ∈ S} [f_h(x_i,x) − λ c(x_i,x)]` (`T0`, `lagr`), the
  supremum a real `⨆` over the subtype `S`: in every claim `S` is nonempty and the family is bounded above (in (i)
  because `h` is bounded and `Q(S) = 1`; in (iii) because `S` is bounded; in (iv)–(v) by the hypotheses; in (vii)
  because `S` is finite), so the `⨆` is a genuine supremum. (iii)–(vii) are stated on `E = EuclideanSpace ℝ (Fin d)`
  for an arbitrary set `S` in place of `S_ν` (generalisation: covers `S_ν` and the closed `S` of `rem:ep-support`).
  (iii): `h(x) = ⟨w,x⟩ + b`, `w ≠ 0`, `r ≥ 0`, `S` bounded (the paper's `K` compact; "for instance `K = ℝ^d`"
  is outside the real encoding, see the critic notes), anchors in `S` (`P̂(S) = 1` for the labelled centre), and
  the segments `x_i + t w/|w|`, `0 ≤ t ≤ t*`, in `S` with `t* ≥ 0` and `t*² ≥ r` ("large enough that the budget can be spent
  on them"; only the `+` direction is required — generalisation). "`inf_λ T⁰ = |w|² r`" is "`T⁰(λ) ≥ |w|²r` for
  every `λ ≥ 0`, with equality at `λ = |w|²`" (an attained infimum, no `sInf`). (iv): `|h(x) − h(x_i)| ≤ L|x − x_i|`
  for `x ∈ S`, every anchor; anchors in `S`. (v): radii `δ : ℕ → ℝ` with `δ 0 = 0`, `δ j < δ (j+1)` for `j < J`,
  `J ≥ 1`, `|x − x₀| ≤ δ J` on `S` (for `δ_J ≥ max_S |x − x₀|`), increments `I j ≥ |h(x) − h(x₀)|` whenever
  `x ∈ S`, `|x − x₀| ≤ δ j`, `1 ≤ j ≤ J` (no `sSup`); `e_λ = max_{1≤j≤J}(I_j² − λδ_{j−1}²)` is a `⨆` over
  `Fin J` (`eShell`, nonempty finite: a genuine maximum). The pointwise form `∀ x ∈ S, f_h − λc ≤ e_λ` is the
  printed `sup_S ≤ e_λ` (`S ≠ ∅`). (vi): the box `C = ∏_k [a_k, b_k]` (`box`, `a ≤ b`), its `2^d` vertices
  `vert a b σ`, `σ : Fin d → Bool`, the maximum over vertices a `⨆` over a nonempty finite type,
  `diam(C)` is `Metric.diam` (bounded set, genuine), `dist(x₀,C)` is `Metric.infDist` (nonempty set, genuine); the
  bound is stated pointwise on `C` (equivalent to the printed `sup_C`). "`G_C` a certified bound on `|∇h|` on `C`"
  is encoded twice: `ep_cert0_vi` with `|h(y) − h(z)| ≤ G_C|y − z|` on `C` (what the proof uses), and
  `ep_cert0_vi_grad` with `HasFDerivWithinAt h (h' y) C y` and `‖h' y‖ ≤ G_C` on `C`. The hypothesis `C ⊆ S_ν` is
  not needed for the inequality and is dropped. (vii): `S = {y_1, …, y_m}` is `Set.range y`, `m ≥ 1`; convexity is
  `ConvexOn ℝ univ` (λ ≥ 0 is the domain of interest; the claim is on all of `ℝ`); "piecewise linear" is
  "`T⁰ = max_{k<N}(α_k λ + β_k)` for finitely many affine functions".
* `lem:cal-blind`: `H` any real inner-product space, `e : ℕ → H` (0-indexed basis functions), `Π_K = truncK e K`
  (frozen). `σ(Π_K)` is `MeasurableSpace.comap Π_K` of the Borel σ-algebra of `ℝ^K = EuclideanSpace ℝ (Fin K)`;
  "`σ(Π_K)`-measurable" is `Measurable[σ(Π_K)]` into the Borel `ℝ`. A depth is any `φ : ℝ^K → ℝ`. The refutation of
  the unconditional reading uses `e` orthonormal (the paper's basis), `K ≥ 1`, and a `φ` with values in `{0,1}`.

Critic notes:
* `prop:fixed-point`: the FOC is derived from the frozen `prop:gibbs` (i) applied to the linearised cost
  `M c_{μ⋆}`: along `μ_t = (1−t)μ⋆ + tν` (`ν` the Gibbs measure of `M c_{μ⋆}`), `𝒜(μ_t)` is a polynomial in `t`
  with derivative `M(∫ c_{μ⋆} dν − ∫ c_{μ⋆} dμ⋆)` at `0` (symmetry of `L`), and `KL(μ_t) ≤ (1−t)KL(μ⋆) + tKL(ν)`; so
  `μ⋆` minimises the linearised objective, which by uniqueness in `prop:gibbs` forces `μ⋆ = ν`. The printed "need
  not be unique" should cite the threshold: by the frozen `lem:cond-curvature` (`curv_chord`), `J` is strongly
  convex along segments when `λ > κ_M B_L = B_L √(M(M−1)/2)`, so the minimizer is unique (certified here).
  Existence is declared: the paper's proof outline (compactness of `𝒫(𝒵)` plus Donsker–Varadhan lsc of KL) is
  sound but its infrastructure is missing.
* `thm:ep-cert0`(iii): "for instance `K = ℝ^d`" is in tension with the standing hypotheses (`K` compact, `h`
  bounded — a non-constant linear `h` is unbounded on `ℝ^d`), and on an unbounded `S` the inner supremum is `+∞`
  for `λ < |w|²` (the printed identity still holds in `[0, ∞]`). The hidden condition `t*² ≥ r_s` (the queue note)
  is exactly "large enough that the budget can be spent on them": with `t*² < r_s` and `S` the union of the
  segments, `T⁰(0) = t*²|w|² < |w|² r_s`, so the hypothesis is needed. (i) holds with `λ_s ≥ 0` and any (possibly
  non-Euclidean) Polish `𝒦`. (vi) holds as printed for boxes; the J13 repair (box, not a general cell) is needed:
  the proof's "every point within `diam(C)/2` of a vertex" fails for the equilateral triangle, as the printed
  proof itself notes.
* `lem:cal-blind`: "`σ(Π_K)`-measurable" silently needs `φ` Borel (ranking note 5): since an orthonormal `Π_K` is
  surjective, `φ ∘ Π_K` is `σ(Π_K)`-measurable iff `φ` is Borel, and non-Borel `{0,1}`-valued `φ` exist (the
  Borel σ-algebra of `ℝ^K` has cardinality `𝔠 < 2^𝔠`). The value-equality claim needs nothing. Suggested fix:
  "every depth `x ↦ φ(Π_K x)` with `φ` Borel".
* Proof routes: `Wave14a/Route{FixedPoint,FixedPointFOC,EpCert0,EpCert0i,CalBlind}.lean`, all 15 claims, standard
  axioms `propext, Classical.choice, Quot.sound` only (the routes reuse the untrusted `Wave12c/RouteCurvature`,
  `ICL/Gibbs/Proofs`, `RobustEquality/Certificate/Proofs` and import `Foundations/Distances/TV` — routes only).
* Critic (2026-10-14): ACCEPT-WITH-NOTE. fixed-point: the generalisation is genuine (on the paper's set, `μ ≪ P₀`
  atomless gives `Π_μ = μ^{⊗M}`); `kappaM M = √(M(M−1)/2)`, the review's threshold; EXISTENCE is not covered. Paper:
  "for `M ≥ 2` the objective is not convex" is false (`L ≡ 0` gives `J = λ KL`; for `λ ≥ κ_M B_L` it is strongly convex
  along mixtures) — fix "need not be convex; for `λ > B_L√(M(M−1)/2)` the minimiser is unique" (DEFECTS #53).
  ep-cert0: every `⨆` is a genuine supremum; (iii)'s hypotheses are the paper's setting; (ii) declared. Paper: "for
  instance `K = ℝ^d`" contradicts compact `K` / bounded `h` (S4); "`t*` large enough" should read `t* ≥ √r_s`, and it is
  needed (`n = 1`, segment `S`) (S4) (DEFECTS #54). cal-blind: B has no standing Borel assumption on `φ` or the rank map,
  so `cal_blind_meas_false` is a fair refutation of "σ(Π_K)-measurable" (S3, DEFECTS #55); the value equality needs nothing.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set InformationTheory TauCeti
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave14a

/-! ### ICL `prop:fixed-point` -/

section FixedPoint

variable {𝒵 : Type*} [MeasurableSpace 𝒵]

/-- `J(μ) = ∫ G_μ dP₀ + λ KL(μ|P₀)`, `G_μ(z) = ∫ L(z; z_{1:M}) dμ^{⊗M}`, `M = m + 1`. -/
def mfObj {m : ℕ} (P0 : Measure 𝒵) (L : 𝒵 → (Fin (m + 1) → 𝒵) → ℝ) (lam : ℝ) (μ : Measure 𝒵) : ℝ :=
  ∫ z, (∫ x, L z x ∂(Measure.pi fun _ : Fin (m + 1) => μ)) ∂P0 + lam * (klDiv μ P0).toReal

/-- `c_μ(z') = ∫∫ L(z; z', z_{2:M}) dμ^{⊗(M−1)}(z_{2:M}) dP₀(z)`. -/
def cmu {m : ℕ} (P0 : Measure 𝒵) (L : 𝒵 → (Fin (m + 1) → 𝒵) → ℝ) (μ : Measure 𝒵) (z' : 𝒵) : ℝ :=
  ∫ z, (∫ y, L z (Fin.cons z' y) ∂(Measure.pi fun _ : Fin m => μ)) ∂P0

/-- `μ` minimizes `J` over the probability measures with `KL(·|P₀) < ∞`. -/
def IsMFMinimizer {m : ℕ} (P0 : Measure 𝒵) (L : 𝒵 → (Fin (m + 1) → 𝒵) → ℝ) (lam : ℝ)
    (μ : Measure 𝒵) : Prop :=
  IsProbabilityMeasure μ ∧ klDiv μ P0 ≠ ∞ ∧
    ∀ ν : Measure 𝒵, IsProbabilityMeasure ν → klDiv ν P0 ≠ ∞ → mfObj P0 L lam μ ≤ mfObj P0 L lam ν

/-- `L` is symmetric in the context slots. -/
def SymmCtx {m : ℕ} (L : 𝒵 → (Fin (m + 1) → 𝒵) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (m + 1))) (z : 𝒵) (x : Fin (m + 1) → 𝒵), L z (x ∘ σ) = L z x

end FixedPoint

/-! ### robust equality `thm:ep-cert0` -/

section EpCert0

variable {𝒦 : Type*} [MetricSpace 𝒦]

/-- `f_h(x₀,x) − λ c(x₀,x)` with `c = dist²`. -/
def lagr (h : 𝒦 → ℝ) (lam : ℝ) (x0 x : 𝒦) : ℝ := (h x - h x0) ^ 2 - lam * dist x x0 ^ 2

/-- `T⁰(λ) = λ r + n⁻¹ Σ_i sup_{x ∈ S} [f_h(x_i,x) − λ c(x_i,x)]`. -/
def T0 {n : ℕ} (x : Fin n → 𝒦) (S : Set 𝒦) (h : 𝒦 → ℝ) (r lam : ℝ) : ℝ :=
  lam * r + (n : ℝ)⁻¹ * ∑ i, ⨆ y : S, lagr h lam (x i) y

/-- The shell envelope `e_λ = max_{1≤j≤J} [I_j² − λ δ_{j−1}²]`. -/
def eShell (δ I : ℕ → ℝ) (lam : ℝ) (J : ℕ) : ℝ :=
  ⨆ j : Fin J, I (j + 1) ^ 2 - lam * δ j ^ 2

/-- The box `∏_k [a_k, b_k]` in `ℝ^d`. -/
def box {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ k, a k ≤ x k ∧ x k ≤ b k}

/-- The vertex of the box selecting `b_k` where `σ k` and `a_k` elsewhere. -/
def vert {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) (σ : Fin d → Bool) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun k => if σ k then b k else a k

end EpCert0

namespace Claims

/-! #### `prop:fixed-point` -/

/-- **`prop:fixed-point` (FOC)**: every minimizer `μ⋆` of `J` (over the probability measures with finite KL)
satisfies `dμ⋆/dP₀ ∝ exp{−(M/λ) c_{μ⋆}}` `P₀`-a.s. -/
def fixed_point_foc : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (m : ℕ)
    (L : 𝒵 → (Fin (m + 1) → 𝒵) → ℝ) (lam : ℝ),
    0 < lam → Measurable (Function.uncurry L) → (∃ B, ∀ z x, |L z x| ≤ B) → SymmCtx L →
    ∀ μ : Measure 𝒵, IsMFMinimizer P0 L lam μ →
      μ = P0.tilted (fun z' => -((m + 1 : ℝ) / lam) * cmu P0 L μ z') ∧
      ∀ᵐ z' ∂P0, (μ.rnDeriv P0 z').toReal =
        Real.exp (-((m + 1 : ℝ) / lam) * cmu P0 L μ z') /
          ∫ z'', Real.exp (-((m + 1 : ℝ) / lam) * cmu P0 L μ z'') ∂P0

/-- **`prop:fixed-point` (uniqueness threshold)**: for `0 ≤ L ≤ B_L` and `λ > κ_M B_L = B_L √(M(M−1)/2)`,
`J` has at most one minimizer. -/
def fixed_point_unique : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (m : ℕ)
    (L : 𝒵 → (Fin (m + 1) → 𝒵) → ℝ) (BL lam : ℝ),
    Measurable (Function.uncurry L) → (∀ z x, 0 ≤ L z x ∧ L z x ≤ BL) →
    StatFormal.Wave12c.kappaM (m + 1) * BL < lam →
    ∀ μ ν : Measure 𝒵, IsMFMinimizer P0 L lam μ → IsMFMinimizer P0 L lam ν → μ = ν

/-! #### `thm:ep-cert0` -/

/-- **`thm:ep-cert0` (i)**: for `Q_s ∈ B^{ν_s}_0(r_s)` and `λ₀, λ₁ ≥ 0`,
`W₂(h#Q₀, h#Q₁) ≤ Δ(h) + √T⁰₀(λ₀) + √T⁰₁(λ₁)`. -/
def ep_cert0_i : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] [MeasurableSpace 𝒦] [BorelSpace 𝒦] [SecondCountableTopology 𝒦]
    [CompleteSpace 𝒦] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → 𝒦) (x₁ : Fin n₁ → 𝒦) (ν₀ ν₁ : Measure 𝒦)
    (r₀ r₁ lam₀ lam₁ : ℝ) (h : 𝒦 → ℝ) (Q₀ Q₁ : Measure 𝒦),
    0 < n₀ → 0 < n₁ → Measurable h → (∃ H, ∀ z, |h z| ≤ H) → 0 ≤ lam₀ → 0 ≤ lam₁ →
    Q₀ ∈ StatFormal.Wave6a.epBall x₀ ν₀ 0 r₀ → Q₁ ∈ StatFormal.Wave6a.epBall x₁ ν₁ 0 r₁ →
      wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ≤
        wassersteinEDist 2 ((StatFormal.RobustEquality.Certificate.centre x₀).map h)
            ((StatFormal.RobustEquality.Certificate.centre x₁).map h) +
          ENNReal.ofReal √(T0 x₀ ν₀.support h r₀ lam₀) + ENNReal.ofReal √(T0 x₁ ν₁.support h r₁ lam₁)

/-- **`thm:ep-cert0` (iii), linear rules**: if the segments `x_i + t w/|w|`, `0 ≤ t ≤ t*`, lie in `S` and
`t*² ≥ r`, then `inf_{λ≥0} T⁰(λ) = |w|² r`, attained at `λ = |w|²`. -/
def ep_cert0_iii : Prop :=
  ∀ (d n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) (b r tstar : ℝ),
    0 < n → w ≠ 0 → 0 ≤ r → Bornology.IsBounded S → (∀ i, x i ∈ S) → 0 ≤ tstar → r ≤ tstar ^ 2 →
    (∀ i, ∀ t ∈ Icc 0 tstar, x i + (t / ‖w‖) • w ∈ S) →
      (∀ lam, 0 ≤ lam → ‖w‖ ^ 2 * r ≤ T0 x S (fun z => ⟪w, z⟫_ℝ + b) r lam) ∧
      T0 x S (fun z => ⟪w, z⟫_ℝ + b) r (‖w‖ ^ 2) = ‖w‖ ^ 2 * r

/-- **`thm:ep-cert0` (iii), general case**: if `P̂(S) = 1`, then `T⁰(|w|²) = |w|² r`, so
`inf_λ T⁰ ≤ |w|² r`. -/
def ep_cert0_iii_general : Prop :=
  ∀ (d n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) (b r : ℝ),
    0 < n → (∀ i, x i ∈ S) →
      T0 x S (fun z => ⟪w, z⟫_ℝ + b) r (‖w‖ ^ 2) = ‖w‖ ^ 2 * r

/-- **`thm:ep-cert0` (iv), Lipschitz rules**: `T⁰(L²) ≤ L² r`. -/
def ep_cert0_iv : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] (n : ℕ) (x : Fin n → 𝒦) (S : Set 𝒦) (h : 𝒦 → ℝ) (L r : ℝ),
    0 < n → (∀ i, x i ∈ S) → (∀ i, ∀ y ∈ S, |h y - h (x i)| ≤ L * dist y (x i)) →
      T0 x S h r (L ^ 2) ≤ L ^ 2 * r

/-- **`thm:ep-cert0` (v), per anchor**: `f_h(x₀,x) − λ c(x₀,x) ≤ e_λ(x₀)` for every `x ∈ S`. -/
def ep_cert0_v_pointwise : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] (S : Set 𝒦) (h : 𝒦 → ℝ) (x0 : 𝒦) (J : ℕ) (δ I : ℕ → ℝ) (lam : ℝ),
    1 ≤ J → δ 0 = 0 → (∀ j < J, δ j < δ (j + 1)) → (∀ y ∈ S, dist y x0 ≤ δ J) → 0 ≤ lam →
    (∀ j ∈ Finset.Icc 1 J, ∀ y ∈ S, dist y x0 ≤ δ j → |h y - h x0| ≤ I j) →
      ∀ y ∈ S, lagr h lam x0 y ≤ eShell δ I lam J

/-- **`thm:ep-cert0` (v)**: `T⁰(λ) ≤ λ r + n⁻¹ Σ_i e_λ(x_i)`. -/
def ep_cert0_v : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] (n : ℕ) (x : Fin n → 𝒦) (S : Set 𝒦) (h : 𝒦 → ℝ) (r : ℝ) (J : ℕ)
    (δ : ℕ → ℝ) (I : Fin n → ℕ → ℝ) (lam : ℝ),
    0 < n → S.Nonempty → 1 ≤ J → δ 0 = 0 → (∀ j < J, δ j < δ (j + 1)) →
    (∀ i, ∀ y ∈ S, dist y (x i) ≤ δ J) → 0 ≤ lam →
    (∀ i, ∀ j ∈ Finset.Icc 1 J, ∀ y ∈ S, dist y (x i) ≤ δ j → |h y - h (x i)| ≤ I i j) →
      T0 x S h r lam ≤ lam * r + (n : ℝ)⁻¹ * ∑ i, eShell δ (I i) lam J

/-- **`thm:ep-cert0` (vi), cells**: on a box `C` on which `h` is `G_C`-Lipschitz,
`f_h(x₀,·) − λ c(x₀,·) ≤ (max_v |h(v) − h(x₀)| + G_C diam(C)/2)² − λ dist²(x₀, C)`. -/
def ep_cert0_vi : Prop :=
  ∀ (d : ℕ) (a b x0 : EuclideanSpace ℝ (Fin d)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (G lam : ℝ),
    (∀ k, a k ≤ b k) → 0 ≤ lam → 0 ≤ G →
    (∀ y ∈ box a b, ∀ z ∈ box a b, |h y - h z| ≤ G * dist y z) →
      ∀ y ∈ box a b, lagr h lam x0 y ≤
        ((⨆ σ : Fin d → Bool, |h (vert a b σ) - h x0|) + G * Metric.diam (box a b) / 2) ^ 2 -
          lam * Metric.infDist x0 (box a b) ^ 2

/-- **`thm:ep-cert0` (vi)** with `G_C` a bound on the gradient of `h` on `C`. -/
def ep_cert0_vi_grad : Prop :=
  ∀ (d : ℕ) (a b x0 : EuclideanSpace ℝ (Fin d)) (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (h' : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (G lam : ℝ),
    (∀ k, a k ≤ b k) → 0 ≤ lam → 0 ≤ G →
    (∀ y ∈ box a b, HasFDerivWithinAt h (h' y) (box a b) y ∧ ‖h' y‖ ≤ G) →
      ∀ y ∈ box a b, lagr h lam x0 y ≤
        ((⨆ σ : Fin d → Bool, |h (vert a b σ) - h x0|) + G * Metric.diam (box a b) / 2) ^ 2 -
          lam * Metric.infDist x0 (box a b) ^ 2

/-- **`thm:ep-cert0` (vii), finite references**: for `S = {y_1, …, y_m}`,
`T⁰(λ) = λ r + n⁻¹ Σ_i max_j [f_h(x_i,y_j) − λ c(x_i,y_j)]`, convex and piecewise linear in `λ`. -/
def ep_cert0_vii : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] (n m : ℕ) (x : Fin n → 𝒦) (y : Fin m → 𝒦) (h : 𝒦 → ℝ) (r : ℝ),
    0 < n → 0 < m →
      (∀ lam, T0 x (Set.range y) h r lam = lam * r + (n : ℝ)⁻¹ * ∑ i, ⨆ j, lagr h lam (x i) (y j)) ∧
      ConvexOn ℝ univ (T0 x (Set.range y) h r) ∧
      ∃ (N : ℕ) (α β : Fin N → ℝ), 0 < N ∧ ∀ lam, T0 x (Set.range y) h r lam = ⨆ k, α k * lam + β k

/-! #### `lem:cal-blind` -/

/-- **`lem:cal-blind`**: a depth `x ↦ φ(Π_K x)` with `φ` Borel is `σ(Π_K)`-measurable. -/
def cal_blind_meas : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (φ : EuclideanSpace ℝ (Fin K) → ℝ), Measurable φ →
      Measurable[MeasurableSpace.comap (StatFormal.OTFD.Wave1.truncK e K) inferInstance]
        (φ ∘ StatFormal.OTFD.Wave1.truncK e K)

/-- **`lem:cal-blind`**: if `Π_K x = Π_K x'` then `φ(Π_K x) = φ(Π_K x')`, for every `φ`. -/
def cal_blind_eq : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (φ : EuclideanSpace ℝ (Fin K) → ℝ) (x x' : H),
    StatFormal.OTFD.Wave1.truncK e K x = StatFormal.OTFD.Wave1.truncK e K x' →
      φ (StatFormal.OTFD.Wave1.truncK e K x) = φ (StatFormal.OTFD.Wave1.truncK e K x')

/-- **`lem:cal-blind`, hidden hypothesis**: for an orthonormal basis, `φ ∘ Π_K` is `σ(Π_K)`-measurable iff `φ`
is Borel. -/
def cal_blind_meas_iff : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (φ : EuclideanSpace ℝ (Fin K) → ℝ), Orthonormal ℝ e →
      (Measurable[MeasurableSpace.comap (StatFormal.OTFD.Wave1.truncK e K) inferInstance]
        (φ ∘ StatFormal.OTFD.Wave1.truncK e K) ↔ Measurable φ)

/-- **`lem:cal-blind`, refutation of the unconditional reading**: for `K ≥ 1` some `[0,1]`-valued `φ` makes
`φ ∘ Π_K` not `σ(Π_K)`-measurable. -/
def cal_blind_meas_false : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ),
    Orthonormal ℝ e → 1 ≤ K →
      ∃ φ : EuclideanSpace ℝ (Fin K) → ℝ, (∀ u, φ u ∈ Icc (0 : ℝ) 1) ∧
        ¬ Measurable[MeasurableSpace.comap (StatFormal.OTFD.Wave1.truncK e K) inferInstance]
          (φ ∘ StatFormal.OTFD.Wave1.truncK e K)

end Claims
end StatFormal.Wave14a
