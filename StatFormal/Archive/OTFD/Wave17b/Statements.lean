import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.Wave13a.Statements
import StatFormal.Archive.OTFD.Wave14c.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# FROZEN STATEMENTS — otfd wave 17b (QUEUE rows 176–180): A `lem:app-chain-rule`, A `lem:app-tail`,
# A `lem:app-soft-potential`, R `lem:CMdual`, B `prop:vector-tube-containment`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-{A_sieves,R_robustness,B_bands}.md`;
current text after the 2026-10-13/14 corrections; paths under `otfd/papers/`):
* A `lem:app-chain-rule` (`A_sieves/supplement.tex:1340-1353`, proof `:1355-1385`), with `Π_K`, `ι_K`
  (`A_sieves/main.tex:592-599`: `ι_K z = Σ_{k≤K} z_k e_k`, `ι_K = Π_K^*`) and the stability hypothesis
  "`supp(γ_n) ⊆ ∂ψ_n` for some proper l.s.c. convex `ψ_n`" of `thm:app-ghs-stability` (frozen Wave 13a, `GHSSetting`).
* A `lem:app-tail` (`A_sieves/supplement.tex:1386-1399`, proof `:1401-1411`), with the cubic law
  `X_cub = Σ_k λ_k V_k e_k`, `V_k ~ Unif(−½,½)` and the ball law `X_ball = R ζ/‖ζ‖` (`A_sieves/main.tex:612-650`).
* A `lem:app-soft-potential` (`A_sieves/supplement.tex:3424-3466`, proof `:3468-3479`).
* R `lem:CMdual` (`R_robustness/sections/appendix_a.tex:32-38`, proof `:40-56`), with the CM norm `eq:CMnorm`
  (`:25-30`: `Σ` injective, positive, self-adjoint, trace class; `‖x‖_CM = ‖Σ^{-1/2}x‖` on `ran Σ^{1/2}`, else `+∞`).
* B `prop:vector-tube-containment` (`B_bands/supplement.tex:2818-2840`, proof `:2842-2853`), with the setup
  `eq:vector-band-reconstruction`, `𝒳_p`, `S_p(t)`, `H_p(t,v)` (`:2725-2762`) and the tube
  `eq:vector-directional-tube` (`:2800-2806`).
Reuses the frozen `OTFD/Wave1/Statements.lean` (`truncK`), `OTFD/Wave13a/Statements.lean` (`liftK`, `subdiff`,
`IsGatGrad`, `ProperLscConvex`, `GradPushes`, `IsCoupling`, `WeakConv`) and `OTFD/Wave14c/Statements.lean`
(`vecCurve`, `vecH`), imported, not copied; Tau Ceti's `wassersteinEDist`. No `StatFormal/Foundations` file is imported.

Covered:
* `lem:app-chain-rule`: `chain_convex` (`ψ_K = φ_K∘Π_K` is finite, continuous, convex, proper l.s.c.),
  `chain_subdiff` (exact identity `∂ψ_K(x) = ι_K(∂φ_K(Π_Kx))` at every `x`), `chain_grad` (a gradient of `φ_K` at
  `Π_Kx` lifts to the gradient `ι_K∇φ_K(Π_Kx)` of `ψ_K` at `x`), `chain_ae` (if `∇φ_K = G` `P_K`-a.e. and
  `G#P_K = μ_K`, then `∇ψ_K = ι_K∘G∘Π_K` `P`-a.e., it pushes `P` to `ι_K#μ_K`, and `(Id × ∇ψ_K)#P` is a coupling of
  `P` and `ι_K#μ_K` whose support lies in `∂ψ_K`).
* `lem:app-tail`: `tail_data` (`ρ_K(P) → 0` under a finite second moment), `tail_cubic` (`ρ_K(μ)² = Σ_{j>K} λ_j²/12`
  and `→ 0`), `tail_ball` (`ρ_K(μ)² ≤ E[‖ζ − ι_KΠ_Kζ‖²/‖ζ‖²] → 0`), both with a finite second moment of `μ`;
  `tail_wass` (`W₂(ι_K#P_K, P) ≤ ρ_K(P) → 0` and `ι_K#P_K ⇀ P`, for every law with a finite second moment, hence
  for `P` and for both references).
* `lem:app-soft-potential`: `soft_partition` (normalising constant finite, positive; `q_{ε,x}` a probability),
  `soft_grad` (`T_ε = ∇h_ε`), `soft_hess` (`DT_ε(x) = (2/ε)Cov_{q_{ε,x}}(U)`, i.e. `∇²h_ε`), `soft_monotone`,
  `soft_lipschitz` (`D²/(2ε)`), `soft_strong` (`2γ/ε`-strong monotonicity on a convex region under the covariance
  floor), `soft_grid` (the floor holds on compacts for a full-dimensional finite grid with positive weights),
  `soft_tilt` (the printed `(ν, g_ε)` objects are the `m`-objects for `m = e^{(g_ε − ‖u‖²)/ε}ν`).
* `lem:CMdual`: `cm_dual` (the duality, both cases, as one equality in `EReal`), `cm_norm_range` (the encoded CM norm is
  the printed one: `‖y‖` at `x = Σ^{1/2}y`, `+∞` exactly off `ran Σ^{1/2}`).
* `prop:vector-tube-containment`: (i) `tube_contain`, `tube_prob` (measurable event, probability `≥ p`),
  `tube_exclude`; (ii) `tube_least`, `tube_mono_dir`, `tube_mono_level`; (iii) `tube_hull`, `tube_hull_min`.

Not covered (declared):
* `lem:app-chain-rule`: the existence of `φ_K` (GHS/McCann in `ℝ^K`), its Lipschitz representative and the location
  of its subgradients in `ch(supp μ_K)` (`cor:app-ghs-lipschitz`); the `P_K`-a.e. differentiability of `φ_K` via
  Zajíček's theorem and `lem:app-pullback` — it enters as the hypothesis that a Borel `G` is a gradient of `φ_K`
  `P_K`-a.e. (which "`∇φ_K#P_K = μ_K`" presupposes).
* `lem:app-tail`: the independence of the `V_j` and the Gaussianity of `ζ`, and `R ~ Unif(0,1)` (only `R ∈ [0,1]`
  a.s.) are not used (generalisation); the infinite-dimensional series `X_cub` enters through its coordinates
  (`⟨e_j, X⟩ = λ_jV_j` a.s.); `P ∈ 𝒫^ℓ(H)` is used only through its second moment (generalisation).
* `lem:app-soft-potential`: an extended-valued `g_ε` (`−∞` off a set of positive `ν`-mass) is covered only through the
  `m`-form (arbitrary finite nonzero `m` concentrated on `Ω`); `soft_tilt` treats real-valued `g_ε`. "Differentiation
  under the integral is justified by domination" is a proof remark. The finite-grid constant is existential.
* `lem:CMdual`: the eigenbasis and the trace-class property are not used (generalisation: any positive injective `Σ`).
* `prop:vector-tube-containment`: compactness of `𝒯`, continuity of `𝔪`, `E` and membership in `C(𝒯;ℝ^d)` are not
  used (trajectories are arbitrary functions `𝒯 → ℝ^d`); `μ(A_p) = p` is weakened to `μ(A_p) ≥ p`.

Encodings:
* A: `H` a real inner-product space, `(e_k)` a family `ℕ → H` (orthonormal where needed; a `HilbertBasis ℕ ℝ H` for
  `lem:app-tail`), `Π_K = truncK e K : H → ℝ^K = EuclideanSpace ℝ (Fin K)` (frozen), `ι_K = liftK e K` (frozen).
  Convex potentials are real-valued (everywhere finite, as printed) and enter the frozen extended-real API through the
  coercion (`liftPot`); `∂` is the frozen `subdiff` (graph in `H × H`); gradients are the frozen Gâteaux `IsGatGrad`.
  "`∇ψ_K = ι_K∘∇φ_K∘Π_K` `P`-a.e." is: a.e., the gradients of `ψ_K` at `x` are exactly `{ι_K G(Π_Kx)}`.
  `(Id × ∇ψ_K)#P` is `P.map (x ↦ (x, ι_K G(Π_Kx)))` (measurable, so not junk); `supp` is Mathlib's `Measure.support`.
* A `lem:app-tail`: `ρ_K(P)² = ∫‖x − ι_KΠ_Kx‖²dP` (`truncErrSq`; finite second moment `∫⁻‖x‖ₑ² < ∞` is a
  hypothesis wherever used, so the integral is not the non-integrable junk `0`), `ρ_K = √ρ_K²` (`truncErr`). Indices
  are 0-based: the kept coordinates are `j < K`, so the paper's tail `j > K` is `j ≥ K`, `Σ' j, λ_{j+K}²/12`.
  `Unif(−½,½)` is `volume.restrict (Icc (−½) ½)`. Weak convergence is the frozen `WeakConv` (bounded continuous test
  functions); `W₂` is Tau Ceti's `wassersteinEDist 2` (an `ℝ≥0∞` infimum over couplings).
* A `lem:app-soft-potential`: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `m` stands for `e^{(g_ε(u) − ‖u‖²)/ε}ν(du)` (the
  common factor `e^{−‖x‖²/ε}` cancels as printed); `Z(x) = ∫ e^{2⟨x,u⟩/ε} dm`, `q_{ε,x} = Z(x)⁻¹ e^{2⟨x,u⟩/ε}·m`
  (`gibbs`), `h_ε = (ε/2) log Z`, `T_ε(x) = ∫ u dq_{ε,x}`. `Cov_q(U)y = ∫⟨y,u−T⟩(u−T) dq` (`softCov`),
  `yᵀCov_q(U)y = ∫⟨y,u−T⟩² dq` (`softVar`), so "`λ_min(Cov) ≥ γ`" is `γ‖y‖² ≤ softVar` for all `y`. The Hessian is
  stated as the Fréchet derivative of `T_ε = ∇h_ε`. Diameter: `Metric.diam Ω ≤ D` with `Ω` compact (so the diameter
  is not the unbounded-set junk `0`). The grid is `m = Σ_i a_i δ_{z_i}`, `a_i > 0` (`= ν_i e^{(g_i − ‖z_i‖²)/ε}`),
  `affineSpan (range z) = ⊤`.
* R `lem:CMdual`: `Σ^{1/2}` is encoded as a positive `S` with `S∘S = Σ` (the positive square root is unique, so this
  is `Σ^{1/2}`; a real Hilbert space has no CFC); `‖x‖_CM = ⨅_{S y = x} ‖y‖ ∈ EReal` (`cmNorm`: `+∞` off the range,
  `‖Σ^{-1/2}x‖` on it by injectivity); the supremum is `⨆_{v≠0} ⟨v,x⟩/‖Σ^{1/2}v‖` in `EReal`, where `‖Σ^{1/2}v‖ > 0`
  by injectivity (no `x/0` junk). `H` nontrivial (else the supremum is over `∅`, `= ⊥`) and complete (Riesz).
* B `prop:vector-tube-containment`: `ℝ^D = Fin D → ℝ`, outputs `Fin d → ℝ`, `vᵀy = v ⬝ᵥ y`; `x_u(t) = 𝔪(t) + E(t)Q̂(u)`
  (`vTraj`, from the frozen `vecCurve`), `H_p(t,v)` = frozen `vecH` (an `sSup`; bounded and attained because `A` is
  compact, nonempty and `Q̂` continuous on it — hypotheses wherever `H_p` is used); `𝕊^{d−1} = {v : v ⬝ᵥ v = 1}`
  (Euclidean unit sphere; the product topology on `Fin d → ℝ` is the Euclidean one), "`V` dense in `𝕊^{d−1}`" is
  `𝕊^{d−1} ⊆ closure V`; `T_{p,V}(t)` = `vTubeAt`, `B_{p,V}` = `vTube`. The fitted law of `U` is `μ` on `ℝ^D`, so
  `P(X ∈ B_{p,V}) = μ{u : x_u ∈ B_{p,V}}`; `Q̂` Borel. Nested regions `p ≤ p'` are `A ⊆ A'`.
* All claims quantify spaces over `Type` (universe 0), as elsewhere in the repo.

Critic notes:
* `lem:CMdual`: the extracted (older) statement omitted "`Σ` injective"; the current text puts it in the standing
  definition (`appendix_a.tex:25`). Without it the ratio is `x/0` at `v ∈ ker Σ` (undefined), so it is assumed.
* `lem:app-tail` (b): the stated bound only uses `ζ ≠ 0` a.s. and `0 ≤ R ≤ 1`; constants as printed (cubic `λ²/12`).
* `prop:vector-tube-containment` (iii) needs compactness of `S_p(t)` (closedness of its hull) — supplied by
  compact `A` and continuity of `Q̂` on `A`.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 26 TRUE, no paper defects. `chain_ae` is CONDITIONAL on Zajíček's
  theorem (a Borel `G` that is a Gâteaux gradient of `φ_K` `P_K`-a.e. with `G#P_K = μ_K`), exactly what the paper's
  hypothesis "`∇φ_K#P_K = μ_K`" presupposes; `chain_grad`/`chain_ae` hold even for non-orthonormal `e` (`ι_K = Π_K^*`).
  tail: only `E V_j² = 1/12`, `R ∈ [0,1]` are used (no independence/Gaussianity). soft-potential: `soft_tilt` makes the
  printed `(ν, g_ε)` objects an instance (real-valued `g_ε`; extended values via the general `m`-form). CMdual: trace
  class dropped (density of `ran S` suffices); `Σ` injective as in `appendix_a.tex:25`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave17b

open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave13a (liftK subdiff IsGatGrad ProperLscConvex GradPushes IsCoupling WeakConv)
open StatFormal.OTFD.Wave14c (vecCurve vecH)

/-! ### A `lem:app-chain-rule`, `lem:app-tail` -/

section Sieve
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `ψ_K = φ_K ∘ Π_K`, as an (everywhere finite) extended-real function on `H`. -/
def liftPot (e : ℕ → H) (K : ℕ) (φ : EuclideanSpace ℝ (Fin K) → ℝ) (x : H) : EReal :=
  ((φ (truncK e K x) : ℝ) : EReal)

/-- A real function on `ℝ^K` as an extended-real one. -/
def toE {K : ℕ} (φ : EuclideanSpace ℝ (Fin K) → ℝ) (z : EuclideanSpace ℝ (Fin K)) : EReal := ((φ z : ℝ) : EReal)

/-- The lifted gradient `x ↦ ι_K G(Π_K x)`. -/
def liftGrad (e : ℕ → H) (K : ℕ) (G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (x : H) : H :=
  liftK e K (G (truncK e K x))

/-- `ι_K Π_K x`. -/
def projK (e : ℕ → H) (K : ℕ) (x : H) : H := liftK e K (truncK e K x)

variable [MeasurableSpace H]

/-- `ρ_K(P)² = E‖X − ι_KΠ_KX‖²`, `X ~ P`. -/
def truncErrSq (e : ℕ → H) (K : ℕ) (P : Measure H) : ℝ := ∫ x, ‖x - projK e K x‖ ^ 2 ∂P

/-- `ρ_K(P)`. -/
def truncErr (e : ℕ → H) (K : ℕ) (P : Measure H) : ℝ := √(truncErrSq e K P)

end Sieve

/-! ### A `lem:app-soft-potential` -/

section Soft
variable {K : ℕ}

/-- The Gibbs factor `exp(2⟨x,u⟩/ε)`. -/
def gibbsW (ε : ℝ) (x u : EuclideanSpace ℝ (Fin K)) : ℝ := Real.exp (2 * ⟪x, u⟫_ℝ / ε)

/-- The normalising constant `Z(x) = ∫ exp(2⟨x,u⟩/ε) m(du)`. -/
def partZ (m : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) (x : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ∫ u, gibbsW ε x u ∂m

/-- `q_{ε,x}(du) = Z(x)⁻¹ exp(2⟨x,u⟩/ε) m(du)` (`eq:app-soft-conditional`). -/
def gibbs (m : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) (x : EuclideanSpace ℝ (Fin K)) :
    Measure (EuclideanSpace ℝ (Fin K)) :=
  ENNReal.ofReal (partZ m ε x)⁻¹ • m.withDensity fun u => ENNReal.ofReal (gibbsW ε x u)

/-- `h_ε(x) = (ε/2) log Z(x)` (`eq:app-soft-log-partition`). -/
def softH (m : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) (x : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ε / 2 * Real.log (partZ m ε x)

/-- `T_ε(x) = ∫ u q_{ε,x}(du)`. -/
def softT (m : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) (x : EuclideanSpace ℝ (Fin K)) :
    EuclideanSpace ℝ (Fin K) :=
  ∫ u, u ∂(gibbs m ε x)

/-- `Cov_{q_{ε,x}}(U) y = ∫ ⟨y, u − T_ε(x)⟩ (u − T_ε(x)) q_{ε,x}(du)`. -/
def softCov (m : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) (x y : EuclideanSpace ℝ (Fin K)) :
    EuclideanSpace ℝ (Fin K) :=
  ∫ u, ⟪y, u - softT m ε x⟫_ℝ • (u - softT m ε x) ∂(gibbs m ε x)

/-- `yᵀ Cov_{q_{ε,x}}(U) y = Var_{q_{ε,x}} ⟨y, U⟩`. -/
def softVar (m : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) (x y : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ∫ u, ⟪y, u - softT m ε x⟫_ℝ ^ 2 ∂(gibbs m ε x)

/-- The tilted reference `m(du) = exp((g(u) − ‖u‖²)/ε) ν(du)`. -/
def tilt (ν : Measure (EuclideanSpace ℝ (Fin K))) (g : EuclideanSpace ℝ (Fin K) → ℝ) (ε : ℝ) :
    Measure (EuclideanSpace ℝ (Fin K)) :=
  ν.withDensity fun u => ENNReal.ofReal (Real.exp ((g u - ‖u‖ ^ 2) / ε))

/-- The finite grid reference `Σ_i a_i δ_{z_i}`. -/
def gridMeas {n : ℕ} (a : Fin n → ℝ) (z : Fin n → EuclideanSpace ℝ (Fin K)) : Measure (EuclideanSpace ℝ (Fin K)) :=
  ∑ i, ENNReal.ofReal (a i) • Measure.dirac (z i)

end Soft

/-! ### R `lem:CMdual` -/

section CM
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `‖x‖_CM = ⨅_{Σ^{1/2}y = x} ‖y‖ ∈ [0,+∞]` (`+∞` off `ran Σ^{1/2}`). -/
def cmNorm (S : H →L[ℝ] H) (x : H) : EReal := ⨅ (y : H) (_ : S y = x), ((‖y‖ : ℝ) : EReal)

/-- `sup_{v ≠ 0} ⟨v,x⟩/‖Σ^{1/2}v‖ ∈ EReal`. -/
def cmSup (S : H →L[ℝ] H) (x : H) : EReal := ⨆ (v : H) (_ : v ≠ 0), ((⟪v, x⟫_ℝ / ‖S v‖ : ℝ) : EReal)

end CM

/-! ### B `prop:vector-tube-containment` -/

section Tube
variable {T : Type*} {d D : ℕ}

/-- The reconstructed trajectory `x_u(t) = 𝔪(t) + E(t)Q̂(u)`. -/
def vTraj (Q : (Fin D → ℝ) → Fin D → ℝ) (mo : T → Fin d → ℝ) (E : T → Matrix (Fin d) (Fin D) ℝ)
    (u : Fin D → ℝ) : T → Fin d → ℝ :=
  fun t => vecCurve (mo t) (E t) (Q u)

/-- `T_{p,V}(t) = ⋂_{v∈V} {y : vᵀy ≤ H_p(t,v)}`. -/
def vTubeAt (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (V : Set (Fin d → ℝ)) (t : T) : Set (Fin d → ℝ) :=
  {y | ∀ v ∈ V, v ⬝ᵥ y ≤ vecH Q A (mo t) (E t) v}

/-- `B_{p,V} = {x : x(t) ∈ T_{p,V}(t) ∀ t}`. -/
def vTube (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (V : Set (Fin d → ℝ)) : Set (T → Fin d → ℝ) :=
  {x | ∀ t, x t ∈ vTubeAt Q A mo E V t}

/-- The Euclidean unit sphere `𝕊^{d−1}`. -/
def unitSph (d : ℕ) : Set (Fin d → ℝ) := {v | v ⬝ᵥ v = 1}

end Tube

namespace Claims

/-! #### A `lem:app-chain-rule` -/

/-- `ψ_K = φ_K∘Π_K` is finite, continuous and convex on `H` (hence proper l.s.c. convex). -/
def chain_convex : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (φ : EuclideanSpace ℝ (Fin K) → ℝ), ConvexOn ℝ univ φ →
      ConvexOn ℝ univ (fun x => φ (truncK e K x)) ∧ Continuous (fun x => φ (truncK e K x)) ∧
        ProperLscConvex (liftPot e K φ)

/-- Exact subdifferential identity: `∂ψ_K(x) = ι_K(∂φ_K(Π_Kx))` for every `x ∈ H`. -/
def chain_subdiff : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (φ : EuclideanSpace ℝ (Fin K) → ℝ), Orthonormal ℝ e →
      ∀ x v : H, (x, v) ∈ subdiff (liftPot e K φ) ↔
        ∃ w, (truncK e K x, w) ∈ subdiff (toE φ) ∧ v = liftK e K w

/-- Chain rule at a point: if `g` is a gradient of `φ_K` at `Π_Kx`, then `ι_K g` is a gradient of `ψ_K` at `x`. -/
def chain_grad : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (φ : EuclideanSpace ℝ (Fin K) → ℝ) (x : H) (g : EuclideanSpace ℝ (Fin K)),
      IsGatGrad (toE φ) (truncK e K x) g → IsGatGrad (liftPot e K φ) x (liftK e K g)

/-- `P`-a.e. formula and the stability hypothesis: if a Borel `G` is a gradient of `φ_K` `P_K`-a.e. with
`G#P_K = μ_K`, then `P`-a.e. the gradients of `ψ_K` are exactly `ι_K G(Π_K x)`, this map pushes `P` to `ι_K#μ_K`,
and `(Id × ∇ψ_K)#P` couples `P` and `ι_K#μ_K` with support in `∂ψ_K`. -/
def chain_ae : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (e : ℕ → H) (K : ℕ) (φ : EuclideanSpace ℝ (Fin K) → ℝ)
    (P : Measure H) (μK : Measure (EuclideanSpace ℝ (Fin K)))
    (G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsProbabilityMeasure P → ConvexOn ℝ univ φ → Measurable G →
    (∀ᵐ z ∂(P.map (truncK e K)), IsGatGrad (toE φ) z (G z)) → (P.map (truncK e K)).map G = μK →
      Measurable (liftGrad e K G) ∧
      (∀ᵐ x ∂P, ∀ g : H, IsGatGrad (liftPot e K φ) x g ↔ g = liftGrad e K G x) ∧
      P.map (liftGrad e K G) = μK.map (liftK e K) ∧
      GradPushes (liftPot e K φ) P (μK.map (liftK e K)) ∧
      IsCoupling (P.map fun x => (x, liftGrad e K G x)) P (μK.map (liftK e K)) ∧
      (P.map fun x => (x, liftGrad e K G x)).support ⊆ subdiff (liftPot e K φ)

/-! #### A `lem:app-tail` -/

/-- `ρ_K(P) → 0` for every law with a finite second moment (in particular `P ∈ 𝒫^ℓ(H)`). -/
def tail_data : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ℕ ℝ H) (P : Measure H), IsFiniteMeasure P → ∫⁻ x, ‖x‖ₑ ^ 2 ∂P < ⊤ →
      Tendsto (fun K => truncErr b K P) atTop (𝓝 0)

/-- (a) Cubic law `X = Σ_j λ_jV_je_j`, `V_j ~ Unif(−½,½)`: `μ` has a finite second moment,
`ρ_K(μ)² = Σ_{j>K} λ_j²/12` (0-based: `Σ_j λ_{j+K}²/12`), and `ρ_K(μ) → 0`. -/
def tail_cubic : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ℕ ℝ H) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H),
    Summable (fun j => lam j ^ 2) → (∀ j, Measurable (V j)) →
    (∀ j, P.map (V j) = volume.restrict (Icc (-1 / 2 : ℝ) (1 / 2))) →
    Measurable X → (∀ᵐ ω ∂P, ∀ j, ⟪b j, X ω⟫_ℝ = lam j * V j ω) →
      ∫⁻ x, ‖x‖ₑ ^ 2 ∂(P.map X) < ⊤ ∧
      (∀ K, truncErrSq b K (P.map X) = ∑' j, lam (j + K) ^ 2 / 12) ∧
      Tendsto (fun K => truncErr b K (P.map X)) atTop (𝓝 0)

/-- (b) Ball law `X = Rζ/‖ζ‖` (`ζ ≠ 0` a.s., `R ∈ [0,1]`): `μ` has a finite second moment,
`ρ_K(μ)² ≤ E[‖ζ − ι_KΠ_Kζ‖²/‖ζ‖²]`, and the bound tends to `0`. -/
def tail_ball : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ℕ ℝ H) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ζ : Ω → H) (R : Ω → ℝ),
    Measurable ζ → Measurable R → (∀ᵐ ω ∂P, ζ ω ≠ 0) → (∀ᵐ ω ∂P, R ω ∈ Icc (0 : ℝ) 1) →
      ∫⁻ x, ‖x‖ₑ ^ 2 ∂(P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω) < ⊤ ∧
      (∀ K, truncErrSq b K (P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω) ≤
        ∫ ω, ‖ζ ω - projK b K (ζ ω)‖ ^ 2 / ‖ζ ω‖ ^ 2 ∂P) ∧
      Tendsto (fun K => ∫ ω, ‖ζ ω - projK b K (ζ ω)‖ ^ 2 / ‖ζ ω‖ ^ 2 ∂P) atTop (𝓝 0)

/-- `W₂(ι_K#P_K, P) ≤ ρ_K(P) → 0` and `ι_K#P_K ⇀ P`, for every law with a finite second moment (so for `P` and,
by `tail_cubic`/`tail_ball`, for both references). -/
def tail_wass : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (P : Measure H), IsProbabilityMeasure P →
    ∫⁻ x, ‖x‖ₑ ^ 2 ∂P < ⊤ →
      (∀ K, TauCeti.wassersteinEDist 2 (P.map (projK b K)) P ≤ ENNReal.ofReal (truncErr b K P)) ∧
      Tendsto (fun K => TauCeti.wassersteinEDist 2 (P.map (projK b K)) P) atTop (𝓝 0) ∧
      WeakConv (fun K => P.map (projK b K)) P

/-! #### A `lem:app-soft-potential` -/

/-- The normalising constant is finite and strictly positive, and `q_{ε,x}` is a probability, for every `x`. -/
def soft_partition : Prop :=
  ∀ (K : ℕ) (m : Measure (EuclideanSpace ℝ (Fin K))) (Ω : Set (EuclideanSpace ℝ (Fin K))) (ε : ℝ),
    0 < ε → IsFiniteMeasure m → m ≠ 0 → IsCompact Ω → m Ωᶜ = 0 → ∀ x,
      Integrable (gibbsW ε x) m ∧ 0 < partZ m ε x ∧ IsProbabilityMeasure (gibbs m ε x)

/-- `T_ε = ∇h_ε`. -/
def soft_grad : Prop :=
  ∀ (K : ℕ) (m : Measure (EuclideanSpace ℝ (Fin K))) (Ω : Set (EuclideanSpace ℝ (Fin K))) (ε : ℝ),
    0 < ε → IsFiniteMeasure m → m ≠ 0 → IsCompact Ω → m Ωᶜ = 0 → ∀ x,
      HasGradientAt (softH m ε) (softT m ε x) x

/-- `∇²h_ε(x) = DT_ε(x) = (2/ε) Cov_{q_{ε,x}}(U)`. -/
def soft_hess : Prop :=
  ∀ (K : ℕ) (m : Measure (EuclideanSpace ℝ (Fin K))) (Ω : Set (EuclideanSpace ℝ (Fin K))) (ε : ℝ),
    0 < ε → IsFiniteMeasure m → m ≠ 0 → IsCompact Ω → m Ωᶜ = 0 → ∀ x,
      ∃ L : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K), HasFDerivAt (softT m ε) L x ∧
        ∀ y, L y = (2 / ε) • softCov m ε x y

/-- `T_ε` is monotone. -/
def soft_monotone : Prop :=
  ∀ (K : ℕ) (m : Measure (EuclideanSpace ℝ (Fin K))) (Ω : Set (EuclideanSpace ℝ (Fin K))) (ε : ℝ),
    0 < ε → IsFiniteMeasure m → m ≠ 0 → IsCompact Ω → m Ωᶜ = 0 → ∀ x y,
      0 ≤ ⟪softT m ε x - softT m ε y, x - y⟫_ℝ

/-- `T_ε` is `D²/(2ε)`-Lipschitz when `diam Ω ≤ D`. -/
def soft_lipschitz : Prop :=
  ∀ (K : ℕ) (m : Measure (EuclideanSpace ℝ (Fin K))) (Ω : Set (EuclideanSpace ℝ (Fin K))) (ε D : ℝ),
    0 < ε → IsFiniteMeasure m → m ≠ 0 → IsCompact Ω → m Ωᶜ = 0 → Metric.diam Ω ≤ D → ∀ x y,
      ‖softT m ε x - softT m ε y‖ ≤ D ^ 2 / (2 * ε) * ‖x - y‖

/-- On a convex `𝒳`, `inf_{x∈𝒳} λ_min(Cov_{q_{ε,x}}(U)) ≥ γ > 0` gives `2γ/ε`-strong monotonicity. -/
def soft_strong : Prop :=
  ∀ (K : ℕ) (m : Measure (EuclideanSpace ℝ (Fin K))) (Ω : Set (EuclideanSpace ℝ (Fin K))) (ε γ : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin K))),
    0 < ε → IsFiniteMeasure m → m ≠ 0 → IsCompact Ω → m Ωᶜ = 0 → Convex ℝ X → 0 < γ →
    (∀ x ∈ X, ∀ y, γ * ‖y‖ ^ 2 ≤ softVar m ε x y) →
      ∀ x ∈ X, ∀ y ∈ X, 2 * γ / ε * ‖x - y‖ ^ 2 ≤ ⟪softT m ε x - softT m ε y, x - y⟫_ℝ

/-- Finite grid with full affine hull and positive weights: the covariance floor holds on every compact `𝒳`. -/
def soft_grid : Prop :=
  ∀ (K n : ℕ) (a : Fin n → ℝ) (z : Fin n → EuclideanSpace ℝ (Fin K)) (ε : ℝ) (X : Set (EuclideanSpace ℝ (Fin K))),
    0 < ε → (∀ i, 0 < a i) → affineSpan ℝ (range z) = ⊤ → IsCompact X →
      ∃ γ > 0, ∀ x ∈ X, ∀ y, γ * ‖y‖ ^ 2 ≤ softVar (gridMeas a z) ε x y

/-- The printed objects: for a finite `ν` on a compact `Ω` and a measurable `g_ε` bounded above on `Ω`, the tilted
`m` is finite, nonzero (if `ν` is), concentrated on `Ω`, its normalising constant is `∫ exp{[g − ‖u‖² + 2⟨x,u⟩]/ε} dν`
and `q_{ε,x}` is the printed Gibbs conditional. -/
def soft_tilt : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) (Ω : Set (EuclideanSpace ℝ (Fin K))) (ε : ℝ)
    (g : EuclideanSpace ℝ (Fin K) → ℝ),
    0 < ε → IsFiniteMeasure ν → IsCompact Ω → ν Ωᶜ = 0 → Measurable g → BddAbove (g '' Ω) →
      IsFiniteMeasure (tilt ν g ε) ∧ (ν ≠ 0 → tilt ν g ε ≠ 0) ∧ tilt ν g ε Ωᶜ = 0 ∧
      ∀ x, partZ (tilt ν g ε) ε x = ∫ u, Real.exp ((g u - ‖u‖ ^ 2 + 2 * ⟪x, u⟫_ℝ) / ε) ∂ν ∧
        gibbs (tilt ν g ε) ε x = ENNReal.ofReal (∫ u, Real.exp ((g u - ‖u‖ ^ 2 + 2 * ⟪x, u⟫_ℝ) / ε) ∂ν)⁻¹ •
          ν.withDensity fun u => ENNReal.ofReal (Real.exp ((g u - ‖u‖ ^ 2 + 2 * ⟪x, u⟫_ℝ) / ε))

/-! #### R `lem:CMdual` -/

/-- Cameron–Martin duality: `sup_{v≠0} ⟨v,x⟩/‖Σ^{1/2}v‖ = ‖x‖_CM` for every `x` (both sides `+∞` off `ran Σ^{1/2}`). -/
def cm_dual : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (Sig S : H →L[ℝ] H), Sig.IsPositive → S.IsPositive → S ∘L S = Sig → Function.Injective Sig →
      ∀ x : H, cmSup S x = cmNorm S x

/-- The encoded CM norm is the printed one: `‖Σ^{1/2}y‖_CM = ‖y‖`, and `‖x‖_CM = +∞` iff `x ∉ ran Σ^{1/2}`. -/
def cm_norm_range : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Sig S : H →L[ℝ] H), Sig.IsPositive → S.IsPositive → S ∘L S = Sig → Function.Injective Sig →
      (∀ y : H, cmNorm S (S y) = ((‖y‖ : ℝ) : EReal)) ∧ ∀ x : H, cmNorm S x = ⊤ ↔ x ∉ range S

/-! #### B `prop:vector-tube-containment` -/

/-- (i) `𝒳_p ⊆ B_{p,V}`. -/
def tube_contain : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (V : Set (Fin d → ℝ)),
    IsCompact A → A.Nonempty → ContinuousOn Q A →
      ∀ u ∈ A, vTraj Q mo E u ∈ vTube Q A mo E V

/-- (i) `P(X ∈ B_{p,V}) ≥ p` under the fitted law, as a measurable event. -/
def tube_prob : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (V : Set (Fin d → ℝ)) (μ : Measure (Fin D → ℝ)) (p : ℝ),
    IsCompact A → A.Nonempty → ContinuousOn Q A → Measurable Q → ENNReal.ofReal p ≤ μ A →
      MeasurableSet {u | vTraj Q mo E u ∈ vTube Q A mo E V} ∧
        ENNReal.ofReal p ≤ μ {u | vTraj Q mo E u ∈ vTube Q A mo E V}

/-- (i) One violated pair `(t,v)` excludes a curve from `𝒳_p`. -/
def tube_exclude : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (y : T → Fin d → ℝ) (t : T) (v : Fin d → ℝ),
    IsCompact A → A.Nonempty → ContinuousOn Q A → vecH Q A (mo t) (E t) v < v ⬝ᵥ y t →
      y ∉ vTraj Q mo E '' A

/-- (ii) `H_p(t,v)` is the smallest valid upper threshold at `(t,v)` for the values of `𝒳_p`. -/
def tube_least : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (t : T) (v : Fin d → ℝ),
    IsCompact A → A.Nonempty → ContinuousOn Q A →
      IsLeast {c : ℝ | ∀ u ∈ A, v ⬝ᵥ vTraj Q mo E u t ≤ c} (vecH Q A (mo t) (E t) v)

/-- (ii) More directions give smaller tubes. -/
def tube_mono_dir : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (V V' : Set (Fin d → ℝ)), V ⊆ V' →
      (∀ t, vTubeAt Q A mo E V' t ⊆ vTubeAt Q A mo E V t) ∧ vTube Q A mo E V' ⊆ vTube Q A mo E V

/-- (ii) Larger (nested) regions `A_p ⊆ A_{p'}` give larger tubes. -/
def tube_mono_level : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A A' : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (V : Set (Fin d → ℝ)),
    A ⊆ A' → IsCompact A' → A.Nonempty → ContinuousOn Q A' →
      (∀ t, vTubeAt Q A mo E V t ⊆ vTubeAt Q A' mo E V t) ∧ vTube Q A mo E V ⊆ vTube Q A' mo E V

/-- (iii) For `V = 𝕊^{d−1}` or any dense subset, `T_{p,V}(t) = conv S_p(t)`. -/
def tube_hull : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (V : Set (Fin d → ℝ)),
    IsCompact A → A.Nonempty → ContinuousOn Q A → V ⊆ unitSph d → unitSph d ⊆ closure V →
      ∀ t, vTubeAt Q A mo E V t = convexHull ℝ ((fun u => vTraj Q mo E u t) '' A)

/-- (iii) `conv S_p(t)` is the smallest closed convex set containing `S_p(t)`. -/
def tube_hull_min : Prop :=
  ∀ (T : Type) (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : T → Fin d → ℝ)
    (E : T → Matrix (Fin d) (Fin D) ℝ) (t : T),
    IsCompact A → ContinuousOn Q A →
      IsLeast {C : Set (Fin d → ℝ) | IsClosed C ∧ Convex ℝ C ∧ (fun u => vTraj Q mo E u t) '' A ⊆ C}
        (convexHull ℝ ((fun u => vTraj Q mo E u t) '' A))

end Claims
end StatFormal.OTFD.Wave17b
