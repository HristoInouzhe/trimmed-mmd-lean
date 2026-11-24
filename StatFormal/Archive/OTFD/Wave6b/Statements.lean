import StatFormal.Archive.OTFDR.Statements
import StatFormal.Archive.OTFDR.Lift.Statements
import StatFormal.Archive.OTFD.Wave1.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# FROZEN STATEMENTS — otfd wave 6b: T `eq:sphereone` (`prop:sphere`), A `lem:app-empirical-wass`,
# R `thm:region-breakdown`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-T_tangent.md`, `otfd-A_sieves.md`,
`otfd-R_robustness.md`; paths below are under `otfd/papers/`):
* T `prop:sphere` / `eq:sphereone` (`T_tangent/supp_moved.tex:4-21`), proof `T_tangent/app_proofs.tex:310-315`;
  `eq:L` (`L_b`) and the reading of `L_b` as a Lipschitz constant (ranking note 6, `inventory/ranking/otfd-C-G-T.md:259`).
* A `lem:app-empirical-wass` (`A_sieves/supplement.tex:3838-3855`), proof `supplement.tex:3857-3885`.
* R `thm:region-breakdown` (`R_robustness/sections/s4_regions.tex:75-83`, proof `:85-93`), with `thm:entropic`
  (`s4_regions.tex:42-64`), `eq:mass` (`:28-31`), `eq:oos` (`s2_setting.tex:25-28`), `def:bp` (`s2_setting.tex:53-58`),
  `H_{t,D}`, `d^±` (`s2_setting.tex:62-71`), `β(A;ν)` (`s2_setting.tex:73`) and `prop:support` (`s4_regions.tex:5-11`).
Reuses the frozen `OTFDR/Statements.lean` (`piCond`, `Qhat`), `OTFDR/Lift/Statements.lean` (`Contam`, `Explodes`, `BP`)
and `OTFD/Wave1/Statements.lean` (`HtD`, `tukeyDepth`, `regionDepth`), imported, not copied; Tau Ceti's
`wassersteinEDist` (`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean:173`).

Covered:
* T: `sphereone` (`eq:sphereone`, every `d ≥ 1`, every base point and all tangent `v, w`, no norm restriction, no
  injectivity); `sphereone_so3` (the `SO(3)` sentence: the same bound for the bi-invariant metric normalised so that a
  rotation by `θ` is at distance `θ` from the identity). `sphereone` is literally "`L_b = 1`" in the Lipschitz reading.
* A: `empirical_wass` (first display, every `ℓ ≥ 1`); `empirical_wass_rate` (the choice `ℓ = ⌊n^{1/(K+4)}⌋`, constant
  `4(4K+1)`, every `n ≥ 1`); `empirical_wass_rate20` (constant `20(K+1)`); `rate_tendsto` ("in particular … `→ 0`
  whenever `2 log n/(K_n+4) − log(K_n+1) → ∞`"); `rate_littleO` (`K_n = o(log n/log log n)` gives that condition);
  `rate_sqrtlog` (`K_n = ⌊√log n⌋` is `o(log n/log log n)`).
* R: `region_bounded` (`ℓ < nβ⁺(A)` ⇒ `sup_{u∈A}‖Q̂(u)‖` bounded over `𝔠_ℓ(𝒵)`); `region_unbounded`
  (`ℓ > n inf_A d⁻` ⇒ unbounded); `betaPlus_eq` (`β⁺(A) = inf_{u∈A} d⁻(u;ν)` for **every** measure and compact `A`:
  the Dini step of the proof, sharpened); `region_bp_general` (`β⁻ ≤ BP ≤ β⁻ + 1/n`, `β⁻ := inf_A d⁻`, every `ν`);
  `region_bp` (the last sentence, region part: for absolutely continuous `ν`, `β(A;ν) ≤ BP ≤ β(A;ν) + 1/n`).

Not covered (declared):
* T: the follow-up sentences (`thm:tubes`(iii) turning the tangent radius into a cap; the remark on injectivity; the
  differential statement "transverse singular values `|2 sin(r/2)|/r ≤ 1`", which the metric bound does not need; the
  citation sentence). Spheres of radius `≠ 1` (they are in a separate item).
* A: nothing of the lemma; the measurability of `ω ↦ W₂²(ν̂_n(ω), ν)` (the expectation is a lower Lebesgue integral,
  see encodings).
* R: `thm:entropic` itself (estimate 8–12 d, **not certified**: `certify/targets.toml` has no target for it). It enters
  as two explicit hypotheses, `EntropicA` (the displacement bound of (a), at every `u₀`, `t > 0`, `D`, `ℓ`) and
  `EntropicB` (the conclusion of (b)), stated for the fitted map of the theorem (potentials selected by `fsel`,
  recomputed on every contaminated sample, satisfying `eq:mass`). Given them, `region_bounded`/`region_unbounded` are
  short; the real content here is `betaPlus_eq` and the breakdown-point bracket. The data-dependent temperature clause
  of `thm:entropic` (ε fixed here). The **band** half of the last sentence (needs the evaluation functionals `e(t)` to
  be bounded and to span `ℝ^K`, the remark after `def:bp`; with `e ≡ 0` the band never breaks down).
  Convexity of `A` (unused, review), so `region_bp` holds for every nonempty compact `A`.

Encodings (see card):
* T: `S^d ⊂ ℝ^{d+1} = EuclideanSpace ℝ (Fin (d+1))`, `d_{S^d}(y,z) = arccos⟨y,z⟩` (`sphDist`; `arccos` clamps outside
  `[−1,1]`, never reached on unit vectors), `Exp_x v = cos‖v‖ x + (sin‖v‖/‖v‖) v` (`sphExp`; at `v = 0` Lean's
  `sin 0/0 = 0` multiplies `v = 0`, so the value `x` is the true one: no junk). Tangent at `x`: `⟨x,v⟩ = 0`.
  `SO(3)` is `S³/±1` through unit quaternions `q ∈ ℝ⁴`: `d_{SO(3)}([p],[q]) = 2 arccos|⟨p,q⟩|` (the rotation angle of
  `R_p⁻¹R_q`), the tangent space at `[q]` is `q^⊥ ⊂ ℝ⁴` with the Euclidean norm (left translation identifies `ξ ∈ so(3)`
  with `q·(0,ξ)`, `‖q·(0,ξ)‖ = |ξ|`), and `Exp_{[q]} V = [Exp^{S³}_q(V/2)]` (`so3Exp`; the radius-2 sphere covers).
* A: `ℝ^K = EuclideanSpace ℝ (Fin K)`; "supported in a Euclidean ball of radius `M`" is `ν(closedBall c M) = 1` for some
  centre `c`; `n` iid draws are `X : Fin n → Ω → ℝ^K`, measurable, `iIndepFun`, each with law `ν`
  (`P.map (X i) = ν`); `ν̂_n = n⁻¹ Σ δ_{X_i}` (`empMeasure`); `W₂²` is Tau Ceti's `wassersteinEDist 2 ^ 2`
  (`ℝ≥0∞`-valued, an infimum over couplings, no attainment assumed); `E[·]` is the lower Lebesgue integral `∫⁻`, which
  equals the expectation for a measurable integrand (here `ω ↦ W₂(ν̂(X(ω)), ν)` is continuous in `(X₁,…,X_n)`, hence
  measurable, so `∫⁻` is exactly `E`; for a non-measurable integrand it would sit below the outer expectation); right-hand sides are `ENNReal.ofReal` of nonnegative reals. `n ≥ 1` (for `n = 0` the empirical
  measure is `0` and `√(ℓ^K/0) = 0` would be junk), `ℓ ≥ 1` as printed. Rates: `n^{−2/(K+4)}` is `Real.rpow`
  (`n ≥ 1`); limits are along `n → ∞` in `ℕ`, `K_n : ℕ → ℕ`; `o(·)` is Mathlib's `=o[atTop]` (`log log n` is junk only at
  finitely many `n`, irrelevant for `atTop`).
* R: `ℝ^K = EuclideanSpace ℝ (Fin K)`, `K ≥ 1` (for `K = 0` there is no unit vector and every infimum over `‖e‖ = 1`
  is `⊤`); measures and depths are `ℝ≥0∞` (`⨅` exact); `d⁻(u;ν) = inf_{‖e‖=1} ν{⟨u'−u,e⟩ > 0}` (`dMinus`);
  `δ_{t,D}(u) = inf_{‖e‖=1} ν(H_{t,D}(e))` with the frozen `HtD u t D e` centred at `u` (`halfMass`);
  `β⁺(A) = sup_{t>0, D∈ℝ} inf_{u∈A} δ_{t,D}(u)` (`betaPlus`; `D < 0` gives empty sets, harmless in a sup). The fitted map
  on a sample `Z'` is the frozen `Qhat Z' (fsel Z') ε` (`eq:oos`), `fsel Z'` any potentials with `eq:mass`
  (`IsEntPot`, row masses `1/n`). `𝔠_ℓ(𝒵)` is the frozen `Contam`. In `EntropicA`, `B` is any bound on the unreplaced
  points `{j : Z'_j = Z_j}` (the bound is increasing in `B`, so this is equivalent to `B = max`), `δ = δ_{t,D}(u₀)`
  as a real (`toReal`, finite since `ν` is a probability and `K ≥ 1`), `κ = 1 − ℓ/(nδ)`. "Bounded over `𝔠_ℓ`" is
  `∃ M, ∀ Z' ∈ 𝔠_ℓ, ∀ u ∈ A, ‖Q̂_{Z'}(u)‖ ≤ M` (no `sup`). For `region_bp*` the region estimator is
  `regionSup = ⨆_{u∈A} ‖Q̂(u)‖` (a real `iSup`, bounded by `Σ‖Z'_i‖` since `Q̂` is a convex combination, `A ≠ ∅`:
  no junk), fed to the frozen `BP` (`def:bp`, with `BP = 1` if nothing explodes). "Absolutely continuous" is
  `ν ≪ volume` (Lebesgue = Haar measure of `EuclideanSpace`). "Up to `1/n`" is `β ≤ BP ≤ β + 1/n` (the
  bracket of `thm:entropic`). The standing hypothesis `∫‖u‖²dν < ∞` is kept (unused given `EntropicA/B`).
  `A ≠ ∅` is assumed in `region_unbounded` and `region_bp*` (for `A = ∅`, `n = 0`: `0 · ⊤ = 0 < ℓ` in `ℝ≥0∞`
  while no `u ∈ A` exists; the paper's regions have content `p > 0`).

Critic notes:
* T: the printed proof is a path-length argument; the route instead proves the global bound from the half-angle
  inequality `sin²(d/2) ≤ ‖v−w‖²/4` (exact identity of the ranking note plus `|sin a sin b| ≤ ab`), which alone only
  gives `d ≤ 2 arcsin(‖v−w‖/2)`, **not** `d ≤ ‖v−w‖`; the route upgrades it by subdividing the tangent segment and the
  angle triangle inequality (local error `O(r³)`). The ranking note's one-line derivation ("sin monotone on `[0,π/2]`")
  is therefore incomplete, but the statement is true for all `v, w` (no `‖v‖, ‖w‖ ≤ π` needed).
* A: the deterministic step bounds the unmatched cost by `4M² Σ_c (ν̂(c) − ν(c))₊`, which is `2M² Σ_c |ν̂(c) − ν(c)|`
  — the paper's constant; the printed lemma has slack `4M²` in front of `√(ℓ^K/n)` (the proof gives `2M²`). Not an error.
* R: `betaPlus_eq` shows `β⁺(A) = inf_A d⁻` for every Borel `ν` (not only absolutely continuous), so the theorem's
  two thresholds always coincide and the breakdown point of the region is `inf_A d⁻(·;ν)` up to `1/n` for every
  reference, e.g. an `m`-point design (`region_bp_general`); absolute continuity is only needed for `d⁻ = TD`.
* R: `region_bounded`/`region_unbounded` are conditional on `thm:entropic`, which is unverified.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. `EntropicA`/`EntropicB` are exactly `thm:entropic`(a),(b) (not stronger), and
  both follow from `EntSetting` (mass argument for (a); odds bound + mass equation for (b)), so they can later be
  discharged once `thm:entropic` is formalised. The band half of `thm:region-breakdown` is a coverage gap, not a
  paper defect (in the setting `e(t)` are values of `K` continuous linearly independent functions on compact `T`).
  `lem:app-empirical-wass` has slack: the proof gives `4M²K/ℓ² + 2M²√(ℓ^K/n)`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped InnerProductSpace ENNReal Topology

namespace StatFormal.OTFD.Wave6b

open StatFormal.OTFDR (piCond Qhat)
open StatFormal.OTFDR.Lift (Contam BP)
open StatFormal.OTFD.Wave1 (HtD regionDepth)
open TauCeti (wassersteinEDist)

/-! ### T `prop:sphere` -/

section Sphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Round-sphere distance `d(y,z) = arccos⟨y,z⟩` (for unit `y, z`). -/
def sphDist (y z : E) : ℝ := Real.arccos ⟪y, z⟫_ℝ

/-- `Exp_x v = cos‖v‖ x + (sin‖v‖/‖v‖) v`. -/
def sphExp (x v : E) : E := Real.cos ‖v‖ • x + (Real.sin ‖v‖ / ‖v‖) • v

/-- `SO(3)` distance of the rotations of unit quaternions `p, q`: `2 arccos|⟨p,q⟩|`. -/
def so3Dist (p q : EuclideanSpace ℝ (Fin 4)) : ℝ := 2 * Real.arccos |⟪p, q⟫_ℝ|

/-- `SO(3)` exponential at `[q]`: `[Exp^{S³}_q(V/2)]` (the radius-2 sphere covers `SO(3)`). -/
def so3Exp (q V : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := sphExp q ((1 / 2 : ℝ) • V)

end Sphere

/-! ### A `lem:app-empirical-wass` -/

/-- Empirical measure `ν̂_n = n⁻¹ Σ_i δ_{x_i}`. -/
def empMeasure {E : Type*} [MeasurableSpace E] {n : ℕ} (x : Fin n → E) : Measure E :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- The rate exponent function `2 log n/(K_n + 4) − log(K_n + 1)`. -/
def rateExponent (Kn : ℕ → ℕ) (n : ℕ) : ℝ :=
  2 * Real.log n / ((Kn n : ℝ) + 4) - Real.log ((Kn n : ℝ) + 1)

/-! ### R `thm:region-breakdown` -/

section Region
variable {K : ℕ}

/-- `d⁻(u₀;ν) = inf_{‖e‖=1} ν{u : ⟨u − u₀, e⟩ > 0}`. -/
def dMinus (ν : Measure (EuclideanSpace ℝ (Fin K))) (u₀ : EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  ⨅ (e : EuclideanSpace ℝ (Fin K)) (_ : ‖e‖ = 1), ν {u | 0 < ⟪u - u₀, e⟫_ℝ}

/-- `δ_{t,D}(u₀) = inf_{‖e‖=1} ν(H_{t,D}(e))`, `H` centred at `u₀`. -/
def halfMass (ν : Measure (EuclideanSpace ℝ (Fin K))) (u₀ : EuclideanSpace ℝ (Fin K)) (t D : ℝ) : ℝ≥0∞ :=
  ⨅ (e : EuclideanSpace ℝ (Fin K)) (_ : ‖e‖ = 1), ν (HtD u₀ t D e)

/-- `β⁺(A) = sup_{t>0, D} inf_{u∈A} inf_{‖e‖=1} ν(H_{t,D}(e))`. -/
def betaPlus (ν : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K))) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t) (D : ℝ), ⨅ u ∈ A, halfMass ν u t D

/-- `eq:mass`: `∫ π(i|u) ν(du) = 1/n` for every `i` (the potentials are entropic dual potentials). -/
def IsEntPot (ν : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin K))
    (f : Fin n → ℝ) : Prop :=
  ∀ i, ∫ u, piCond z f ε u i ∂ν = 1 / n

/-- The displacement bound of `thm:entropic`(a): `B + ℓ(DB + ε log(n/κ) + ε)/t`, `κ = 1 − ℓ/(nδ)`. -/
def entBound (n ℓ : ℕ) (t D B ε δ : ℝ) : ℝ :=
  B + ℓ * (D * B + ε * Real.log (n / (1 - ℓ / (n * δ))) + ε) / t

/-- Hypothesis: the conclusion of `thm:entropic`(a) (displacement) for the fitted map `Z' ↦ Qhat Z' (fsel Z') ε`. -/
def EntropicA (ν : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) {n : ℕ}
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) : Prop :=
  ∀ (ℓ : ℕ) (u₀ : EuclideanSpace ℝ (Fin K)) (t D : ℝ), 0 < t → (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal →
    ∀ Z' ∈ Contam Z ℓ, ∀ B : ℝ, (∀ j, Z' j = Z j → ‖Z' j‖ ≤ B) →
      ‖Qhat Z' (fsel Z') ε u₀‖ ≤ entBound n ℓ t D B ε (halfMass ν u₀ t D).toReal

/-- Hypothesis: the conclusion of `thm:entropic`(b): if `ℓ > n d⁻(u₀;ν)`, `‖Q̂(u₀)‖` is unbounded over `𝔠_ℓ(𝒵)`. -/
def EntropicB (ν : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) {n : ℕ}
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) : Prop :=
  ∀ (ℓ : ℕ) (u₀ : EuclideanSpace ℝ (Fin K)), (n : ℝ≥0∞) * dMinus ν u₀ < ℓ →
    ∀ M : ℝ, ∃ Z' ∈ Contam Z ℓ, M < ‖Qhat Z' (fsel Z') ε u₀‖

/-- The region estimator `Z' ↦ sup_{u∈A} ‖Q̂_{Z'}(u)‖`. -/
def regionSup (ε : ℝ) {n : ℕ} (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (A : Set (EuclideanSpace ℝ (Fin K))) (Z' : Fin n → EuclideanSpace ℝ (Fin K)) : ℝ :=
  ⨆ u : A, ‖Qhat Z' (fsel Z') ε u‖

/-- Standing hypotheses of `thm:entropic` (fixed `ε > 0`, `ν` with finite second moment, entropic potentials). -/
def EntSetting (ν : Measure (EuclideanSpace ℝ (Fin K))) (ε : ℝ) {n : ℕ}
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) : Prop :=
  0 < ε ∧ ∫⁻ u, ‖u‖ₑ ^ 2 ∂ν < ⊤ ∧ ∀ Z', IsEntPot ν ε Z' (fsel Z')

end Region

namespace Claims

/-! ### T -/

/-- T `eq:sphereone`: `d_{S^d}(Exp_x v, Exp_x w) ≤ ‖v − w‖` for every unit `x` and tangent `v, w`. -/
def sphereone : Prop :=
  ∀ (d : ℕ) (x v w : EuclideanSpace ℝ (Fin (d + 1))), ‖x‖ = 1 → ⟪x, v⟫_ℝ = 0 → ⟪x, w⟫_ℝ = 0 →
    sphDist (sphExp x v) (sphExp x w) ≤ ‖v - w‖

/-- T `prop:sphere`, `SO(3)` sentence: `d_{SO(3)}(Exp_{[q]} V, Exp_{[q]} W) ≤ ‖V − W‖`. -/
def sphereone_so3 : Prop :=
  ∀ q V W : EuclideanSpace ℝ (Fin 4), ‖q‖ = 1 → ⟪q, V⟫_ℝ = 0 → ⟪q, W⟫_ℝ = 0 →
    so3Dist (so3Exp q V) (so3Exp q W) ≤ ‖V - W‖

/-! ### A -/

/-- A `lem:app-empirical-wass`, first display: `E W₂²(ν̂_n, ν) ≤ 4M²(K/ℓ² + √(ℓ^K/n))` for every `ℓ ≥ 1`. -/
def empirical_wass : Prop :=
  ∀ (K n ℓ : ℕ) (M : ℝ) (c : EuclideanSpace ℝ (Fin K)) (ν : Measure (EuclideanSpace ℝ (Fin K)))
    [IsProbabilityMeasure ν] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin K)),
    1 ≤ n → 1 ≤ ℓ → ν (Metric.closedBall c M) = 1 → (∀ i, Measurable (X i)) → iIndepFun X P →
      (∀ i, P.map (X i) = ν) →
      ∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => X i ω) ν ^ 2 ∂P ≤
        ENNReal.ofReal (4 * M ^ 2 * (K / (ℓ : ℝ) ^ 2 + Real.sqrt ((ℓ : ℝ) ^ K / n)))

/-- A `lem:app-empirical-wass`, second display (`ℓ = ⌊n^{1/(K+4)}⌋`): `E W₂² ≤ 4(4K+1)M² n^{−2/(K+4)}`. -/
def empirical_wass_rate : Prop :=
  ∀ (K n : ℕ) (M : ℝ) (c : EuclideanSpace ℝ (Fin K)) (ν : Measure (EuclideanSpace ℝ (Fin K)))
    [IsProbabilityMeasure ν] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin K)),
    1 ≤ n → ν (Metric.closedBall c M) = 1 → (∀ i, Measurable (X i)) → iIndepFun X P →
      (∀ i, P.map (X i) = ν) →
      ∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => X i ω) ν ^ 2 ∂P ≤
        ENNReal.ofReal (4 * (4 * K + 1) * M ^ 2 * (n : ℝ) ^ (-(2 : ℝ) / (K + 4)))

/-- A `lem:app-empirical-wass`, second display, last bound: `E W₂² ≤ 20M²(K+1) n^{−2/(K+4)}`. -/
def empirical_wass_rate20 : Prop :=
  ∀ (K n : ℕ) (M : ℝ) (c : EuclideanSpace ℝ (Fin K)) (ν : Measure (EuclideanSpace ℝ (Fin K)))
    [IsProbabilityMeasure ν] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin K)),
    1 ≤ n → ν (Metric.closedBall c M) = 1 → (∀ i, Measurable (X i)) → iIndepFun X P →
      (∀ i, P.map (X i) = ν) →
      ∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => X i ω) ν ^ 2 ∂P ≤
        ENNReal.ofReal (20 * M ^ 2 * (K + 1) * (n : ℝ) ^ (-(2 : ℝ) / (K + 4)))

/-- A: `(K_n+1) n^{−2/(K_n+4)} → 0` whenever `2 log n/(K_n+4) − log(K_n+1) → ∞`. -/
def rate_tendsto : Prop :=
  ∀ Kn : ℕ → ℕ, Tendsto (rateExponent Kn) atTop atTop →
    Tendsto (fun n : ℕ => ((Kn n : ℝ) + 1) * (n : ℝ) ^ (-(2 : ℝ) / ((Kn n : ℝ) + 4))) atTop (𝓝 0)

/-- A: `K_n = o(log n/log log n)` implies `2 log n/(K_n+4) − log(K_n+1) → ∞`. -/
def rate_littleO : Prop :=
  ∀ Kn : ℕ → ℕ, (fun n : ℕ => (Kn n : ℝ)) =o[atTop] (fun n : ℕ => Real.log n / Real.log (Real.log n)) →
    Tendsto (rateExponent Kn) atTop atTop

/-- A: `K_n = ⌊√log n⌋` is `o(log n/log log n)`. -/
def rate_sqrtlog : Prop :=
  (fun n : ℕ => (⌊Real.sqrt (Real.log n)⌋₊ : ℝ)) =o[atTop] (fun n : ℕ => Real.log n / Real.log (Real.log n))

/-! ### R -/

/-- R `thm:region-breakdown`, first clause: if `ℓ < nβ⁺(A)`, `sup_{u∈A}‖Q̂(u)‖` is bounded over `𝔠_ℓ(𝒵)`
(conditional on `thm:entropic`(a)). -/
def region_bounded : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (ℓ : ℕ),
    0 < K → EntSetting ν ε fsel → EntropicA ν ε fsel Z → IsCompact A → (ℓ : ℝ≥0∞) < n * betaPlus ν A →
      ∃ M : ℝ, ∀ Z' ∈ Contam Z ℓ, ∀ u ∈ A, ‖Qhat Z' (fsel Z') ε u‖ ≤ M

/-- R `thm:region-breakdown`, second clause: if `ℓ > n inf_{u∈A} d⁻(u;ν)`, it is unbounded
(conditional on `thm:entropic`(b)). -/
def region_unbounded : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (ℓ : ℕ),
    0 < K → EntSetting ν ε fsel → EntropicB ν ε fsel Z → IsCompact A → A.Nonempty →
      (n : ℝ≥0∞) * (⨅ u ∈ A, dMinus ν u) < ℓ →
      ∀ M : ℝ, ∃ Z' ∈ Contam Z ℓ, ∃ u ∈ A, M < ‖Qhat Z' (fsel Z') ε u‖

/-- R, the Dini step, sharpened: `β⁺(A) = inf_{u∈A} d⁻(u;ν)` for every measure `ν` and compact `A`. -/
def betaPlus_eq : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K))),
    IsCompact A → betaPlus ν A = ⨅ u ∈ A, dMinus ν u

/-- R `thm:region-breakdown` for every reference: `β⁻ ≤ BP(region) ≤ β⁻ + 1/n`, `β⁻ = inf_A d⁻`. -/
def region_bp_general : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))),
    0 < K → 1 ≤ n → EntSetting ν ε fsel → EntropicA ν ε fsel Z → EntropicB ν ε fsel Z → IsCompact A →
      A.Nonempty →
      (⨅ u ∈ A, dMinus ν u).toReal ≤ BP (regionSup ε fsel A) Z ∧
        BP (regionSup ε fsel A) Z ≤ (⨅ u ∈ A, dMinus ν u).toReal + 1 / n

/-- R `thm:region-breakdown`, last sentence (region): for absolutely continuous `ν`, the breakdown point of the
fitted region is `β(A;ν)` up to `1/n`. -/
def region_bp : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))),
    0 < K → 1 ≤ n → ν ≪ volume → EntSetting ν ε fsel → EntropicA ν ε fsel Z → EntropicB ν ε fsel Z →
      IsCompact A → A.Nonempty →
      (regionDepth ν A).toReal ≤ BP (regionSup ε fsel A) Z ∧
        BP (regionSup ε fsel A) Z ≤ (regionDepth ν A).toReal + 1 / n

end Claims
end StatFormal.OTFD.Wave6b
