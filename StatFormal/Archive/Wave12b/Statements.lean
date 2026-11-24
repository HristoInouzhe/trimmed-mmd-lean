import StatFormal.Archive.OTFDR.Statements
import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.Wave11a.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# FROZEN STATEMENTS — wave 12b (QUEUE rows 103–106): otfd R `prop:unb-consistency`, C `prop:fixed-sieve-collapse`,
# C `lem:conditional-weights`, robust equality paper 2 `prop:robustdp`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-R_robustness.md`, `otfd-C_conditional.md`,
`robust-equality-paper2.md`; current text 2026-10-14):
* `prop:unb-consistency` (`otfd/papers/R_robustness/sections/s8_unbalanced.tex:67-80`), with `def:unbalanced` and
  `eq:unb-kkt` (`:8-19`), `eq:oos` (`s2_setting.tex:25-28`); proof `appendix_b.tex:157-223`.
* `prop:fixed-sieve-collapse` (`otfd/papers/C_conditional/supplement.tex:2363-2464`), proof `:2476-2613`, with the
  covariate weights `eq:self-ent`, `eq:self-quad` (`main.tex:338-347`).
* `lem:conditional-weights` (`otfd/papers/C_conditional/main.tex:439-450`), proof `supplement.tex:89-109`, with
  `P̂_{K,n,x} = Σ_i w_{n,i}(x) δ_{Z_i}` (`main.tex:322-324`).
* `prop:robustdp` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:601-609`), with `eq:BN`
  (`:222-225`), independent sets and `eq:F` (`:234-243`).
Reuses the frozen `OTFDR/Statements.lean` (`piCond`, `Qhat`), `OTFD/Bands/Statements.lean` (`simplex`, `softmax`,
`IsSimplexProj`), `RobustEquality/Certificate/Statements.lean` (`centre`, `KernelWitness`), `Wave4b/Statements.lean`
(`InBall`, `nominal`), `Wave11a/Statements.lean` (`freeClass`) and Tau Ceti's `wassersteinEDist`, `HasFiniteMoment`,
imported, not copied. No `StatFormal/Foundations` library file is imported.

Covered:
* `prop:unb-consistency`: `unb_exists_unique` (for every `τ ∈ (0,∞)` the potentials of `eq:unb-kkt` exist and are
  unique), `bal_exists_unique` (the centred balanced potentials exist and are unique), `unb_tendsto` (`w^τ → w^∞`
  and `m_i^τ → 1/n`), `unb_sup_bound` (`‖Q̂_τ(u) − Q̂_∞(u)‖ ≤ (e^{2δ_τ/ε} − 1) max_i‖z_i‖` for every `u`, and the
  bound `→ 0`), `qhat_shift_bound` (the same bound for any two potentials, any inner product space),
  `unb_schedule` (the diagonal choice of deterministic `τ_n → ∞`, abstract form).
* `prop:fixed-sieve-collapse`: (a) `fs_select` (unique `R`-minimiser over `Opt(r,b)`, unique regularised plan,
  both regularisers), `fs_limit` (`π_θ^R → π_0^R`, the grid limit `eq:response-grid-hard`, the barycentric rank
  limit), `fs_offgrid_ent` / `fs_offgrid_quad` (`eq:response-oos-hard`); (b) `fs_softmax_gap`
  (`1 − w_{i⋆} ≤ (n−1)e^{−Δ/θ}`), `fs_proj_gap` (`P_Δ(s/θ) = δ_{i⋆}` when the gap is `≥ θ`), `fs_cov_ent`
  (`w_{θ_X}(x) → δ_{i⋆}`), `fs_cov_quad` (active set eventually `{i⋆}`); (c) `fs_joint_grid`
  (`eq:joint-grid-collapse` at arbitrary relative rates), `fs_joint_const` (double quadratic: constant map on the
  grid once the support is `{i⋆}`), `fs_joint_offgrid_ent` (off-grid collapse under `eq:stable-response-cell`).
* `lem:conditional-weights`: `cw_prob` (the in-probability statement).
* `prop:robustdp`: `robustdp_const` (the main implication), `robustdp_wball` (Wasserstein balls, `r > 0`),
  `robustdp_entropic` (single full-support reference, `r` above the floor), `robustdp_free` (free end, `r` above
  its floor), `robustdp_linear` (`F(w) ≥ Δ² − g² + (|g| + S|w|)² ≥ S²|w|²`, and `Δ(w) < ∞`),
  `robustdp_linear_small` (`F(w) ≤ δ ⇒ S|w| ≤ √δ`).

Not covered (declared):
* `prop:unb-consistency`: the concrete error criteria (e.g. the mean-square error over the reference being
  dominated by the sup distance: the triangle inequality in `L²(ν)`) and the consistency schedules of
  `\cite{InouzheA}` (entered abstractly in `unb_schedule`: the per-`n` pointwise convergence it needs is
  `unb_sup_bound`); the proof's strict concavity / profile-gap route (replaced by a maximum principle).
* `prop:fixed-sieve-collapse`: "`f_0` is a hard-OT dual potential" and "if the normalised hard row potential is
  unique, no subsequence extraction is needed" (KKT limits; `fs_offgrid_*` take any converging scores); the
  precompactness of the stage-one potentials (proved in the paper from the KKT oscillation bounds; entered as the
  boundedness hypothesis of `fs_cov_*`); "the two selected plans need not coincide" (an existence remark, no
  witness built); "an unrestricted joint off-grid limit is not implied" and the "literal mirror" rank statement
  (non-claims, review note 9); the quadratic off-grid rank remark (no claim made in the paper).
* `lem:conditional-weights`: the almost-sure version (needs one probability space carrying the whole iid sequence
  and a conditional Borel–Cantelli argument given all covariates); "`x` is a support point" (not needed).
* `prop:robustdp`: references with `0 < ν(K) < 1` (`robustdp_entropic` takes a probability reference); linear rules
  with an intercept (a common translation of both prediction laws, which leaves `W₂` unchanged).

Encodings (see card):
* R: `ℝ^K` is `EuclideanSpace ℝ (Fin K)`; the reference is a probability with `∫‖u‖² dν < ∞` (`RefLaw`; a law or
  an `m`-point design); "the potentials of `def:unbalanced`" are the solutions of the second identity of
  `eq:unb-kkt` (`UnbKKT`; the first identity eliminates `g`, and `π(i|u)` is the frozen `piCond`); `m_i` is
  `rowMass` (the Bochner integral of a bounded continuous function); the balanced potentials are the solutions of
  `eq:mass` (`BalKKT`), `w^∞` the one with `Σ w = 0`; `w^τ` is `centred f^τ`; `δ_τ = supDev`, `max_i ‖z_i‖ =
  maxNorm` (finite `⨆`, `n ≥ 1`). `Q̂_∞` is `Qhat z w^∞` (the map is invariant under constants). `unb_schedule`:
  random sup-distances `D_n(τ)`, relaxed and balanced errors `e_n(τ)`, `e_n`, measurable, with `D_n(τ,ω) → 0`
  for every `n, ω`, `|e_n(τ) − e_n| ≤ D_n(τ)`, and Mathlib's `TendstoInMeasure`.
* C fixed sieve: plans are arrays `Fin n → Fin m → ℝ`; zero-mass rows removed is `r_i > 0` (`Marg`); `C` is any
  real cost (paper: `‖u_j − Z_i‖²_{M_K}`), `b` any positive law (paper: uniform); `R_ent` uses `Real.log 0 = 0`,
  i.e. `0 log 0 = 0`; "minimiser" is `IsMinOn`, `θ ↓ 0` is `𝓝[>] 0`. Off the grid, the response scores are
  `f_{r,i} − d_i` with `d_i = ‖u − Z_i‖²_{M_K}` left general, `Z_i` in any normed space (for `dist_{M_K}` take `ℝ^K`
  with the `M_K` norm); `dist(·, ch)` is `Metric.infDist` to `convexHull ℝ (Z '' argmaxSet …)`; `I_{f_0}(u)` is
  `argmaxSet` (non-empty for `n ≥ 1`); the quadratic map is the frozen `IsSimplexProj` of `s/θ`
  (`θ = γ/m`). Covariate stage: stage-one potentials `F : ℝ → ℝ^n` bounded on `(0,θ₀)`, `𝔉_X` = the
  `MapClusterPt`s at `𝓝[>] 0`, `δ_{i⋆} = Pi.single i⋆ 1`; quadratic scale `θ = nη`.
* C conditional weights: covariates in any pseudometric space `X` (paper: whitened `ℝ^q`), responses in `ℝ^K`; the
  joint law of a pair is `P_C ⊗ₘ κ` with `κ` a Markov kernel (the version `c ↦ P_{K,c}`), every `κ c` carried by
  `B̄(0,R)`; the sample is `(P_C ⊗ₘ κ)^{⊗n}` (`Measure.pi`); weights `W n : (Fin n → X) → Fin n → ℝ` measurable,
  `≥ 0`, summing to one for `n ≥ 1`; `W₁` is Tau Ceti's `wassersteinEDist 1`; `W₁`-continuity at `x` is the
  `ε`–`a` form; "in probability" is `P^{⊗n}(event) → 0`, with the outer measure for the conclusion's event (the
  measurable-event convention: equivalently a measurable superset of probability `→ 0`).
* `prop:robustdp`: `K` any topological space with measurable open sets; `𝓑₀, 𝓑₁` sets of probability measures;
  `F` is `worstIndep` (`⨆` in `ℝ≥0∞` of Tau Ceti `W₂²` of the pushforwards; equal to the frozen `Findep` when
  `𝓑_s = {Q | InBall …}`); `MassMovable` is the printed definition (`U ∈ 𝓝 x`, mixture weights `ENNReal.ofReal`);
  Wasserstein balls are `wBall P r = {Q : W₂²(P,Q) ≤ r}` (Tau Ceti, any centre with a finite second moment);
  entropic and free-end sets are the frozen kernel form `InBall` of `eq:BN` with `𝒩 = {ν}` resp. `freeClass`,
  bounded measurable cost; "full support" is `ν(U) > 0` for non-empty open `U`; "`r` above the floor (the smallest
  radius at which the set is non-empty)" is `AboveFloor` (non-empty at some `r' < r`, i.e. `r > inf{r' : 𝓑(r') ≠ ∅}`).
  Linear rules: `h(y) = ⟨w, y⟩` on `ℝ^d`, `P̂_s` the frozen `centre`, `m_s = atomMean`, `Δ(w)` the frozen `nominal`
  (`toReal`, finite by the claim), `S = √r₀ + √r₁`.
Critic notes:
* `prop:unb-consistency` holds as printed (all four conclusions). The route avoids the profile/strict-concavity
  argument: uniqueness is a maximum principle on `eq:unb-kkt` (balanced case: strict, by positivity of every
  weight); existence is by maximising `Ψ_τ` (bounded superlevel sets) and one-sided variations; KKT ⇒ maximiser
  bounds `w^τ` uniformly in `τ`, `Σ_i m_i = 1` pins the mean in `[0, nB₀]`, hence `m_i^τ → 1/n`, and limit points of
  `w^τ` solve the centred balanced system.
* `prop:fixed-sieve-collapse` (a)–(c) hold as printed in the covered parts; the covariate claims are conditional on
  boundedness of the potentials (the paper proves it). `fs_joint_grid` needs `Σ_j b_j = 1` (true: `b = 1/m`).
* `lem:conditional-weights` (in probability) holds as printed; the route conditions on covariates through the
  product structure (integrate the `i`-th pair first), so no conditional expectation is needed.
* `prop:robustdp`: the main implication needs `𝓑₁ ≠ ∅` (otherwise `F = sup ∅ = 0` and `h` is arbitrary); the paper's
  sets are non-empty. Mass-movability of the entropic set uses `ν_V = ν(V)⁻¹ ν|_V` on `V = int U` (full support
  gives `ν(V) > 0`), of the free end `δ_x` together with the reference `(1−t)ν + tδ_x`; both through the joint
  convexity of `KL`. The linear-rule bound is attained by translating `P̂₀`, `P̂₁` by `±√r_s w/|w|` in the direction of
  `sign g`.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. The kernel version of `lem:conditional-weights` puts outer measure on the BAD
  event — the strong direction (`measure_eq_iInf` gives a measurable superset of the same measure). The a.s. version is
  declared, but it IS expressible (Mathlib `Measure.infinitePi` carries the iid sequence: hypotheses `∀ᵐ s` for locality
  and `v_n log n → 0`, conclusion `∀ᵐ s, W₁ → 0`) — left for later, not impossible. `unb_schedule` is a generic lemma;
  linking it to the maps needs measurability of the data in the potentials. `fs_cov_*` boundedness holds in the paper's
  setting (oscillation bounds + `Σ f = 0`); "`f₀` is a hard-dual potential" is a real positive conclusion left for later.
  `robustdp`: `B₁ ≠ ∅` is needed (`sup ∅ = 0`); a probability reference is WLOG (`KL(Γ‖cν) = KL − log c`). Paper notes:
  C supplement `:2560` notation (undefined `A` for `𝒥`, `X_{cov,i⋆}` for `C_{i⋆}`, `D_⋆` for `D`) (S4); R says
  "mean-square error" where the proof uses the `L²` norm (root-MSE) — MSE is not 1-Lipschitz in the sup distance
  (`Q* = 0`, constant maps `a`, `a+δ`: gap `2aδ+δ² > δ`) (S4); paper2 `𝓑₁ ≠ ∅` implicit (S3, cosmetic).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory TauCeti Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave12b

/-! ## R `prop:unb-consistency` -/

section Unbalanced
open StatFormal.OTFDR

/-- `ℝ^K`. -/
abbrev Euc (K : ℕ) := EuclideanSpace ℝ (Fin K)

/-- The reference: a law with `∫ ‖u‖² dν < ∞` (a law or an `m`-point design). -/
def RefLaw {K : ℕ} (ν : Measure (Euc K)) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun u => ‖u‖ ^ 2) ν

/-- Data mass `m_i = ∫ π(i|u) ν(du)`, with `π(·|u)` the softmax of `eq:oos` (frozen `piCond`). -/
def rowMass {K n : ℕ} (ν : Measure (Euc K)) (z : Fin n → Euc K) (ε : ℝ) (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∫ u, piCond z f ε u i ∂ν

/-- `eq:unb-kkt`: the potentials of the semi-unbalanced problem, `m_i = n⁻¹ e^{−f_i/τ}` for every `i`
(the reference potential `g` is eliminated by the first identity, so `π(i|u)` is `piCond z f ε u i`). -/
def UnbKKT {K n : ℕ} (ν : Measure (Euc K)) (z : Fin n → Euc K) (ε τ : ℝ) (f : Fin n → ℝ) : Prop :=
  ∀ i, rowMass ν z ε f i = (n : ℝ)⁻¹ * Real.exp (-f i / τ)

/-- `eq:mass`: the balanced potentials, `m_i = 1/n` for every `i`. -/
def BalKKT {K n : ℕ} (ν : Measure (Euc K)) (z : Fin n → Euc K) (ε : ℝ) (f : Fin n → ℝ) : Prop :=
  ∀ i, rowMass ν z ε f i = (n : ℝ)⁻¹

/-- `w = f − f̄ 1`. -/
def centred {n : ℕ} (f : Fin n → ℝ) : Fin n → ℝ := fun i => f i - (∑ j, f j) / n

/-- `max_i |f_i − f'_i|`. -/
def supDev {n : ℕ} (f f' : Fin n → ℝ) : ℝ := ⨆ i, |f i - f' i|

/-- `max_i ‖z_i‖`. -/
def maxNorm {E : Type*} [Norm E] {n : ℕ} (z : Fin n → E) : ℝ := ⨆ i, ‖z i‖

end Unbalanced

/-! ## robust equality paper 2 `prop:robustdp` -/

section RobustDP

/-- Mass-movability of a set `𝓑₀` of laws. -/
def MassMovable {K : Type} [TopologicalSpace K] [MeasurableSpace K] (B : Set (Measure K)) : Prop :=
  ∀ x : K, ∀ U ∈ 𝓝 x, ∃ Q ∈ B, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    ∃ QU : Measure K, IsProbabilityMeasure QU ∧ QU U = 1 ∧
      ENNReal.ofReal (1 - t) • Q + ENNReal.ofReal t • QU ∈ B

/-- `F(h) = sup_{(Q₀,Q₁) ∈ 𝓑₀ × 𝓑₁} W₂²(h#Q₀, h#Q₁)` for independent sets (`eq:F`), in `ℝ≥0∞`. -/
def worstIndep {K : Type} [MeasurableSpace K] (B₀ B₁ : Set (Measure K)) (h : K → ℝ) : ℝ≥0∞ :=
  ⨆ Q₀ ∈ B₀, ⨆ Q₁ ∈ B₁, wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ^ 2

/-- The Wasserstein ball `{Q : W₂²(P, Q) ≤ r}` (Tau Ceti `W₂`). -/
def wBall {K : Type} [PseudoEMetricSpace K] [MeasurableSpace K] (P : Measure K) (r : ℝ) :
    Set (Measure K) :=
  {Q | IsProbabilityMeasure Q ∧ wassersteinEDist 2 P Q ^ 2 ≤ ENNReal.ofReal r}

/-- "`r` above the floor": the set `𝓑^𝒩(P̂; r')` (frozen `InBall`) is non-empty at some radius `r' < r`. -/
def AboveFloor {K : Type} [MeasurableSpace K] {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ)
    (N : Set (Measure K)) : Prop :=
  ∃ r' < r, ∃ Q : Measure K, StatFormal.Wave4b.InBall x c ε r' N Q

/-- The mean `n⁻¹ Σ_i x_i` of the atoms of `P̂`. -/
def atomMean {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, x i

end RobustDP

/-! ## C `prop:fixed-sieve-collapse` -/

section FixedSieve
variable {n m : ℕ}

/-- `Π(r,b)`: nonnegative `n × m` arrays with row sums `r` and column sums `b`. -/
def coup (r : Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → Fin m → ℝ) :=
  {π | (∀ i j, 0 ≤ π i j) ∧ (∀ i, ∑ j, π i j = r i) ∧ ∀ j, ∑ i, π i j = b j}

/-- `⟨C, π⟩`. -/
def cost (C π : Fin n → Fin m → ℝ) : ℝ := ∑ i, ∑ j, C i j * π i j

/-- The hard-optimal face `Opt(r,b) = argmin_{Π(r,b)} ⟨C,π⟩`. -/
def optFace (C : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → Fin m → ℝ) :=
  {π | π ∈ coup r b ∧ ∀ π' ∈ coup r b, cost C π ≤ cost C π'}

/-- `R_ent(π) = KL(π ‖ r⊗b) = Σ_{ij} π_ij log(π_ij/(r_i b_j))` (`Real.log 0 = 0` gives `0 log 0 = 0`). -/
def rEnt (r : Fin n → ℝ) (b : Fin m → ℝ) (π : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, π i j * Real.log (π i j / (r i * b j))

/-- `R_quad(π) = ½ Σ_j ‖π_{·j}‖²`. -/
def rQuad (π : Fin n → Fin m → ℝ) : ℝ := (1 / 2) * ∑ j, ∑ i, π i j ^ 2

/-- Standing marginals: zero-mass rows removed (`r_i > 0`), `Σ r = 1`; `b_j > 0`, `Σ b = 1`. -/
def Marg (r : Fin n → ℝ) (b : Fin m → ℝ) : Prop :=
  (∀ i, 0 < r i) ∧ ∑ i, r i = 1 ∧ (∀ j, 0 < b j) ∧ ∑ j, b j = 1

/-- The response map at a fitted reference point, `Q(u_j) = b_j⁻¹ Σ_i π_ij Z_i`. -/
def gridMap {E : Type*} [AddCommGroup E] [Module ℝ E] (b : Fin m → ℝ) (Z : Fin n → E)
    (π : Fin n → Fin m → ℝ) (j : Fin m) : E :=
  (b j)⁻¹ • ∑ i, π i j • Z i

/-- The barycentric rank at a fitted response point, `r_i⁻¹ Σ_j π_ij u_j`. -/
def rankMap {E : Type*} [AddCommGroup E] [Module ℝ E] (r : Fin n → ℝ) (u : Fin m → E)
    (π : Fin n → Fin m → ℝ) (i : Fin n) : E :=
  (r i)⁻¹ • ∑ j, π i j • u j

/-- `argmax_i s_i`. -/
def argmaxSet (s : Fin n → ℝ) : Set (Fin n) := {i | ∀ k, s k ≤ s i}

end FixedSieve

/-! ## C `lem:conditional-weights` -/

section Weights

/-- The weighted response law `P̂_{K,n,x} = Σ_i w_{n,i}(x) δ_{Z_i}`. -/
def wEmp {K n : ℕ} (w : Fin n → ℝ) (Z : Fin n → Euc K) : Measure (Euc K) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (Z i)

/-- The locality mass `Σ_i w_i 1{‖C_i − x‖ > a}`. -/
def locMass {X : Type*} [Dist X] {n : ℕ} (w : Fin n → ℝ) (C : Fin n → X) (x : X) (a : ℝ) : ℝ :=
  ∑ i, if a < dist (C i) x then w i else 0

/-- `v_n = Σ_i w_i²`. -/
def vn {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, w i ^ 2

end Weights

/-! ## Claims -/

namespace Claims

open StatFormal.OTFDR StatFormal.OTFD.Bands StatFormal.RobustEquality.Certificate ProbabilityTheory

/-! ### R `prop:unb-consistency` -/

/-- For every `τ ∈ (0,∞)` the semi-unbalanced potentials exist and are unique. -/
def unb_exists_unique : Prop :=
  ∀ (K n : ℕ) (ν : Measure (Euc K)) (z : Fin n → Euc K) (ε τ : ℝ),
    0 < n → RefLaw ν → 0 < ε → 0 < τ → ∃! f : Fin n → ℝ, UnbKKT ν z ε τ f

/-- The balanced potentials normalised to mean zero exist and are unique. -/
def bal_exists_unique : Prop :=
  ∀ (K n : ℕ) (ν : Measure (Euc K)) (z : Fin n → Euc K) (ε : ℝ),
    0 < n → RefLaw ν → 0 < ε → ∃! w : Fin n → ℝ, ∑ i, w i = 0 ∧ BalKKT ν z ε w

/-- `w^τ → w^∞` and `m_i^τ → 1/n` as `τ → ∞`. -/
def unb_tendsto : Prop :=
  ∀ (K n : ℕ) (ν : Measure (Euc K)) (z : Fin n → Euc K) (ε : ℝ) (fτ : ℝ → Fin n → ℝ)
    (w : Fin n → ℝ),
    0 < n → RefLaw ν → 0 < ε → (∀ τ, 0 < τ → UnbKKT ν z ε τ (fτ τ)) → ∑ i, w i = 0 →
      BalKKT ν z ε w →
      Tendsto (fun τ => centred (fτ τ)) atTop (𝓝 w) ∧
        ∀ i, Tendsto (fun τ => rowMass ν z ε (fτ τ) i) atTop (𝓝 (n : ℝ)⁻¹)

/-- The sup-norm bound `sup_u ‖Q̂_τ(u) − Q̂_∞(u)‖ ≤ (e^{2δ_τ/ε} − 1) max_i ‖z_i‖ → 0`. -/
def unb_sup_bound : Prop :=
  ∀ (K n : ℕ) (ν : Measure (Euc K)) (z : Fin n → Euc K) (ε : ℝ) (fτ : ℝ → Fin n → ℝ)
    (w : Fin n → ℝ),
    0 < n → RefLaw ν → 0 < ε → (∀ τ, 0 < τ → UnbKKT ν z ε τ (fτ τ)) → ∑ i, w i = 0 →
      BalKKT ν z ε w →
      (∀ τ, 0 < τ → ∀ u, ‖Qhat z (fτ τ) ε u - Qhat z w ε u‖ ≤
          (Real.exp (2 * supDev (centred (fτ τ)) w / ε) - 1) * maxNorm z) ∧
        Tendsto (fun τ => (Real.exp (2 * supDev (centred (fτ τ)) w / ε) - 1) * maxNorm z) atTop
          (𝓝 0)

/-- The weight-ratio bound behind `unb_sup_bound`, for any two potentials and any inner product space. -/
def qhat_shift_bound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) (z : Fin n → E)
    (f f' : Fin n → ℝ) (ε : ℝ) (u : E),
    0 < n → 0 < ε →
      ‖Qhat z f ε u - Qhat z f' ε u‖ ≤ (Real.exp (2 * supDev f f' / ε) - 1) * maxNorm z

/-- The deterministic schedule (diagonal choice): if, for every `n` and every realisation, the
sup-distance `D_n(τ)` between the relaxed and the balanced maps tends to `0` as `τ → ∞`, the error
criterion is dominated by it, and the balanced errors tend to `0` in probability, then there are
deterministic `τ_n → ∞` along which the relaxed errors tend to `0` in probability. -/
def unb_schedule : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → ℝ → Ω → ℝ) (eRel : ℕ → ℝ → Ω → ℝ) (eBal : ℕ → Ω → ℝ),
    (∀ n τ, Measurable (D n τ)) → (∀ n τ, Measurable (eRel n τ)) → (∀ n, Measurable (eBal n)) →
    (∀ n ω, Tendsto (fun τ => D n τ ω) atTop (𝓝 0)) →
    (∀ n τ ω, |eRel n τ ω - eBal n ω| ≤ D n τ ω) →
    TendstoInMeasure P eBal atTop (fun _ => 0) →
      ∃ τn : ℕ → ℝ, Tendsto τn atTop atTop ∧
        TendstoInMeasure P (fun n => eRel n (τn n)) atTop (fun _ => 0)

/-! ### robust equality paper 2 `prop:robustdp` -/

/-- The main implication: independent sets, `𝓑₁ ≠ ∅`, `𝓑₀` mass-movable, `h` continuous and
`F(h) = 0` force `h` to be constant on `K`. -/
def robustdp_const : Prop :=
  ∀ (K : Type) [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
    (B₀ B₁ : Set (Measure K)) (h : K → ℝ),
    (∀ Q ∈ B₀, IsProbabilityMeasure Q) → (∀ Q ∈ B₁, IsProbabilityMeasure Q) → B₁.Nonempty →
    MassMovable B₀ → Continuous h → worstIndep B₀ B₁ h = 0 → ∀ x y, h x = h y

/-- Wasserstein balls with `r > 0` are mass-movable (any centre with finite second moment). -/
def robustdp_wball : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (P : Measure K) (r : ℝ),
    IsProbabilityMeasure P → HasFiniteMoment 2 P → 0 < r → MassMovable (wBall P r)

/-- Entropic single-reference sets whose reference has full support, with `r` above the floor, are
mass-movable (frozen `InBall`, kernel form of `eq:BN`; bounded measurable cost). -/
def robustdp_entropic : Prop :=
  ∀ (K : Type) [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K] (n : ℕ)
    (x : Fin n → K) (c : K → K → ℝ) (ε r B : ℝ) (ν : Measure K),
    0 < n → 0 < ε → (∀ i, Measurable (c (x i))) → (∀ y z, |c y z| ≤ B) →
    IsProbabilityMeasure ν → (∀ U : Set K, IsOpen U → U.Nonempty → 0 < ν U) →
    AboveFloor x c ε r {ν} →
      MassMovable {Q | StatFormal.Wave4b.InBall x c ε r {ν} Q}

/-- The free end with `r` above its floor is mass-movable. -/
def robustdp_free : Prop :=
  ∀ (K : Type) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ)
    (x : Fin n → K) (c : K → K → ℝ) (ε r B : ℝ),
    0 < n → 0 < ε → (∀ i, Measurable (c (x i))) → (∀ y z, |c y z| ≤ B) →
    AboveFloor x c ε r StatFormal.Wave11a.freeClass →
      MassMovable {Q | StatFormal.Wave4b.InBall x c ε r StatFormal.Wave11a.freeClass Q}

/-- Linear rules and Wasserstein balls on `K = ℝ^d`:
`F(w) ≥ Δ(w)² − g(w)² + (|g(w)| + S|w|)² ≥ S²|w|²`, `g(w) = ⟨w, m₀ − m₁⟩`, `S = √r₀ + √r₁`
(and `Δ(w) < ∞`, so `Δ(w)² = (toReal Δ)²`). -/
def robustdp_linear : Prop :=
  ∀ (d n₀ n₁ : ℕ) (x₀ : Fin n₀ → Euc d) (x₁ : Fin n₁ → Euc d) (r₀ r₁ : ℝ) (w : Euc d),
    0 < n₀ → 0 < n₁ → 0 ≤ r₀ → 0 ≤ r₁ →
      StatFormal.Wave4b.nominal x₀ x₁ (fun y => inner ℝ w y) ≠ ⊤ ∧
      ENNReal.ofReal ((StatFormal.Wave4b.nominal x₀ x₁ (fun y => inner ℝ w y)).toReal ^ 2
          - (inner ℝ w (atomMean x₀ - atomMean x₁)) ^ 2
          + (|inner ℝ w (atomMean x₀ - atomMean x₁)| + (√r₀ + √r₁) * ‖w‖) ^ 2) ≤
        worstIndep (wBall (centre x₀) r₀) (wBall (centre x₁) r₁) (fun y => inner ℝ w y) ∧
      (√r₀ + √r₁) ^ 2 * ‖w‖ ^ 2 ≤
        (StatFormal.Wave4b.nominal x₀ x₁ (fun y => inner ℝ w y)).toReal ^ 2
          - (inner ℝ w (atomMean x₀ - atomMean x₁)) ^ 2
          + (|inner ℝ w (atomMean x₀ - atomMean x₁)| + (√r₀ + √r₁) * ‖w‖) ^ 2

/-- Consequence: `F(w) ≤ δ` forces `S|w| ≤ √δ` (i.e. `|w| ≤ √δ/S` when `S > 0`). -/
def robustdp_linear_small : Prop :=
  ∀ (d n₀ n₁ : ℕ) (x₀ : Fin n₀ → Euc d) (x₁ : Fin n₁ → Euc d) (r₀ r₁ δ : ℝ) (w : Euc d),
    0 < n₀ → 0 < n₁ → 0 ≤ r₀ → 0 ≤ r₁ → 0 ≤ δ →
      worstIndep (wBall (centre x₀) r₀) (wBall (centre x₁) r₁) (fun y => inner ℝ w y) ≤
        ENNReal.ofReal δ →
      (√r₀ + √r₁) * ‖w‖ ≤ √δ

/-! ### C `prop:fixed-sieve-collapse` -/

/-- (a) Each regulariser selects one hard-optimal plan: the minimiser of `R` over `Opt(r,b)` is
unique, and so is the minimiser of `⟨C,π⟩ + θR(π)` over `Π(r,b)` for every `θ > 0`. -/
def fs_select : Prop :=
  ∀ (n m : ℕ) (C : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (b : Fin m → ℝ)
    (R : (Fin n → Fin m → ℝ) → ℝ),
    Marg r b → (R = rEnt r b ∨ R = rQuad) →
      (∃! π, π ∈ optFace C r b ∧ IsMinOn R (optFace C r b) π) ∧
        ∀ θ, 0 < θ → ∃! π, π ∈ coup r b ∧ IsMinOn (fun π => cost C π + θ * R π) (coup r b) π

/-- (a) `π_θ^R → π_0^R` as `θ ↓ 0`, hence the grid limit `eq:response-grid-hard` and the barycentric
rank limit at every fitted response point. -/
def fs_limit : Prop :=
  ∀ (n m : ℕ) (C : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (b : Fin m → ℝ)
    (R : (Fin n → Fin m → ℝ) → ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Fin n → E) (u : Fin m → E) (πθ : ℝ → Fin n → Fin m → ℝ) (π₀ : Fin n → Fin m → ℝ),
    Marg r b → (R = rEnt r b ∨ R = rQuad) →
    (∀ θ, 0 < θ → πθ θ ∈ coup r b ∧ IsMinOn (fun π => cost C π + θ * R π) (coup r b) (πθ θ)) →
    π₀ ∈ optFace C r b → IsMinOn R (optFace C r b) π₀ →
      Tendsto πθ (𝓝[>] 0) (𝓝 π₀) ∧
        (∀ j, Tendsto (fun θ => gridMap b Z (πθ θ) j) (𝓝[>] 0) (𝓝 (gridMap b Z π₀ j))) ∧
        ∀ i, Tendsto (fun θ => rankMap r u (πθ θ) i) (𝓝[>] 0) (𝓝 (rankMap r u π₀ i))

/-- (a) off-grid, entropic: along `θ_r ↓ 0` with row potentials `f_r → f₀`, the softmax map at `u`
(scores `f_{r,i} − d_i`, `d_i = ‖u − Z_i‖²_{M_K}`) approaches `ch{Z_i : i ∈ I_{f₀}(u)}`. -/
def fs_offgrid_ent : Prop :=
  ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Fin n → E) (d : Fin n → ℝ)
    (θ : ℕ → ℝ) (f : ℕ → Fin n → ℝ) (f₀ : Fin n → ℝ),
    0 < n → Tendsto θ atTop (𝓝[>] 0) → Tendsto f atTop (𝓝 f₀) →
      Tendsto (fun r => Metric.infDist (∑ i, softmax (fun k => (f r k - d k) / θ r) i • Z i)
          (convexHull ℝ (Z '' argmaxSet (fun k => f₀ k - d k)))) atTop (𝓝 0)

/-- (a) off-grid, quadratic: the same for the simplex projection `q_r = P_Δ(s_r/θ_r)`. -/
def fs_offgrid_quad : Prop :=
  ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Fin n → E) (d : Fin n → ℝ)
    (θ : ℕ → ℝ) (f : ℕ → Fin n → ℝ) (f₀ : Fin n → ℝ) (q : ℕ → Fin n → ℝ),
    0 < n → Tendsto θ atTop (𝓝[>] 0) → Tendsto f atTop (𝓝 f₀) →
    (∀ r, IsSimplexProj (fun k => (f r k - d k) / θ r) (q r)) →
      Tendsto (fun r => Metric.infDist (∑ i, q r i • Z i)
          (convexHull ℝ (Z '' argmaxSet (fun k => f₀ k - d k)))) atTop (𝓝 0)

/-- (b) the displayed entropic gap bound `1 − w_{i⋆} ≤ (n−1) e^{−Δ/θ}`. -/
def fs_softmax_gap : Prop :=
  ∀ (n : ℕ) (s : Fin n → ℝ) (istar : Fin n) (θ Δ : ℝ),
    0 < θ → (∀ i, i ≠ istar → s i + Δ ≤ s istar) →
      1 - softmax (fun i => s i / θ) istar ≤ ((n : ℝ) - 1) * Real.exp (-Δ / θ)

/-- (b) the quadratic gap criterion: `P_Δ(s/θ) = δ_{i⋆}` when `s_{i⋆} − max_{i≠i⋆} s_i ≥ θ`. -/
def fs_proj_gap : Prop :=
  ∀ (n : ℕ) (s q : Fin n → ℝ) (istar : Fin n) (θ : ℝ),
    0 < θ → (∀ i, i ≠ istar → s i + θ ≤ s istar) → IsSimplexProj (fun i => s i / θ) q →
      q = Pi.single istar 1

/-- (b) covariate stage, entropic: if the stage-one potentials are bounded as `θ_X ↓ 0` and every
accumulation point has the strict cell `eq:covariate-hard-cell` at `i⋆`, then `w_{θ_X}(x) → δ_{i⋆}`. -/
def fs_cov_ent : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ) (F : ℝ → Fin n → ℝ) (istar : Fin n) (θ₀ M : ℝ),
    0 < θ₀ → (∀ θ ∈ Ioo 0 θ₀, ∀ i, |F θ i| ≤ M) →
    (∀ f₀, MapClusterPt f₀ (𝓝[>] 0) F → argmaxSet (fun i => f₀ i - d i) = {istar}) →
      Tendsto (fun θ => fun i => softmax (fun k => (F θ k - d k) / θ) i) (𝓝[>] 0)
        (𝓝 (Pi.single istar 1))

/-- (b) covariate stage, quadratic: under the same hypotheses the active set of
`w_θ = P_Δ((F_θ − d)/θ)` is eventually `{i⋆}`. -/
def fs_cov_quad : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ) (F : ℝ → Fin n → ℝ) (istar : Fin n) (θ₀ M : ℝ) (w : ℝ → Fin n → ℝ),
    0 < θ₀ → (∀ θ ∈ Ioo 0 θ₀, ∀ i, |F θ i| ≤ M) →
    (∀ f₀, MapClusterPt f₀ (𝓝[>] 0) F → argmaxSet (fun i => f₀ i - d i) = {istar}) →
    (∀ θ, 0 < θ → IsSimplexProj (fun k => (F θ k - d k) / θ) (w θ)) →
      ∀ᶠ θ in 𝓝[>] 0, ∀ i, (0 < w θ i ↔ i = istar)

/-- (c) joint grid collapse at arbitrary relative rates: any couplings `π_r ∈ Π(w_r, b)` whose row
weight at `i⋆` tends to `1` give `max_j ‖Q_r(u_j) − Z_{i⋆}‖ → 0`. -/
def fs_joint_grid : Prop :=
  ∀ (n m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Fin n → E) (b : Fin m → ℝ)
    (istar : Fin n) (w : ℕ → Fin n → ℝ) (π : ℕ → Fin n → Fin m → ℝ),
    (∀ j, 0 < b j) → ∑ j, b j = 1 → (∀ k, π k ∈ coup (w k) b) →
      Tendsto (fun k => w k istar) atTop (𝓝 1) →
      Tendsto (fun k => ⨆ j, ‖gridMap b Z (π k) j - Z istar‖) atTop (𝓝 0)

/-- (c) double quadratic: once the stage-one support is `{i⋆}`, every response coupling is the
constant map `Z_{i⋆}` on the grid. -/
def fs_joint_const : Prop :=
  ∀ (n m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Fin n → E) (b : Fin m → ℝ)
    (istar : Fin n) (π : Fin n → Fin m → ℝ),
    (∀ j, 0 < b j) → π ∈ coup (Pi.single istar 1) b → ∀ j, gridMap b Z π j = Z istar

/-- (c) double entropic, off the grid: under a stable response gap `eq:stable-response-cell`, the
softmax map at `u` tends to `Z_{i⋆}`. -/
def fs_joint_offgrid_ent : Prop :=
  ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Fin n → E) (d : Fin n → ℝ)
    (θ : ℕ → ℝ) (f : ℕ → Fin n → ℝ) (istar : Fin n) (δ : ℝ),
    0 < δ → Tendsto θ atTop (𝓝[>] 0) →
    (∀ᶠ k in atTop, ∀ i, i ≠ istar → f k i - d i + δ ≤ f k istar - d istar) →
      Tendsto (fun k => ∑ i, softmax (fun i => (f k i - d i) / θ k) i • Z i) atTop (𝓝 (Z istar))

/-! ### C `lem:conditional-weights` -/

/-- The in-probability version: iid pairs `(C_i, Z_i) ∼ P_C ⊗ P_{K,·}` with `Z_i ∈ B̄(0,R)`, weights
`w_{n,i}(x) ≥ 0` summing to one and depending on the covariates only, `c ↦ P_{K,c}` `W₁`-continuous at
`x`, locality and `v_n → 0` in probability; then `W₁(P̂_{K,n,x}, P_{K,x}) → 0` in probability
(outer probability of the bad event). -/
def cw_prob : Prop :=
  ∀ (X : Type) [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (K : ℕ) (R : ℝ)
    (PC : Measure X) [IsProbabilityMeasure PC] (κ : ProbabilityTheory.Kernel X (Euc K))
    [ProbabilityTheory.IsMarkovKernel κ] (W : ∀ n : ℕ, (Fin n → X) → Fin n → ℝ) (x : X),
    (∀ c, κ c (Metric.closedBall 0 R)ᶜ = 0) →
    (∀ n, 0 < n → Measurable (W n) ∧ ∀ c, (∀ i, 0 ≤ W n c i) ∧ ∑ i, W n c i = 1) →
    (∀ η, 0 < η → ∃ a, 0 < a ∧ ∀ c, dist c x < a →
      wassersteinEDist 1 (κ c) (κ x) ≤ ENNReal.ofReal η) →
    (∀ a, 0 < a → ∀ η, 0 < η → Tendsto (fun n => Measure.pi (fun _ : Fin n => PC ⊗ₘ κ)
        {s | η ≤ locMass (W n (fun i => (s i).1)) (fun i => (s i).1) x a}) atTop (𝓝 0)) →
    (∀ η, 0 < η → Tendsto (fun n => Measure.pi (fun _ : Fin n => PC ⊗ₘ κ)
        {s | η ≤ vn (W n (fun i => (s i).1))}) atTop (𝓝 0)) →
    ∀ η, 0 < η → Tendsto (fun n => Measure.pi (fun _ : Fin n => PC ⊗ₘ κ)
        {s | ENNReal.ofReal η ≤
          wassersteinEDist 1 (wEmp (W n (fun i => (s i).1)) (fun i => (s i).2)) (κ x)}) atTop (𝓝 0)

end Claims
end StatFormal.Wave12b
