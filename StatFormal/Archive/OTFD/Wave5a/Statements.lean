import StatFormal.Archive.OTFD.Ranks.Statements
import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.Bands2.Statements
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FROZEN STATEMENTS — otfd wave 5a: A `prop:rt-randomized`, A `prop:T-proxy`, R `prop:depth-regions`,
# B `thm:fixedK-df` (B copy), B `prop:rk-symmetry`, B `prop:pop-band-coverage`, B `lem:cal-no-l2`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`, `otfd-R_robustness.md`,
`otfd-B_bands.md`; read against the manuscripts as corrected on 2026-10-14; paths under `otfd/papers/`):
* A `prop:rt-randomized` (`A_sieves/supplement.tex:5468-5500`), proof `supplement.tex:4261-4295`.
* A `prop:T-proxy` (`A_sieves/main.tex:1287-1295`), with `Ĉ_Υ`, `𝓡_𝒜`, `β_𝓑` (`main.tex:1276-1285`); proof
  `supplement.tex:4982-5000`.
* R `prop:depth-regions` (`R_robustness/sections/s5_families.tex:47-56`), proof `:58-65`; `def:beta`
  (`s3_infinite.tex:112-117`), `D_α` (`s3_infinite.tex:8`), `lem:convex` (`appendix_a.tex:8-21`), `eq:TDH`
  (`s2_setting.tex:7-10`), `β(A;ν)` (`s2_setting.tex:80`).
* B `thm:fixedK-df` (`B_bands/supplement.tex:6352-6363`), proof `supplement.tex:508-525`.
* B `prop:rk-symmetry` (`B_bands/main.tex:1105-1131`), notation `main.tex:1061-1070`, `def:depth-family`
  (`main.tex:502-515`); proof `supplement.tex:5227-5239`.
* B `prop:pop-band-coverage` (`B_bands/supplement.tex:793-802`), population band `supplement.tex:778-791`; proof
  `supplement.tex:2002-2009`.
* B `lem:cal-no-l2` (`B_bands/supplement.tex:5742-5755`), proof `supplement.tex:5757-5772`.
Reuses the frozen `OTFD/Ranks/Statements.lean` (`cost`, `IsMin`, `UniqueMin`), `OTFD/Wave1/Statements.lean`
(`tukeyDepth`, `regionDepth`, `supportFn`, `PellClass`) and `OTFD/Bands2/Statements.lean` (`curve`, `band`),
imported, not copied.

Covered:
* A `prop:rt-randomized`: (a) `rt_uniform_indep` (`W = 𝔛∘τ` has the law of `𝔛`, `σ̃` is uniform and independent
  of `W`, in product form), `rt_rank_law` (`R̃ ≐ (u_{π(i)})_i`, `π` uniform), `rt_size` (size `≤ α` for every
  statistic and critical value); (b) `rt_equivariant`; (c) `rt_equal`; (d) `rt_optimal_shift`, `rt_optimal`
  (reordering-invariant coefficients), `rt_optimal_basis` (order-dependent basis).
* A `prop:T-proxy`: `tproxy_oracle` (the oracle inequality, measurable-event form, for every minimiser `θ̂`).
* R `prop:depth-regions`: `depth_regions_optimal`, `depth_regions_content` (content `≥ p` and robustness `≥ α`
  for `α < β*`), `depth_regions_closed_convex`, `depth_regions_compact` (`α > 0`), `depth_regions_support`
  (`h_{D_α} = q`).
* B `thm:fixedK-df`: `fixedK_rank_law` (rank vector uniform over the orderings; every rank statistic
  distribution-free), `fixedK_unique_of_atomless` (iid + atomless 1-D projections + distinct grid ⇒ a.s. unique
  assignment), `fixedK_pell_atomless` (`𝒫^ℓ` ⇒ atomless 1-D projections). The first sentence ("`σ̂` is
  uniform") and "non-atomicity alone does not suffice" are A's certified `Ranks.Claims.fixedK_df`,
  `Ranks.Claims.nonatomic_not_sufficient`.
* B `prop:rk-symmetry`: (i) `rk_sym_pushforward`; (ii) `rk_sym_depth`; (iii) `rk_sym_depth_law`,
  `rk_sym_two_sample`; (iv) `rk_sym_sign`.
* B `prop:pop-band-coverage`: `pop_band_coverage` (the event is measurable and has probability `≥ μ_K(A)`).
* B `lem:cal-no-l2`: `cal_no_l2`.

Not covered (declared):
* A (a): "exactly `α` when randomized at the quantile" (the randomized test is not defined in the paper); the
  link "`H_0` ⇒ the pooled sample is exchangeable" (exchangeability is the hypothesis). (c): that the
  pipelines of `prop:rt-df`(i)–(ii) satisfy the equivariance hypothesis, and the transfer of `thm:rt-fixedK`,
  `thm:rt-coherent` (immediate from `σ̃ = 𝔯(𝔛)` a.s.). (d): only the assignment step is formalised (the
  basis, centering and scaling enter through the coefficient map `Zc`).
* A `prop:T-proxy`: the asymptotic sentence ("Hence, if `β_𝓑 → 0` …, consistent whenever one of the candidates
  is"), which needs `lem:T-risk`; the package's swapped average.
* R: "the band enclosures of [B] apply to it unchanged" (a remark).
* B `thm:fixedK-df`: "for instance, iid curves" ⇒ exchangeable (not restated; A's certified claim takes
  exchangeability).
* B `prop:rk-symmetry`: which `G` qualify for which reference family (`−Id`, `GᵀM_KG = M_K`, sign flips): these
  are properties of the reference families; existence of `F`, `Q` (`thm:prob-content`) — they enter as
  hypotheses. The sentence "at most its size, and equal to it for an exact test" is the definition of size
  once the law identity `rk_sym_two_sample` holds.
* B `lem:cal-no-l2`: the "In particular …" sentence about `ρ_K(P)` (informal).

Encodings (see card):
* A `prop:rt-randomized`: `H` is any measurable space `X`; `x ∘ π = (x_{π(1)},…,x_{π(N)})` is `x ∘ ⇑π`;
  `σ̃ = 𝔯(𝔛∘τ) ∘ τ⁻¹` is `rtSigma r x t = r (x ∘ t) * t⁻¹`; "Borel rule" = every fibre `{x | 𝔯 x = h}`
  measurable; `τ` uniform = `P(τ = t) = 1/N!` with measurable fibres; "independent of `𝔛`" =
  `P(𝔛 ∈ B, τ = t) = P(𝔛 ∈ B) P(τ = t)` for measurable `B`; exchangeable = `law(𝔛 ∘ π) = law(𝔛)` (as in the
  frozen `fixedK_df`). "Uniform and independent of `W`" is the product formula
  `P(W ∈ B, σ̃ = g) = P(𝔛 ∈ B)/N!`. Size: any statistic `T` of the rank vector and any `c` with
  `#{π : T(u∘π) > c} ≤ α N!` (the defining property of `c_{N,α}`). (b) is stated over `τ` alone (any law space).
  (c) needs neither uniformity nor independence. Grid `u : Fin N → E`, `E` any real inner-product space.
* A `prop:T-proxy`: conditionally on `𝒜`, the candidates `a_θ = Υ F̂^𝒜_θ` and the target `c = Υ F_K` are fixed
  maps `X → F` into the closed `R`-ball of a real normed space `F` (the property of `Υ` used), with measurable
  losses `‖a_θ − c‖`; the pilot values `b_i = Υ F̂^𝓑_0(Z_i)` are arbitrary (no measurability: the event does
  not involve them); `𝓑 = Fin m`, `m > 0`, `Z_i` independent with law `P_K`. "with probability `≥ 1 − γ`,
  simultaneously for all `θ`" is: there is a measurable event of probability `≥ 1 − γ` on which the inequality
  holds for all `θ` and for **every** minimiser `θ̂` (no measurable selection needed). `|Θ| = Fintype.card Θ`.
* R: `ℝ^K = EuclideanSpace ℝ (Fin K)`; depths, contents, `α`, `p` and `β*` are `ℝ≥0∞`-valued (`β*` is an
  `sSup` in a complete lattice, no junk; for `p ≤ 1` the set contains `α = 0`); `D_α = {u : TD(u) ≥ α}`;
  `q_v = sSup {s : ν{⟨X,v⟩ ≥ s} ≥ α}` (`dirQuantile`) is stated for `0 < α < 1`, where that set is nonempty and
  bounded above (at `α = 1` it can be empty, e.g. Gaussian `ν`, where the paper's `q_v = −∞` and `sSup ∅ = 0` is
  junk); `h_{D_α}` is the frozen `supportFn` (an `sSup`; the claim shows it is attained). "Sublinear" =
  subadditive and positively homogeneous; **lower semicontinuity is dropped** (generalisation: in finite
  dimension a finite sublinear function is continuous; the proof is Hahn–Banach). The optimality and
  content claims hold for every `p` and every measure `ν` (generalisation: no `p ∈ (0,1)`, no
  probability).
* B `thm:fixedK-df`: sample `Z : Ω → Fin n → E` with `E` any real inner-product space (the `M_K` geometry);
  "iid" = `iIndepFun` of the coordinates with common law `P_K`; "every 1-D projection atomless" =
  `P_K{z : ⟨w,z⟩ = c} = 0` for all `w ≠ 0`, `c`; distinct grid points (`u` injective) are assumed, as in the
  proof (with a repeated grid point uniqueness fails everywhere, `Ranks.Claims.unique_forces_distinct`).
  "Rank vector uniform over the orderings" = `P(R ∈ S) = #{π : u∘π ∈ S}/n!` for every set `S`.
* B `prop:rk-symmetry`: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `F`, `Q` measurable with `F#P_K = μ_K`,
  `Q#μ_K = P_K`, `Q∘F = id` `P_K`-a.e. and `F∘Q = id` `μ_K`-a.e. (the property of `thm:prob-content`(c),(d)
  used); `P_K ∈ 𝒫^ℓ` enters only through these. `G` linear with `G#μ_K = μ_K`; "`ρ∘G = ρ` on `𝒰_K`" is
  `ρ(Gu) = ρ(u)` for `μ_K`-a.e. `u` (generalisation: `μ_K(𝒰_K) = 1`). `D^geom = 1 − ρ∘F`,
  `D^prob = 1 − c_K∘ρ∘F` for any measurable `ρ`, `c_K`; `S(u) = ρ(u)⁻¹ u` (at `u = 0` this is `0`, a
  convention: `S(0) = 0 = G S(0)`, so the identity is unaffected). "Same law under `C` and `T_G#C`" is
  stated for the depth pair; "every statistic of the depths of two samples" is the law identity of the depth
  vectors of `(C^{⊗m}, (T_G#C)^{⊗m'})` and `(C^{⊗m}, C^{⊗m'})` (any test has the same rejection probability).
  `C` is any probability with `C ≪ P_K`.
* B `prop:pop-band-coverage`: `ℝ^K = Fin K → ℝ`, `⟨·,·⟩ = dotProduct` (as in Bands2); the ess-sup support
  function is `essSup` in `EReal` of `u ↦ ⟨v, Q(u)⟩` under `μ_K|_A` (no junk: `⊥` if `μ_K(A) = 0`, `⊤` if
  unbounded); edges `𝔪 + h(e(t))`, `𝔪 − h(−e(t))`; band and curve are the frozen `band`, `curve`.
  `Π_K X` is any measurable `Zc` with `law(Zc) = Q#μ_K`; `Q` is any measurable map (no injectivity or
  continuity); `A_{K,p}` is generalised to any measurable `A`, and the bound is `P(·) ≥ μ_K(A)`
  (`= p` for `A_{K,p}` under `ass:fixedK-oos`(i)). The event is asserted measurable (simultaneity over
  uncountable `𝒯` goes through the essential range, see the route).
* B `lem:cal-no-l2`: `𝒯 = [0,1]` with Lebesgue measure (`volume.restrict (Icc 0 1)`); `x ∈ H ∩ L^∞` is
  `MemLp x 2 ∧ MemLp x ⊤`; `‖·‖_H`, `‖·‖_∞` are `eLpNorm · 2`, `eLpNorm · ⊤` (finite for every admissible
  `x`, so `toReal` is exact); `P^rec_K x = Σ_k ⟨x, e_k⟩ e_k` with `⟨x,e⟩ = ∫ x e`, `𝔪 = 0`; the `e_k` are any
  measurable functions bounded by a common `C` (**orthonormality dropped**, generalisation); `φ : ℝ → ℝ` with
  `φ(s) → 0` as `s ↓ 0` (`𝓝[>] 0`, so `φ(0)` is free); nonnegativity of `φ` dropped (generalisation).
  The bound `|e_k t| ≤ C` is asked on all of `ℝ`; only values on `[0,1]` enter (cut off a family bounded
  on `[0,1]` by `0` outside).
Critic notes:
* A (c) holds without the independence of `𝔛` and `τ` and without uniformity of `τ` (the printed proof invokes
  independence, unnecessarily).
* B `lem:cal-no-l2`: the printed proof's detour through `g_j = h_j − P h_j` uses that `P^rec_K` is an
  orthogonal projection; the bump itself already works for any bounded (not necessarily orthonormal) family.
* B `fixedK-df`: the printed sufficient condition omits "distinct grid points", which the proof uses and which is
  necessary (`Ranks.Claims.unique_forces_distinct`); "the grid `{u_1,…,u_n}`" (a set of `n` points) implies it.
  Critic (2026-10-14): a genuine S3 (missing hypothesis, low impact; DEFECTS #37) — B's proof (`supplement.tex:523`)
  uses distinctness and A's version (`main.tex:507`) also omits it in the statement (A notes it at `:504`); fix:
  "for iid sampling and distinct grid points, uniqueness holds …".
* R `prop:depth-regions` (support claim): the restriction `0 < α < 1` is necessary, not cosmetic — at `α = 1`
  `D_1 = ∅` and `sSup ∅ = 0` would make it false (`ν = Exp(1) + 1`, `K = 1`); a real-valued sublinear `q` at
  `α = 1` forces `ν` to be a Dirac, so only a degenerate case is lost.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave5a

open StatFormal.OTFD.Ranks StatFormal.OTFD.Wave1 StatFormal.OTFD.Bands2

/-! ### A `prop:rt-randomized` -/

/-- `σ̃(x,t) = 𝔯(x ∘ t) ∘ t⁻¹`: solve on the shuffled sample, then undo the shuffle. -/
def rtSigma {X : Type} {N : ℕ} (r : (Fin N → X) → Equiv.Perm (Fin N)) (x : Fin N → X)
    (t : Equiv.Perm (Fin N)) : Equiv.Perm (Fin N) :=
  r (x ∘ t) * t⁻¹

/-! ### A `prop:T-proxy` -/

/-- Mean square distance on the fold, `|𝓑|⁻¹ Σ_{i∈𝓑} ‖f_i − g_i‖²`. -/
def msq {F : Type} [NormedAddCommGroup F] {m : ℕ} (f g : Fin m → F) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, ‖f i - g i‖ ^ 2

/-! ### R `prop:depth-regions` -/

/-- `D_α(ν) = {u : TD(u;ν) ≥ α}`. -/
def depthRegion {K : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) (α : ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin K)) :=
  {u | α ≤ tukeyDepth ν u}

/-- `def:beta`: `β*_K(p;ν) = sup{α ≥ 0 : ν(D_α(ν)) ≥ p}`. -/
def betaStar {K : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) (p : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {α | p ≤ ν (depthRegion ν α)}

/-- The directional quantile `q_v = sup{s : ν{⟨X,v⟩ ≥ s} ≥ α}`. -/
def dirQuantile {K : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) (α : ℝ≥0∞)
    (v : EuclideanSpace ℝ (Fin K)) : ℝ :=
  sSup {s : ℝ | α ≤ ν {X | s ≤ ⟪X, v⟫_ℝ}}

/-! ### B `prop:rk-symmetry` -/

section RkSym
variable {K : ℕ}
local notation "𝔼K" => EuclideanSpace ℝ (Fin K)

/-- `T_G = Q ∘ G ∘ F`. -/
def symMap (Q : 𝔼K → 𝔼K) (G : 𝔼K →ₗ[ℝ] 𝔼K) (F : 𝔼K → 𝔼K) (z : 𝔼K) : 𝔼K := Q (G (F z))

/-- Geometric depth `D^geom(z) = 1 − ρ(F z)`. -/
def depthGeom (ρ : 𝔼K → ℝ) (F : 𝔼K → 𝔼K) (z : 𝔼K) : ℝ := 1 - ρ (F z)

/-- Probability-calibrated depth `D^prob(z) = 1 − c_K(ρ(F z))`. -/
def depthProb (c : ℝ → ℝ) (ρ : 𝔼K → ℝ) (F : 𝔼K → 𝔼K) (z : 𝔼K) : ℝ := 1 - c (ρ (F z))

/-- The sign `S(u) = u/ρ(u)` (the value at `ρ(u) = 0` is `0`). -/
def signMap (ρ : 𝔼K → ℝ) (u : 𝔼K) : 𝔼K := (ρ u)⁻¹ • u

end RkSym

/-! ### B `prop:pop-band-coverage` -/

/-- `h^pop(v) = μ_K-ess sup_{u ∈ A} ⟨v, Q(u)⟩`, in `EReal`. -/
def hEss {K : ℕ} (μ : Measure (Fin K → ℝ)) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ))
    (v : Fin K → ℝ) : EReal :=
  essSup (fun u => ((v ⬝ᵥ Q u : ℝ) : EReal)) (μ.restrict A)

/-- Upper population edge `𝔪(t) + h^pop(e(t))`. -/
def popUp {K : ℕ} (μ : Measure (Fin K → ℝ)) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ))
    (mo : ℝ) (v : Fin K → ℝ) : EReal :=
  (mo : EReal) + hEss μ Q A v

/-- Lower population edge `𝔪(t) − h^pop(−e(t))`. -/
def popLo {K : ℕ} (μ : Measure (Fin K → ℝ)) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ))
    (mo : ℝ) (v : Fin K → ℝ) : EReal :=
  (mo : EReal) - hEss μ Q A (-v)

/-! ### B `lem:cal-no-l2` -/

/-- `P^rec_K x = Σ_k ⟨x, e_k⟩ e_k` on `[0,1]` (`𝔪 = 0`). -/
def precK {K : ℕ} (e : Fin K → ℝ → ℝ) (x : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∑ k, (∫ s in Icc (0 : ℝ) 1, x s * e k s) * e k t

namespace Claims

/-! ### A `prop:rt-randomized` -/

/-- (a) For an exchangeable sample and an independent uniform shuffle `τ`, `W = 𝔛 ∘ τ` and `σ̃` satisfy
`P(W ∈ B, σ̃ = g) = P(𝔛 ∈ B)/N!` (measurable event): `W ≐ 𝔛`, `σ̃` uniform, independent of `W`. -/
def rt_uniform_indep : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : ℕ) (𝔛 : Ω → Fin N → X) (τ : Ω → Equiv.Perm (Fin N))
    (r : (Fin N → X) → Equiv.Perm (Fin N)),
    Measurable 𝔛 → (∀ h, MeasurableSet {x | r x = h}) →
    (∀ t, MeasurableSet {ω | τ ω = t}) → (∀ t, P {ω | τ ω = t} = (Nat.factorial N : ℝ≥0∞)⁻¹) →
    (∀ B : Set (Fin N → X), MeasurableSet B → ∀ t,
      P ({ω | 𝔛 ω ∈ B} ∩ {ω | τ ω = t}) = P {ω | 𝔛 ω ∈ B} * P {ω | τ ω = t}) →
    (∀ π : Equiv.Perm (Fin N), P.map (fun ω => 𝔛 ω ∘ π) = P.map 𝔛) →
      ∀ B : Set (Fin N → X), MeasurableSet B → ∀ g : Equiv.Perm (Fin N),
        MeasurableSet {ω | 𝔛 ω ∘ τ ω ∈ B ∧ rtSigma r (𝔛 ω) (τ ω) = g} ∧
        P {ω | 𝔛 ω ∘ τ ω ∈ B ∧ rtSigma r (𝔛 ω) (τ ω) = g} =
          P.map 𝔛 B * (Nat.factorial N : ℝ≥0∞)⁻¹

open scoped Classical in
/-- (a) `(R̃_1,…,R̃_N) ≐ (u_{π(1)},…,u_{π(N)})`, `π` uniform: `P(R̃ ∈ S) = #{π : u∘π ∈ S}/N!` for every
set `S`, for every exchangeable sample (no uniqueness, atoms allowed). -/
def rt_rank_law : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : ℕ) (𝔛 : Ω → Fin N → X) (τ : Ω → Equiv.Perm (Fin N))
    (r : (Fin N → X) → Equiv.Perm (Fin N)) (u : Fin N → Y),
    Measurable 𝔛 → (∀ h, MeasurableSet {x | r x = h}) →
    (∀ t, MeasurableSet {ω | τ ω = t}) → (∀ t, P {ω | τ ω = t} = (Nat.factorial N : ℝ≥0∞)⁻¹) →
    (∀ B : Set (Fin N → X), MeasurableSet B → ∀ t,
      P ({ω | 𝔛 ω ∈ B} ∩ {ω | τ ω = t}) = P {ω | 𝔛 ω ∈ B} * P {ω | τ ω = t}) →
    (∀ π : Equiv.Perm (Fin N), P.map (fun ω => 𝔛 ω ∘ π) = P.map 𝔛) →
      ∀ S : Set (Fin N → Y),
        P {ω | (fun i => u (rtSigma r (𝔛 ω) (τ ω) i)) ∈ S} =
          ((Finset.univ.filter (fun π : Equiv.Perm (Fin N) => u ∘ π ∈ S)).card : ℝ≥0∞) *
            (Nat.factorial N : ℝ≥0∞)⁻¹

open scoped Classical in
/-- (a) Size: for any statistic `T` of the rank vector and any critical value `c` with
`#{π : T(u∘π) > c} ≤ α N!`, the test rejecting when `T(R̃) > c` has size `≤ α`. -/
def rt_size : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : ℕ) (𝔛 : Ω → Fin N → X) (τ : Ω → Equiv.Perm (Fin N))
    (r : (Fin N → X) → Equiv.Perm (Fin N)) (u : Fin N → Y) (T : (Fin N → Y) → ℝ) (c α : ℝ),
    Measurable 𝔛 → (∀ h, MeasurableSet {x | r x = h}) →
    (∀ t, MeasurableSet {ω | τ ω = t}) → (∀ t, P {ω | τ ω = t} = (Nat.factorial N : ℝ≥0∞)⁻¹) →
    (∀ B : Set (Fin N → X), MeasurableSet B → ∀ t,
      P ({ω | 𝔛 ω ∈ B} ∩ {ω | τ ω = t}) = P {ω | 𝔛 ω ∈ B} * P {ω | τ ω = t}) →
    (∀ π : Equiv.Perm (Fin N), P.map (fun ω => 𝔛 ω ∘ π) = P.map 𝔛) →
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin N) => c < T (u ∘ π))).card : ℝ) ≤
      α * (Nat.factorial N : ℝ) →
      P {ω | c < T (fun i => u (rtSigma r (𝔛 ω) (τ ω) i))} ≤ ENNReal.ofReal α

/-- (b) For fixed `x` and `π`, `σ̃(x∘π) ≐ σ̃(x)∘π` over the uniform shuffle `τ`. -/
def rt_equivariant : Prop :=
  ∀ (X : Type) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (τ : Ω → Equiv.Perm (Fin N)) (r : (Fin N → X) → Equiv.Perm (Fin N)),
    (∀ t, MeasurableSet {ω | τ ω = t}) → (∀ t, P {ω | τ ω = t} = (Nat.factorial N : ℝ≥0∞)⁻¹) →
      ∀ (x : Fin N → X) (π g : Equiv.Perm (Fin N)),
        P {ω | rtSigma r (x ∘ π) (τ ω) = g} = P {ω | rtSigma r x (τ ω) * π = g}

/-- (c) If `𝔯(𝔛∘π) = 𝔯(𝔛)∘π` a.s. for every `π`, then `σ̃ = 𝔯(𝔛)` a.s. (any `τ`). -/
def rt_equal : Prop :=
  ∀ (X : Type) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ) (𝔛 : Ω → Fin N → X)
    (τ : Ω → Equiv.Perm (Fin N)) (r : (Fin N → X) → Equiv.Perm (Fin N)),
    (∀ π : Equiv.Perm (Fin N), ∀ᵐ ω ∂P, r (𝔛 ω ∘ π) = r (𝔛 ω) * π) →
      ∀ᵐ ω ∂P, rtSigma r (𝔛 ω) (τ ω) = r (𝔛 ω)

/-- (d), the assignment step: an optimal assignment of the shuffled coefficients, composed with `τ⁻¹`, is an
optimal assignment of the original ones. -/
def rt_optimal_shift : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N : ℕ) (u z : Fin N → E)
    (σ t : Equiv.Perm (Fin N)), IsMin u (z ∘ t) σ → IsMin u z (σ * t⁻¹)

/-- (d) With reordering-invariant coefficients (`Zc(x∘τ) = Zc(x)∘τ`) and `𝔯` optimal, `σ̃` is optimal for the
original sample, for every shuffle. -/
def rt_optimal : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : Type) (N : ℕ) (u : Fin N → E)
    (Zc : (Fin N → X) → Fin N → E) (r : (Fin N → X) → Equiv.Perm (Fin N)),
    (∀ x (t : Equiv.Perm (Fin N)), Zc (x ∘ t) = Zc x ∘ t) → (∀ x, IsMin u (Zc x) (r x)) →
      ∀ x t, IsMin u (Zc x) (rtSigma r x t)

/-- (d), last sentence: with an order-dependent basis, `σ̃` is optimal for the coefficients of the original
sample in the basis computed from `𝔛∘τ`, namely `Zc(x∘t)∘t⁻¹`. -/
def rt_optimal_basis : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : Type) (N : ℕ) (u : Fin N → E)
    (Zc : (Fin N → X) → Fin N → E) (r : (Fin N → X) → Equiv.Perm (Fin N)),
    (∀ x, IsMin u (Zc x) (r x)) →
      ∀ x (t : Equiv.Perm (Fin N)), IsMin u (Zc (x ∘ t) ∘ ⇑t⁻¹) (rtSigma r x t)

/-! ### A `prop:T-proxy` -/

/-- Oracle inequality for the cross-fitted proxy, given `𝒜`: on a measurable event of probability
`≥ 1 − γ`, for every minimiser `θ̂` of `Ĉ_Υ` and every `θ`,
`𝓡(θ̂)^{1/2} ≤ 𝓡(θ)^{1/2} + 2β^{1/2} + 2R(8 log(2|Θ|/γ)/|𝓑|)^{1/4}`. -/
def tproxy_oracle : Prop :=
  ∀ (X F Θ : Type) [MeasurableSpace X] [NormedAddCommGroup F] [Fintype Θ] [Nonempty Θ]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (PK : Measure X)
    (m : ℕ) (Z : Fin m → Ω → X) (b : Fin m → Ω → F) (a : Θ → X → F) (c : X → F) (R γ : ℝ),
    0 < m → 0 < γ → γ < 1 → (∀ i, Measurable (Z i)) → iIndepFun Z P → (∀ i, P.map (Z i) = PK) →
    (∀ θ, Measurable (fun x => ‖a θ x - c x‖)) → (∀ θ x, ‖a θ x‖ ≤ R) → (∀ x, ‖c x‖ ≤ R) →
      ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - γ) ≤ P S ∧
        ∀ ω ∈ S, ∀ θhat : Θ,
          (∀ θ, msq (fun i => a θhat (Z i ω)) (fun i => b i ω) ≤
            msq (fun i => a θ (Z i ω)) (fun i => b i ω)) →
          ∀ θ, √(∫ x, ‖a θhat x - c x‖ ^ 2 ∂PK) ≤
            √(∫ x, ‖a θ x - c x‖ ^ 2 ∂PK) + 2 * √(msq (fun i => b i ω) (fun i => c (Z i ω))) +
              2 * R * (8 * Real.log (2 * Fintype.card Θ / γ) / m) ^ ((1 : ℝ) / 4)

/-! ### R `prop:depth-regions` -/

/-- Every region of content `≥ p` has robustness `≤ β*_K(p)`. -/
def depth_regions_optimal : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) (p : ℝ≥0∞)
    (A : Set (EuclideanSpace ℝ (Fin K))),
    p ≤ ν A → regionDepth ν A ≤ betaStar ν p

/-- For `α < β*_K(p)`, `D_α(ν)` has content `≥ p` and robustness `≥ α`. -/
def depth_regions_content : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) (p α : ℝ≥0∞),
    α < betaStar ν p → p ≤ ν (depthRegion ν α) ∧ α ≤ regionDepth ν (depthRegion ν α)

/-- `D_α(ν)` is closed and convex. -/
def depth_regions_closed_convex : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (α : ℝ≥0∞),
    IsClosed (depthRegion ν α) ∧ Convex ℝ (depthRegion ν α)

/-- `D_α(ν)` is compact for `α > 0`. -/
def depth_regions_compact : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (α : ℝ≥0∞),
    0 < α → IsCompact (depthRegion ν α)

/-- `h_{D_α}(v) = q_v` whenever `v ↦ q_v` is sublinear (`0 < α < 1`; lower semicontinuity not needed). -/
def depth_regions_support : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (α : ℝ≥0∞),
    0 < α → α < 1 →
    (∀ v w, dirQuantile ν α (v + w) ≤ dirQuantile ν α v + dirQuantile ν α w) →
    (∀ (s : ℝ) v, 0 < s → dirQuantile ν α (s • v) = s * dirQuantile ν α v) →
      ∀ v, supportFn (depthRegion ν α) v = dirQuantile ν α v

/-! ### B `thm:fixedK-df` (B copy) -/

open scoped Classical in
/-- Under the hypotheses of `thm:fixedK-df`, the rank vector `(u_{σ̂(i)})_i` is uniform over the `n!`
orderings: `P(R ∈ S) = #{π : u∘π ∈ S}/n!` for every `S` (every rank statistic is distribution-free). -/
def fixedK_rank_law : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (u : Fin n → E) (Z : Ω → Fin n → E) (sel : (Fin n → E) → Equiv.Perm (Fin n)),
    Measurable Z → (∀ z, IsMin u z (sel z)) → (∀ h, MeasurableSet {z | sel z = h}) →
    (∀ τ : Equiv.Perm (Fin n), P.map (fun ω => Z ω ∘ τ) = P.map Z) →
    (∀ᵐ ω ∂P, UniqueMin u (Z ω)) →
      ∀ S : Set (Fin n → E),
        P {ω | (fun i => u (sel (Z ω) i)) ∈ S} =
          ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => u ∘ π ∈ S)).card : ℝ≥0∞) *
            (Nat.factorial n : ℝ≥0∞)⁻¹

/-- iid sampling, distinct grid points and atomless one-dimensional projections of `P_K` give an a.s.
unique optimal assignment. -/
def fixedK_unique_of_atomless : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (u : Fin n → E) (Z : Ω → Fin n → E) (PK : Measure E),
    Measurable Z → iIndepFun (fun i ω => Z ω i) P → (∀ i, P.map (fun ω => Z ω i) = PK) →
    Function.Injective u → (∀ w : E, w ≠ 0 → ∀ c : ℝ, PK {z | ⟪w, z⟫_ℝ = c} = 0) →
      ∀ᵐ ω ∂P, UniqueMin u (Z ω)

/-- `P_K ∈ 𝒫^ℓ` ⇒ every one-dimensional projection of `P_K` is atomless (hyperplanes are Lipschitz
hypersurfaces). -/
def fixedK_pell_atomless : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] (PK : Measure E),
    PellClass PK → ∀ w : E, w ≠ 0 → ∀ c : ℝ, PK {z | ⟪w, z⟫_ℝ = c} = 0

/-! ### B `prop:rk-symmetry` -/

/-- (i) `T_G#P_K = P_K`. -/
def rk_sym_pushforward : Prop :=
  ∀ (K : ℕ) (PK μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure PK]
    [IsProbabilityMeasure μ] (F Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (G : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K)),
    Measurable F → Measurable Q → PK.map F = μ → μ.map Q = PK → μ.map G = μ →
      PK.map (symMap Q G F) = PK

/-- (ii) For `P_K`-a.e. `z`: `D^geom(T_G z) = D^geom(z)`, `D^prob(T_G z) = D^prob(z)` and
`S(F(T_G z)) = G S(F z)`. -/
def rk_sym_depth : Prop :=
  ∀ (K : ℕ) (PK μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure PK]
    [IsProbabilityMeasure μ] (F Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (G : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K))
    (ρ : EuclideanSpace ℝ (Fin K) → ℝ) (c : ℝ → ℝ),
    Measurable F → Measurable Q → PK.map F = μ → μ.map Q = PK →
    (∀ᵐ z ∂PK, Q (F z) = z) → (∀ᵐ u ∂μ, F (Q u) = u) → μ.map G = μ →
    (∀ᵐ u ∂μ, ρ (G u) = ρ u) →
      ∀ᵐ z ∂PK, depthGeom ρ F (symMap Q G F z) = depthGeom ρ F z ∧
        depthProb c ρ F (symMap Q G F z) = depthProb c ρ F z ∧
        signMap ρ (F (symMap Q G F z)) = G (signMap ρ (F z))

/-- (iii) For every law `C ≪ P_K`, the depth pair `(D^geom, D^prob)` has the same law under `C` and
under `T_G#C`. -/
def rk_sym_depth_law : Prop :=
  ∀ (K : ℕ) (PK μ C : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure PK]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure C]
    (F Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (G : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K))
    (ρ : EuclideanSpace ℝ (Fin K) → ℝ) (c : ℝ → ℝ),
    Measurable F → Measurable Q → Measurable ρ → Measurable c → PK.map F = μ → μ.map Q = PK →
    (∀ᵐ z ∂PK, Q (F z) = z) → (∀ᵐ u ∂μ, F (Q u) = u) → μ.map G = μ →
    (∀ᵐ u ∂μ, ρ (G u) = ρ u) → C ≪ PK →
      (C.map (symMap Q G F)).map (fun z => (depthGeom ρ F z, depthProb c ρ F z)) =
        C.map (fun z => (depthGeom ρ F z, depthProb c ρ F z))

/-- (iii) Two samples: the depth vectors of `(C^{⊗m}, (T_G#C)^{⊗m'})` have the law of those of
`(C^{⊗m}, C^{⊗m'})`; hence every depth-based two-sample test has power equal to its rejection probability
when both samples come from `C`. -/
def rk_sym_two_sample : Prop :=
  ∀ (K : ℕ) (PK μ C : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure PK]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure C]
    (F Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (G : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K))
    (ρ : EuclideanSpace ℝ (Fin K) → ℝ) (c : ℝ → ℝ) (m m' : ℕ),
    Measurable F → Measurable Q → Measurable ρ → Measurable c → PK.map F = μ → μ.map Q = PK →
    (∀ᵐ z ∂PK, Q (F z) = z) → (∀ᵐ u ∂μ, F (Q u) = u) → μ.map G = μ →
    (∀ᵐ u ∂μ, ρ (G u) = ρ u) → C ≪ PK →
      ((Measure.pi fun _ : Fin m => C).prod (Measure.pi fun _ : Fin m' => C.map (symMap Q G F))).map
          (fun xy => ((fun i => (depthGeom ρ F (xy.1 i), depthProb c ρ F (xy.1 i))),
            (fun j => (depthGeom ρ F (xy.2 j), depthProb c ρ F (xy.2 j))))) =
        ((Measure.pi fun _ : Fin m => C).prod (Measure.pi fun _ : Fin m' => C)).map
          (fun xy => ((fun i => (depthGeom ρ F (xy.1 i), depthProb c ρ F (xy.1 i))),
            (fun j => (depthGeom ρ F (xy.2 j), depthProb c ρ F (xy.2 j)))))

/-- (iv) `S#(F#(T_G#C)) = G#(S#(F#C))`, and the two sign laws coincide iff `S#(F#C)` is `G`-invariant. -/
def rk_sym_sign : Prop :=
  ∀ (K : ℕ) (PK μ C : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure PK]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure C]
    (F Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (G : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K))
    (ρ : EuclideanSpace ℝ (Fin K) → ℝ),
    Measurable F → Measurable Q → Measurable ρ → PK.map F = μ → μ.map Q = PK →
    (∀ᵐ z ∂PK, Q (F z) = z) → (∀ᵐ u ∂μ, F (Q u) = u) → μ.map G = μ →
    (∀ᵐ u ∂μ, ρ (G u) = ρ u) → C ≪ PK →
      ((C.map (symMap Q G F)).map F).map (signMap ρ) = ((C.map F).map (signMap ρ)).map G ∧
      (((C.map (symMap Q G F)).map F).map (signMap ρ) = (C.map F).map (signMap ρ) ↔
        ((C.map F).map (signMap ρ)).map G = (C.map F).map (signMap ρ))

/-! ### B `prop:pop-band-coverage` -/

/-- The population band has simultaneous coverage: the event `{𝔪 + ⟨e(·), Π_K X⟩ ∈ B^pop}` is measurable and
has probability `≥ μ_K(A)` (`= p` for `A = A_{K,p}`), with no injectivity or continuity of `Q`. -/
def pop_band_coverage : Prop :=
  ∀ (K : ℕ) (𝒯 Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Zc : Ω → Fin K → ℝ) (μ : Measure (Fin K → ℝ)) [IsProbabilityMeasure μ]
    (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (mo : 𝒯 → ℝ) (e : 𝒯 → Fin K → ℝ),
    Measurable Zc → Measurable Q → MeasurableSet A → P.map Zc = μ.map Q →
      MeasurableSet {ω | curve mo e (Zc ω) ∈
        band (fun t => popLo μ Q A (mo t) (e t)) (fun t => popUp μ Q A (mo t) (e t))} ∧
      μ A ≤ P {ω | curve mo e (Zc ω) ∈
        band (fun t => popLo μ Q A (mo t) (e t)) (fun t => popUp μ Q A (mo t) (e t))}

/-! ### B `lem:cal-no-l2` -/

/-- No `φ` with `φ(s) → 0` as `s ↓ 0` bounds the sup-norm residual by the `L²` residual:
`‖x − P^rec_K x‖_∞ ≤ φ(‖x − P^rec_K x‖_H)` fails for some `x ∈ H ∩ L^∞`. -/
def cal_no_l2 : Prop :=
  ∀ (K : ℕ) (e : Fin K → ℝ → ℝ) (C : ℝ), (∀ k, Measurable (e k)) → (∀ k t, |e k t| ≤ C) →
    ¬ ∃ φ : ℝ → ℝ, Tendsto φ (𝓝[>] 0) (𝓝 0) ∧
      ∀ x : ℝ → ℝ, MemLp x 2 (volume.restrict (Icc (0 : ℝ) 1)) →
        MemLp x ⊤ (volume.restrict (Icc (0 : ℝ) 1)) →
        (eLpNorm (x - precK e x) ⊤ (volume.restrict (Icc (0 : ℝ) 1))).toReal ≤
          φ ((eLpNorm (x - precK e x) 2 (volume.restrict (Icc (0 : ℝ) 1))).toReal)

end Claims
end StatFormal.OTFD.Wave5a
