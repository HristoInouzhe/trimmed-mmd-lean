import StatFormal.Archive.RobustEquality.Certificate.Statements
import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import StatFormal.Archive.OTFD.Wave6b.Statements
import TauCeti.Probability.Quantile
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Fintype.Perm

/-!
# FROZEN STATEMENTS — wave 7b (QUEUE rows 66–70): otfd G `lem:stratified`, T `eq:bilip` (`prop:distortion`);
# robust equality JASA `prop:tight`, `prop:exact`, `lem:convex`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-G_geodesic.md`, `otfd-T_tangent.md`,
`robust-equality-jasa.md`; current text after the 2026-10-13/14 corrections; otfd paths under `otfd/papers/`,
robust-equality paths under `robust-equality-outcomes-under-distribution-shift/jasa/`):
* otfd G `lem:stratified` (`G_geodesic/appendix.tex:558-581`, proof `:583-620`), with `def:reference`
  (`G_geodesic/main.tex:323-332`: `V = τ G/‖G‖`, `τ ∼ Unif[0,1]`, `G ∼ N(0,Σ)` independent, `μ = 𝓛(V)`).
* otfd T `prop:distortion` / `eq:bilip`, `eq:neargeo` (`T_tangent/supp_moved.tex:23-42`, proof
  `T_tangent/app_proofs.tex:317-330`), with `prop:sphere` (`supp_moved.tex:4-20`, frozen in `OTFD/Wave6b`).
* robust equality `prop:tight` (`supp_proofs.tex:412-423`, proof `:425-429`), with `thm:certificate` (frozen).
* robust equality `prop:exact` (`main.tex:209-215`, proof `supp_proofs.tex:129-137`), with `eq:robust`
  (`main.tex:198-201`).
* robust equality `lem:convex` (`supp_proofs.tex:106-112`, proof `:114-125`), with the conventions
  (`supp_proofs.tex:5-45`: `OT_ε(μ,Q) = inf_{γ∈Π(μ,Q)} E_γ c + ε KL(γ‖μ⊗Q)`, labelled atoms, `B_c = sup c`).
Reuses the frozen `RobustEquality/Statements.lean` (`klRef`), `RobustEquality/Certificate/Statements.lean`
(`centre`), `RobustEquality/SemidualStrong/Statements.lean` (`OTdisc`, `muDisc`) and `OTFD/Wave6b/Statements.lean`
(`sphDist`, `sphExp`), imported, not copied.

Covered:
* `lem:stratified`: `stratified_law` ((a): every `V_l` has law `μ`, and `‖V_l‖ ≤ 1` a.s. for unit directions),
  `stratified_bound` ((b): `E‖r⁻¹Σψ(V_l) − μψ‖² ≤ (1 + 2⌊r/2⌋/r)Var_μψ/r ≤ 2Var_μψ/r ≤ 2 sup‖ψ‖²/r`),
  `stratified_sharp` ((b), last sentence: equality for even `r` and `ψ = ψ₀(v/‖v‖)`, `ψ₀` even),
  `stratified_iid` ((c): without pairing the left side equals `(Var_μψ − V̄)/r ≤ Var_μψ/r`),
  `stratified_conditional` ((d): (b) and (c) integrated against an independent `χ ∼ ξ`).
* `prop:distortion`: `bilip` (`eq:bilip`, both sides, every `0 < r < π`), `bilip_sharp` (the factor is approached by
  nearby points at radius `r`, on `S^d`, `d ≥ 2`), `distortion_cost` (`a_r² J₀ ≤ J_g ≤ J₀`), `neargeo`
  (`eq:neargeo`, subtraction-free in `ℝ≥0∞`), `neargeo_real` (`eq:neargeo` as printed, in `ℝ`).
* `prop:tight`: `tight_line` (equality in the three-term triangle inequality iff the quantile increments are
  nonnegative multiples of one `L²(0,1)` function), `tight_line_direction` (when the middle distance is `> 0`, the
  function is the nominal direction), `tight` (both, for `h#Q₀, h#P̂₀, h#P̂₁, h#Q₁`, `h` bounded measurable).
* `prop:exact`: `exact_line` (Kantorovich duality on `ℝ` with bounded continuous potentials feasible on all of `ℝ²`,
  for laws carried by a compact interval), `exact` (the representation of `F(h)`, for any sets `𝔅₀, 𝔅₁`).
* `lem:convex`: `convex_left`, `convex_right` ((i), both arguments), `bdd_diff_left`, `bdd_diff_right` ((ii), both
  arguments: `|OT_ε(μ,Q) − OT_ε(μ',Q)| ≤ B_c/n` and the same for `OT_ε(Q,·)`).

Not covered (declared):
* `lem:stratified`: the Gaussian `N(0,Σ)` on `H_m` itself (abstracted, see Encodings); the remark on the package's
  implementation after the proof; the closing sentence of (b)'s proof "`Var_μψ ≤ sup‖ψ‖²`" is used, not stated.
* `prop:distortion`: the "faithful logarithmic chart" (needed only to read `J_g` as the geodesic cost of the curves,
  which here is the definition); existence of the minimisers `π₀, π_g` (assumed, as printed); the sentences after
  the proposition (Rauch comparison, `π/2`, experiment T5).
* `prop:tight`: the remarks after the proof (coupling-step slack, the numbers 24.7/11.5/8.3, translation families).
* `prop:exact`: the remark that maximising parameterised potentials gives lower bounds (prose).
* `lem:convex`: `OT_ε(P̂,Q)` for an empirical centre written over `K × K` (ties merged); (ii) is stated in the
  labelled-atom form the paper's proof uses (see Encodings).

Encodings (see card):
* `lem:stratified`: `H` any real inner-product space with Borel σ-algebra and second-countable topology (paper:
  `H_m`, separable Hilbert); `E` any complete real inner-product space (paper: `ℝ` or separable Hilbert); `ψ` strongly
  measurable with `‖ψ‖ ≤ C` ("bounded and Borel"; `sup‖ψ‖` is any bound `C`). The direction law is abstracted to
  any probability `ρ` on `H` with `ρ ∘ (−·)⁻¹ = ρ` (`SymmDir`; for `ρ = 𝓛(G/‖G‖)` this is `G =ᵈ −G`, the only
  property of the Gaussian the proof uses: queue note), with `‖θ‖ = 1` `ρ`-a.s. assumed only for `‖V_l‖ ≤ 1`.
  `μ = refLaw ρ = (Unif[0,1] ⊗ ρ)∘(τ,θ ↦ τθ)⁻¹`. Draws are 0-indexed: `θ_l = Θ_l` for `l < h = ⌈r/2⌉ = (r+1)/2`,
  `θ_l = −Θ_{l−h}` otherwise (`antiDir`), `τ_l = (π(l) + U_l)/r` with `π(l) ∈ {0,…,r−1}` (`stratRadius`); the
  uniform permutation is the finite average `(r!)⁻¹ Σ_π`, `U ∼ Unif[0,1]^r` and `Θ ∼ ρ^{⊗h}` are `Measure.pi`; the
  expectation `E‖·‖²` is the iterated lower integral of `ofReal ‖·‖²` (`stratMSE`, no integrability junk; it equals
  the Bochner expectation, which the route computes). (a) is a measure identity (the mixture over `π` of the laws
  of `V_l`); (c) uses i.i.d. `Θ ∼ ρ^{⊗r}`, `θ_l = Θ_l`, and `a_j = r ∫_{j/r}^{(j+1)/r} φ − μψ`, `φ(u) = ∫ψ(uθ)dρ`
  (`stratA`, set integral over `Icc`), `V̄ = r⁻¹Σ_j‖a_j‖²` (`stratVbar`). (d): `χ` ranges over a probability space
  `(X, ξ)`, `ψ : X → H → E` with `uncurry ψ` strongly measurable and `‖ψ_χ‖ ≤ C`; "conditionally on `χ`" is the
  bound/identity integrated over `ξ` (the joint expectation, by Fubini, since `χ` is independent of the draws).
* `prop:distortion`: `S^d ⊂ ℝ^{d+1}` with the frozen `Wave6b` encoding (`sphDist = arccos⟨·,·⟩`, `sphExp`, tangent
  `⟨x,v⟩ = 0`). Fields over a time space `(T, λ)` (any measure), base curve `m : T → S^d`; a plan is a measure `π` on
  any measurable space `Z` of pairs, with the two fields `U z, V z : T → ℝ^{d+1}` (for couplings of field laws take
  `Z = H₀ × H₀`). `J₀(π) = ½∫∫_T‖u − v‖² dλ dπ`, `J_g(π) = ½∫∫_T d(Exp_m u, Exp_m v)² dλ dπ` as lower integrals
  in `ℝ≥0∞` (no measurability needed, no junk). "Bounded pointwise by `r`" is `BoundedTangent` (`π`-a.e. pair,
  `λ`-a.e. time: tangent and norm `≤ r`). "`π₀` minimises `J₀`, `π_g` minimises `J_g`" is over an arbitrary common set
  `Π` of such plans (a generalisation of the coupling set). `a_r = sin r / r`. `neargeo_real` adds `J₀(π₀) < ∞`
  (automatic for bounded fields and finite `λ`) so that `toReal` is not junk.
* `prop:tight`: laws on `ℝ` are probability measures; `q_μ` is Tau Ceti's `Measure.quantile`; `L²([0,1])` is
  `L²(volume|(0,1))` (`unitI`), and "nonnegative multiples of one function" is `Aligned` (a.e. equalities with an
  `L²` function `g` and coefficients `a, b, c ≥ 0`). `tight_line` assumes the three `W₂` finite (for laws with finite
  second moments this holds; it is the weaker hypothesis); `tight` is the certificate setting (frozen `centre`,
  `n_s > 0`, `h` bounded measurable, any probability laws `Q_s`, not only members of `𝔅_s`), where all `W₂` are
  finite. `Δ(h) = W₂(h#P̂₀, h#P̂₁)`. Equalities of `W₂` are in `ℝ≥0∞` (Tau Ceti `wassersteinEDist 2`).
* `prop:exact`: `K` any measurable space (paper: compact `K ⊂ ℝ^d`), `h` measurable with `|h| ≤ H`, `𝔅_s` any sets of
  probability measures; `Φ_b` is pairs of `ℝ →ᵇ ℝ` with `φ(u) + ψ(v) ≤ (u − v)²` for all `u, v ∈ ℝ` (`phiB`).
  `F(h)` and the right side are suprema in `EReal` (`worstF`, `dualF`; `⊥` for an empty set on both sides, so "any
  sets" includes `∅` without junk).
* `lem:convex`: `OT_ε` is `otEnt` (infimum in `EReal` over probability couplings on `K × K` of
  `∫c dγ + ε klRef(γ‖μ⊗Q)`, the frozen `OTdisc` convention), `K` any measurable space, `c` jointly measurable with
  `0 ≤ c ≤ B` (`CostSetting`; paper `c = ‖x − x'‖²`, `B = B_c`), `ε > 0`; mixtures `θμ + (1−θ)μ'` use
  `ENNReal.ofReal` weights. (ii): "uniform on `n` labelled atoms" is the frozen `OTdisc` with weights `1/n` and cost
  rows `c(x_i,·)` (first argument), resp. `otDiscR` (couplings on `K × Fin n`, rows `c(·, x_i)`, second argument);
  "differ in one atom" is `x' = Function.update x k y`; the result gives both values as reals.
Critic notes:
* `lem:stratified` holds as printed. The route centres each draw at its stratum mean, so the paper's non-partner
  covariance `−V̄/(r−1)` appears as `0` plus the `−‖b_j‖²` terms; the proof of `stratified_sharp` shows the first
  inequality of (b) is an equality for every `r` (constant `2 − 1/r` for odd `r`), not only for even `r`.
* `prop:distortion` holds as printed for `d ≥ 2`. The sharpness sentence fails on the circle `S¹` (`d = 1`): for
  `r ≤ π/2`, tangent vectors at `x` are `a e, b e`, `Exp_x(ae) = cos a·x + sin a·e`, so `d = |a − b| = ‖v − w‖` and the
  ratio is `1 > sin r / r`; `bilip_sharp` therefore assumes `d ≥ 2` (the bound itself holds for every `d`).
* `prop:tight`, `prop:exact`, `lem:convex` hold as printed. `prop:exact`'s duality uses potentials feasible on all of
  `ℝ²` (the queue check): continuous potentials on `[−H,H]` are extended by the `1`-Lipschitz projection.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. `lem:stratified`: the proof uses only `G =ᵈ −G` and independence, so any
  symmetric `ρ` is a genuine generalisation; equality in `stratified_sharp` holds for every `r` (the paper's "even `r`"
  is correct, just not strongest); (d) is (b),(c) integrated over `ξ`, as the paper's "apply and integrate".
  T `prop:distortion`: the sharpness sentence ("`sin r/r` is approached by nearby points at radius `r`") is false on
  `S¹` (ratio `1`; overall infimum `min(1,(π−r)/r) > sin r/r`) — DEFECTS #41 (S3, `d ≥ 2` missing); `d ≥ 2` is not a
  standing assumption (`sec_tangent_theory.tex:433` works on `S¹`). `neargeo` in ℝ≥0∞ is equivalent to the printed form.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave7b

open StatFormal.RobustEquality StatFormal.RobustEquality.Certificate

/-! ### otfd G `lem:stratified` -/

section Stratified

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The uniform law on `[0,1]`. -/
def unif01 : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- The reference law `μ = 𝓛(τθ)`, `τ ∼ Unif[0,1]` independent of the direction `θ ∼ ρ`
(`def:reference` with the direction law `ρ = 𝓛(G/‖G‖)` abstracted). -/
def refLaw (ρ : Measure H) : Measure H := (unif01.prod ρ).map fun p => p.1 • p.2

/-- Antithetic directions: `θ_l = Θ_l` for `l < h = ⌈r/2⌉` and `θ_l = −Θ_{l−h}` for `l ≥ h` (0-indexed). -/
def antiDir (r : ℕ) (Θ : Fin ((r + 1) / 2) → H) (l : Fin r) : H :=
  if hl : (l : ℕ) < (r + 1) / 2 then Θ ⟨l, hl⟩ else -Θ ⟨(l : ℕ) - (r + 1) / 2, by omega⟩

/-- Stratified radii `τ_l = (π(l) + U_l)/r` (0-indexed strata `π(l) ∈ {0,…,r−1}`). -/
def stratRadius (r : ℕ) (σ : Equiv.Perm (Fin r)) (U : Fin r → ℝ) (l : Fin r) : ℝ :=
  (((σ l : ℕ) : ℝ) + U l) / r

/-- `E‖r⁻¹ Σ_l ψ(V_l) − m‖²` for `V_l = τ_l θ_l`, the permutation uniform (a finite average), `U ∼ Unif[0,1]^r`,
and directions `θ = dir D`, `D ∼ κ`, all independent (iterated lower integrals: no integrability junk). -/
def stratMSE (r : ℕ) {D : Type*} [MeasurableSpace D] (κ : Measure D) (dir : D → Fin r → H)
    (ψ : H → E) (m : E) : ℝ≥0∞ :=
  ((Fintype.card (Equiv.Perm (Fin r)) : ℝ≥0∞))⁻¹ * ∑ σ : Equiv.Perm (Fin r),
    ∫⁻ U, ∫⁻ Θ, ENNReal.ofReal (‖(r : ℝ)⁻¹ • ∑ l, ψ (stratRadius r σ U l • dir Θ l) - m‖ ^ 2) ∂κ
      ∂(Measure.pi fun _ : Fin r => unif01)

/-- `Var_μ ψ = ∫ ‖ψ − μψ‖² dμ`. -/
def varMu (μ : Measure H) (ψ : H → E) : ℝ := ∫ v, ‖ψ v - ∫ w, ψ w ∂μ‖ ^ 2 ∂μ

/-- `a_j = r ∫_{j/r}^{(j+1)/r} φ(u) du − μψ` with `φ(u) = E ψ(uθ)`, `θ ∼ ρ` (0-indexed strata). -/
def stratA (r : ℕ) (ρ : Measure H) (ψ : H → E) (j : Fin r) : E :=
  (r : ℝ) • (∫ u in Icc ((j : ℝ) / r) (((j : ℝ) + 1) / r), ∫ θ, ψ (u • θ) ∂ρ) - ∫ w, ψ w ∂(refLaw ρ)

/-- `V̄ = r⁻¹ Σ_j ‖a_j‖²`. -/
def stratVbar (r : ℕ) (ρ : Measure H) (ψ : H → E) : ℝ := (r : ℝ)⁻¹ * ∑ j, ‖stratA r ρ ψ j‖ ^ 2

/-- The direction law is symmetric (`θ =ᵈ −θ`), the only property of `G/‖G‖` the proof uses. -/
def SymmDir (ρ : Measure H) : Prop := ρ.map (fun θ => -θ) = ρ

end Stratified

/-! ### otfd T `prop:distortion` (`eq:bilip`, `eq:neargeo`) -/

section Distortion

open StatFormal.OTFD.Wave6b

variable {Z T : Type*} [MeasurableSpace Z] [MeasurableSpace T] {d : ℕ}

/-- `J₀(π) = ½ ∫ ‖u − v‖²_{H₀} dπ`, `‖u − v‖²_{H₀} = ∫_T ‖u(t) − v(t)‖² dλ(t)`; the pair of fields of `z` is
`(U z, V z)`. -/
def jZero (lam : Measure T) (U V : Z → T → EuclideanSpace ℝ (Fin (d + 1))) (π : Measure Z) : ℝ≥0∞ :=
  2⁻¹ * ∫⁻ z, ∫⁻ t, ENNReal.ofReal (‖U z t - V z t‖ ^ 2) ∂lam ∂π

/-- `J_g(π) = ½ ∫ D₂(E_m u, E_m v)² dπ`, `D₂(x,y)² = ∫_T d_{S^d}(x(t), y(t))² dλ(t)`, `E_m u (t) = Exp_{m(t)} u(t)`. -/
def jGeo (lam : Measure T) (m : T → EuclideanSpace ℝ (Fin (d + 1)))
    (U V : Z → T → EuclideanSpace ℝ (Fin (d + 1))) (π : Measure Z) : ℝ≥0∞ :=
  2⁻¹ * ∫⁻ z, ∫⁻ t, ENNReal.ofReal (sphDist (sphExp (m t) (U z t)) (sphExp (m t) (V z t)) ^ 2) ∂lam ∂π

/-- Both fields of `π`-a.e. pair are tangent along `m` and bounded pointwise by `r` (for `λ`-a.e. time). -/
def BoundedTangent (lam : Measure T) (m : T → EuclideanSpace ℝ (Fin (d + 1)))
    (U V : Z → T → EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (π : Measure Z) : Prop :=
  ∀ᵐ z ∂π, ∀ᵐ t ∂lam, ⟪m t, U z t⟫_ℝ = 0 ∧ ⟪m t, V z t⟫_ℝ = 0 ∧ ‖U z t‖ ≤ r ∧ ‖V z t‖ ≤ r

end Distortion

/-! ### robust equality `prop:tight` -/

/-- The uniform law on `(0,1)`, the domain of quantile functions. -/
def unitI : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- Three functions are nonnegative multiples of one function of `L²(0,1)`. -/
def Aligned (f₁ f₂ f₃ : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, MemLp g 2 unitI ∧ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
    f₁ =ᵐ[unitI] (fun t => a * g t) ∧ f₂ =ᵐ[unitI] (fun t => b * g t) ∧ f₃ =ᵐ[unitI] (fun t => c * g t)

/-- The three increments `q_{m₀} − q_{μ₀}`, `q_{m₁} − q_{m₀}`, `q_{μ₁} − q_{m₁}` are nonnegative multiples of the
middle one (the nominal direction). -/
def AlignedNominal (f₁ f₂ f₃ : ℝ → ℝ) : Prop :=
  ∃ a c : ℝ, 0 ≤ a ∧ 0 ≤ c ∧ f₁ =ᵐ[unitI] (fun t => a * f₂ t) ∧ f₃ =ᵐ[unitI] (fun t => c * f₂ t)

/-- The quantile increment `t ↦ q_ν(t) − q_μ(t)`. -/
def qInc (μ ν : Measure ℝ) : ℝ → ℝ := fun t => ν.quantile t - μ.quantile t

/-! ### robust equality `prop:exact` -/

/-- `Φ_b`: pairs of bounded continuous functions on `ℝ` with `φ(u) + ψ(v) ≤ |u − v|²`. -/
def phiB : Set ((ℝ →ᵇ ℝ) × (ℝ →ᵇ ℝ)) := {p | ∀ u v : ℝ, p.1 u + p.2 v ≤ (u - v) ^ 2}

/-- The worst-case disparity `F(h) = sup_{Q₀∈𝔅₀, Q₁∈𝔅₁} W₂²(h#Q₀, h#Q₁)`, in `EReal` (`⊥` for an empty set). -/
def worstF {K : Type*} [MeasurableSpace K] (h : K → ℝ) (B₀ B₁ : Set (Measure K)) : EReal :=
  ⨆ Q₀ ∈ B₀, ⨆ Q₁ ∈ B₁, (((wassersteinEDist 2 (Q₀.map h) (Q₁.map h)) ^ 2 : ℝ≥0∞) : EReal)

/-- The dual side `sup_{(φ,ψ)∈Φ_b} [sup_{Q₀} E_{Q₀} φ∘h + sup_{Q₁} E_{Q₁} ψ∘h]`, in `EReal`. -/
def dualF {K : Type*} [MeasurableSpace K] (h : K → ℝ) (B₀ B₁ : Set (Measure K)) : EReal :=
  ⨆ p ∈ phiB, ((⨆ Q₀ ∈ B₀, ((∫ z, p.1 (h z) ∂Q₀ : ℝ) : EReal)) + ⨆ Q₁ ∈ B₁, ((∫ z, p.2 (h z) ∂Q₁ : ℝ) : EReal))

/-! ### robust equality `lem:convex` -/

/-- `OT_ε(μ, Q) = inf_{γ ∈ Π(μ,Q)} E_γ c + ε KL(γ ‖ μ⊗Q)`, in `EReal` (`KL` = the paper's `klRef`). -/
def otEnt {K : Type*} [MeasurableSpace K] (ε : ℝ) (c : K → K → ℝ) (μ Q : Measure K) : EReal :=
  sInf {v | ∃ γ : Measure (K × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = μ ∧ γ.map Prod.snd = Q ∧
    v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) + (ε : EReal) * klRef γ (μ.prod Q)}

/-- `OT_ε(Q, μ)` with the discrete **second** marginal `μ = Σ_i a_i δ_i` on labels (cost row `c_i(y) = c(y, x_i)`). -/
def otDiscR {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) : EReal :=
  sInf {v | ∃ γ : Measure (K × Fin k), IsProbabilityMeasure γ ∧ γ.map Prod.fst = Q ∧
    γ.map Prod.snd = StatFormal.RobustEquality.Semidual.muDisc a ∧
    v = ((∫ z, c z.2 z.1 ∂γ : ℝ) : EReal) +
      (ε : EReal) * klRef γ (Q.prod (StatFormal.RobustEquality.Semidual.muDisc a))}

/-- The cost setting: `c` jointly measurable with `0 ≤ c ≤ B` (paper: `c = ‖x − x'‖²` on compact `K`, `B = B_c`). -/
def CostSetting {K : Type*} [MeasurableSpace K] (c : K → K → ℝ) (B : ℝ) : Prop :=
  Measurable (Function.uncurry c) ∧ (∀ x y, 0 ≤ c x y) ∧ ∀ x y, c x y ≤ B

namespace Claims

open StatFormal.OTFD.Wave6b StatFormal.RobustEquality.SemidualStrong

/-! #### `lem:stratified` -/

/-- `lem:stratified`(a): every `V_l` has law `μ` (law of `V_l` under the uniform permutation and the independent draws),
and `‖V_l‖ ≤ 1` a.s. when the directions are unit vectors. -/
def stratified_law : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (r : ℕ) (ρ : Measure H) [IsProbabilityMeasure ρ],
    2 ≤ r → SymmDir ρ → ∀ l : Fin r,
      ((Fintype.card (Equiv.Perm (Fin r)) : ℝ≥0∞))⁻¹ • ∑ σ : Equiv.Perm (Fin r),
          ((Measure.pi fun _ : Fin r => unif01).prod (Measure.pi fun _ : Fin ((r + 1) / 2) => ρ)).map
            (fun p => stratRadius r σ p.1 l • antiDir r p.2 l) = refLaw ρ ∧
        ((∀ᵐ θ ∂ρ, ‖θ‖ = 1) → ∀ σ : Equiv.Perm (Fin r),
          ∀ᵐ p ∂((Measure.pi fun _ : Fin r => unif01).prod (Measure.pi fun _ : Fin ((r + 1) / 2) => ρ)),
            ‖stratRadius r σ p.1 l • antiDir r p.2 l‖ ≤ 1)

/-- `lem:stratified`(b): `E‖r⁻¹ Σ ψ(V_l) − μψ‖² ≤ (1 + 2⌊r/2⌋/r) Var_μψ / r ≤ 2 Var_μψ / r ≤ 2 sup‖ψ‖² / r`. -/
def stratified_bound : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (r : ℕ) (ρ : Measure H) [IsProbabilityMeasure ρ] (ψ : H → E) (C : ℝ),
    2 ≤ r → SymmDir ρ → StronglyMeasurable ψ → (∀ v, ‖ψ v‖ ≤ C) →
      stratMSE r (Measure.pi fun _ : Fin ((r + 1) / 2) => ρ) (antiDir r) ψ (∫ w, ψ w ∂(refLaw ρ)) ≤
          ENNReal.ofReal ((1 + 2 * ((r / 2 : ℕ) : ℝ) / r) * varMu (refLaw ρ) ψ / r) ∧
        (1 + 2 * ((r / 2 : ℕ) : ℝ) / r) * varMu (refLaw ρ) ψ / r ≤ 2 * varMu (refLaw ρ) ψ / r ∧
        2 * varMu (refLaw ρ) ψ / r ≤ 2 * C ^ 2 / r

/-- `lem:stratified`(b), sharpness: for even `r` and `ψ(v) = ψ₀(v/‖v‖)` with `ψ₀` even, the first inequality of (b)
is an equality (so the constant `2` cannot be improved). -/
def stratified_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (r : ℕ) (ρ : Measure H) [IsProbabilityMeasure ρ] (ψ₀ : H → E) (C : ℝ),
    2 ≤ r → Even r → SymmDir ρ → StronglyMeasurable ψ₀ → (∀ v, ‖ψ₀ v‖ ≤ C) → (∀ u, ψ₀ (-u) = ψ₀ u) →
      stratMSE r (Measure.pi fun _ : Fin ((r + 1) / 2) => ρ) (antiDir r) (fun v => ψ₀ (‖v‖⁻¹ • v))
          (∫ w, ψ₀ (‖w‖⁻¹ • w) ∂(refLaw ρ)) =
        ENNReal.ofReal ((1 + 2 * ((r / 2 : ℕ) : ℝ) / r) * varMu (refLaw ρ) (fun v => ψ₀ (‖v‖⁻¹ • v)) / r)

/-- `lem:stratified`(c): without antithetic pairing (i.i.d. directions) the left side of (b) equals
`(Var_μψ − V̄)/r ≤ Var_μψ / r`. -/
def stratified_iid : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (r : ℕ) (ρ : Measure H) [IsProbabilityMeasure ρ] (ψ : H → E) (C : ℝ),
    2 ≤ r → StronglyMeasurable ψ → (∀ v, ‖ψ v‖ ≤ C) →
      stratMSE r (Measure.pi fun _ : Fin r => ρ) id ψ (∫ w, ψ w ∂(refLaw ρ)) =
          ENNReal.ofReal ((varMu (refLaw ρ) ψ - stratVbar r ρ ψ) / r) ∧
        (varMu (refLaw ρ) ψ - stratVbar r ρ ψ) / r ≤ varMu (refLaw ρ) ψ / r

/-- `lem:stratified`(d): (b) and (c) hold conditionally on an independent `χ ∼ ξ`, for `ψ_χ` jointly measurable and
bounded: integrated over `χ`, the joint mean square error obeys the bound of (b) and the identity of (c). -/
def stratified_conditional : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Type) [MeasurableSpace X] (ξ : Measure X) [IsProbabilityMeasure ξ]
    (r : ℕ) (ρ : Measure H) [IsProbabilityMeasure ρ] (ψ : X → H → E) (C : ℝ),
    2 ≤ r → SymmDir ρ → StronglyMeasurable (Function.uncurry ψ) → (∀ χ v, ‖ψ χ v‖ ≤ C) →
      (∫⁻ χ, stratMSE r (Measure.pi fun _ : Fin ((r + 1) / 2) => ρ) (antiDir r) (ψ χ)
            (∫ w, ψ χ w ∂(refLaw ρ)) ∂ξ ≤
          ENNReal.ofReal ((1 + 2 * ((r / 2 : ℕ) : ℝ) / r) / r * ∫ χ, varMu (refLaw ρ) (ψ χ) ∂ξ)) ∧
        ∫⁻ χ, stratMSE r (Measure.pi fun _ : Fin r => ρ) id (ψ χ) (∫ w, ψ χ w ∂(refLaw ρ)) ∂ξ =
          ENNReal.ofReal ((∫ χ, varMu (refLaw ρ) (ψ χ) ∂ξ - ∫ χ, stratVbar r ρ (ψ χ) ∂ξ) / r)

/-! #### `eq:bilip`, `eq:neargeo` -/

/-- `eq:bilip`: for `0 < r < π` and tangent `v, w` of norm `≤ r` at a point `x` of `S^d`,
`(sin r / r)‖v − w‖ ≤ d_{S^d}(Exp_x v, Exp_x w) ≤ ‖v − w‖`. -/
def bilip : Prop :=
  ∀ (d : ℕ) (x v w : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ), 0 < r → r < Real.pi →
    ‖x‖ = 1 → ⟪x, v⟫_ℝ = 0 → ⟪x, w⟫_ℝ = 0 → ‖v‖ ≤ r → ‖w‖ ≤ r →
      Real.sin r / r * ‖v - w‖ ≤ sphDist (sphExp x v) (sphExp x w) ∧
        sphDist (sphExp x v) (sphExp x w) ≤ ‖v - w‖

/-- `prop:distortion`, sharpness: on `S^d`, `d ≥ 2`, the factor `sin r / r` is approached by nearby points at
radius `r`. -/
def bilip_sharp : Prop :=
  ∀ (d : ℕ) (r η : ℝ), 2 ≤ d → 0 < r → r < Real.pi → 0 < η →
    ∃ x v w : EuclideanSpace ℝ (Fin (d + 1)), ‖x‖ = 1 ∧ ⟪x, v⟫_ℝ = 0 ∧ ⟪x, w⟫_ℝ = 0 ∧ ‖v‖ = r ∧ ‖w‖ = r ∧
      0 < ‖v - w‖ ∧ ‖v - w‖ < η ∧ sphDist (sphExp x v) (sphExp x w) < (Real.sin r / r + η) * ‖v - w‖

/-- `prop:distortion`: the cost sandwich `a_r² J₀ ≤ J_g ≤ J₀`, `a_r = sin r / r`, for every plan carried by
tangent fields bounded by `r`. -/
def distortion_cost : Prop :=
  ∀ (d : ℕ) (Z T : Type) [MeasurableSpace Z] [MeasurableSpace T] (lam : Measure T)
    (m : T → EuclideanSpace ℝ (Fin (d + 1))) (U V : Z → T → EuclideanSpace ℝ (Fin (d + 1)))
    (r : ℝ) (π : Measure Z),
    0 < r → r < Real.pi → (∀ t, ‖m t‖ = 1) → BoundedTangent lam m U V r π →
      ENNReal.ofReal ((Real.sin r / r) ^ 2) * jZero lam U V π ≤ jGeo lam m U V π ∧
        jGeo lam m U V π ≤ jZero lam U V π

/-- `eq:neargeo` (subtraction-free, in `ℝ≥0∞`): if `π₀` minimises `J₀` and `π_g` minimises `J_g` over a common set
`Π` of plans carried by bounded tangent fields, then `J_g(π_g) ≤ J_g(π₀) ≤ J_g(π_g) + (1 − a_r²) J₀(π₀)`. -/
def neargeo : Prop :=
  ∀ (d : ℕ) (Z T : Type) [MeasurableSpace Z] [MeasurableSpace T] (lam : Measure T)
    (m : T → EuclideanSpace ℝ (Fin (d + 1))) (U V : Z → T → EuclideanSpace ℝ (Fin (d + 1)))
    (r : ℝ) (Pi : Set (Measure Z)) (π₀ πg : Measure Z),
    0 < r → r < Real.pi → (∀ t, ‖m t‖ = 1) → (∀ π ∈ Pi, BoundedTangent lam m U V r π) →
    π₀ ∈ Pi → πg ∈ Pi → (∀ π ∈ Pi, jZero lam U V π₀ ≤ jZero lam U V π) →
    (∀ π ∈ Pi, jGeo lam m U V πg ≤ jGeo lam m U V π) →
      jGeo lam m U V πg ≤ jGeo lam m U V π₀ ∧
        jGeo lam m U V π₀ ≤ jGeo lam m U V πg + ENNReal.ofReal (1 - (Real.sin r / r) ^ 2) * jZero lam U V π₀

/-- `eq:neargeo` as printed, in `ℝ`: `0 ≤ J_g(π₀) − J_g(π_g) ≤ (1 − a_r²) J₀(π₀)` (when `J₀(π₀) < ∞`; then every
term is finite). -/
def neargeo_real : Prop :=
  ∀ (d : ℕ) (Z T : Type) [MeasurableSpace Z] [MeasurableSpace T] (lam : Measure T)
    (m : T → EuclideanSpace ℝ (Fin (d + 1))) (U V : Z → T → EuclideanSpace ℝ (Fin (d + 1)))
    (r : ℝ) (Pi : Set (Measure Z)) (π₀ πg : Measure Z),
    0 < r → r < Real.pi → (∀ t, ‖m t‖ = 1) → (∀ π ∈ Pi, BoundedTangent lam m U V r π) →
    π₀ ∈ Pi → πg ∈ Pi → (∀ π ∈ Pi, jZero lam U V π₀ ≤ jZero lam U V π) →
    (∀ π ∈ Pi, jGeo lam m U V πg ≤ jGeo lam m U V π) → jZero lam U V π₀ ≠ ⊤ →
      jGeo lam m U V π₀ ≠ ⊤ ∧ jGeo lam m U V πg ≠ ⊤ ∧
        0 ≤ (jGeo lam m U V π₀).toReal - (jGeo lam m U V πg).toReal ∧
        (jGeo lam m U V π₀).toReal - (jGeo lam m U V πg).toReal ≤
          (1 - (Real.sin r / r) ^ 2) * (jZero lam U V π₀).toReal

/-! #### `prop:tight` -/

/-- `prop:tight` on the line: for laws with `W₂(μ₀,m₀), W₂(m₀,m₁), W₂(m₁,μ₁) < ∞`, the triangle inequality
`W₂(μ₀,μ₁) ≤ W₂(μ₀,m₀) + W₂(m₀,m₁) + W₂(m₁,μ₁)` is an equality iff the three quantile increments are nonnegative
multiples of one `L²(0,1)` function. -/
def tight_line : Prop :=
  ∀ (μ₀ m₀ m₁ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure m₀] [IsProbabilityMeasure m₁]
    [IsProbabilityMeasure μ₁],
    wassersteinEDist 2 μ₀ m₀ ≠ ⊤ → wassersteinEDist 2 m₀ m₁ ≠ ⊤ → wassersteinEDist 2 m₁ μ₁ ≠ ⊤ →
      (wassersteinEDist 2 μ₀ μ₁ = wassersteinEDist 2 μ₀ m₀ + wassersteinEDist 2 m₀ m₁ + wassersteinEDist 2 m₁ μ₁ ↔
        Aligned (qInc μ₀ m₀) (qInc m₀ m₁) (qInc m₁ μ₁))

/-- `prop:tight` on the line, second sentence: if moreover `W₂(m₀,m₁) > 0`, equality holds iff the outer increments
are nonnegative multiples of the nominal direction `q_{m₁} − q_{m₀}`. -/
def tight_line_direction : Prop :=
  ∀ (μ₀ m₀ m₁ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure m₀] [IsProbabilityMeasure m₁]
    [IsProbabilityMeasure μ₁],
    wassersteinEDist 2 μ₀ m₀ ≠ ⊤ → wassersteinEDist 2 m₀ m₁ ≠ ⊤ → wassersteinEDist 2 m₁ μ₁ ≠ ⊤ →
    0 < wassersteinEDist 2 m₀ m₁ →
      (wassersteinEDist 2 μ₀ μ₁ = wassersteinEDist 2 μ₀ m₀ + wassersteinEDist 2 m₀ m₁ + wassersteinEDist 2 m₁ μ₁ ↔
        AlignedNominal (qInc μ₀ m₀) (qInc m₀ m₁) (qInc m₁ μ₁))

/-- `prop:tight` in the certificate setting: for a bounded measurable rule `h`, centres `P̂_s` and any laws `Q_s`,
the triangle step `W₂(h#Q₀,h#Q₁) ≤ W₂(h#Q₀,h#P̂₀) + Δ(h) + W₂(h#P̂₁,h#Q₁)` is an equality iff the three increments
`q_{h#P̂₀} − q_{h#Q₀}`, `q_{h#P̂₁} − q_{h#P̂₀}`, `q_{h#Q₁} − q_{h#P̂₁}` are nonnegative multiples of one `L²(0,1)`
function; when `Δ(h) > 0`, iff the outer two are nonnegative multiples of the nominal direction. -/
def tight : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (h : K → ℝ)
    (Q₀ Q₁ : Measure K) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁],
    0 < n₀ → 0 < n₁ → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
      (wassersteinEDist 2 (Q₀.map h) (Q₁.map h) =
          wassersteinEDist 2 (Q₀.map h) ((centre x₀).map h) +
            wassersteinEDist 2 ((centre x₀).map h) ((centre x₁).map h) +
              wassersteinEDist 2 ((centre x₁).map h) (Q₁.map h) ↔
        Aligned (qInc (Q₀.map h) ((centre x₀).map h)) (qInc ((centre x₀).map h) ((centre x₁).map h))
          (qInc ((centre x₁).map h) (Q₁.map h))) ∧
      (0 < wassersteinEDist 2 ((centre x₀).map h) ((centre x₁).map h) →
        (wassersteinEDist 2 (Q₀.map h) (Q₁.map h) =
            wassersteinEDist 2 (Q₀.map h) ((centre x₀).map h) +
              wassersteinEDist 2 ((centre x₀).map h) ((centre x₁).map h) +
                wassersteinEDist 2 ((centre x₁).map h) (Q₁.map h) ↔
          AlignedNominal (qInc (Q₀.map h) ((centre x₀).map h)) (qInc ((centre x₀).map h) ((centre x₁).map h))
            (qInc ((centre x₁).map h) (Q₁.map h))))

/-! #### `prop:exact` -/

/-- Kantorovich duality on the line with bounded continuous potentials, for laws carried by a compact interval:
`W₂²(μ,ν) = sup_{(φ,ψ)∈Φ_b} (E_μ φ + E_ν ψ)`. -/
def exact_line : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : ℝ),
    μ (Icc (-H) H)ᶜ = 0 → ν (Icc (-H) H)ᶜ = 0 →
      (((wassersteinEDist 2 μ ν) ^ 2 : ℝ≥0∞) : EReal) =
        ⨆ p ∈ phiB, ((∫ u, p.1 u ∂μ + ∫ v, p.2 v ∂ν : ℝ) : EReal)

/-- `prop:exact`: for every bounded measurable rule `h` and any sets `𝔅₀, 𝔅₁` of laws on `K`,
`F(h) = sup_{(φ,ψ)∈Φ_b} [sup_{Q₀∈𝔅₀} E_{Q₀} φ∘h + sup_{Q₁∈𝔅₁} E_{Q₁} ψ∘h]`. -/
def exact : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (h : K → ℝ) (B₀ B₁ : Set (Measure K)),
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → (∀ Q ∈ B₀, IsProbabilityMeasure Q) → (∀ Q ∈ B₁, IsProbabilityMeasure Q) →
      worstF h B₀ B₁ = dualF h B₀ B₁

/-! #### `lem:convex` -/

/-- `lem:convex`(i), first argument: `OT_ε(θμ + (1−θ)μ', Q) ≤ θ OT_ε(μ,Q) + (1−θ) OT_ε(μ',Q)`. -/
def convex_left : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ε B θ : ℝ) (c : K → K → ℝ) (μ μ' Q : Measure K)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure Q],
    0 < ε → CostSetting c B → 0 ≤ θ → θ ≤ 1 →
      otEnt ε c (ENNReal.ofReal θ • μ + ENNReal.ofReal (1 - θ) • μ') Q ≤
        (θ : EReal) * otEnt ε c μ Q + ((1 - θ : ℝ) : EReal) * otEnt ε c μ' Q

/-- `lem:convex`(i), second argument: `OT_ε(μ, θQ + (1−θ)Q') ≤ θ OT_ε(μ,Q) + (1−θ) OT_ε(μ,Q')`. -/
def convex_right : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ε B θ : ℝ) (c : K → K → ℝ) (μ Q Q' : Measure K)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'],
    0 < ε → CostSetting c B → 0 ≤ θ → θ ≤ 1 →
      otEnt ε c μ (ENNReal.ofReal θ • Q + ENNReal.ofReal (1 - θ) • Q') ≤
        (θ : EReal) * otEnt ε c μ Q + ((1 - θ : ℝ) : EReal) * otEnt ε c μ Q'

/-- `lem:convex`(ii), first argument: for `μ, μ'` uniform on `n` labelled atoms differing in the atom `k`,
`|OT_ε(μ,Q) − OT_ε(μ',Q)| ≤ B_c / n` (both values finite). -/
def bdd_diff_left : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (k : Fin n) (y : K) (ε B : ℝ) (c : K → K → ℝ)
    (Q : Measure K) [IsProbabilityMeasure Q],
    0 < ε → CostSetting c B →
      ∃ t t' : ℝ, OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (x i)) Q = t ∧
        OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (Function.update x k y i)) Q = t' ∧ |t - t'| ≤ B / n

/-- `lem:convex`(ii), second argument: the same for `OT_ε(Q, μ)` against `OT_ε(Q, μ')`. -/
def bdd_diff_right : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (k : Fin n) (y : K) (ε B : ℝ) (c : K → K → ℝ)
    (Q : Measure K) [IsProbabilityMeasure Q],
    0 < ε → CostSetting c B →
      ∃ t t' : ℝ, otDiscR ε (fun _ => (n : ℝ)⁻¹) (fun i z => c z (x i)) Q = t ∧
        otDiscR ε (fun _ => (n : ℝ)⁻¹) (fun i z => c z (Function.update x k y i)) Q = t' ∧ |t - t'| ≤ B / n

end Claims
end StatFormal.Wave7b
