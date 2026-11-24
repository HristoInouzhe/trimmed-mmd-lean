import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import TauCeti.MeasureTheory.OptimalTransport.Coupling
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic
import Mathlib.Probability.CondVar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# FROZEN STATEMENTS — wave 8a (QUEUE rows 71–73): SB fairness repair `lem:sharp`;
# trimmed MMD `prop:georep`, `lem:cvar`

Sources (verbatim in `lean-formalisation/inventory/extracted/data-fairness-repair.md` and `trimmed-mmd.md`; current
text after the 2026-10-13/14 corrections):
* SB `lem:sharp` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:903-910`, proof `:912-918`), with
  `ass:main` (`:352`, `R_s, ν ∈ 𝒫₂(ℝ^d)`), `eq:static` (`:385-390`, `π^⋆_ε` minimises `½∫|x−y|² dπ − ε Ent(π)`) and
  `rem:convention` (`:2273-2285`, the Sinkhorn normalisation `ε KL(π‖μ⊗ν)` has the same plan).
* trimmed MMD `prop:georep` (`trimmed-mmd/paper.tex:653-670`, proof `supplement.tex:52-79`), with `eq:trimset` (`:76-84`),
  `eq:trimMMDpop` (`:188-193`), `eq:qp` (`:607-616`), `eq:region` (`:633-642`), `ass:regularity` (`:546-560`).
* trimmed MMD `lem:cvar` (`paper.tex:699-717`, proof `supplement.tex:119-…`).
Reuses the frozen `TrimmedMMD/Concentration` (`region`, `empirical`), `TrimmedMMD/Unconditional` (`setDist`, `Dpop`,
`Demp`), `TrimmedMMD/ZeroSet` (`IsTrimDensity`) and `TrimmedMMD/BangBang` (`cap`, `capped`, `qp`) statements, and Tau
Ceti's `IsCoupling`, `HasFiniteMoment`, `entropicTransportCost`, imported, not copied.

Covered:
* `lem:sharp`: `sharp_bary_exists` (a measurable version `T` of `x ↦ E[X₁|X₀ = x]` exists), `sharp_iff` (`T_#R = ν` iff
  `E‖X₁ − T(X₀)‖² = 0` iff the plan is a graph `(id,S)_#R`), `sharp_condVar` (the same with the literal
  `E[Var(X₁ⁱ|X₀)] = 0` for every coordinate), `sharp_density` (positive density against `R ⊗ ν` ⇒ `T_#R = ν` iff `ν` is
  Dirac), `sharp_entropic` (for the **actual** entropic plan, `ε > 0`, `R, ν` carried by a ball: the plan exists and
  `T_#R = ν` iff `ν` is Dirac).
* `prop:georep`: `georep_embed` (`{μ_{P'} : P' ∈ R_α(P)} = 𝒞_{α,k}(P)`), `georep_dist` (`eq:setdist`),
  `georep_empirical` (`𝒞_{α,k}(P_n)` = capped-simplex polytope, ties allowed), `georep_qp` (`D̂²` is the attained
  minimum of `eq:qp`), `georep_ties_weights` (the ties trap: the weight map `g ↦ (g(X_i)/n)_i` is not onto `Δ_α(n)`).
* `lem:cvar`: `cvar_rkhs` (`f ∈ H`: `h_𝒞(f) = sup_g E[gf] = inf_t {t + βE(f−t)₊}`, sup and inf attained),
  `cvar_bounded` (the second equality, attained, for every bounded measurable `f`).

Not covered (declared):
* `lem:sharp`: the general (non-compact) entropic plan with quadratic cost on `𝒫₂(ℝ^d)` — Tau Ceti's Schrödinger
  system needs a bounded cost; there positivity of the density is the hypothesis of `sharp_density`. The covariance
  form of the proof (`Cov(X₁) = Cov(T) + E Cov(X₁|X₀)`) is replaced by the equivalent second-moment form.
* `prop:georep`: "convex" in "two convex polytopes" (immediate, not stated); closedness of the set (proof remark).
* `lem:cvar`: the CVaR/Rockafellar–Uryasev naming sentence (a remark).

Encodings (see card):
* `lem:sharp`: `ℝ^d = EuclideanSpace ℝ (Fin d)`; `π` any coupling of `R` and `ν` (`IsCoupling`), `ν ∈ 𝒫₂`
  (`HasFiniteMoment 2`; `R ∈ 𝒫₂` is not needed). `T` is a version of the barycentric projection (`IsBaryProj`:
  measurable, `T ∘ fst =ᵐ[π] π[snd | σ(fst)]`, Mathlib `condExp`). `E[Var(X₁|X₀)] = 0` for vector `X₁` is
  `E[tr Cov(X₁|X₀)] = E‖X₁ − T(X₀)‖² = 0` (`condVarTrace`, an `ℝ≥0∞` lower integral, no junk), equivalently the
  diagonal `E[Var(X₁ⁱ|X₀)] = 0` (Mathlib `condVar`; integrable, so the real integral is genuine) — `E Cov` is PSD, so
  zero diagonal is zero matrix. "Induced by a map": `π = R.map (x ↦ (x, S x))`, `S` measurable. "Not a Dirac
  measure": `¬ ∃ y, ν = dirac y` (stated as the iff). Positive density: `π = (R ⊗ ν).withDensity f`, `f` measurable,
  `f > 0` `(R⊗ν)`-a.e. The entropic plan (`IsEntropicPlan ε`): a coupling attaining Tau Ceti's
  `inf_π ∫ ‖x−y‖² dπ + ε KL(π‖R⊗ν)` (Sinkhorn normalisation, `rem:convention`); the paper's
  `½∫|x−y|² − ε Ent` plan at `ε` is ours at `2ε` when `R, ν` are a.c. with finite entropy (`ass:ac`), and `ε` ranges
  over all of `(0,∞)`, so the family of plans is the same. Compact supports `R(B̄(0,M)ᶜ) = ν(B̄(0,M)ᶜ) = 0` are a
  specialisation of `ass:main`.
* `prop:georep`: setting of `TrimmedMMD/Concentration` (`H` a real Hilbert space, `φ` strongly measurable,
  `‖φ‖ ≤ κ`; A2/A3 unused). `R_α(P)` is literal (`trimSet`: probability measures `Q ≪ P` with
  `dQ/dP ≤ (1−α)⁻¹` `P`-a.s., Mathlib `rnDeriv`); `D_{α,k}` is the real `sInf` of `‖μ_{P'} − μ_{Q'}‖` (`dTrim`;
  nonempty and bounded below, no junk); `μ_{P'} = ∫ φ dP'` (Bochner, integrable). The region is the frozen `region`
  (densities bounded everywhere — same set as `L^∞(P)`). Empirical: frozen `empirical` (weights `1/n`), any
  measurable space, **ties allowed** (also σ-inseparable distinct points); polytope over the frozen `capped n α`.
  `eq:qp` with the same `α` for both samples, as printed.
* `lem:cvar`: `f ∈ H` acts as the function `x ↦ ⟪f, φ x⟫` (reproducing property); `h_C(f) = sup_{a∈C} ⟪a, f⟫`;
  `𝒢_α(P)` = `IsTrimDensity P α` (frozen); `β = 1/(1−α)`; each equality is stated as one value `v` that is the
  greatest element of the left set(s) and the least element of `{t + βE(f−t)₊ : t ∈ ℝ}` (attainment, no `sSup` junk).
Critic notes:
* `lem:sharp` holds as printed (for every coupling, not only the entropic one; `ν ∈ 𝒫₂` is needed for the
  Pythagoras step). The infimum attainment and positivity for the entropic plan are proved only for compactly
  supported marginals (bounded cost); in general they are a hypothesis.
* `prop:georep` holds as printed. The **ties trap** is real but harmless: with `X_i = X_j` an `L^∞(P_n)` density gives
  tied points equal weights, so the parametrisation is not onto `Δ_α(n)` (`georep_ties_weights`), yet the set of
  embeddings is the whole polytope by averaging over tie classes. In an arbitrary measurable space the "tie classes"
  are the classes of points no measurable set separates; the identity still holds because `φ` is (strongly)
  measurable (A1) and hence constant on them — without A1 it would fail. `0 ≤ α` is not used in `georep_empirical`.
* `lem:cvar` holds as printed in the current text: the first equality is stated for `f ∈ H` and the second for every
  bounded measurable `f`, so the T2-6 typing issue noted in `QUEUE.md` row 73 is already repaired. The infimum over
  `t` is also attained (at an upper-tail quantile), which is more than printed.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. Paper `ε` ↔ `2ε` here is exact under `ass:ac` (`½∫|x−y|² − εEnt =
  ½[∫|x−y|² + 2ε KL(π‖R⊗ν)]` + const) and harmless (every `ε > 0` is quantified). `sharp_entropic` is a declared partial
  coverage (marginals carried by a ball); general `𝒫₂` marginals are covered only conditionally via `sharp_density`.
  Paper notes: `lem:sharp` does not cite `ass:ac`, without which `eq:static` is `+∞` on every coupling (S3, DEFECTS #39);
  `eq:static` is posed on `𝒫₂(ℝ)` although `R_s ∈ 𝒫₂(ℝ^d)` (S4). `prop:georep` is TRUE as printed (the current proof
  averages within tie groups; in a non-separating σ-algebra these must be the classes of inseparable points, on which
  `φ` is constant by (A1) — minor S2); "a trimming of `P_n` is a weight vector" (`paper.tex:603`) is loose (onto, not
  injective; S4). `lem:cvar`: review T2-6 is fixed in the current text; attainment holds even at `α = 0`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set InformationTheory
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave8a

/-! ### SB `lem:sharp` -/

section Sharp

/-- `T` is a version of the barycentric projection `T(x) = E_π[X₁ | X₀ = x]` of the plan `π` on `ℝ^d × ℝ^d`:
`T` is measurable and `T ∘ fst` is `π`-a.e. the conditional expectation of `X₁ = snd` given `σ(X₀) = σ(fst)`. -/
def IsBaryProj {d : ℕ} (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  Measurable T ∧
    (fun p => T p.1) =ᵐ[π] π[fun p => p.2 | MeasurableSpace.comap Prod.fst inferInstance]

/-- `E[tr Cov(X₁ | X₀)] = E_π ‖X₁ − T(X₀)‖²`, in `ℝ≥0∞` (no integrability junk). -/
def condVarTrace {d : ℕ} (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ p, ‖p.2 - T p.1‖ₑ ^ 2 ∂π

/-- The quadratic cost `c(x,y) = ‖x − y‖²` on `ℝ^d × ℝ^d`, in `ℝ≥0∞`. -/
def quadCost {d : ℕ} (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ‖z.1 - z.2‖ₑ ^ 2

/-- `π` is an entropic optimal plan `π^⋆_ε(R,ν)` for the quadratic cost:
a coupling attaining `inf_π ∫ c dπ + ε KL(π ‖ R ⊗ ν)` (Tau Ceti `entropicTransportCost`). -/
def IsEntropicPlan {d : ℕ} (ε : ℝ≥0) (R ν : Measure (EuclideanSpace ℝ (Fin d)))
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) : Prop :=
  IsCoupling π R ν ∧
    ∫⁻ z, quadCost z ∂π + ε * klDiv π (R.prod ν) = entropicTransportCost quadCost ε R ν

end Sharp

/-! ### trimmed MMD `prop:georep` -/

section Georep

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `R_α(P) = {Q ≪ P : dQ/dP ≤ 1/(1−α) P-a.s.}`, the `α`-trimmings of `P` (laws), `eq:trimset`. -/
def trimSet (P : Measure 𝒳) (α : ℝ) : Set (Measure 𝒳) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ P ∧ ∀ᵐ x ∂P, Q.rnDeriv P x ≤ ENNReal.ofReal (1 / (1 - α))}

/-- `D_{α,k}(P,Q) = inf_{P' ∈ R_α(P), Q' ∈ R_α(Q)} MMD_k(P',Q')`, `MMD_k(P',Q') = ‖μ_{P'} − μ_{Q'}‖`
(`eq:trimMMDpop`). -/
def dTrim (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : ℝ :=
  sInf {r | ∃ P' ∈ trimSet P α, ∃ Q' ∈ trimSet Q α, r = ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖}

/-- The polytope `{Σ_i w_i φ(X_i) : w ∈ Δ_α(n)}` (capped simplex `0 ≤ w_i ≤ [n(1−α)]⁻¹`, `Σ w_i = 1`). -/
def polytope {n : ℕ} (φ : 𝒳 → H) (x : Fin n → 𝒳) (α : ℝ) : Set H :=
  {z | ∃ w ∈ StatFormal.TrimmedMMD.BangBang.capped n α, z = ∑ i, w i • φ (x i)}

end Georep

namespace Claims

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
open StatFormal.TrimmedMMD.ZeroSet StatFormal.TrimmedMMD.BangBang

/-! #### SB `lem:sharp` -/

/-- The barycentric projection exists: for a coupling `π` of `R` and `ν` with `ν ∈ 𝒫₂`, some measurable `T` is a
version of `x ↦ E_π[X₁ | X₀ = x]`. -/
def sharp_bary_exists : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))),
    IsCoupling π R ν → HasFiniteMoment 2 ν → ∃ T, IsBaryProj π T

/-- `lem:sharp`, the two equivalences, for any coupling `π` of `R` and `ν ∈ 𝒫₂`: `T_#R = ν` iff
`E‖X₁ − T(X₀)‖² = E[tr Cov(X₁ | X₀)] = 0`, iff the plan is induced by a map (`π = (id, S)_#R`). -/
def sharp_iff : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
    IsCoupling π R ν → HasFiniteMoment 2 ν → IsBaryProj π T →
      (R.map T = ν ↔ condVarTrace π T = 0) ∧
        (condVarTrace π T = 0 ↔
          ∃ S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), Measurable S ∧
            π = R.map fun x => (x, S x))

/-- `lem:sharp`, literal form: `T_#R = ν` iff `E[Var(X₁ⁱ | X₀)] = 0` for every coordinate `i` (the diagonal of the
positive semidefinite `E[Cov(X₁ | X₀)]`, Mathlib `condVar`). -/
def sharp_condVar : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
    IsCoupling π R ν → HasFiniteMoment 2 ν → IsBaryProj π T →
      (R.map T = ν ↔
        ∀ i : Fin d, ∫ p, condVar (MeasurableSpace.comap Prod.fst inferInstance)
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2 i) π p ∂π = 0)

/-- `lem:sharp`, last sentence, with positivity of the plan's density as a hypothesis: if `π` has a density `f > 0`
(`R ⊗ ν`-a.e.) with respect to `R ⊗ ν`, then `T_#R = ν` iff `ν` is a Dirac measure. -/
def sharp_density : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
    IsCoupling π R ν → HasFiniteMoment 2 ν → IsBaryProj π T → Measurable f →
    (∀ᵐ z ∂(R.prod ν), 0 < f z) → π = (R.prod ν).withDensity f →
      (R.map T = ν ↔ ∃ y, ν = Measure.dirac y)

/-- `lem:sharp` for the actual entropic plan, compactly supported marginals: for `ε > 0` and `R, ν` carried by a
ball, an entropic optimal plan `π^⋆_ε(R,ν)` exists, and for every such plan and every version `T` of its
barycentric projection, `T_#R = ν` iff `ν` is a Dirac measure. -/
def sharp_entropic : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (M : ℝ) (ε : ℝ≥0),
    R (Metric.closedBall 0 M)ᶜ = 0 → ν (Metric.closedBall 0 M)ᶜ = 0 → ε ≠ 0 →
      (∃ π, IsEntropicPlan ε R ν π) ∧
        ∀ (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
          (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
          IsEntropicPlan ε R ν π → IsBaryProj π T → (R.map T = ν ↔ ∃ y, ν = Measure.dirac y)

/-! #### trimmed MMD `prop:georep` -/

/-- `prop:georep`, the embeddings of the `α`-trimmings are exactly the region: `{μ_{P'} : P' ∈ R_α(P)} = 𝒞_{α,k}(P)`. -/
def georep_embed : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      (fun P' => ∫ x, φ x ∂P') '' trimSet P α = region φ α P

/-- `prop:georep`, `eq:setdist`: `D_{α,k}(P,Q) = dist_H(𝒞_{α,k}(P), 𝒞_{α,k}(Q))`. -/
def georep_dist : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      dTrim φ P Q α = Dpop φ P Q α

/-- `prop:georep`, empirical laws (ties allowed, any measurable space): `𝒞_{α,k}(P_n)` is the capped-simplex
polytope `{Σ_i w_i φ(X_i)}`. -/
def georep_empirical : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (α : ℝ) (n : ℕ) (x : Fin n → 𝒳),
    StronglyMeasurable φ → 0 ≤ α → α < 1 → 0 < n →
      region φ α (empirical x) = polytope φ x α

/-- `prop:georep`, last clause: `eq:qp` computes `D̂²_{α,k}`, the squared distance between the two polytopes; the
minimum is attained. -/
def georep_qp : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (α : ℝ) (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳),
    StronglyMeasurable φ → 0 ≤ α → α < 1 → 0 < n → 0 < m →
      ∃ p ∈ capped n α ×ˢ capped m α,
        IsMinOn (qp (φ ∘ x) (φ ∘ y)) (capped n α ×ˢ capped m α) p ∧
          Demp φ x y α ^ 2 = qp (φ ∘ x) (φ ∘ y) p

/-- The ties trap (why the empirical identity is not a bijection of weights): with a tie `X₁ = X₂`, a density
`g ∈ L^∞(P_n)` gives equal weights `g(X_i)/n` to tied points, so some capped-simplex weight vector is not of the form
`(g(X_i)/n)_i` for any admissible `g` (here `𝒳 = Unit`, `n = 2`, `α = 1/2`, `w = (1, 0)`). -/
def georep_ties_weights : Prop :=
  ∃ w ∈ capped 2 (1 / 2), ∀ g : Unit → ℝ, IsTrimDensity (empirical fun _ : Fin 2 => ()) (1 / 2) g →
    ¬ ∀ i, w i = g () / 2

/-! #### trimmed MMD `lem:cvar` -/

/-- `lem:cvar` for `f ∈ H` (`f(x) = ⟪f, φ(x)⟫`): `h_{𝒞_{α,k}(P)}(f) = sup_{g ∈ 𝒢_α(P)} E_P[g f] =
inf_t {t + β E_P (f − t)₊}`, `β = (1−α)⁻¹`, with the supremum (and the infimum) attained. -/
def cvar_rkhs : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α : ℝ) (f : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      ∃ v : ℝ, IsGreatest ((fun a => ⟪a, f⟫_ℝ) '' region φ α P) v ∧
        IsGreatest {r | ∃ g, IsTrimDensity P α g ∧ r = ∫ x, g x * ⟪f, φ x⟫_ℝ ∂P} v ∧
        IsLeast (range fun t : ℝ => t + 1 / (1 - α) * ∫ x, max (⟪f, φ x⟫_ℝ - t) 0 ∂P) v

/-- `lem:cvar`, second equality for every bounded measurable `f`: `sup_{g ∈ 𝒢_α(P)} E_P[g f] =
inf_t {t + β E_P (f − t)₊}`, both attained. -/
def cvar_bounded : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] (f : 𝒳 → ℝ) (α : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 →
      ∃ v : ℝ, IsGreatest {r | ∃ g, IsTrimDensity P α g ∧ r = ∫ x, g x * f x ∂P} v ∧
        IsLeast (range fun t : ℝ => t + 1 / (1 - α) * ∫ x, max (f x - t) 0 ∂P) v

end Claims
end StatFormal.Wave8a
