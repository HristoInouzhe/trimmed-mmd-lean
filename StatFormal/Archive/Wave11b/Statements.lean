import StatFormal.Archive.Wave9b.Statements
import StatFormal.Archive.Wave8a.Statements
import StatFormal.Archive.ICL.Statements
import StatFormal.Archive.ICL.Cond.Statements
import StatFormal.Archive.ICL.Diag.Statements
import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic
import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Topology.MetricSpace.Basic

/-!
# FROZEN STATEMENTS — wave 11b (QUEUE rows 97–100): SB `thm:flow`; trimmed MMD `lem:attainment`;
# ICL `lem:cond-nonunique`, `prop:swor-score`

Sources (verbatim in `lean-formalisation/inventory/extracted/data-fairness-repair.md`, `trimmed-mmd.md`,
`context-distribution-icl.md`; current text after the 2026-10-13/14 corrections):
* SB `thm:flow` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:538-563`, proof `:2702-2724`),
  with `ass:atomless` (`:357-360`), `ass:main` (`:352-355`), the scalar notation (`:337-343`:
  `F⁻¹_μ(p) = inf{x : F_μ(x) ≥ p}`, `U = h(X)`, `R_s = 𝓛(U | S = s)`), `eq:flowmap` (`:542-545`),
  `def:repair` (`:435-447`) and `prop:mixture` (`:456-471`).
* trimmed MMD `lem:attainment` (`trimmed-mmd/paper.tex:673-687`, proof `supplement.tex:82-118`), with
  `eq:trimset` (`paper.tex:76-84`), `eq:trimMMDpop` (`:188-193`), `ass:regularity` (`:546-560`), `eq:region`
  (`:633-643`) and `prop:georep` (`:654-670`).
* ICL `lem:cond-nonunique` (`context-distribution-ICL/paper/v3/supp/proofs_conditional.tex:223-228`, proof
  `:230-260`), with the notation and conventions (`:21-31`: `𝒵 = 𝒳 × 𝒴` compact metric, `P_{Y|x}` a fixed
  regular conditional law, `𝓜 = {μ ∈ 𝒫(S) : μ^{⊗M}(D_M) > 0}`, `S = supp P₀`, `φ_λ(x,μ) = Ḡ_μ(x) + λ KL(μ|P₀)`),
  `Π_μ = μ^{⊗M}(· | D_M)` (`sections/03_framework.tex:18-22`), `J_cond` and `prop:cond-target`
  (`sections/06b_cond_theory.tex:1-30`; policies are Borel maps into `𝓜`).
* ICL `prop:swor-score` (`supp/proofs_score.tex:346-353`, proof `:355-408`), with `as:compact`–`as:loss`
  (`:14-32`), `J^iid_{n,m}` (`:53-66`), the CPS law and `J_m` (`sections/03_framework.tex:56-74`) and the coverage
  functional on the one-slot marginal (`sections/04_selector.tex:4-14`).
Reuses the frozen `Wave9b` (`flowMap`, through it `Wave4b.endpointMixture1`), `Wave8a` (`trimSet`, `dTrim`),
`TrimmedMMD/Concentration` (`region`), `TrimmedMMD/ZeroSet` (`Characteristic`), `ICL` (`cps`, `Grisk`, `incl`,
`InDeltaM`), `ICL/Cond` (`iidLaw`) and `ICL/Diag` (`klUnif`) statements, and Tau Ceti's `wassersteinEDist`,
`IsOptimalCoupling`, `graphPlan`, imported, not copied. No `Foundations` library file is imported directly (the
frozen `ZeroSet` statements already lock `Foundations/Distances/TV`).

Covered:
* `thm:flow`: `flow_mixture_prob` (`μ^ε_{s,t}` is a probability law, so the claims below, stated for any
  probability law `μ`, apply to it), `flow_push` ((i), `𝓛(Ψ(U) | S = s) = μ`), `flow_monotone` ((ii),
  non-decreasing), `flow_optimal` ((ii), "hence it is the `W₂`-optimal map": the graph plan is an optimal
  coupling), `flow_cost` ((ii), `E[(Ψ(U) − U)² | S = s] = W₂²(R_s, μ)`), `flow_minimal` ((iii), any `V` with the
  right conditional law, no atomless hypothesis), `flow_ode_unique` ((iv) with the ODE as a hypothesis: every
  non-decreasing map transporting `R_s` to `μ` equals `Ψ` `R_s`-a.s.).
* `lem:attainment`: `attain_convex`, `attain_bounded` (`‖·‖ ≤ κ`), `attain_weak_compact`, `attain_closed`
  (norm-closed), `attain_inf` ((i): attained at genuine trimmings), `attain_zero` ((ii): `D = 0` ⇒ the regions
  meet), `attain_common` ((ii): every point of the intersection is the embedding of a common trimming).
* `lem:cond-nonunique`: `cond_nonunique` (both sentences: two distinct minimisers of `φ_λ(x, ·)` over `𝓜` at
  every `x`, and two optimal policies that differ at every `x`).
* `prop:swor-score`: `swor_collision` (`p ≤ binom(M,2) Σ w_j²`), `swor_collision_score`
  (`p ≤ M(M−1)s_+/(2s_-n)`, `≤ ½` for `n ≥ M(M−1)s_+/s_-`), `swor_perturb` (`eq:swor-perturb` and
  `|E°f − Ef| ≤ 2‖f‖p/(1−p) ≤ 4‖f‖p`), `swor_cps` (`Π_w` is the conditioned i.i.d. index law up to order:
  `G(w) = E°L`, `π_l/M = E°[#{k : I_k = l}/M]`), `swor_value` (the value bound
  `sup_Θ |J_{n,m} − J^iid_{n,m}| ≤ C₀/n`, with an explicit `C₀`).

Not covered (declared):
* `thm:flow`(iv) itself (the probability-flow ODE, its well-posedness and the continuity-equation argument,
  L4 per the queue note): only its uniqueness step is stated, with "the flow map is non-decreasing and
  transports `R_s` to `μ^ε_{s,t}`" as the hypothesis. The paragraph after the theorem (commentary).
* `lem:attainment`: the parenthetical "so `eq:zeroeq` holds without separately positing attainment" is the
  certified `TrimmedMMD/ZeroSet` `zeroeq`; the reviewer remark that the region is even norm-compact (QUEUE row 98,
  T1-8) is not in the statement and is not formalised.
* `prop:swor-score`: the derivative bounds `C₁/n`, `C₂/n` under `as:smooth` (the queue's "the rest"; the value
  bound is the L1 core), and "Consequently `thm:score` and `cor:inference` hold for the minimiser of `J_{n,m}`"
  (the transfer argument (a)–(d) of the proof); the `CVaR_α` aggregation (the proposition's `J_{n,m}` uses the
  mean risk, which is what the proof treats).

Encodings (see card):
* `thm:flow`: dimension one, two groups `S : Ω → Fin 2` on a probability space `(Ω, P)`; `U` measurable,
  `𝓛(W | S = s) = (P[· | S = s]).map W` (`condLaw`; Mathlib `cond`), with `P(S = s) ≠ 0` (otherwise the
  conditional law is the junk zero measure). `Ψ = flowMap R μ = μ.quantile ∘ cdf R` (frozen; Tau Ceti's
  `inf{x : t ≤ F(x)}`). Atomless is `NullSingletonClass`. "Non-decreasing" is `MonotoneOn` on `{0 < F_R < 1}`
  together with `R({0 < F_R < 1}ᶜ) = 0` for atomless `R`: off that null set the paper's `F⁻¹_μ(0) = −∞` (and
  `F⁻¹_μ(1)` possibly `+∞`) is extended-real, while Tau Ceti returns the junk `0`, so `Ψ` is not monotone on all
  of `ℝ` in Lean — a convention artefact on an `R`-null set, not a defect. Costs and `W₂²` are in `ℝ≥0∞`
  (`edist² ` lower integrals, Tau Ceti's `wassersteinEDist 2`), so no `𝒫₂` hypothesis is needed (`ass:main`
  only generalised away). "`W₂`-optimal map" is `IsOptimalCoupling` of the graph plan `(id, Ψ)_# R` for
  `|x − y|²`. `μ = μ^ε_{s,t}` enters only as a probability law (`flow_mixture_prob`). In (iv) the flow map is any
  `Φ : ℝ → ℝ` with `Monotone Φ` and `R.map Φ = μ` (strictly increasing, as the proof derives, is a special case).
* `lem:attainment`: the setting of `Wave8a.georep_*` (`H` real Hilbert, `φ` strongly measurable with
  `‖φ‖ ≤ κ` (A1); (A2) separability unused, dropped — a generalisation; (A3) only in `attain_common`, as the
  frozen `Characteristic`: the mean embedding is injective on probability measures). `𝒞_{α,k}(P)` is the frozen
  `region` (densities bounded everywhere, the same set as with `L^∞(P)` densities, `georep_embed`). Weak
  compactness is `IsCompact (toWeakSpace ℝ H '' 𝒞)` for Mathlib's `WeakSpace ℝ H` (topology `σ(H, H*)`). The
  infimum in `eq:trimMMDpop` is the frozen `dTrim` (real `sInf`, nonempty and bounded below); (i) is
  `‖μ_{P*} − μ_{Q*}‖ = dTrim` with `P* ∈ R_α(P)`, `Q* ∈ R_α(Q)` (frozen `trimSet`). `attain_common` is stated for
  every point of the intersection, without `D = 0` (as printed: "any element of the intersection").
* `lem:cond-nonunique`: an existence statement over compact metric `𝒳, 𝒴` with Borel σ-algebras
  (`𝒵 = 𝒳 × 𝒴`, product metric and σ-algebra), `P₀` a probability measure with `P₀{z} = 0` for all `z`, a Markov
  kernel `P_{Y|·}` with `P₀ = P_X ⊗ P_{Y|·}` (`P_X = P₀.fst`), `L` continuous on `𝒵 × 𝒵^M` (product topology),
  invariant under permutations of the `M` context slots, with values in `[0, B_L]`. `D_M` = injective tuples
  (`distinctSet`), `Π_μ = μ^{⊗M}(· | D_M)` (`ctxLaw`, Mathlib `cond` of `Measure.pi`), `𝓜` = probability measures
  with `μ((supp P₀)ᶜ) = 0` (Mathlib `Measure.support`) and `μ^{⊗M}(D_M) > 0` (`Admissible`; `Π_μ` is no junk
  there). `Ḡ_μ(x) = ∫⁻∫⁻ L((x,y); t) P_{Y|x}(dy) Π_μ(dt)` and `φ_λ = Ḡ_μ + λ KL(μ|P₀)` are `[0,∞]`-valued
  (`klDiv = ∞` off `μ ≪ P₀` is the paper's `+∞`, not junk; `λ > 0`). A minimiser is a member of `𝓜` with
  `φ_λ(x, μ) ≤ φ_λ(x, ν)` for all `ν ∈ 𝓜`. A (Borel) policy is a Markov kernel `𝒳 → 𝒵` with values in `𝓜`
  (`IsPolicy`; for compact metric `𝒵` the Giry σ-algebra on `𝒫(𝒵)` is the Borel σ-algebra of the weak topology,
  so kernels are exactly the Borel policies); `J_cond(π) = ∫⁻ φ_λ(x, μ_x) dP_X` (the disintegrated form of
  `06b_cond_theory.tex:5`); optimal = minimal over all policies. `κ'_M = M(M−1)/(binom(M,2) + ⌊M/2⌋)`
  (`kappaPrime`, ℕ division for `⌊M/2⌋`).
* `prop:swor-score`: conditionally on the pool (`z : Fin n → 𝒵`, indices, so ties are harmless) and the
  validation points (`z̃ : Fin m → 𝒵`), as in the proof. Score family `s : Θ → 𝒵 → ℝ` with `s_- ≤ s ≤ s_+`,
  `0 < s_-` (`as:score`; continuity and compactness of `Θ` are unused — a generalisation);
  `w_j(θ) = s_θ(z_j)/Σ_l s_θ(z_l)` (`wScore`); `sup_Θ |·| ≤ C₀/n` is `∀ θ, |·| ≤ C₀/n` (no `sSup` junk).
  `J_{n,m}(θ) = J_m(w(θ))` with the mean risk, `G_i(w) = Σ_S Π_w(S) L(z̃_i; z_S)` (frozen `Grisk`, `cps`; `z_S`
  listed in index order, `lossSub` — any order by symmetry), coverage `ρ(z̃) = Σ_l (π_l/M) K(z̃, z_l)` (frozen
  `incl`), `Φ_m = −m⁻¹ Σ_i log ρ(z̃_i)`, plus `λ_KL KL(w | u_n)` (frozen `klUnif`); `J^iid_{n,m}` uses
  `w^{⊗M}` (frozen `iidLaw`) and the one-slot marginal `w`. `λ_KL ∈ ℝ` is arbitrary (the terms cancel);
  `0 ≤ λ_cov ≤ Λ` encodes `sup_n λ_cov,n`. The unspecified constant is made explicit,
  `C₀ = 2M(M−1)(s_+/s_-)(B_L + Λ K_max/K_min)` (`swC0`), which depends only on the listed quantities. `1 ≤ M ≤ n`
  is added (`M ≤ n` follows from `n ≥ M(M−1)s_+/s_-` for `M ≥ 2`; for `M = 1` it says the pool is nonempty).
  `E°f = Σ_{j injective} Π w_{j_k} f(j) / (1 − p)` (`swoExp`), `E f`, `N_f`, `p` (`iidExp`, `collisionPart`,
  `collision`).

Critic notes:
* `thm:flow` (i)–(iii) hold as printed; (i)–(iii) restate, in the random-variable form, the certified
  `Wave9b.pareto_flow`/`pareto_weak` (which already used them). (iii) needs no atomless hypothesis, as printed.
  (iv) is certified only conditionally (uniqueness of the monotone transport, `R` atomless).
* `lem:attainment` holds as printed. The proof here avoids the weak-* topology on `L^∞`: closedness and
  attainment come from nested closed convex sets in `L²(P)` (minimal-norm points are Cauchy), weak compactness from
  Banach–Alaoglu through the Riesz isomorphism and Mazur's theorem.
* `lem:cond-nonunique` holds as printed. **The witness differs from the paper's** (`[0,1]²`, a continuous
  approximation of a sign function, and an appeal to the existence step of `prop:cond-target`(iii)): following
  the queue note it uses `𝒳 = [0,1]`, `𝒴 = {0,1} ⊂ ℝ`, `P₀ = Leb ⊗ Unif{0,1}` (atomless; `𝒵` is two intervals),
  `L(z;t) = b(C − e₂(ψ(t)))` with `ψ = ∓1` on the two clopen cells. Data processing reduces `φ_λ` exactly to
  the symmetric double well `F(q) = bC(1−(1−2q)²) + λ KL(Bern q | Bern ½)` on `[0,1]`, so existence of a
  minimiser is compactness of `[0,1]` and no fixed-point theory is needed. The witness is fair: compact metric
  `𝒵 = 𝒳 × 𝒴`, atomless `P₀`, continuous symmetric `L` into `[0, B_L]`, as the standing setting requires.
* `prop:swor-score`: the value bound holds as printed (with the explicit `C₀`); the collision and perturbation
  steps hold with the printed constants. Minor typo (S4): `proofs_score.tex:6-7` reads "the without-replacement
  objective `J^iid_{n,m}` differs from `J^iid_{n,m}`"; the first should be `J_{n,m}`.
* No statement looks wrong; no refutation was needed.
* Proof routes: `Wave11b/Route{Flow,Attain,Swor,Nonunique}.lean`, all 20 claims, standard axioms
  `propext, Classical.choice, Quot.sound` only.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. `flow_monotone` on `{0 < F_R < 1}` is faithful (full `R`-measure for atomless
  `R`; Lean's `sInf ℝ = 0` stands in for the paper's `−∞` off it). `flow_ode_unique` is the uniqueness step of (iv) only;
  the ODE part (flow strictly increasing and transporting `R_s`) is not covered. `lem:attainment`: `WeakSpace ℝ H` is
  the paper's `σ(H, H*)`; dropping (A2) is a genuine generalisation (Pettis). The `lem:cond-nonunique` witness
  (`[0,1] × {0,1}`, Lebesgue ⊗ uniform) satisfies every standing assumption. `prop:swor-score`: the explicit `C₀` is an
  instance of the paper's constant; `1 ≤ M ≤ n` is implicit in the setting. Paper typo (S4): `proofs_score.tex:5-6`
  "`J^iid_{n,m}` differs from `J^iid_{n,m}`" — the first should be `J_{n,m}` (DEFECTS #44).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set InformationTheory Finset
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave11b

/-! ### SB `thm:flow` -/

section Flow

/-- The conditional law `𝓛(W | S = s) = (P[· | S = s]).map W` of a real random variable `W` given the group
label `S = s`. -/
def condLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Fin 2) (s : Fin 2) (W : Ω → ℝ) :
    Measure ℝ :=
  (P[|S ⁻¹' {s}]).map W

end Flow

/-! ### ICL `lem:cond-nonunique` -/

section CondNonunique

variable {Z : Type*} [MeasurableSpace Z]

/-- `D_M = {t ∈ 𝒵^M : t_k ≠ t_l for k ≠ l}`. -/
def distinctSet (M : ℕ) : Set (Fin M → Z) := {t | Function.Injective t}

/-- `Π_μ = μ^{⊗M}(· | D_M)`: `M` i.i.d. draws from `μ` conditioned on being distinct. -/
def ctxLaw (μ : Measure Z) (M : ℕ) : Measure (Fin M → Z) :=
  ProbabilityTheory.cond (Measure.pi fun _ : Fin M => μ) (distinctSet M)

/-- The admissible set `𝓜 = {μ ∈ 𝒫(S) : μ^{⊗M}(D_M) > 0}`, `S = supp P₀`. -/
def Admissible [TopologicalSpace Z] (P0 : Measure Z) (M : ℕ) (μ : Measure Z) : Prop :=
  IsProbabilityMeasure μ ∧ μ P0.supportᶜ = 0 ∧ 0 < Measure.pi (fun _ : Fin M => μ) (distinctSet M)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The conditional risk `Ḡ_μ(x) = ∫ L̄_x dΠ_μ`, `L̄_x(t) = ∫ L((x,y); t) P_{Y|x}(dy)` (`[0,∞]`-valued). -/
def condRisk {M : ℕ} (κ : Kernel X Y) (L : X × Y → (Fin M → X × Y) → ℝ) (μ : Measure (X × Y)) (x : X) :
    ℝ≥0∞ :=
  ∫⁻ t, ∫⁻ y, ENNReal.ofReal (L (x, y) t) ∂(κ x) ∂(ctxLaw μ M)

/-- `φ_λ(x, μ) = Ḡ_μ(x) + λ KL(μ | P₀) ∈ [0, ∞]`. -/
def phiObj {M : ℕ} (κ : Kernel X Y) (L : X × Y → (Fin M → X × Y) → ℝ) (P0 : Measure (X × Y)) (lam : ℝ)
    (μ : Measure (X × Y)) (x : X) : ℝ≥0∞ :=
  condRisk κ L μ x + ENNReal.ofReal lam * klDiv μ P0

/-- `μ` minimises `φ_λ(x, ·)` over the admissible set `𝓜`. -/
def IsMinimizer [TopologicalSpace X] [TopologicalSpace Y] {M : ℕ} (κ : Kernel X Y)
    (L : X × Y → (Fin M → X × Y) → ℝ) (P0 : Measure (X × Y)) (lam : ℝ) (x : X) (μ : Measure (X × Y)) :
    Prop :=
  Admissible P0 M μ ∧ ∀ ν, Admissible P0 M ν → phiObj κ L P0 lam μ x ≤ phiObj κ L P0 lam ν x

/-- A (Borel) policy `x ↦ μ_x` with values in `𝓜`: a Markov kernel `X → 𝒵` with admissible values. -/
def IsPolicy [TopologicalSpace X] [TopologicalSpace Y] (P0 : Measure (X × Y)) (M : ℕ)
    (π : Kernel X (X × Y)) : Prop :=
  ∀ x, Admissible P0 M (π x)

/-- `J_cond(π) = E_X[Ḡ_{μ_X}(X) + λ KL(μ_X | P₀)]`, `X ~ P_X = P₀.fst`. -/
def condObj {M : ℕ} (κ : Kernel X Y) (L : X × Y → (Fin M → X × Y) → ℝ) (P0 : Measure (X × Y)) (lam : ℝ)
    (π : Kernel X (X × Y)) : ℝ≥0∞ :=
  ∫⁻ x, phiObj κ L P0 lam (π x) x ∂P0.fst

/-- `π` is an optimal policy: it minimises `J_cond` over all policies. -/
def IsOptimalPolicy [TopologicalSpace X] [TopologicalSpace Y] {M : ℕ} (κ : Kernel X Y)
    (L : X × Y → (Fin M → X × Y) → ℝ) (P0 : Measure (X × Y)) (lam : ℝ) (π : Kernel X (X × Y)) : Prop :=
  IsPolicy P0 M π ∧ ∀ π', IsPolicy P0 M π' → condObj κ L P0 lam π ≤ condObj κ L P0 lam π'

/-- `κ'_M = M(M−1)/(binom(M,2) + ⌊M/2⌋)`. -/
def kappaPrime (M : ℕ) : ℝ := ((M : ℝ) * ((M : ℝ) - 1)) / ((M.choose 2 : ℝ) + ((M / 2 : ℕ) : ℝ))

end CondNonunique

/-! ### ICL `prop:swor-score` -/

section Swor

variable {Z : Type*} {n M m : ℕ}

/-- Score-induced weights `w_j(θ) = s_θ(z_j) / Σ_l s_θ(z_l)` on the pool `z_1, …, z_n`. -/
def wScore {Θ : Type*} (s : Θ → Z → ℝ) (z : Fin n → Z) (θ : Θ) (j : Fin n) : ℝ :=
  s θ (z j) / ∑ l, s θ (z l)

/-- `L(x; z_S)` for an `M`-subset `S` of the pool, its points listed in increasing index order (any order
gives the same value for a symmetric loss); `0` off `M`-subsets (never used). -/
def lossSub (L : Z → (Fin M → Z) → ℝ) (x : Z) (z : Fin n → Z) (S : Finset (Fin n)) : ℝ :=
  if h : S.card = M then L x (fun k => z (S.orderEmbOfFin h k)) else 0

/-- The collision probability `p = Pr(D^c)`: `M` i.i.d. indices from `w` are not all distinct. -/
def collision (w : Fin n → ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin M → Fin n => ¬ Function.Injective j), StatFormal.ICL.Cond.iidLaw w M j

/-- `N_f = E[f 1_{D^c}]` under i.i.d. indices. -/
def collisionPart (w : Fin n → ℝ) (M : ℕ) (f : (Fin M → Fin n) → ℝ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin M → Fin n => ¬ Function.Injective j), StatFormal.ICL.Cond.iidLaw w M j * f j

/-- `E f` under `M` i.i.d. indices from `w`. -/
def iidExp (w : Fin n → ℝ) (M : ℕ) (f : (Fin M → Fin n) → ℝ) : ℝ :=
  ∑ j, StatFormal.ICL.Cond.iidLaw w M j * f j

/-- `E° f`: expectation under the i.i.d. index law conditioned on the distinctness event `D`. -/
def swoExp (w : Fin n → ℝ) (M : ℕ) (f : (Fin M → Fin n) → ℝ) : ℝ :=
  (∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
      StatFormal.ICL.Cond.iidLaw w M j * f j) / (1 - collision w M)

/-- `J_{n,m}` at weights `w`, conditional Poisson contexts (mean risk, coverage on the one-slot marginal
`π/M`, `KL(w | u_n)`): `m⁻¹ Σ_i G_i(w) − λ_cov m⁻¹ Σ_i log ρ(z̃_i) + λ_KL KL(w | u_n)`. -/
def jSwor (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (z : Fin n → Z) (zt : Fin m → Z) (lcov lKL : ℝ)
    (w : Fin n → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, StatFormal.ICL.Grisk w M (lossSub L (zt i) z) +
    lcov * (-(1 / (m : ℝ)) * ∑ i, Real.log (∑ l, StatFormal.ICL.incl w M l / M * K (zt i) (z l))) +
    lKL * StatFormal.ICL.Diag.klUnif n w

/-- `J^iid_{n,m}` at weights `w`: the same objective with `M` i.i.d. contexts from `w` (one-slot marginal `w`). -/
def jIid (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (z : Fin n → Z) (zt : Fin m → Z) (lcov lKL : ℝ)
    (w : Fin n → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, ∑ j, StatFormal.ICL.Cond.iidLaw w M j * L (zt i) (z ∘ j) +
    lcov * (-(1 / (m : ℝ)) * ∑ i, Real.log (∑ l, w l * K (zt i) (z l))) +
    lKL * StatFormal.ICL.Diag.klUnif n w

/-- The constant `C₀ = 2M(M−1)(s₊/s₋)(B_L + Λ K_max/K_min)`, `Λ ≥ λ_cov`. -/
def swC0 (M : ℕ) (sm sp BL Kmin Kmax Λ : ℝ) : ℝ :=
  2 * M * ((M : ℝ) - 1) * (sp / sm) * (BL + Λ * (Kmax / Kmin))

end Swor

namespace Claims

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.ZeroSet

/-! #### SB `thm:flow` -/

/-- `μ^ε_{s,t}` (the frozen `endpointMixture1`) is a probability law whenever the plan is, so the claims
below, stated for an arbitrary probability law `μ`, apply to it. -/
def flow_mixture_prob : Prop :=
  ∀ (ε t : ℝ) (π : Measure (ℝ × ℝ)), IsProbabilityMeasure π →
    IsProbabilityMeasure (StatFormal.Wave4b.endpointMixture1 ε t π)

/-- `thm:flow`(i): for atomless `R_s = 𝓛(U | S = s)`, `𝓛(Ψ(U) | S = s) = μ`, `Ψ = F⁻¹_μ ∘ F_{R_s}`. -/
def flow_push : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Fin 2) (U : Ω → ℝ) (s : Fin 2)
    (μ : Measure ℝ), IsProbabilityMeasure P → Measurable S → Measurable U → P (S ⁻¹' {s}) ≠ 0 →
    IsProbabilityMeasure μ → NullSingletonClass (condLaw P S s U) →
      condLaw P S s (fun ω => StatFormal.Wave9b.flowMap (condLaw P S s U) μ (U ω)) = μ

/-- `thm:flow`(ii), "non-decreasing": `Ψ` is non-decreasing on `{0 < F_R < 1}`, which carries `R` when `R` is
atomless (off it the generalized inverse is `±∞` in the paper and a junk `0` here). -/
def flow_monotone : Prop :=
  ∀ (R μ : Measure ℝ), IsProbabilityMeasure R → NullSingletonClass R →
    MonotoneOn (StatFormal.Wave9b.flowMap R μ) {u | 0 < cdf R u ∧ cdf R u < 1} ∧
      R {u | 0 < cdf R u ∧ cdf R u < 1}ᶜ = 0

/-- `thm:flow`(ii), "hence it is the `W₂`-optimal transport map": the graph plan `(id, Ψ)_# R` is an optimal
coupling of `R` and `μ` for the cost `|x − y|²`. -/
def flow_optimal : Prop :=
  ∀ (R μ : Measure ℝ), IsProbabilityMeasure R → IsProbabilityMeasure μ → NullSingletonClass R →
    IsOptimalCoupling (fun z : ℝ × ℝ => edist z.1 z.2 ^ (2 : ℝ))
      (graphPlan (StatFormal.Wave9b.flowMap R μ) R) R μ

/-- `thm:flow`(ii), the identity `E[(Ψ(U) − U)² | S = s] = W₂²(R_s, μ)` for atomless `R_s`. -/
def flow_cost : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Fin 2) (U : Ω → ℝ) (s : Fin 2)
    (μ : Measure ℝ), IsProbabilityMeasure P → Measurable S → Measurable U → P (S ⁻¹' {s}) ≠ 0 →
    IsProbabilityMeasure μ → NullSingletonClass (condLaw P S s U) →
      ∫⁻ ω, edist (StatFormal.Wave9b.flowMap (condLaw P S s U) μ (U ω)) (U ω) ^ (2 : ℝ) ∂(P[|S ⁻¹' {s}]) =
        wassersteinEDist 2 (condLaw P S s U) μ ^ (2 : ℝ)

/-- `thm:flow`(iii) (no atomless hypothesis): every `V` on the same probability space with
`𝓛(V | S = s) = μ` has `W₂²(R_s, μ) ≤ E[(V − U)² | S = s]`. -/
def flow_minimal : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Fin 2) (U V : Ω → ℝ) (s : Fin 2)
    (μ : Measure ℝ), IsProbabilityMeasure P → Measurable S → Measurable U → Measurable V →
    P (S ⁻¹' {s}) ≠ 0 → condLaw P S s V = μ →
      wassersteinEDist 2 (condLaw P S s U) μ ^ (2 : ℝ) ≤
        ∫⁻ ω, edist (V ω) (U ω) ^ (2 : ℝ) ∂(P[|S ⁻¹' {s}])

/-- `thm:flow`(iv), with the ODE as a hypothesis: any non-decreasing map `Φ` transporting the atomless `R` to
`μ` (as the flow map of a well-posed one-dimensional probability-flow ODE does) agrees with `Ψ` `R`-a.s. -/
def flow_ode_unique : Prop :=
  ∀ (R μ : Measure ℝ) (Φ : ℝ → ℝ), IsProbabilityMeasure R → IsProbabilityMeasure μ → NullSingletonClass R →
    Monotone Φ → R.map Φ = μ → Φ =ᵐ[R] StatFormal.Wave9b.flowMap R μ

/-! #### trimmed MMD `lem:attainment` -/

/-- `lem:attainment`: `𝒞_{α,k}(P)` is convex. -/
def attain_convex : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      Convex ℝ (region φ α P)

/-- `lem:attainment`: `𝒞_{α,k}(P)` is norm-bounded by `κ`. -/
def attain_bounded : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      ∀ z ∈ region φ α P, ‖z‖ ≤ κ

/-- `lem:attainment`: `𝒞_{α,k}(P)` is weakly compact (compact in `WeakSpace ℝ H`). -/
def attain_weak_compact : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      IsCompact (toWeakSpace ℝ H '' region φ α P)

/-- `lem:attainment`: `𝒞_{α,k}(P)` is norm-closed (no closure is taken in its definition). -/
def attain_closed : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      IsClosed (region φ α P)

/-- `lem:attainment`(i): the infimum in `eq:trimMMDpop` is attained at genuine trimmings. -/
def attain_inf : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      ∃ P' ∈ StatFormal.Wave8a.trimSet P α, ∃ Q' ∈ StatFormal.Wave8a.trimSet Q α,
        ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖ = StatFormal.Wave8a.dTrim φ P Q α

/-- `lem:attainment`(ii), first half: `D_{α,k}(P,Q) = 0` forces `𝒞_{α,k}(P) ∩ 𝒞_{α,k}(Q) ≠ ∅`. -/
def attain_zero : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      StatFormal.Wave8a.dTrim φ P Q α = 0 → (region φ α P ∩ region φ α Q).Nonempty

/-- `lem:attainment`(ii), second half: for a characteristic kernel every element of the intersection is the
embedding of a common trimming `R ∈ R_α(P) ∩ R_α(Q)`. -/
def attain_common : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ → 0 ≤ α → α < 1 →
      ∀ z ∈ region φ α P ∩ region φ α Q,
        ∃ R ∈ StatFormal.Wave8a.trimSet P α ∩ StatFormal.Wave8a.trimSet Q α, ∫ x, φ x ∂R = z

/-! #### ICL `lem:cond-nonunique` -/

/-- `lem:cond-nonunique`: for `M ≥ 2`, `B_L > 0` and `0 < λ < κ'_M B_L` there are compact metric `𝒳, 𝒴`
(`𝒵 = 𝒳 × 𝒴`), an atomless law `P₀` on `𝒵` with a regular conditional law `P_{Y|x}` (`P₀ = P_X ⊗ P_{Y|·}`), and
a continuous symmetric `L : 𝒵 × 𝒵^M → [0, B_L]` such that at every `x`, `φ_λ(x, ·)` has two distinct minimizers
over `𝓜`; hence two optimal policies differ at every `x`. -/
def cond_nonunique : Prop :=
  ∀ (M : ℕ) (BL lam : ℝ), 2 ≤ M → 0 < BL → 0 < lam → lam < kappaPrime M * BL →
    ∃ (X Y : Type) (_ : MetricSpace X) (_ : MetricSpace Y) (_ : CompactSpace X) (_ : CompactSpace Y)
      (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : BorelSpace X) (_ : BorelSpace Y)
      (P0 : Measure (X × Y)) (κ : Kernel X Y) (L : X × Y → (Fin M → X × Y) → ℝ),
      IsProbabilityMeasure P0 ∧ (∀ z, P0 {z} = 0) ∧ IsMarkovKernel κ ∧ P0 = P0.fst ⊗ₘ κ ∧
      Continuous (fun p : (X × Y) × (Fin M → X × Y) => L p.1 p.2) ∧
      (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) ∧ (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) ∧
      (∀ x, ∃ μ₁ μ₂, μ₁ ≠ μ₂ ∧ IsMinimizer κ L P0 lam x μ₁ ∧ IsMinimizer κ L P0 lam x μ₂) ∧
      ∃ π₁ π₂ : Kernel X (X × Y), IsOptimalPolicy κ L P0 lam π₁ ∧ IsOptimalPolicy κ L P0 lam π₂ ∧
        ∀ x, π₁ x ≠ π₂ x

/-! #### ICL `prop:swor-score` -/

/-- Collision probability, union bound: `p ≤ binom(M,2) Σ_j w_j²` for any probability vector `w`. -/
def swor_collision : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ), (∀ j, 0 ≤ w j) → ∑ j, w j = 1 →
    collision w M ≤ (M.choose 2 : ℝ) * ∑ j, w j ^ 2

/-- Collision probability for score-induced weights, `s_- ≤ s_θ ≤ s_+`: `p ≤ M(M−1)s_+/(2s_-n)`, and
`p ≤ 1/2` for `n ≥ M(M−1)s_+/s_-`. -/
def swor_collision_score : Prop :=
  ∀ (Z Θ : Type) (n M : ℕ) (z : Fin n → Z) (s : Θ → Z → ℝ) (sm sp : ℝ) (θ : Θ),
    0 < n → 0 < sm → (∀ θ x, sm ≤ s θ x ∧ s θ x ≤ sp) →
      collision (wScore s z θ) M ≤ M * ((M : ℝ) - 1) * sp / (2 * sm * n) ∧
        (M * ((M : ℝ) - 1) * sp / sm ≤ n → collision (wScore s z θ) M ≤ 1 / 2)

/-- The perturbation identity `eq:swor-perturb` and its bound: for `f` bounded by `F` and `p < 1`,
`E°f − Ef = (p Ef − N_f)/(1−p)`, `|E°f − Ef| ≤ 2F p/(1−p)`, and `≤ 4Fp` when `p ≤ 1/2`. -/
def swor_perturb : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ) (f : (Fin M → Fin n) → ℝ) (F : ℝ), (∀ j, 0 ≤ w j) → ∑ j, w j = 1 →
    collision w M < 1 → (∀ j, |f j| ≤ F) →
      swoExp w M f - iidExp w M f =
          (collision w M * iidExp w M f - collisionPart w M f) / (1 - collision w M) ∧
        |swoExp w M f - iidExp w M f| ≤ 2 * F * collision w M / (1 - collision w M) ∧
        (collision w M ≤ 1 / 2 → |swoExp w M f - iidExp w M f| ≤ 4 * F * collision w M)

/-- The conditional Poisson law is the i.i.d. index law conditioned on distinctness, up to order: for
`w ∈ Δ^(M)` and a symmetric loss, `G(w) = Σ_S Π_w(S) L(x; z_S) = E°[L(x; z_I)]`, and the one-slot marginal is
`π_l / M = E°[#{k : I_k = l}/M]`. -/
def swor_cps : Prop :=
  ∀ (Z : Type) (n M : ℕ) (w : Fin n → ℝ) (L : Z → (Fin M → Z) → ℝ) (x : Z) (z : Fin n → Z) (l : Fin n),
    StatFormal.ICL.InDeltaM w M → (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
      collision w M < 1 ∧
      StatFormal.ICL.Grisk w M (lossSub L x z) = swoExp w M (fun j => L x (z ∘ j)) ∧
      (1 ≤ M → StatFormal.ICL.incl w M l / M =
        swoExp w M (fun j => ((univ.filter fun k => j k = l).card : ℝ) / M))

/-- `prop:swor-score`, value bound: under `as:score` (`0 < s_- ≤ s_θ ≤ s_+`), `as:kernel`
(`0 < K_min ≤ K ≤ K_max`) and `as:loss` (`L ∈ [0, B_L]`, symmetric), for `n ≥ M(M−1)s_+/s_-`,
`sup_Θ |J_{n,m} − J^iid_{n,m}| ≤ C₀/n` with `C₀ = 2M(M−1)(s_+/s_-)(B_L + Λ K_max/K_min)`, `0 ≤ λ_cov ≤ Λ`. -/
def swor_value : Prop :=
  ∀ (Z Θ : Type) (n M m : ℕ) (z : Fin n → Z) (zt : Fin m → Z) (s : Θ → Z → ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (sm sp BL Kmin Kmax lcov Λ lKL : ℝ),
    1 ≤ M → M ≤ n → 0 < m → 0 < sm → (∀ θ x, sm ≤ s θ x ∧ s θ x ≤ sp) →
    (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) → (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) → 0 ≤ lcov → lcov ≤ Λ →
    M * ((M : ℝ) - 1) * sp / sm ≤ n →
      ∀ θ, |jSwor L K z zt lcov lKL (wScore s z θ) - jIid L K z zt lcov lKL (wScore s z θ)| ≤
        swC0 M sm sp BL Kmin Kmax Λ / n

end Claims

end StatFormal.Wave11b
