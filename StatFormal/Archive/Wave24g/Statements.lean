import StatFormal.Archive.Wave9b.Statements
import StatFormal.Archive.Wave24d.Statements

/-!
# FROZEN STATEMENTS — wave 24g: refutation of SB `cor:field-local` as printed (DEFECTS #82)

Sources (current text, read 2026-10-16; `research-lines/data-fairness-repair/schrodinger_bridge_fairness_repair.tex`):
* `cor:field-local` (`:1088-1096`), with `def:standardisable` (`:933-949`), `thm:field` and its proof (`:957-995`),
  `ass:main` (`:352-355`, "in force throughout"), `ass:atomless`/`ass:ac` (`:357-360`, `:394-398`; not invoked by the
  corollary), the scalar `W₂` (`:338-343`), `rem:cheapparity` (`:1000-1012`) and `rem:local-scope` (`:1098-1114`).
  **Verbatim `cor:field-local`**: "Suppose only that $\mathrm{dist}(R_s,\mathfrak M)\le\delta_n$ and
  $\mathrm{dist}(\nu,\mathfrak M)\le\delta_n$ in $W_2$, and let $T_s$ be built from the $\mathfrak M$-projections. Then
  the parity gap of the plug-in is $O_\Prob(r_n+\delta_n)$. In particular if $\delta_n=O(n^{-1/2})$ the model error is
  statistically invisible: no test based on $n$ observations can distinguish the repair from an exactly
  parity-preserving one."
  **Verbatim `def:standardisable`**: "$\mathfrak M\subset\Pcal_2(\R^d)$ is standardisable at rate $r_n$ onto $\gamma$
  if there is a map $\mu\mapsto\Sbb_\mu$, defined on $\mathfrak M$, such that (i) $(\Sbb_\mu)_\#\mu=\gamma$ and
  $\Sbb_\mu$ is invertible $\gamma$-a.e.; (ii) from $n$ i.i.d. observations of $\mu$ one can construct
  $\widehat\Sbb_\mu$ with $\|\widehat\Sbb_\mu-\Sbb_\mu\|_{L^2(\mu)}=O_\Prob(r_n)$ and
  $\|\widehat\Sbb_\mu^{-1}-\Sbb_\mu^{-1}\|_{L^2(\gamma)}=O_\Prob(r_n)$ […]; (iii) $\Sbb_\nu^{-1}$ is $L$-Lipschitz on the
  support of $\gamma$, and $\widehat\Sbb_\nu^{-1}$ is $L$-Lipschitz on all of $\R^d$ with probability tending to one."
  The parity gap of the plug-in is `W₂((T̂₀)_#R₀, (T̂₁)_#R₁)`, `T̂_s = Ŝ_ν⁻¹ ∘ Ŝ_{R_s}` (`thm:field`).
Reuses the frozen `Wave9b` `Standardises` and the frozen `Wave24d` `Claims.field_local` (the repaired corollary, with
the added hypothesis that `Ŝ_{R'_s}` is `L_s`-Lipschitz), and Tau Ceti's `wassersteinEDist`, `HasFiniteMoment`.

Covered:
* `field_local_refuted_literal`: the printed corollary is false in the literal reading, for both readings of where the
  data of `Ŝ_{R'_s}` come from (`fromProj = true`: `n` i.i.d. observations of the projection `R'_s`, as
  `def:standardisable`(ii) literally says; `false`: of the data law `R_s`, the plug-in actually computable), and the
  data of `Ŝ_{ν'}⁻¹` likewise from `ν'` or `ν`; even with `R_s`, `ν` absolutely continuous.
* `field_local_refuted_charitable`: false in the charitable (population, oracle) reading as well: no estimation at all
  (`Ŝ = S`, which satisfies (ii) at every rate, so `r_n` may be taken `≤ δ_n` and the conclusion is `O(δ_n)`), all
  laws absolutely continuous, the forward maps continuous; the gap `W₂((T₀)_#R₀, (T₁)_#R₁)` of the population repair
  built from the projections is not `O(δ_n)` for a sequence `δ_n → 0`.
* `field_local_gap_lower`: the deterministic core, `W₂((F_b)_#μ_b, (F_b)_#μ_b(· − δ)) ≥ δ^{3/4}/100` for `δ ∈ (0,1]`
  (the mass `√δ/2` of `μ_b` on `(−δ, 0)` crosses the jump of `F_b'` at `0`; exactly, `W₂² ≥ δ^{3/2}/8`).
* `field_local_counterexample`: the instance satisfies every hypothesis (standardisable at every positive rate with the
  sign estimator, the unique projections, the distances, `ass:main`, absolute continuity).
* `field_local_forward_not_lipschitz`: `S_{μ_b} = F_b` is not Lipschitz (the hypothesis added by the frozen repair
  fails, as it must).
* `field_local_frozen_nonvacuous`: the hypotheses of the frozen repaired `field_local` hold for a Lipschitz instance
  with `δ > 0` and `R₁ ≠ R'₁`.

Fairness (every hypothesis of the corollary and of the standing assumptions is encoded, none weakened):
* `ass:main` (`R_s ∈ 𝒫₂`, "in force throughout"; `ν ∈ 𝒫₂` as in `def:repair`); `def:standardisable` (i)–(iii) with
  (ii) and (iii) strengthened (below); "`dist(·,𝔐) ≤ δ_n` in `W₂`" with the projections genuine **and unique**
  nearest points (the definite article; strengthened); the plug-in of `thm:field` built from the projections.
* `ass:atomless` and `ass:ac` are not standing (`:362-364`: `ass:main` "is in force throughout", `ass:atomless` "is
  invoked only where stated"; `:367-368`: "No density […] assumption is imposed on `R_0,R_1`"; `ass:ac` is invoked
  explicitly, e.g. `:906`), and the corollary invokes neither; nevertheless both readings assume absolute continuity of `R_s`, `ν` (hence atomlessness). The
  finite-entropy clause of `ass:ac` is not encoded (no differential entropy in Mathlib) but holds for the instance:
  `h(μ_b) = −∫ f log f = 2·log 2 − 1 = log 4 − 1` for `f = |x|^{-1/2}/4` on `[−1,1]` (`∫₀¹ x^{-1/2} log x dx = −4`),
  translation invariant, and `h(Unif[0,1]) = 0`.
* The target `ν = γ` is admissible: `thm:field` takes any `ν ∈ 𝔐`, and `rem:cheapparity` explicitly allows target `γ`
  ("one may simply take `T_s = S_{R_s}` with target `γ`"); the corollary does not require a barycentric target.
* (ii)'s `Ŝ_μ⁻¹` is an estimator of `S_μ⁻¹`, not required to invert `Ŝ_μ` (in `cor:field-cop` it is the empirical
  quantile function, which does not invert the empirical CDF); the instance's pair does invert a.e. in any case.
* Rates: `r_n` is the rate of `def:standardisable`; the statement is quantified over every admissible `r_n` and every
  `δ_n`, as printed. The instance is standardisable at **every** positive rate, so the printed conclusion must hold
  with `r_n = (n+1)^{-1/2}` and `δ_n = r_n/16 = O(n^{-1/2})`: the "in particular" regime itself.
* `O_P`: in the conclusion the weakest (eventual-in-`n`) form, so its negation is the strongest; in (ii) the eventual
  form together with finiteness of the errors for every sample, which implies the uniform-in-`n` form.

Readings. The natural reading (encoded): the plug-in `T̂_s` built from the projections is applied to the data, and
the gap is `W₂((T̂₀)_#R₀, (T̂₁)_#R₁)`. A degenerate reading applies `T̂_s` to the projections, gap
`W₂((T̂₀)_#R'₀, (T̂₁)_#R'₁)`: that is `thm:field` for `R'_s, ν' ∈ 𝔐` and is **true**, at `O_P(r_n)`, but then `δ_n`
plays no role and the "in particular" sentence (the repair is indistinguishable from an exactly parity-preserving
one) is empty; it is not encoded. So the printed corollary is ambiguous, and false under its natural reading. The
repaired statement (frozen `Wave24d` `field_local`) adds that `Ŝ_{R'_s}` is `L_s`-Lipschitz, which the instance's
`F_b` is not. "No test based on `n` observations can distinguish …" is informal (and withdrawn by `rem:local-scope`);
not encoded.

Encodings:
* `ℝ^d = EuclideanSpace ℝ (Fin d)`, `W₂ = wassersteinEDist 2` (infimum over couplings of `‖edist‖_{L²(π)}`, `ℝ≥0∞`; in
  `d = 1` it equals the paper's quantile formula), `L²` norms `eLpNorm · 2` (`ℝ≥0∞`); `𝒫₂` is `InP2` (probability with
  finite second moment, Tau Ceti `HasFiniteMoment 2`).
* `𝔐 : Set (Measure ℝ^d)`; the map `μ ↦ S_μ` and the inverses `μ ↦ S_μ⁻¹` are functions on all measures, constrained
  only on `𝔐`; (i) is the frozen `Standardises` (measurable `S`, `S⁻¹`, `S_#μ = γ`, two-sided a.e. inverses).
* (ii): the estimators are **procedures** `est n : (Fin n → ℝ^d) → (ℝ^d → ℝ^d)` (and `estInv`) applied to the sample
  alone, the same procedure for every member (it may not know `μ`); `O_P(r_n)` under `X ∼ μ^{⊗n}` (`iid μ n`, a
  `Measure.pi`) is `BigOPSeq` (the frozen Wave 9b `BigOP` with `n`-dependent sample spaces: for every `η > 0` there are
  `M`, `N` and, for `n ≥ N`, a measurable event of probability `≥ 1 − η` on which the quantity is `≤ M r_n`).
* (iii) strengthened (safe for a refutation): `S_μ⁻¹` `L`-Lipschitz on all of `ℝ^d` for **every** member, and
  `est⁻¹` `L`-Lipschitz for **every** sample.
* The corollary: triangular arrays `R n s`, `ν n` in `𝒫₂` (`ass:main`), absolutely continuous, projections
  `R' n s`, `ν' n ∈ 𝔐` that are the unique `W₂`-nearest points (`IsW2Proj`) at distance `≤ δ_n`, `0 < δ_n ≤ r_n`, `0 < r_n → 0` (the "in particular"
  regime; extra hypotheses are safe for a refutation); the plug-in `T̂_s = est⁻¹(Xν) ∘ est(X_s)` with independent
  samples `X₀, X₁, Xν` of size `n` (`sampleLaw`); the conclusion `gap_n = O_P(r_n + δ_n)`.
* The counterexample (`d = 1`): `γ = ν = Unif[0,1]` (`gammaU`), `μ_b = (Q_b)_#Unif[0,1]` (`muB`, density
  `|x|^{-1/2}/4` on `[−1,1]`), `Q_b(u) = (2u−1)|2u−1|` on `[0,1]` (clamped outside, so globally 4-Lipschitz),
  `F_b(x) = ½ + sign(x)√|x|/2` on `[−1,1]` (the CDF of `μ_b`, `0`/`1` outside; written with `max`/`min` so that no `√`
  of a negative number occurs), `𝔐 = {γ, μ_b}` (`famM`), `S_γ = id`, `S_{μ_b} = F_b`; the sign estimator
  `est n X = F_b` if some observation is negative, `id` otherwise (`signEst`, `signEstInv` with `Q_b`); `R₀ = μ_b`,
  `R₁ = μ_b(· − δ_n)` (`shiftLaw`), both projecting uniquely onto `μ_b`; `r_n = (n+1)^{-1/2}`, `δ_n = r_n/16`.
DRAFT — not yet in `certify/statements.lock`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set Filter
open scoped ENNReal NNReal Topology

namespace StatFormal.Wave24g

open StatFormal.Wave9b (Standardises)

local notation "𝔼" d => EuclideanSpace ℝ (Fin d)

/-! ### The printed corollary -/

/-- `X_n = O_P(a_n)` for a triangular array (sample spaces `Ω n` depending on `n`): for every `η > 0` there are `M`
and `N` such that for every `n ≥ N` some measurable event of probability `≥ 1 − η` carries `X_n ≤ M a_n`. -/
def BigOPSeq {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n)) (a : ℕ → ℝ)
    (X : ∀ n, Ω n → ℝ≥0∞) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∃ A : Set (Ω n), MeasurableSet A ∧
    ENNReal.ofReal (1 - η) ≤ P n A ∧ ∀ ω ∈ A, X n ω ≤ ENNReal.ofReal (M * a n)

/-- The law of `n` i.i.d. observations of `μ`. -/
def iid {d : ℕ} (μ : Measure (𝔼 d)) (n : ℕ) : Measure (Fin n → 𝔼 d) := Measure.pi fun _ => μ

/-- `μ ∈ 𝒫₂(ℝ^d)`. -/
def InP2 {d : ℕ} (μ : Measure (𝔼 d)) : Prop := IsProbabilityMeasure μ ∧ HasFiniteMoment 2 μ

/-- `μ'` is the `W₂`-projection of `μ` onto `𝔐`: a nearest point, and the only one (uniqueness is an extra
hypothesis, safe for a refutation; it covers the reading in which "the `𝔐`-projection" presupposes it). -/
def IsW2Proj {d : ℕ} (𝔐 : Set (Measure (𝔼 d))) (μ μ' : Measure (𝔼 d)) : Prop :=
  μ' ∈ 𝔐 ∧ (∀ ρ ∈ 𝔐, wassersteinEDist 2 μ μ' ≤ wassersteinEDist 2 μ ρ) ∧
    ∀ ρ ∈ 𝔐, wassersteinEDist 2 μ ρ ≤ wassersteinEDist 2 μ μ' → ρ = μ'

/-- `def:standardisable` at rate `r` with the estimating procedures `est`, `estInv` (functions of the sample alone);
(ii) strengthened by finiteness of both errors for every sample (so the eventual and the uniform-in-`n` forms of
`O_P` coincide), (iii) strengthened to every member and every sample. -/
def IsStandardisable {d : ℕ} (𝔐 : Set (Measure (𝔼 d))) (γ : Measure (𝔼 d))
    (S Sinv : Measure (𝔼 d) → (𝔼 d) → 𝔼 d) (r : ℕ → ℝ)
    (est estInv : ∀ n : ℕ, (Fin n → 𝔼 d) → (𝔼 d) → 𝔼 d) (L : ℝ≥0) : Prop :=
  InP2 γ ∧ (∀ μ ∈ 𝔐, InP2 μ) ∧ (∀ μ ∈ 𝔐, Standardises μ γ (S μ) (Sinv μ)) ∧
    (∀ n X, Measurable (est n X)) ∧ (∀ n X, Measurable (estInv n X)) ∧
    (∀ μ ∈ 𝔐, BigOPSeq (Ω := fun n => Fin n → 𝔼 d) (iid μ) r
      fun n X => eLpNorm (fun x => est n X x - S μ x) 2 μ) ∧
    (∀ μ ∈ 𝔐, BigOPSeq (Ω := fun n => Fin n → 𝔼 d) (iid μ) r
      fun n X => eLpNorm (fun z => estInv n X z - Sinv μ z) 2 γ) ∧
    (∀ μ ∈ 𝔐, ∀ n X, eLpNorm (fun x => est n X x - S μ x) 2 μ ≠ ∞) ∧
    (∀ μ ∈ 𝔐, ∀ n X, eLpNorm (fun z => estInv n X z - Sinv μ z) 2 γ ≠ ∞) ∧
    (∀ μ ∈ 𝔐, LipschitzWith L (Sinv μ)) ∧ (∀ n X, LipschitzWith L (estInv n X))

/-- The joint law of three independent samples of size `n` (group `0`, group `1`, target). -/
def sampleLaw {d : ℕ} (D₀ D₁ Dν : Measure (𝔼 d)) (n : ℕ) :
    Measure ((Fin n → 𝔼 d) × (Fin n → 𝔼 d) × (Fin n → 𝔼 d)) :=
  (iid D₀ n).prod ((iid D₁ n).prod (iid Dν n))

/-- The parity gap `W₂((T̂₀)_#R₀, (T̂₁)_#R₁)` of the plug-in `T̂_s = est⁻¹(Xν) ∘ est(X_s)`. -/
def plugGap {d : ℕ} (est estInv : ∀ n : ℕ, (Fin n → 𝔼 d) → (𝔼 d) → 𝔼 d) (R₀ R₁ : Measure (𝔼 d)) (n : ℕ)
    (ω : (Fin n → 𝔼 d) × (Fin n → 𝔼 d) × (Fin n → 𝔼 d)) : ℝ≥0∞ :=
  wassersteinEDist 2 (R₀.map (estInv n ω.2.2 ∘ est n ω.1)) (R₁.map (estInv n ω.2.2 ∘ est n ω.2.1))

/-- SB `cor:field-local`, literal reading: for every family standardisable at rate `r_n` and every `δ_n`, if the
(absolutely continuous, `𝒫₂`) laws `R_s`, `ν` lie within `δ_n` of their unique `W₂`-projections `R'_s`, `ν'`, then the
parity gap of the plug-in `T̂_s = Ŝ_{ν'}⁻¹ ∘ Ŝ_{R'_s}` applied to the data `R_s` is `O_P(r_n + δ_n)`.
`fromProj = true`: the estimators of the projections are computed from observations of the projections
(`def:standardisable`(ii) verbatim); `false`: from the data laws `R_s`, `ν`. (Applying `T̂_s` to `R'_s` instead is
the degenerate reading, which is `thm:field` and true; see the module header.) -/
def FieldLocalPrinted (fromProj : Bool) : Prop :=
  ∀ (d : ℕ) (𝔐 : Set (Measure (𝔼 d))) (γ : Measure (𝔼 d)) (S Sinv : Measure (𝔼 d) → (𝔼 d) → 𝔼 d)
    (est estInv : ∀ n : ℕ, (Fin n → 𝔼 d) → (𝔼 d) → 𝔼 d) (L : ℝ≥0) (r δ : ℕ → ℝ)
    (R R' : ℕ → Fin 2 → Measure (𝔼 d)) (ν ν' : ℕ → Measure (𝔼 d)),
    IsStandardisable 𝔐 γ S Sinv r est estInv L → (∀ n, 0 < r n) → Tendsto r atTop (𝓝 0) →
    (∀ n, 0 < δ n) → (∀ n, δ n ≤ r n) →
    (∀ n s, InP2 (R n s) ∧ R n s ≪ volume) → (∀ n, InP2 (ν n) ∧ ν n ≪ volume) →
    (∀ n s, IsW2Proj 𝔐 (R n s) (R' n s)) → (∀ n, IsW2Proj 𝔐 (ν n) (ν' n)) →
    (∀ n s, wassersteinEDist 2 (R n s) (R' n s) ≤ ENNReal.ofReal (δ n)) →
    (∀ n, wassersteinEDist 2 (ν n) (ν' n) ≤ ENNReal.ofReal (δ n)) →
      BigOPSeq (Ω := fun n => (Fin n → 𝔼 d) × (Fin n → 𝔼 d) × (Fin n → 𝔼 d))
        (fun n => sampleLaw (if fromProj then R' n 0 else R n 0) (if fromProj then R' n 1 else R n 1)
          (if fromProj then ν' n else ν n) n)
        (fun n => r n + δ n) (fun n ω => plugGap est estInv (R n 0) (R n 1) n ω)

/-- The population version of `def:standardisable`, (i) and (iii), with absolutely continuous members and reference
and continuous forward maps. -/
def PopStandardisable {d : ℕ} (𝔐 : Set (Measure (𝔼 d))) (γ : Measure (𝔼 d))
    (S Sinv : Measure (𝔼 d) → (𝔼 d) → 𝔼 d) (L : ℝ≥0) : Prop :=
  InP2 γ ∧ γ ≪ volume ∧ (∀ μ ∈ 𝔐, InP2 μ ∧ μ ≪ volume) ∧ (∀ μ ∈ 𝔐, Standardises μ γ (S μ) (Sinv μ)) ∧
    (∀ μ ∈ 𝔐, Continuous (S μ)) ∧ (∀ μ ∈ 𝔐, LipschitzWith L (Sinv μ))

/-- SB `cor:field-local`, charitable reading: the oracle (population) repair `T_s = S_{ν'}⁻¹ ∘ S_{R'_s}` built from
the projections, applied to the true `R_s`, has parity gap `O(δ_n)` along every sequence `δ_n → 0`, for absolutely
continuous `R_s`, `ν` (hence atomless). -/
def FieldLocalCharitable : Prop :=
  ∀ (d : ℕ) (𝔐 : Set (Measure (𝔼 d))) (γ : Measure (𝔼 d)) (S Sinv : Measure (𝔼 d) → (𝔼 d) → 𝔼 d)
    (L : ℝ≥0) (δ : ℕ → ℝ) (R R' : ℕ → Fin 2 → Measure (𝔼 d)) (ν ν' : ℕ → Measure (𝔼 d)),
    PopStandardisable 𝔐 γ S Sinv L → (∀ n, 0 < δ n) → Tendsto δ atTop (𝓝 0) →
    (∀ n s, InP2 (R n s) ∧ R n s ≪ volume) → (∀ n, InP2 (ν n) ∧ ν n ≪ volume) →
    (∀ n s, IsW2Proj 𝔐 (R n s) (R' n s)) → (∀ n, IsW2Proj 𝔐 (ν n) (ν' n)) →
    (∀ n s, wassersteinEDist 2 (R n s) (R' n s) ≤ ENNReal.ofReal (δ n)) →
    (∀ n, wassersteinEDist 2 (ν n) (ν' n) ≤ ENNReal.ofReal (δ n)) →
      ∃ C : ℝ, ∀ᶠ n in atTop,
        wassersteinEDist 2 ((R n 0).map (Sinv (ν' n) ∘ S (R' n 0))) ((R n 1).map (Sinv (ν' n) ∘ S (R' n 1))) ≤
          ENNReal.ofReal (C * δ n)

/-! ### The counterexample (`d = 1`) -/

/-- `ℝ¹`. -/
abbrev E1 : Type := EuclideanSpace ℝ (Fin 1)

/-- `t ↦ (t) ∈ ℝ¹`. -/
def toE1 (t : ℝ) : E1 := WithLp.toLp 2 (fun _ => t)

/-- `Unif[0,1]`. -/
def unif01 : Measure ℝ := volume.restrict (Icc 0 1)

/-- Clamp to `[0,1]`. -/
def clamp01 (u : ℝ) : ℝ := max 0 (min u 1)

/-- `Q_b(u) = (2u − 1)|2u − 1|` on `[0,1]` (the quantile function of `μ_b`), clamped outside. -/
def Qb (u : ℝ) : ℝ := (2 * clamp01 u - 1) * |2 * clamp01 u - 1|

/-- `F_b(x) = ½ + sign(x)√|x|/2` on `[−1,1]`, `0` below, `1` above: the CDF of `μ_b`. -/
def Fb (x : ℝ) : ℝ := (1 + Real.sqrt (max 0 (min x 1)) - Real.sqrt (max 0 (min (-x) 1))) / 2

/-- `γ = ν = Unif[0,1]` on `ℝ¹`. -/
def gammaU : Measure E1 := unif01.map toE1

/-- `μ_b = (Q_b)_#Unif[0,1]`, density `|x|^{−1/2}/4` on `[−1,1]`. -/
def muB : Measure E1 := unif01.map (toE1 ∘ Qb)

/-- `μ(· − δ)`, the law of `X + δ`, `X ∼ μ`. -/
def shiftLaw (δ : ℝ) (μ : Measure E1) : Measure E1 := μ.map fun x => x + toE1 δ

/-- `S_{μ_b} = F_b` on `ℝ¹`. -/
def SbE (x : E1) : E1 := toE1 (Fb (x 0))

/-- `S_{μ_b}⁻¹ = Q_b` on `ℝ¹`. -/
def QbE (z : E1) : E1 := toE1 (Qb (z 0))

/-- `𝔐 = {Unif[0,1], μ_b}`. -/
def famM : Set (Measure E1) := {gammaU, muB}

open scoped Classical in
/-- `μ ↦ S_μ`: `F_b` for `μ_b`, the identity otherwise. -/
def famS (μ : Measure E1) : E1 → E1 := if μ = muB then SbE else id

open scoped Classical in
/-- `μ ↦ S_μ⁻¹`: `Q_b` for `μ_b`, the identity otherwise. -/
def famSinv (μ : Measure E1) : E1 → E1 := if μ = muB then QbE else id

open scoped Classical in
/-- The sign estimator: `F_b` if some observation is negative, the identity otherwise. -/
def signEst (n : ℕ) (X : Fin n → E1) : E1 → E1 := if ∃ i, (X i) 0 < 0 then SbE else id

open scoped Classical in
/-- Its inverse: `Q_b` if some observation is negative, the identity otherwise. -/
def signEstInv (n : ℕ) (X : Fin n → E1) : E1 → E1 := if ∃ i, (X i) 0 < 0 then QbE else id

namespace Claims

/-- SB `cor:field-local` is false as printed (literal reading, plug-in applied to the data), whichever data the
projections' estimators use. -/
def field_local_refuted_literal : Prop := ∀ fromProj : Bool, ¬ FieldLocalPrinted fromProj

/-- It is false in the charitable (population, oracle, absolutely continuous) reading too. -/
def field_local_refuted_charitable : Prop := ¬ FieldLocalCharitable

/-- The deterministic core: the population parity gap of the counterexample is at least `δ^{3/4}/100`, so it is not
`O(δ)`. -/
def field_local_gap_lower : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ENNReal.ofReal (δ ^ (3 / 4 : ℝ) / 100) ≤ wassersteinEDist 2 (muB.map SbE) ((shiftLaw δ muB).map SbE)

/-- The counterexample satisfies the hypotheses: `𝔐 = {γ, μ_b}` is standardisable onto `γ` at every positive rate with
the sign estimator and `L = 4`, and in the population sense; `μ_b ≠ γ`; for `δ ∈ (0, 1/16]` the shifted law is in
`𝒫₂`, absolutely continuous, within `δ` of `μ_b`, and `μ_b` is its unique `W₂`-projection onto `𝔐`. -/
def field_local_counterexample : Prop :=
  (∀ r : ℕ → ℝ, (∀ n, 0 < r n) → IsStandardisable famM gammaU famS famSinv r signEst signEstInv 4) ∧
    PopStandardisable famM gammaU famS famSinv 4 ∧ muB ≠ gammaU ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 →
      InP2 (shiftLaw δ muB) ∧ shiftLaw δ muB ≪ volume ∧ IsW2Proj famM (shiftLaw δ muB) muB ∧
        wassersteinEDist 2 (shiftLaw δ muB) muB ≤ ENNReal.ofReal δ

/-- The forward map `S_{μ_b} = F_b` is not Lipschitz (the hypothesis added by the frozen repaired `field_local`). -/
def field_local_forward_not_lipschitz : Prop := ∀ K : ℝ≥0, ¬ LipschitzWith K SbE

/-- Nonvacuity of the frozen repaired corollary (`Wave24d.Claims.field_local`): its hypotheses hold for an instance
with `δ > 0`, `δ < ∞` and `R₁ ≠ R'₁` (`R₁ = Unif[0,1] + ½`, everything else `Unif[0,1]`, all maps the identity). -/
def field_local_frozen_nonvacuous : Prop :=
  ∃ (R R' : Fin 2 → Measure E1) (ν' γ : Measure E1) (S Sinv Shat : Fin 2 → E1 → E1)
    (Sν Sνinv Sνinvhat : E1 → E1) (L : ℝ≥0) (Ls : Fin 2 → ℝ≥0) (δ : ℝ≥0∞),
    (∀ s, IsProbabilityMeasure (R s)) ∧ (∀ s, IsProbabilityMeasure (R' s)) ∧ IsProbabilityMeasure ν' ∧
    IsProbabilityMeasure γ ∧ (∀ s, Standardises (R' s) γ (S s) (Sinv s)) ∧ Standardises ν' γ Sν Sνinv ∧
    (∀ s, Measurable (Shat s)) ∧ (∀ s, LipschitzWith (Ls s) (Shat s)) ∧ Measurable Sνinvhat ∧
    LipschitzWith L Sνinvhat ∧ (∀ s, wassersteinEDist 2 (R s) (R' s) ≤ δ) ∧ 0 < δ ∧ δ ≠ ⊤ ∧ R 1 ≠ R' 1

end Claims
end StatFormal.Wave24g
