import StatFormal.Archive.Wave30z.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Statements

/-!
# FROZEN STATEMENTS (DRAFT) — wave 30ah: trimmed-mmd `thm:boundary` / `cor:boundary-linear`, the declared gaps
# of wave 30z (attainment, nearest pair, the contact level `α*_r`, `α*_r ≤ TV`, the half-normal / chi-bar-square
# shape), the proof lemmas `lem:supdir`, `lem:Hprops`, and `prop:bangbang` "nonempty, convex and compact"

Source (read 2026-10-20, working tree): `trimmed-mmd/supplement.tex`, setting `supp:boundarystate` (`:2765-2822`;
`α*_r` and "It satisfies `α*_r ≤ TV(P,Q)` when `TV(P,Q) < 1` (a common trimming embeds into both regions)" at
`:2814-2819`), `thm:boundary` (`:2824-2848`: (i) "max", "`G* ⊆ 𝔹_r` is the nonempty compact set of maximizers",
"for any nearest pair"; (ii) "in particular at `α = α*_r`, whenever the two regions meet at some level below one",
"max"), the sentences after the theorem (`:2850-2852`: "The limit in (ii) is nonnegative (take `g = 0`, using
Lemma lem:Hprops(a)), and it is degenerate at zero when `K° = {0}`"), `cor:boundary-linear` (a) (`:2877-2879`:
"a law with an atom of mass `1/2` at zero and a half-normal law on `(0,∞)` when `σ > 0`; its square is `σ²` times
the chi-bar-square variable `½δ₀ + ½χ²₁`"), `lem:supdir` (`:2916-2928`), `lem:Hprops` (`:2950-2958`);
`paper.tex:1302-1325` (`eq:trimset-emp`, `prop:bangbang`: "`𝒯_α` is nonempty, convex and compact").
Imports the frozen wave-30z statements (`hinge`, `Idx1`, `Idx2`, `argminSet`, `Hfun`, `Gstar`, `boundaryLim`,
`IsLimitGP`, `SampleModel`, `Scaling`) and through them the wave-30v ones (`supFun`, `supportFn`, `Ball`, `ballNeg`,
`polarSet`, `coneHull`), the frozen `TrimmedMMD/ZeroSet` (`tvDist` through `Foundations/Distances/TV`), and the
frozen `TrimmedMMD/BangBang` (`capped`, `qp`); not copied.

Covered (targets; label map):
* `thm:boundary` (i), attainment — `boundary_max_every`: `G*` is nonempty and COMPACT, and for EVERY path `v` of the
  limit process (`c_P, c_Q ≥ 0`) the supremum of `g ↦ −c_P H_P(−g) − c_Q H_Q(g)` over `G*` is a maximum (attained;
  it equals the frozen `sSup` of wave 30z `boundary_every`).
* `thm:boundary` (ii), attainment — `boundary_max_contact`: `K° ∩ 𝔹_r` is nonempty and compact and the supremum
  over it is attained, for every path.
* `thm:boundary` (i), "for any nearest pair" — `boundary_nearest`: a nearest pair `a* ∈ A`, `b* ∈ B`,
  `‖a* − b*‖ = D`, exists (so the `D > 0` description of `G*` in `boundary_every` is not vacuous).
* setting, `α*_r` — `boundary_contact_level`: if the regions meet at some level in `[0, 1)`, then
  `α*_r ∈ [0, 1)` and they meet AT `α*_r` (the infimum is attained); `boundary_contact_star`: hence (ii) holds at
  `α = α*_r` (its three conclusions, the limit law included).
* setting, `α*_r ≤ TV` — `boundary_level_tv`: `TV(P, Q) < 1 ⇒ α*_r ≤ TV(P, Q)` (any bounded feature map).
* sentences after `thm:boundary` — `boundary_contact_nonneg`: almost surely the limit of (ii) is `≥ 0`, and it is
  `0` when `K° = {0}`.
* `cor:boundary-linear` (a), shape — `boundary_ray_shape`: for `Z ∼ N(0, σ²)`, `σ > 0`: the law of `Z_+` is
  `½δ₀ + ½·HN(σ)` (`HN(σ)` = law of `|Z|`, the half-normal law, carried by `(0, ∞)`), and the law of `Z_+²` is the
  law of `σ²·χ̄²`, `χ̄² ∼ ½δ₀ + ½χ²₁`; `boundary_ray_square`: in the setting of (a) with unique quantiles,
  `(r_k D̂)² ⇒ Z_+²` (whose law is that of `σ² χ̄²`).
* `lem:supdir` — `boundary_supdir`: for `Θ` compact (nonempty), `z₀, h ∈ C(Θ)`, bounded `h_k → h` uniformly
  (`ℓ^∞(Θ)` convergence, `h_k` NOT required continuous), `t_k ↓ 0`: `Θ₀` is nonempty compact, `max_{Θ₀} h` is
  attained, and `(Ψ(z₀ + t_k h_k) − Ψ(z₀))/t_k → max_{Θ₀} h`, `Ψ(z) = sup_Θ z`.
* `lem:Hprops` — `boundary_Hprops`: almost surely (a) `H(0) = 0`, (b) `H(λf) = λH(f)` for `λ ∈ [0,1]`; (c) at
  `α = 0`, a.s. `H_P(f) = 𝔾_P ℓ_{f,−κ} = 𝔾_P⟨f, φ⟩` for every `f`, and this equals `⟨f, G⟩` for a random vector
  `G` (`= 𝔾_P φ`) with `⟨u, G⟩ ∼ N(0, Var_P⟨u, φ⟩)` for every `u` (the law of `𝔾_P φ`); (d) `q_P(f) = {t_f}` ⇒
  `H_P(f) = β 𝔾_P ℓ_{f,t_f} ∼ N(0, β² Var_P ℓ_{f,t_f})`; the same for `H_Q`.
* `prop:bangbang`, first sentence — `bangbang_set`: `𝒯_α` is nonempty, convex and compact.

Not covered (declared): that `α*_r` "can lie strictly below" `TV` (`rem:boundary-examples`, an example);
`rem:boundary-reading` (`H_P` as the limit of the support-function process); the density form of the half-normal
law (`HN(σ)` is stated as the law of `|Z|`); the Hausdorff continuity in `α` of Step 5 (only the attainment of
`α*_r` is stated, via nested compact sets, not via Hausdorff continuity).

Encodings (to be checked by the critic):
* Setting of wave 30z (finite-dimensional `E`, `φ` strongly measurable, `‖φ‖ ≤ κ`, `α ∈ [0,1)`).
* `α*_r` is `contactLevel φ P Q = sInf {α | 0 ≤ α ∧ α < 1 ∧ (𝒞_α(P) ∩ 𝒞_α(Q)).Nonempty}` (real `sInf`; junk `0`
  for the empty set — every claim on it assumes the set nonempty, or `TV < 1`, which makes it nonempty).
* `TV` is the frozen `tvDist` (`sup_A |P(A) − Q(A)|`, the paper's normalisation `TV ∈ [0, 1]`).
* "max" is `IsGreatest` of the image (attainment), plus the identity with the frozen `sSup`.
* Half-normal law `HN(σ)` = `(gaussianReal 0 σ²).map |·|`; `χ²₁` = `(gaussianReal 0 1).map (·²)`;
  `χ̄² = ½δ₀ + ½χ²₁` (`chiBarSq`); "`σ²` times `χ̄²`" = `chiBarSq.map (σ² · ·)`.
* `ℓ^∞(Θ)`: functions `Θ → ℝ` that are bounded; `h_k → h` in `ℓ^∞` is `TendstoUniformly`. `Ψ(z) = sSup (range z)`.
* `𝔾_P φ` (lem:Hprops (c)): the limit process is indexed by the hinges only; `𝔾_P⟨f, φ⟩` is `𝔾_P ℓ_{f,−κ}`
  (`ℓ_{f,−κ} = ⟨f, φ⟩ + κ`, and `𝔾_P` kills constants), and `G` is the random vector with `⟨f, G⟩ = 𝔾_P ℓ_{f,−κ}`.
* `𝒯_α` (`trimSetEmp`): the minimisers of the frozen `qp` over the frozen `capped n α ×ˢ capped m β`.
* `lem:supdir`: `Θ` is assumed NONEMPTY (the printed lemma says "compact metric space"; its proof uses
  `Θ₀ ≠ ∅`, false for `Θ = ∅`, where `max_{Θ₀}` is undefined) — see the report's OLD/NEW.

Junk audit:
* `contactLevel` is a real `sInf`: `0` on the empty set; `boundary_contact_level`/`_star` assume a meeting level in
  `[0, 1)` (non-vacuous: e.g. `P = Q`), `boundary_level_tv` assumes `TV < 1`, under which the set contains `TV`.
* The frozen `sSup` in `boundary_every`/`boundary_contact` is of a nonempty set bounded by `(|c_P| + |c_Q|) β ‖v‖`
  (`abs_Hfun_le`), so it is genuine; the attainment claims add `IsGreatest` and identify it with that `sSup`.
* `Hfun` is `β · sInf` over the nonempty compact `argminSet` (genuine). In (c), the index point `(f, −κ)` is quantified
  as `∀ t, (t : ℝ) = −κ → …`; such a `t` exists because `κ ≥ 0` (`P` is a probability measure and `‖φ‖ ≤ κ`).
* `halfNormal`, `chiSq1`, `chiBarSq` are probability measures (maps / convex combinations of probability measures);
  `σ² > 0` as printed (`σ = 0` gives the Dirac law, no half-normal part).
* `Var` (Mathlib `variance`) of bounded measurable functions: genuine. `μ'.map` of a non-a.e.-measurable map would be
  `0`; the equalities with Gaussian laws therefore also force a.e.-measurability.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30ah

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)
open StatFormal.Wave30v (supFun supportFn Ball ballNeg polarSet coneHull)
open StatFormal.Wave30z (hinge Idx1 Idx2 argminSet Hfun Gstar boundaryLim IsLimitGP SampleModel Scaling)
open StatFormal.TrimmedMMD.BangBang (capped qp)

/-- The `r`-feature contact level `α*_r = inf {α ∈ [0, 1) : 𝒞_α(P) ∩ 𝒞_α(Q) ≠ ∅}`. -/
def contactLevel {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝒳 → E) (P Q : Measure 𝒳) : ℝ :=
  sInf {α : ℝ | 0 ≤ α ∧ α < 1 ∧ (region φ α P ∩ region φ α Q).Nonempty}

/-- The half-normal law: the law of `|Z|`, `Z ∼ N(0, σ²)`. -/
def halfNormal (σ2 : ℝ) : Measure ℝ := (gaussianReal 0 σ2.toNNReal).map fun x => |x|

/-- The chi-square law with one degree of freedom, `χ²₁`: the law of `N²`, `N ∼ N(0, 1)`. -/
def chiSq1 : Measure ℝ := (gaussianReal 0 1).map fun x => x ^ 2

/-- The chi-bar-square law `½δ₀ + ½χ²₁`. -/
def chiBarSq : Measure ℝ := (1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • chiSq1

/-- The empirical trimming set `𝒯_α` (`eq:trimset-emp`): the minimisers of `eq:qp` over `Δ_α(n) × Δ_β(m)`. -/
def trimSetEmp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n m : ℕ} (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ) : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | p ∈ capped n α ×ˢ capped m β ∧ IsMinOn (qp x y) (capped n α ×ˢ capped m β) p}

namespace Claims

/-- `thm:boundary` (i), "max" and "`G* ⊆ 𝔹_r` is the nonempty compact set of maximizers": `G*` is nonempty and
compact, and for every path `v` of the limit process and `c_P, c_Q ≥ 0` the supremum of
`g ↦ −c_P H_P(−g) − c_Q H_Q(g)` over `G*` is attained (and equals the `sSup` of wave 30z `boundary_every`). -/
def boundary_max_every : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (cP cQ : ℝ) (v : C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 ≤ cP → 0 ≤ cQ →
      (Gstar φ α P Q).Nonempty ∧ IsCompact (Gstar φ α P Q) ∧
      ∃ g ∈ Gstar φ α P Q, IsGreatest (boundaryLim φ α P Q κ cP cQ v '' Gstar φ α P Q)
          (boundaryLim φ α P Q κ cP cQ v g) ∧
        sSup (boundaryLim φ α P Q κ cP cQ v '' Gstar φ α P Q) = boundaryLim φ α P Q κ cP cQ v g

/-- `thm:boundary` (ii), "max": `K° ∩ 𝔹_r` is nonempty and compact, and for every path `v` and `c_P, c_Q ≥ 0` the
supremum over it of `g ↦ −c_P H_P(−g) − c_Q H_Q(g)` is attained (the contact hypothesis is not needed). -/
def boundary_max_contact : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (cP cQ : ℝ) (v : C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 ≤ cP → 0 ≤ cQ →
      let S : Set (Ball E) := {g | (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))}
      S.Nonempty ∧ IsCompact S ∧
      ∃ g ∈ S, IsGreatest (boundaryLim φ α P Q κ cP cQ v '' S) (boundaryLim φ α P Q κ cP cQ v g) ∧
        sSup (boundaryLim φ α P Q κ cP cQ v '' S) = boundaryLim φ α P Q κ cP cQ v g

/-- `thm:boundary` (i), "for any nearest pair `a* ∈ A`, `b* ∈ B`": a nearest pair exists. -/
def boundary_nearest : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      ∃ a ∈ region φ α P, ∃ b ∈ region φ α Q, ‖a - b‖ = Dpop φ P Q α

/-- Setting of `thm:boundary` and (ii) "in particular at `α = α*_r`, whenever the two regions meet at some level
below one": if `𝒞_α(P) ∩ 𝒞_α(Q) ≠ ∅` for some `α ∈ [0, 1)`, then `α*_r ∈ [0, 1)` and the regions meet at `α*_r`. -/
def boundary_contact_level : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    (∃ α, 0 ≤ α ∧ α < 1 ∧ (region φ α P ∩ region φ α Q).Nonempty) →
      0 ≤ contactLevel φ P Q ∧ contactLevel φ P Q < 1 ∧
        (region φ (contactLevel φ P Q) P ∩ region φ (contactLevel φ P Q) Q).Nonempty

/-- `thm:boundary` (ii) at `α = α*_r`: whenever the regions meet at some level below one, the three conclusions of
(ii) hold at `α = α*_r` (the cone identity, `G* = K° ∩ 𝔹_r`, and `r_k D̂ ⇒ max_{K° ∩ 𝔹_r} {…}`). -/
def boundary_contact_star : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (∃ α, 0 ≤ α ∧ α < 1 ∧ (region φ α P ∩ region φ α Q).Nonempty) →
      let a := contactLevel φ P Q
      (∀ z ∈ region φ a P ∩ region φ a Q, closure (coneHull (region φ a Q - region φ a P)) =
        closure (StatFormal.Wave30v.tanCone (region φ a Q) z - StatFormal.Wave30v.tanCone (region φ a P) z)) ∧
      (∀ g : Ball E, g ∈ Gstar φ a P Q ↔ (g : E) ∈ polarSet (closure (coneHull (region φ a Q - region φ a P)))) ∧
      TendstoInDistribution
        (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) a)
        atTop (fun ω' => sSup (boundaryLim φ a P Q κ cP cQ (𝔾 ω') ''
          {g | (g : E) ∈ polarSet (closure (coneHull (region φ a Q - region φ a P)))})) (fun _ => μ) μ'

/-- Setting of `thm:boundary`: "`α*_r ≤ TV(P,Q)` when `TV(P,Q) < 1` (a common trimming embeds into both regions)". -/
def boundary_level_tv : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 →
      contactLevel φ P Q ≤ StatFormal.Distances.tvDist P Q

/-- After `thm:boundary`: "The limit in (ii) is nonnegative (take `g = 0`, using Lemma lem:Hprops(a)), and it is
degenerate at zero when `K° = {0}`": almost surely `max_{K° ∩ 𝔹_r} {−c_P H_P(−g) − c_Q H_Q(g)} ≥ 0`, and `= 0`
when `K° = {0}`. -/
def boundary_contact_nonneg : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → IsLimitGP φ P Q 1 1 κ μ' 𝔾 →
      ∀ᵐ ω' ∂μ',
        0 ≤ sSup (boundaryLim φ α P Q κ cP cQ (𝔾 ω') ''
          {g | (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))}) ∧
        (polarSet (closure (coneHull (region φ α Q - region φ α P))) = {0} →
          sSup (boundaryLim φ α P Q κ cP cQ (𝔾 ω') ''
            {g | (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))}) = 0)

/-- `cor:boundary-linear` (a), the shape of the limit: for `Z ∼ N(0, σ²)` with `σ > 0`, `Z_+` has "an atom of mass
`1/2` at zero and a half-normal law on `(0,∞)`": `law(Z_+) = ½δ₀ + ½ law(|Z|)`, with `law(|Z|)` carried by `(0, ∞)`;
and "its square is `σ²` times the chi-bar-square variable `½δ₀ + ½χ²₁`": `law(Z_+²) = law(σ² χ̄²)`. -/
def boundary_ray_shape : Prop :=
  ∀ σ2 : ℝ, 0 < σ2 →
    (gaussianReal 0 σ2.toNNReal).map (fun x => max x 0) =
        (1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • halfNormal σ2 ∧
      halfNormal σ2 (Iic 0) = 0 ∧
      (gaussianReal 0 σ2.toNNReal).map (fun x => (max x 0) ^ 2) = chiBarSq.map (fun y => σ2 * y)

/-- `cor:boundary-linear` (a), "its square": in the setting of (a) with unique quantiles `q_P(−ν) = {t_P}`,
`q_Q(ν) = {s_Q}`, `(r_k D̂)² ⇒ Z_+²`, `Z ∼ N(0, σ²)` with the printed `σ²`; for `σ > 0` the law of `Z_+²` is that of
`σ² χ̄²` (`boundary_ray_shape`). -/
def boundary_ray_square : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (ν : Ball E) (tP sQ : Icc (-κ) κ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty → ‖(ν : E)‖ = 1 →
    polarSet (closure (coneHull (region φ α Q - region φ α P))) = {x | ∃ c : ℝ, 0 ≤ c ∧ x = c • (ν : E)} →
    argminSet φ α P κ (-(ν : E)) = {tP} → argminSet φ α Q κ (ν : E) = {sQ} →
      let σ2 := (1 / (1 - α)) ^ 2 * (cP ^ 2 * Var[hinge φ (-(ν : E)) tP; P] + cQ ^ 2 * Var[hinge φ (ν : E) sQ; Q])
      TendstoInDistribution
        (fun k ω => (r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α) ^ 2)
        atTop (fun x : ℝ => (max x 0) ^ 2) (fun _ => μ) (gaussianReal 0 σ2.toNNReal) ∧
      (0 < σ2 → (gaussianReal 0 σ2.toNNReal).map (fun x => (max x 0) ^ 2) = chiBarSq.map (fun y => σ2 * y))

/-- `lem:supdir` (directional derivative of the supremum): `Θ` compact (nonempty), `Ψ(z) = sup_Θ z` on bounded
functions, `z₀ ∈ C(Θ)`, `Θ₀ = {θ : z₀(θ) = Ψ(z₀)}`. For every `h ∈ C(Θ)`, `t_k > 0`, `t_k → 0`, and bounded
`h_k → h` uniformly (in `ℓ^∞(Θ)`): `Θ₀` is nonempty and compact, `max_{Θ₀} h` is attained, and
`(Ψ(z₀ + t_k h_k) − Ψ(z₀))/t_k → max_{Θ₀} h`. -/
def boundary_supdir : Prop :=
  ∀ (Θ : Type) [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] (z0 h : C(Θ, ℝ)) (hk : ℕ → Θ → ℝ) (t : ℕ → ℝ),
    (∀ k, ∃ C, ∀ θ, |hk k θ| ≤ C) → TendstoUniformly hk h atTop → (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
      let Θ0 := {θ | z0 θ = sSup (range z0)}
      Θ0.Nonempty ∧ IsCompact Θ0 ∧ (∃ θ ∈ Θ0, IsGreatest (h '' Θ0) (h θ)) ∧
      Tendsto (fun k => (sSup (range fun θ => z0 θ + t k * hk k θ) - sSup (range z0)) / t k) atTop
        (𝓝 (sSup (h '' Θ0)))

/-- `lem:Hprops` (properties of `H_P`), as printed, for both `H_P` (left copy, `P`) and `H_Q` (right copy, `Q`):
almost surely (a) `H(0) = 0` and (b) `H(λf) = λH(f)` for all `λ ∈ [0, 1]`, `f ∈ 𝔹_r`; (c) if `α = 0`, almost surely
`H_P(f) = 𝔾_P ℓ_{f,−κ}` (`= 𝔾_P⟨f, φ⟩`) `= ⟨f, G⟩` for every `f ∈ 𝔹_r`, with `G` (`= 𝔾_P φ`) satisfying
`⟨u, G⟩ ∼ N(0, Var_P⟨u, φ⟩)` for every `u`; (d) for fixed `f` with `q_P(f) = {t_f}`, `H_P(f) = β 𝔾_P ℓ_{f,t_f}` and
`H_P(f) ∼ N(0, β² Var_P(ℓ_{f,t_f}))`. -/
def boundary_Hprops : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → IsLimitGP φ P Q 1 1 κ μ' 𝔾 →
      -- (a), (b)
      (∀ᵐ ω' ∂μ', (∀ f : Ball E, (f : E) = 0 →
          Hfun φ α P κ Sum.inl (𝔾 ω') f = 0 ∧ Hfun φ α Q κ Sum.inr (𝔾 ω') f = 0) ∧
        ∀ f g : Ball E, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → (g : E) = c • (f : E) →
          Hfun φ α P κ Sum.inl (𝔾 ω') g = c * Hfun φ α P κ Sum.inl (𝔾 ω') f ∧
          Hfun φ α Q κ Sum.inr (𝔾 ω') g = c * Hfun φ α Q κ Sum.inr (𝔾 ω') f) ∧
      -- (c)
      (α = 0 → ∃ GP GQ : Ω' → E,
        (∀ᵐ ω' ∂μ', ∀ (f : Ball E) (t : Icc (-κ) κ), (t : ℝ) = -κ →
          Hfun φ α P κ Sum.inl (𝔾 ω') f = 𝔾 ω' (Sum.inl (f, t)) ∧
          Hfun φ α P κ Sum.inl (𝔾 ω') f = ⟪(f : E), GP ω'⟫ ∧
          Hfun φ α Q κ Sum.inr (𝔾 ω') f = 𝔾 ω' (Sum.inr (f, t)) ∧
          Hfun φ α Q κ Sum.inr (𝔾 ω') f = ⟪(f : E), GQ ω'⟫) ∧
        (∀ u : E, μ'.map (fun ω' => ⟪u, GP ω'⟫) = gaussianReal 0 (Var[fun x => ⟪u, φ x⟫; P]).toNNReal ∧
          μ'.map (fun ω' => ⟪u, GQ ω'⟫) = gaussianReal 0 (Var[fun x => ⟪u, φ x⟫; Q]).toNNReal)) ∧
      -- (d)
      (∀ (f : Ball E) (tf : Icc (-κ) κ), argminSet φ α P κ (f : E) = {tf} →
        (∀ ω', Hfun φ α P κ Sum.inl (𝔾 ω') f = 1 / (1 - α) * 𝔾 ω' (Sum.inl (f, tf))) ∧
        μ'.map (fun ω' => Hfun φ α P κ Sum.inl (𝔾 ω') f) =
          gaussianReal 0 ((1 / (1 - α)) ^ 2 * Var[hinge φ (f : E) tf; P]).toNNReal) ∧
      (∀ (f : Ball E) (tf : Icc (-κ) κ), argminSet φ α Q κ (f : E) = {tf} →
        (∀ ω', Hfun φ α Q κ Sum.inr (𝔾 ω') f = 1 / (1 - α) * 𝔾 ω' (Sum.inr (f, tf))) ∧
        μ'.map (fun ω' => Hfun φ α Q κ Sum.inr (𝔾 ω') f) =
          gaussianReal 0 ((1 / (1 - α)) ^ 2 * Var[hinge φ (f : E) tf; Q]).toNNReal)

/-- `prop:bangbang`, first sentence: "`𝒯_α` is nonempty, convex and compact". -/
def bangbang_set : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ), 0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
      (trimSetEmp x y α β).Nonempty ∧ Convex ℝ (trimSetEmp x y α β) ∧ IsCompact (trimSetEmp x y α β)

end Claims

end StatFormal.Wave30ah
