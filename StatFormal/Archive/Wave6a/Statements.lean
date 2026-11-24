import StatFormal.Archive.RobustEquality.Certificate.Statements
import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.SBFairness.Defects.Statements
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.CDF

/-!
# FROZEN STATEMENTS — wave 6a (QUEUE rows 57–60): robust equality JASA `prop:strict`, `prop:ep-calib`;
# SB fairness repair `lem:excess`, `cor:ks`

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-jasa.md` and
`data-fairness-repair.md`; current text after the 2026-10-13/14 corrections):
* robust equality `prop:strict` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_proofs.tex:305-318`,
  proof `:320-324`), with `eq:T` (`main.tex`, single-reference `T^{{ν}}_s`, the frozen `Tref1`), `f_h(x₀,x) =
  (h(x) − h(x₀))²`, references with `0 < ν(K) ≤ 1` (`supp_proofs.tex:15-23`), and `thm:certificate` (frozen).
* robust equality `prop:ep-calib` (`jasa/supp_eps.tex:385-390`, proof `:392-396`), with the notation block
  (`supp_eps.tex:5-15`: `c(x,y) = |x−y|²`, `W^ν_ε(P̂,Q) = inf_γ E_γ c + ε KL(γ‖P̂⊗ν)`) and `def:ep-member`
  (`supp_eps.tex:38-52`: `B^ν_0(r) = {Q : Q(S_ν) = 1, W₂²(P̂,Q) ≤ r}`).
* SB `lem:excess` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:1218-1225`, proof `:1227-1233`),
  with `eq:repaircost` (`:1202-1208`) — the frozen `SBFairness/Defects` encoding.
* SB `cor:ks` (`schrodinger_bridge_fairness_repair.tex:2413-2430`), with `cor:smoothing` (`:479-491`, frozen in
  `Wave4b`: `endpointMixture1`, `smoothing_density_one`).
Reuses the frozen `RobustEquality/Statements.lean` (`klRef`), `RobustEquality/Certificate/Statements.lean`
(`centre`, `Tref1`), `Wave4b/Statements.lean` (`nominal`, `sqrtT`, `RefClass`, `endpointMixture1`) and
`SBFairness/Defects/Statements.lean` (`repairCost`, `J`, `baryF`, `Jstar`), imported, not copied.

Covered:
* `prop:strict`: `strict_closed` (the closed form of `T^{{ν}}_s(h,L²)`, the bound `≤ L² r_s`, and equality iff
  `ν(K) = 1` and `f_h(x₀,·) = L²c(x₀,·)` `ν`-a.e. at every anchor), `strict_closed_euclid` (the same with the printed
  hypothesis `|h(x) − h(x₀)| ≤ L‖x − x₀‖` and `c = ‖·‖²` on `ℝ^d`), `strict_cert` (the certificate at
  `λ₀ = λ₁ = L²` is `≤ (Δ(h) + L√r₀ + L√r₁)²`, strictly unless both equality conditions hold), `strict_class` (Lipschitz
  on all of `K` ⇒ `T^𝒩_s(h,L²) ≤ L² r_s` for every class).
* `prop:ep-calib`: `ep_calib` (the "if and only if"), `ep_calib_necessary` (the forward direction for any, possibly
  non-measurable, radius), `ep_ball_wasserstein` (`S_ν = K` ⇒ `B^ν_0` is the Wasserstein ball), `ep_calib_product`
  (the product-coupling radius `sup_y ∫ c(x,y) dP̂(x)` is valid for every law and every sample).
* `lem:excess`: `excess_bary` (in `ℝ≥0∞`, additive: `F(ω) ≤ 𝒥 + 2γM` and `𝒥^⋆ ≤ F(ω)`), `excess_real` (the printed
  chain `𝒥 − 𝒥^⋆ ≥ F(ω) − F(ν^⋆) − 2γM ≥ −2γM` in `ℝ`, with every quantity shown finite).
* `cor:ks`: `ks_cube` (the sharp step `‖F_μ − F_ν‖³_∞ ≤ 3B² W₂²` when one law has a density `≤ B`), `ks_interp`
  (`‖F_μ − F_ν‖_∞ ≤ (2B)^{2/3} W₂^{2/3}`), `ks_bridge` (the displayed bound for the bridge marginals,
  `B = (2πεt(1−t))^{-1/2}`, `d = 1`, `t ∈ (0,1)`, `ε > 0`).

Not covered (declared):
* `prop:strict`: the remarks after the proposition (linear rules, the `ε ↓ 0` limit of the gap); the validity of the
  Wasserstein–Lipschitz certificate itself (`W₂²(h#P̂,h#Q) ≤ L²r_s`, stated inside the proof, not in the proposition).
* `prop:ep-calib`: the cross-fitted `W₂` radius (marked heuristic in the source); the Γ-convergence reading of the
  `ε = 0` member (`thm:ep-limit0`).
* `lem:excess`: attainment of `𝒥^⋆` at a barycenter `ν^⋆` (Agueh–Carlier); `F(ν^⋆)` is read as `𝒥^⋆ = inf F`.
* `cor:ks`: disparate-impact statistics; the sentence "without `ε > 0` there is no such transfer" (a remark);
  `cor:smoothing` itself (frozen in `Wave4b`).

Encodings (see card):
* `prop:strict`: the frozen `Certificate` setting: anchors `x : Fin n → K` (labelled, ties allowed), any measurable
  cost `c` (paper `‖x − x₀‖²`; `strict_closed_euclid` is the literal case), `h` measurable, reference `ν` finite with
  `0 < ν(K) ≤ 1`, `ε > 0`, `L > 0` (`λ = L² > 0`, so `λε ≠ 0`). "`|h(x) − h(x₀)| ≤ L‖x − x₀‖` for every anchor and
  `ν`-a.e. `x`" is `f_h(x_i,·) ≤ L²c(x_i,·)` `ν`-a.e. for each `i` (equivalent for `c = ‖·‖²`). "Strict unless" is
  the iff `T = L²r ↔ cond` (the converse is also true). The certificates are in `ℝ≥0∞` as in the frozen
  `certificate`: `(Δ + ofReal √T₀ + ofReal √T₁)²` against `(Δ + ofReal(L√r₀) + ofReal(L√r₁))²`, `Δ = nominal`
  (Tau Ceti `W₂`). `strict_cert` assumes `r_s > 0` and `h` bounded (the `thm:certificate` setting): with `r_s = 0`
  the junk `√(negative) = 0` would equate the two certificates. `T^𝒩_s` is the frozen `sqrtT` (`⨆_ν √T^{{ν}}`).
* `prop:ep-calib`: `K` any compact, uncountable metric space with its Borel σ-algebra (paper: compact `K ⊂ ℝ^d`),
  `c = dist²`. The ball for `ε > 0` is the sublevel set `{Q : G^ν_ε(Q) ≤ r}` of the **infimum** `G^ν_ε(Q) =
  inf { n⁻¹ Σ_i (∫ c(x_i,·) dΓ_i + ε KL(Γ_i‖ν)) : Γ_i probabilities, n⁻¹ Σ_i Γ_i = Q }` (`Geps`, in `EReal`, KL =
  frozen `klRef`); this is `W^ν_ε(P̂,Q)` written over labelled kernels (`lem:kernel`; for tied anchors the coupling
  and kernel infima agree by convexity of KL). For `ε = 0`: `Q(supp ν) = 1 ∧ W₂²(P̂,Q) ≤ r` (`def:ep-member`;
  `supp ν` is Mathlib's `Measure.support`; the comparison is in `EReal`, so a negative radius gives the empty ball,
  not junk). The sample is `X ∼ P^{⊗n}` on `Fin n → K` (`Measure.pi`), `P̂ = centre X`; a radius is any real-valued
  `r̂ : (Fin n → K) → ℝ` ("finite-valued"); "`Pr_P[P ∈ B(r̂)] ≥ 1 − α`" is the measurable-event convention
  (∃ measurable `E ⊆ {X : P ∈ B(r̂(X))}` with `P^{⊗n}(E) ≥ 1 − α`); "finitely supported" is `P(sᶜ) = 0` for a finite
  set `s`. `0 ≤ α < 1`, `0 ≤ ε`, `n ≥ 1`. In `ep_calib` the radius must also be measurable (the stronger reading of
  the "exists" side; `ep_calib_necessary` drops it). The product-coupling radius is the real `⨆_y n⁻¹ Σ_i dist(X_i,y)²`
  (bounded on a compact space, so no junk).
* `lem:excess`: the frozen `Defects` encoding (`ℝ^d = EuclideanSpace ℝ (Fin d)`, `R_s ∈ 𝒫₂`, `T_s` measurable,
  weights `p_s ≥ 0`, `p₀ + p₁ = 1`); `ω = (T₀)_#R₀`, `M = max_s W₂(R_s, ω)`, `γ ∈ [0,∞]` (`excess_bary`) or `γ ≥ 0` real
  (`excess_real`). `excess_bary` is the subtraction-free form (truncated `ℝ≥0∞` subtraction would be junk);
  `excess_real` adds `‖T_s − Id‖_{L²(R_s)} < ∞` and proves every `toReal` argument finite.
* `cor:ks`: laws on `ℝ`; "`μ` has density `≤ B`" is `μ = volume.withDensity (ofReal ∘ ρ)` with `ρ ≤ B` pointwise
  (no measurability of `ρ` needed); `‖F_μ − F_ν‖_∞ = ⨆_x |cdf μ x − cdf ν x|` (Mathlib `cdf`), all in `ℝ≥0∞` with
  `W₂^{2/3}` the `ℝ≥0∞` power (so `W₂ = ∞` gives a true bound, not junk). The bridge marginal `μ^ε_{s,t}` is the frozen
  `endpointMixture1 ε t π_s` (`eq:convolution`), for **any** probability plans `π_s` (a generalisation).
Critic notes:
* `prop:strict` holds as printed. The strictness clause needs `r_s > 0` only because of `√` of a negative `T`; the
  paper's radii are positive.
* `prop:ep-calib` holds as printed. Uncountability is used only for `ε > 0` (a non-atom `z` of the finite `ν`); for
  `ε = 0` the test point is any `z ∉ S_ν`. The radius' measurability plays no role in the forward direction.
* `lem:excess` holds as printed (current text). The step `W₂²(R₁,ω₁) ≥ W₂²(R₁,ω) − 2γW₂(R₁,ω)` also covers
  `W₂(R₁,ω) < γ` (then the right side is negative).
* `cor:ks`: the sharp constant is `3^{1/3} ≈ 1.442 < 2^{2/3} ≈ 1.587`; only **one** of the two laws needs the density
  bound (`ks_cube`, `ks_interp`). The printed constant holds.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. `strict_cert`'s `r_s > 0` is needed only for the strict part (at `r_s = 0`
  the junk `√` of a negative `T_s` makes both sides equal; for `c ≥ 0` a nonempty ball at `r = 0` forces the equality
  condition anyway); the `≤` part holds without it. "`h` bounded" is the `thm:certificate` setting, not needed for
  truth. `cor:ks`: the printed constant `(2B)^{2/3}` is valid but not sharp (`3^{1/3}` suffices, `ks_interp` covers it).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal NNReal

namespace StatFormal.Wave6a

open StatFormal.RobustEquality StatFormal.RobustEquality.Certificate

/-! ### robust equality `prop:strict` -/

/-- The equality condition of `prop:strict` at one group: `ν(K) = 1` and `f_h(x_i,·) = L²c(x_i,·)` `ν`-a.e. at every
anchor. -/
def StrictEqCond {K : Type} [MeasurableSpace K] {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (L : ℝ)
    (ν : Measure K) : Prop :=
  ν Set.univ = 1 ∧ ∀ i, (fun z => (h z - h (x i)) ^ 2) =ᵐ[ν] fun z => L ^ 2 * c (x i) z

/-! ### robust equality `prop:ep-calib` -/

section EpCalib

variable {K : Type} [MetricSpace K] [MeasurableSpace K]

/-- The kernel objective `n⁻¹ Σ_i (∫ c(x_i,·) dΓ_i + ε KL(Γ_i‖ν))`, `c = dist²`, in `EReal`. -/
def kernelValue {n : ℕ} (x : Fin n → K) (ε : ℝ) (ν : Measure K) (Γ : Fin n → Measure K) : EReal :=
  ((n : ℝ)⁻¹ : EReal) *
    ∑ i, (((∫ z, dist (x i) z ^ 2 ∂(Γ i) : ℝ) : EReal) + (ε : EReal) * klRef (Γ i) ν)

/-- `G^ν_ε(Q) = W^ν_ε(P̂,Q)`, the infimum of the kernel objective over kernels averaging to `Q`. -/
def Geps {n : ℕ} (x : Fin n → K) (ε : ℝ) (ν Q : Measure K) : EReal :=
  ⨅ (Γ : Fin n → Measure K) (_ : (∀ i, IsProbabilityMeasure (Γ i)) ∧ Q = (n : ℝ≥0∞)⁻¹ • ∑ i, Γ i),
    kernelValue x ε ν Γ

/-- `B^ν_ε(r)` around `P̂ = centre x`: for `ε ≠ 0` the sublevel set of `G^ν_ε`; for `ε = 0` the member
`{Q : Q(S_ν) = 1, W₂²(P̂,Q) ≤ r}` of `def:ep-member`. -/
def epBall {n : ℕ} (x : Fin n → K) (ν : Measure K) (ε r : ℝ) : Set (Measure K) :=
  {Q | IsProbabilityMeasure Q ∧
    (ε = 0 → Q ν.support = 1 ∧ (((wassersteinEDist 2 (centre x) Q ^ 2 : ℝ≥0∞) : EReal) ≤ (r : EReal))) ∧
    (ε ≠ 0 → Geps x ε ν Q ≤ (r : EReal))}

/-- `r̂` is a valid radius at level `α`: for every finitely supported law `P`, on a measurable event of
`P^{⊗n}`-probability `≥ 1 − α`, `P ∈ B^ν_ε(r̂(X))`. -/
def ValidRadius (n : ℕ) (ν : Measure K) (ε α : ℝ) (rhat : (Fin n → K) → ℝ) : Prop :=
  ∀ P : Measure K, IsProbabilityMeasure P → (∃ s : Finset K, P (↑s : Set K)ᶜ = 0) →
    ∃ E : Set (Fin n → K), MeasurableSet E ∧ E ⊆ {X | P ∈ epBall X ν ε (rhat X)} ∧
      ENNReal.ofReal (1 - α) ≤ Measure.pi (fun _ : Fin n => P) E

end EpCalib

namespace Claims

/-- `prop:strict`: closed form, `T^{{ν}}_s(h,L²) ≤ L² r_s`, and equality iff the equality condition holds. -/
def strict_closed : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε r L : ℝ)
    (ν : Measure K) [IsFiniteMeasure ν],
    0 < n → 0 < ε → 0 < L → Measurable (Function.uncurry c) → Measurable h →
    ν Set.univ ≠ 0 → ν Set.univ ≤ 1 →
    (∀ i, ∀ᵐ z ∂ν, (h z - h (x i)) ^ 2 ≤ L ^ 2 * c (x i) z) →
      Tref1 x c h ε r (L ^ 2) ν = L ^ 2 * r - L ^ 2 * ε * ((n : ℝ)⁻¹ * ∑ i,
          -Real.log (∫ z, Real.exp (((h z - h (x i)) ^ 2 - L ^ 2 * c (x i) z) / (L ^ 2 * ε)) ∂ν)) ∧
        Tref1 x c h ε r (L ^ 2) ν ≤ L ^ 2 * r ∧
        (Tref1 x c h ε r (L ^ 2) ν = L ^ 2 * r ↔ StrictEqCond x c h L ν)

/-- `prop:strict` with the printed hypothesis on `ℝ^d`: `|h(x) − h(x₀)| ≤ L‖x − x₀‖` at every anchor, `ν`-a.e.,
cost `c(x₀,x) = ‖x − x₀‖²`. -/
def strict_closed_euclid : Prop :=
  ∀ (d n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (ε r L : ℝ)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν],
    0 < n → 0 < ε → 0 < L → Measurable h → ν Set.univ ≠ 0 → ν Set.univ ≤ 1 →
    (∀ i, ∀ᵐ z ∂ν, |h z - h (x i)| ≤ L * ‖z - x i‖) →
      Tref1 x (fun a b => ‖b - a‖ ^ 2) h ε r (L ^ 2) ν ≤ L ^ 2 * r ∧
        (Tref1 x (fun a b => ‖b - a‖ ^ 2) h ε r (L ^ 2) ν = L ^ 2 * r ↔
          StrictEqCond x (fun a b => ‖b - a‖ ^ 2) h L ν)

/-- `prop:strict`, consequence: the certificate at `λ₀ = λ₁ = L²` is at most the Wasserstein–Lipschitz certificate
`(Δ(h) + L√r₀ + L√r₁)²`, and strictly below it unless both equality conditions hold. -/
def strict_cert : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ)
    (h : K → ℝ) (ε r₀ r₁ L : ℝ) (ν₀ ν₁ : Measure K) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁],
    0 < n₀ → 0 < n₁ → 0 < ε → 0 < L → 0 < r₀ → 0 < r₁ →
    Measurable (Function.uncurry c) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
    ν₀ Set.univ ≠ 0 → ν₀ Set.univ ≤ 1 → ν₁ Set.univ ≠ 0 → ν₁ Set.univ ≤ 1 →
    (∀ i, ∀ᵐ z ∂ν₀, (h z - h (x₀ i)) ^ 2 ≤ L ^ 2 * c (x₀ i) z) →
    (∀ i, ∀ᵐ z ∂ν₁, (h z - h (x₁ i)) ^ 2 ≤ L ^ 2 * c (x₁ i) z) →
      (StatFormal.Wave4b.nominal x₀ x₁ h + ENNReal.ofReal (√(Tref1 x₀ c h ε r₀ (L ^ 2) ν₀)) +
          ENNReal.ofReal (√(Tref1 x₁ c h ε r₁ (L ^ 2) ν₁))) ^ 2 ≤
        (StatFormal.Wave4b.nominal x₀ x₁ h + ENNReal.ofReal (L * √r₀) + ENNReal.ofReal (L * √r₁)) ^ 2 ∧
      (¬ (StrictEqCond x₀ c h L ν₀ ∧ StrictEqCond x₁ c h L ν₁) →
        (StatFormal.Wave4b.nominal x₀ x₁ h + ENNReal.ofReal (√(Tref1 x₀ c h ε r₀ (L ^ 2) ν₀)) +
            ENNReal.ofReal (√(Tref1 x₁ c h ε r₁ (L ^ 2) ν₁))) ^ 2 <
          (StatFormal.Wave4b.nominal x₀ x₁ h + ENNReal.ofReal (L * √r₀) + ENNReal.ofReal (L * √r₁)) ^ 2)

/-- `prop:strict`, last sentence: if the Lipschitz bound holds on all of `K`, then `T^𝒩_s(h,L²) ≤ L² r_s` for every
class (each member, and the supremum `⨆_ν √T^{{ν}}_s ≤ L√r_s`). -/
def strict_class : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε r L : ℝ)
    (N : Set (Measure K)),
    StatFormal.Wave4b.RefClass N → 0 < n → 0 < ε → 0 < L → Measurable (Function.uncurry c) → Measurable h →
    (∀ i z, (h z - h (x i)) ^ 2 ≤ L ^ 2 * c (x i) z) →
      (∀ ν ∈ N, Tref1 x c h ε r (L ^ 2) ν ≤ L ^ 2 * r) ∧
        StatFormal.Wave4b.sqrtT x c h ε r (L ^ 2) N ≤ ENNReal.ofReal (L * √r)

/-- `prop:ep-calib`: on an uncountable compact `K`, a (measurable) finite-valued radius valid at level `α` for every
finitely supported `P` exists iff `ε = 0` and `S_ν = K`. -/
def ep_calib : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (n : ℕ)
    (ν : Measure K) [IsFiniteMeasure ν] (ε α : ℝ),
    Uncountable K → 0 < n → ν Set.univ ≠ 0 → ν Set.univ ≤ 1 → 0 ≤ ε → 0 ≤ α → α < 1 →
      ((∃ rhat : (Fin n → K) → ℝ, Measurable rhat ∧ ValidRadius n ν ε α rhat) ↔
        (ε = 0 ∧ ν.support = Set.univ))

/-- `prop:ep-calib`, forward direction, for any (not necessarily measurable) radius and any metric `K`. -/
def ep_calib_necessary : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] [BorelSpace K] (n : ℕ)
    (ν : Measure K) [IsFiniteMeasure ν] (ε α : ℝ) (rhat : (Fin n → K) → ℝ),
    Uncountable K → 0 < n → 0 ≤ ε → α < 1 → ValidRadius n ν ε α rhat →
      ε = 0 ∧ ν.support = Set.univ

/-- `prop:ep-calib`: if `S_ν = K`, `B^ν_0` is the Wasserstein ball. -/
def ep_ball_wasserstein : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] [BorelSpace K] (n : ℕ) (x : Fin n → K)
    (ν : Measure K) (r : ℝ), ν.support = Set.univ →
      epBall x ν 0 r = {Q | IsProbabilityMeasure Q ∧
        (((wassersteinEDist 2 (centre x) Q ^ 2 : ℝ≥0∞) : EReal) ≤ (r : EReal))}

/-- `prop:ep-calib`: with `S_ν = K` (compact), the product-coupling radius `sup_{y∈K} n⁻¹ Σ_i c(X_i,y)` is valid for
every law `P` and every sample. -/
def ep_calib_product : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (n : ℕ)
    (ν : Measure K), 0 < n → ν.support = Set.univ →
      ∀ (P : Measure K), IsProbabilityMeasure P → ∀ X : Fin n → K,
        P ∈ epBall X ν 0 (⨆ y : K, (n : ℝ)⁻¹ * ∑ i, dist (X i) y ^ 2)

open StatFormal.SBFairness.Defects in
/-- `lem:excess` in `ℝ≥0∞` (subtraction-free): with `ω = (T₀)_#R₀`, `W₂(ω₀,ω₁) ≤ γ` and `M = max_s W₂(R_s,ω)`,
`F(ω) ≤ 𝒥(T₀,T₁) + 2γM` and `𝒥^⋆ ≤ F(ω)`. -/
def excess_bary : Prop :=
  ∀ (d : ℕ) (R₀ R₁ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R₀] [IsProbabilityMeasure R₁]
    (p₀ p₁ : ℝ) (T₀ T₁ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ≥0∞),
    HasFiniteMoment 2 R₀ → HasFiniteMoment 2 R₁ → 0 ≤ p₀ → 0 ≤ p₁ → p₀ + p₁ = 1 →
    Measurable T₀ → Measurable T₁ → wassersteinEDist 2 (R₀.map T₀) (R₁.map T₁) ≤ γ →
      baryF p₀ p₁ R₀ R₁ (R₀.map T₀) ≤ J p₀ p₁ R₀ R₁ T₀ T₁ +
          2 * γ * max (wassersteinEDist 2 R₀ (R₀.map T₀)) (wassersteinEDist 2 R₁ (R₀.map T₀)) ∧
        Jstar p₀ p₁ R₀ R₁ ≤ baryF p₀ p₁ R₀ R₁ (R₀.map T₀)

open StatFormal.SBFairness.Defects in
/-- `lem:excess` as printed, in `ℝ`: `𝒥 − 𝒥^⋆ ≥ F(ω) − F(ν^⋆) − 2γM ≥ −2γM` (`F(ν^⋆) = 𝒥^⋆`), with all quantities
finite. -/
def excess_real : Prop :=
  ∀ (d : ℕ) (R₀ R₁ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R₀] [IsProbabilityMeasure R₁]
    (p₀ p₁ : ℝ) (T₀ T₁ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ),
    HasFiniteMoment 2 R₀ → HasFiniteMoment 2 R₁ → 0 ≤ p₀ → 0 ≤ p₁ → p₀ + p₁ = 1 →
    Measurable T₀ → Measurable T₁ → repairCost R₀ T₀ ≠ ⊤ → repairCost R₁ T₁ ≠ ⊤ → 0 ≤ γ →
    wassersteinEDist 2 (R₀.map T₀) (R₁.map T₁) ≤ ENNReal.ofReal γ →
      J p₀ p₁ R₀ R₁ T₀ T₁ ≠ ⊤ ∧ Jstar p₀ p₁ R₀ R₁ ≠ ⊤ ∧ baryF p₀ p₁ R₀ R₁ (R₀.map T₀) ≠ ⊤ ∧
        max (wassersteinEDist 2 R₀ (R₀.map T₀)) (wassersteinEDist 2 R₁ (R₀.map T₀)) ≠ ⊤ ∧
        (baryF p₀ p₁ R₀ R₁ (R₀.map T₀)).toReal - (Jstar p₀ p₁ R₀ R₁).toReal -
            2 * γ * (max (wassersteinEDist 2 R₀ (R₀.map T₀)) (wassersteinEDist 2 R₁ (R₀.map T₀))).toReal ≤
          (J p₀ p₁ R₀ R₁ T₀ T₁).toReal - (Jstar p₀ p₁ R₀ R₁).toReal ∧
        -(2 * γ * (max (wassersteinEDist 2 R₀ (R₀.map T₀)) (wassersteinEDist 2 R₁ (R₀.map T₀))).toReal) ≤
          (baryF p₀ p₁ R₀ R₁ (R₀.map T₀)).toReal - (Jstar p₀ p₁ R₀ R₁).toReal -
            2 * γ * (max (wassersteinEDist 2 R₀ (R₀.map T₀)) (wassersteinEDist 2 R₁ (R₀.map T₀))).toReal

/-- `cor:ks`, sharp step: if `μ` has a density bounded by `B`, then `|F_μ(x) − F_ν(x)|³ ≤ 3B² W₂²(μ,ν)` for every `x`. -/
def ks_cube : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ρ : ℝ → ℝ) (B : ℝ),
    0 < B → μ = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) → (∀ y, ρ y ≤ B) →
      ∀ x, ENNReal.ofReal (|cdf μ x - cdf ν x| ^ 3) ≤ ENNReal.ofReal (3 * B ^ 2) * wassersteinEDist 2 μ ν ^ 2

/-- `cor:ks`, the interpolation inequality: `‖F_μ − F_ν‖_∞ ≤ (2B)^{2/3} W₂(μ,ν)^{2/3}` when `μ` has a density
`≤ B`. -/
def ks_interp : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ρ : ℝ → ℝ) (B : ℝ),
    0 < B → μ = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) → (∀ y, ρ y ≤ B) →
      ⨆ x, ENNReal.ofReal |cdf μ x - cdf ν x| ≤
        ENNReal.ofReal ((2 * B) ^ (2 / 3 : ℝ)) * wassersteinEDist 2 μ ν ^ (2 / 3 : ℝ)

/-- `cor:ks`: for `d = 1`, `t ∈ (0,1)`, `ε > 0`, the bridge marginals satisfy
`‖F_{μ_{0,t}} − F_{μ_{1,t}}‖_∞ ≤ (2B_{ε,t})^{2/3} W₂(μ_{0,t},μ_{1,t})^{2/3}`, `B_{ε,t} = (2πεt(1−t))^{-1/2}`. -/
def ks_bridge : Prop :=
  ∀ (ε t : ℝ) (plan₀ plan₁ : Measure (ℝ × ℝ)) [IsProbabilityMeasure plan₀] [IsProbabilityMeasure plan₁],
    0 < ε → 0 < t → t < 1 →
      ⨆ x, ENNReal.ofReal |cdf (StatFormal.Wave4b.endpointMixture1 ε t plan₀) x -
          cdf (StatFormal.Wave4b.endpointMixture1 ε t plan₁) x| ≤
        ENNReal.ofReal ((2 * (2 * Real.pi * (ε * t * (1 - t))) ^ (-(1 : ℝ) / 2)) ^ (2 / 3 : ℝ)) *
          wassersteinEDist 2 (StatFormal.Wave4b.endpointMixture1 ε t plan₀)
            (StatFormal.Wave4b.endpointMixture1 ε t plan₁) ^ (2 / 3 : ℝ)

end Claims
end StatFormal.Wave6a
