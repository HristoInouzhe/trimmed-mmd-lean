import StatFormal.Wave30tu.Full.Statements
import StatFormal.Wave31ta.Statements
import StatFormal.Wave31td.Statements
import StatFormal.Lib.Distances.TV
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tf: trimmed-mmd (jmlr) **v3**, six prose claims without a certified counterpart (G3a, G4, G5, G6, G7, G8)

Printed source: `trimmed-mmd/jmlr/v3/` at trimmed-mmd commit `78c4665` ("JMLR v3: citation check applied"; read-only, read 2026-11-12;
sha256 of the files at that commit, first 16 hex digits: `sections/03_analytic.tex` `b4b2301d2afb42f4`, `sections/04_split.tex`
`b60fdf5effffbdb4`, `sections/05_trimming.tex` `f787aecc1a51fe07`, `sections/07_data.tex` `12576bf95003af69`, `appendix/B_analytic.tex`
`ec1eaeabb71d989c`). The formal targets are those of `jmlr/v3/NEW_STATEMENTS.md`, section "Wave 31tf" (G3a, G4, G5, G6, G7, G8), at
trimmed-mmd commit `d356058` (the binding specification, lines 1-210, file sha256
`311b3b79b12704db129665550b6137172bf8d6d3552e071d0123422157c37cad`). All six sentences are printed outside a numbered environment; the labels
`prose:…` are pseudo-labels (as in waves 31td, 31te). Line numbers below are at `78c4665`.

Covered here (12 claims):
* G3a `prose:linear-margin` (`05_trimming.tex:77`: "the pair also satisfies the margin with `ω(ε) = 3ε/2`"): `linear_margin` — for the
  linear-kernel pair of wave 31td, `α⋆ = TV(P,Q) = ⅓` and Assumption 2 holds with `ω(ε) = 3ε/2` (the frozen `Wave30tu.Margin`).
* G4 `prose:gamma-ge-1` (`03_analytic.tex:162-164`: "a larger `γ` allows a flatter contact, harder to detect, and the Lipschitz continuity of the
  path forces `γ ≥ 1`"): `gamma_ge_one` — under (A1)–(A2) (no (A3)), `0 < α⋆ = TV(P,Q) < 1`, `c₀, γ > 0` and
  `D_{α⋆−ε}(P,Q) ≥ c₀ε^γ` for every `ε ∈ [0,α⋆]` (the polynomial case of Assumption 2), then `γ ≥ 1`.
* G5 `prose:delta-schedule` (`03_analytic.tex:143-146`: "At level `δ_{n,m}`, `α̂` converges in probability to `α⋆` whenever `δ_{n,m} → 0` and
  `log(1/δ_{n,m})/(n∧m) → 0`, as for `δ_{n,m} = 1/(n∧m)` (Corollary `cor:consistency`; …)"; the corollary is `appendix/B_analytic.tex:270-275`):
  `delta_schedule` (the schedule `δ_{n,m} = 1/(n∧m)` lies in `(0,1)` for `n∧m ≥ 2` and satisfies both rate conditions, in the form of the
  hypotheses of the certified `Wave30tu.cor_consistency`: index type, filter, `n`, `m`, `δ`); `consistency_schedule` (the certified
  `Wave30tu.cor_consistency` along this schedule, for any valid thresholds and lower two-sided tools as there);
  `consistency_schedule_full` (`α̂_{n,m} → α⋆` in probability along the schedule for the paper's `τ = min(τ^P, τ^{P'}, τ^A)`, general kernel,
  `Wave30tu.Full.tauFull`, the form of the certified `Wave30tu.Full.cor_consistency_full`); `consistency_schedule_cpl` (the same for the
  coupled form `Wave31ta.tauV2Cpl`, kernels with `k ≥ 0` and constant diagonal).
* G7 `prose:n-of-a` (`03_analytic.tex:226-229`: "The size `n(a)` grows without bound as `a ↑ α⋆`", with
  `n(a) = min{n : τ_{n,n}(a) < D_a(P,Q)}`, `eq:sharpsize`, `:222-225`): `n_of_a_generic` (for nondecreasing `τ_n` with `τ_n(0) > 0` and a
  continuous `D` with `D(α⋆) = 0`, `n(a) > N` near `α⋆`, for every `N`); `n_of_a_full` and `n_of_a_cpl` (the instances at the paper's
  `τ_{n,n}(·,δ)`, general kernel `tauFull` and coupled `tauV2Cpl`, with the path `a ↦ D_a(P,Q)`, i.e. `Dpop φ P Q` (the `D` of `tauFull κ D …` is the
  bound on `‖φ x − φ x′‖`); the positivity `τ_{n,n}(0,δ) > 0` for `κ, D > 0` is proved from the definitions in the proof files, not assumed).
* G8 `prose:no-uniform-rate` (`03_analytic.tex:202-203`: "by Section 4.4 no estimator of `TV` has a rate uniform over all pairs"; Section 4.4
  is `sec:upper`, `thm:impossible`, `04_split.tex:141-148`): `no_uniform_accuracy` (for every `n, m ≥ 1`, `δ ∈ (0,½)`, `r < ½` and every
  measurable, possibly randomised estimator `T̂` of `TV`, it is false that `Pr_{P,Q}(|T̂ − TV(P,Q)| ≤ r) ≥ 1 − δ` for every `(P,Q) ∈ 𝒫₂`);
  `no_uniform_rate` (hence, for every radius sequence `r_{n,m} → 0`, from some size on no estimator is uniformly within `r_{n,m}` over `𝒫₂`,
  nor over all pairs of laws on `[0,1]`).
* G6 `prose:strict-overlap` (`07_data.tex:8-11`: "strict overlap, a propensity score in `[η, 1−η]`, bounds every `f`-divergence between the
  covariate laws of the arms by a constant free of the dimension (for arms of equal size, `TV(P,Q) ≤ 1 − 2η`)"): `strict_overlap`.

Reuses (imported, not copied): `Wave30tu.Margin` (Assumption 2), `Wave31td` (`phiLin`, `Plin`, `Qlin`, the linear-kernel pair),
`TrimmedMMD.Unconditional` (`Dpop`, the regions' distance, `eq:setdist`, the `D_α` of every certified estimator claim; `Demp`, `D̂_α`),
`TrimmedMMD.ZeroSet.Characteristic` ((A3)), `Distances.tvDist` (`TV(P,Q) = sup_A |P(A) − Q(A)|`), `Wave30tu` (`ValidThreshold`, `LowerTool`),
`Wave30tu.Full.tauFull` (the paper's `τ_{n,m}`, general kernel), `Wave31ta.tauV2Cpl` (the paper's `τ_{n,m}`, coupled sharper candidate),
`TrimmedMMD` (`alphaHat`, `tau`), `Wave31ta.Density2` (the class `𝒫₂` of `thm:impossible`), `TrimmedMMD.Impossible.dataLaw`.

Encodings (see the card `certify/cards/wave31tf.md`):
* (A1)–(A2) as in every earlier trimmed-mmd wave: `H` a real Hilbert space, complete and separable, `φ : 𝒳 → H` strongly measurable with
  `‖φ x‖ ≤ κ` (the canonical feature map, `k(x,x′) = ⟪φ x, φ x′⟫`); (A3) is `Characteristic φ` (the mean embedding is injective on probability
  measures); `P`, `Q` probability measures; `α⋆ = TV(P,Q)` is `tvDist P Q`; `D_α(P,Q)` is `Dpop φ P Q α`; `Δ_φ` is any bound `D` on
  `‖φ x − φ x′‖` (the printed `Δ_φ` is the least one and is admissible), as in the certified `tauFull`.
* "`n(a) = min{n : τ_{n,n}(a) < D_a(P,Q)} ∈ ℕ ∪ {∞}`" (`sizeNeeded`): the infimum, in `ℕ∞`, of the sample sizes `n ≥ 1` with
  `τ n a < D a`; `⊤` when no such `n` exists (the convention `min ∅ = ∞`: the value `sInf ∅ = ⊤` of `ℕ∞` is the intended one).
* "`δ_{n,m} = 1/(n∧m)`" is `deltaSched n m = 1/((min n m : ℕ) : ℝ)`; the claims on `α̂` assume `n, m ≥ 2` so that every level is in `(0,1)`.
* Convergence in probability, as in the frozen `Wave30tu.cor_consistency` (the Wave 18b encoding): for every `e > 0` measurable events
  `E_i ⊆ {|α̂ − α⋆| ≤ e}` with `P(E_i) → 1` along the filter.
* "strict overlap" for arms of equal size (`StrictOverlap`): `μ = P + Q`, `p = dP/dμ`, `q = dQ/dμ` (`dens`, `toReal` of the Radon–Nikodym derivative,
  finite `μ`-a.e.), and for `μ`-a.e. `x` with `p(x) + q(x) > 0`, `η ≤ p/(p+q) ≤ 1 − η`; the propensity score of arms of equal size is
  `e = p/(p+q)`. The `f`-divergence is `D_f(P‖Q) = ∫ f(dP/dQ) dQ` (`fDiv`, `dens P Q = (dP/dQ).toReal`), asserted only together with the
  `Q`-integrability of the integrand and with `P ≪ Q` (so that it is the whole `f`-divergence); `f : ℝ → ℝ` convex on `[0,∞)` with `f(1) = 0`.
* `𝒫₂` is `Density2 P ∧ Density2 Q` (`P ≤ 2·λ|_{[0,1]}`, a probability measure), `Law01` is a probability measure on `ℝ` giving mass `0` to the
  complement of `[0,1]`; "possibly randomised" as in the frozen `Wave31ta.impossible_two`: `T` is a measurable function of `(X_{1:n}, Y_{1:m}, ξ)`,
  `ξ ~ R` independent.
* Junk values: `Real.log (1/δ)` only at `δ > 0`; `Dpop` is evaluated only at levels in `[0,1)`; `1/(1−η)` and `1/η` only at `η ∈ (0,½]`; the
  quotient `p/(p+q)` only where `p + q > 0`; the Bochner integral `fDiv` is paired with integrability; the `sInf` in `sizeNeeded` is over a subset of `ℕ∞`
  (a complete lattice, `sInf ∅ = ⊤` as intended); `Real.rpow` appears only at `ε ≥ 0`, `γ > 0`; `deltaSched` has the junk value `1/0 = 0` only at
  `n∧m = 0`, and the claims use `n, m ≥ 2`. `alphaHat` is the `sInf` of the crossing set (`0` if it is empty): for the paper's `τ` the set is nonempty
  (the printed sentence after `eq:alphaest`; certified for `tauV2Cpl` by `tauV2Cpl_facts`; `τ^{P'} → ∞` for `tauFull` is not certified, see
  `Wave30tu.Full`), and on the events of the certified proofs `α⋆` lies in it, so no claim uses the junk value.
* Not covered (declared): that "Appendix B shows that the second condition cannot be dropped" (certified by `Wave30tu` `ratecond_*` and
  `Wave30tu.Full` `ratecond_full*`); the sentence after `eq:sharpsize` ("up to the fluctuation of the empirical path", the numerical solution,
  "a design guide rather than a guarantee"); the claims of Sections 6 and 7 on how fast `n(a)` grows; in G4 the heuristic remarks "with `γ = 1`
  the regions separate at a linear rate" and "a larger `γ` allows a flatter contact, harder to detect" (their quantitative content is the exponent
  `1/γ` of the certified `Wave30tu.rate_poly`); in G5 the general schedule "whenever `δ_{n,m} → 0` and `log(1/δ_{n,m})/(n∧m) → 0`" at the coupled
  form `tauV2Cpl` (stated here for `1/(n∧m)` only; the general schedule is the certified `cor_consistency` with `tauV2Cpl_facts`), and the 4-fold
  minimum `tauFullCpl` and the grid form `tauFullGrid` (not the printed `τ`: the printed `τ` is `tauFull`, resp. `tauV2Cpl` for kernels with `k ≥ 0`
  and constant diagonal; the other two are valid thresholds with `τ ≤ r_n + r_m` and fall under `consistency_schedule` and `n_of_a_generic`); in G6
  the `f`-divergence clause for arms of unequal size (the printed clause is not restricted to equal arms; here, as in the binding target, only equal
  arms: `StrictOverlap` is `p/(p+q)`, i.e. prior `½` each; for proportions `(π, 1−π)` the propensity score is `πp/(πp + (1−π)q)` and the
  likelihood ratio lies in `[((1−π)/π)·η/(1−η), ((1−π)/π)·(1−η)/η]`; not formalised); the cited results of others (D'Amour et al. 2021; Scott 2015,
  Ramaswamy et al. 2016).
FROZEN 2026-11-12 before any proof, after an independent critic's pre-freeze review (12 claims: 6 ACCEPT, 6 ACCEPT-WITH-NOTE, none false, none vacuous,
verdict READY TO FREEZE; the critic back-translated the claims blind from a comment-free copy, checked the printed lines, quotations and file hashes at
`78c4665`, proved in scratch Lean nine of the claims from the certified results (`linear_margin`, `gamma_ge_one`, `delta_schedule`, the three
`consistency_schedule*`, `n_of_a_generic`, `no_uniform_accuracy`, `no_uniform_rate`), built hypothesis witnesses for the others, checked `strict_overlap`
numerically on 18221 random discrete pairs with 11 convex `f` in both orders (no violation) and the positivity of `τ^{P'}(0,δ)` over a parameter
grid; applied before hashing: the declared Not-covered items, the notes on `r < ½` and on the reading of "all pairs", the junk-value remarks on
`alphaHat`, `deltaSched`, `Real.rpow`, the `strict_overlap` remarks). Hashed in `certify/statements.lock` (with its imports); AI agents must not
edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tf

open StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet StatFormal.Wave30tu.Full

/-- The schedule `δ_{n,m} = 1/(n∧m)` (`03_analytic.tex:145`). -/
def deltaSched (n m : ℕ) : ℝ := 1 / ((min n m : ℕ) : ℝ)

/-- `n(a) = min{n : τ_{n,n}(a) < D_a(P,Q)}` (`eq:sharpsize`) for a family of thresholds `τ n a = τ_{n,n}(a)` and a path `D a = D_a(P,Q)`,
over the sample sizes `n ≥ 1`; a value in `ℕ∞`, equal to `⊤` when no `n ≥ 1` has `τ n a < D a` (the infimum of the empty set). -/
def sizeNeeded (τ : ℕ → ℝ → ℝ) (D : ℝ → ℝ) (a : ℝ) : ℕ∞ :=
  ⨅ n ∈ {n : ℕ | 1 ≤ n ∧ τ n a < D a}, (n : ℕ∞)

/-- The density `dP/dμ` as a real function: `toReal` of the Radon–Nikodym derivative (finite `μ`-a.e. for finite `P`). -/
def dens {𝒳 : Type*} [MeasurableSpace 𝒳] (P μ : Measure 𝒳) (x : 𝒳) : ℝ := (P.rnDeriv μ x).toReal

/-- Strict overlap with parameter `η` for arms of equal size: with `μ = P + Q`, `p = dP/dμ`, `q = dQ/dμ`, the propensity score
`e = p/(p+q)` satisfies `η ≤ e ≤ 1 − η` at `μ`-almost every `x` with `p(x) + q(x) > 0`. -/
def StrictOverlap {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) (η : ℝ) : Prop :=
  ∀ᵐ x ∂(P + Q), 0 < dens P (P + Q) x + dens Q (P + Q) x →
    η ≤ dens P (P + Q) x / (dens P (P + Q) x + dens Q (P + Q) x) ∧
    dens P (P + Q) x / (dens P (P + Q) x + dens Q (P + Q) x) ≤ 1 - η

/-- The `f`-divergence `D_f(P‖Q) = ∫ f(dP/dQ) dQ` (the whole `f`-divergence when `P ≪ Q`). -/
def fDiv {𝒳 : Type*} [MeasurableSpace 𝒳] (f : ℝ → ℝ) (P Q : Measure 𝒳) : ℝ :=
  ∫ x, f (dens P Q x) ∂Q

/-- The conclusion (ii) of `strict_overlap` for the ordered pair `(P,Q)`: `P ≪ Q`, `η/(1−η) ≤ dP/dQ ≤ (1−η)/η` `Q`-almost everywhere, and for
every convex `f : [0,∞) → ℝ` with `f(1) = 0` the `f`-divergence `D_f(P‖Q) = ∫ f(dP/dQ) dQ` is finite (the integrand is `Q`-integrable) and at most
`max{f(η/(1−η)), f((1−η)/η)}`, a constant that depends on `η` and `f` only. -/
def FDivBound {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) (η : ℝ) : Prop :=
  P ≪ Q ∧ (∀ᵐ x ∂Q, η / (1 - η) ≤ dens P Q x ∧ dens P Q x ≤ (1 - η) / η) ∧
    ∀ f : ℝ → ℝ, ConvexOn ℝ (Ici 0) f → f 1 = 0 →
      Integrable (fun x => f (dens P Q x)) Q ∧ fDiv f P Q ≤ max (f (η / (1 - η))) (f ((1 - η) / η))

/-- A law on `[0,1]`: a probability measure on `ℝ` that gives mass `0` to the complement of `[0,1]`. -/
def Law01 (P : Measure ℝ) : Prop := IsProbabilityMeasure P ∧ P (Icc (0 : ℝ) 1)ᶜ = 0

namespace Claims

/-! ### G3a `prose:linear-margin` (`05_trimming.tex:77`) -/

/-- "the pair also satisfies the margin with `ω(ε) = 3ε/2`" (`05_trimming.tex:77`, after the linear-kernel instance `k(x,y) = xy` on
`[−1,1]`, `P` uniform on `[−½,1]`, `Q` uniform on `[−1,½]`, `α⋆ = ⅓`): for the pair of wave 31td (`phiLin`, `Plin`, `Qlin`),
`α⋆ = TV(P,Q) = ⅓` and Assumption 2 holds with `ω(ε) = 3ε/2` — `ω` strictly increasing and continuous on `[0,⅓]`, `ω(0) = 0`, `ω ≥ 0` there,
and `D_{⅓−ε}(P,Q) ≥ 3ε/2` for every `ε ∈ [0,⅓]` (`Wave30tu.Margin`). -/
def linear_margin : Prop :=
  StatFormal.Distances.tvDist StatFormal.Wave31td.Plin StatFormal.Wave31td.Qlin = 1 / 3 ∧
    StatFormal.Wave30tu.Margin StatFormal.Wave31td.phiLin StatFormal.Wave31td.Plin StatFormal.Wave31td.Qlin
      (fun ε => 3 * ε / 2)

/-! ### G4 `prose:gamma-ge-1` (`03_analytic.tex:162-164`) -/

/-- "the Lipschitz continuity of the path forces `γ ≥ 1`" (`03_analytic.tex:162-164`, the polynomial case `ω(ε) = c₀ε^γ` of Assumption 2):
under (A1)–(A2) ((A3) is not needed), if `0 < α⋆ = TV(P,Q) < 1`, `c₀ > 0`, `γ > 0` and `D_{α⋆−ε}(P,Q) ≥ c₀ε^γ` for every `ε ∈ [0,α⋆]`,
then `γ ≥ 1`. -/
def gamma_ge_one : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ c₀ γ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < StatFormal.Distances.tvDist P Q →
    StatFormal.Distances.tvDist P Q < 1 → 0 < c₀ → 0 < γ →
    (∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      c₀ * ε ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε)) →
      1 ≤ γ

/-! ### G5 `prose:delta-schedule` (`03_analytic.tex:143-146`, `B_analytic.tex:270-275`) -/

/-- (a) "`δ_{n,m} → 0` and `log(1/δ_{n,m})/(n∧m) → 0`, as for `δ_{n,m} = 1/(n∧m)`": for `n, m ≥ 2` the level `δ_{n,m} = 1/(n∧m)` lies in `(0,1)`,
and along every schedule (index type `ι`, filter `l`, sample sizes `n m : ι → ℕ`) with `n∧m → ∞`, the levels `δ_{n,m} = 1/(n∧m)` tend to `0` and
`log(1/δ_{n,m})/(n∧m) = log(n∧m)/(n∧m)` tends to `0` — the two hypotheses of the certified `Wave30tu.cor_consistency`, in its form. -/
def delta_schedule : Prop :=
  (∀ n m : ℕ, 2 ≤ n → 2 ≤ m → 0 < deltaSched n m ∧ deltaSched n m < 1) ∧
  ∀ (ι : Type) (l : Filter ι) (n m : ι → ℕ), Tendsto (fun i => min (n i) (m i)) l atTop →
    Tendsto (fun i => deltaSched (n i) (m i)) l (𝓝 0) ∧
    Tendsto (fun i => Real.log (1 / deltaSched (n i) (m i)) / (min (n i) (m i) : ℕ)) l (𝓝 0)

/-- (b) the certified `Wave30tu.cor_consistency` instantiated with (a): under (A1)–(A3) and `α⋆ = TV(P,Q) < 1`, for any valid thresholds `τ` and
lower two-sided tools `τA` at every level `d ∈ (0,1)` that are `≤ r_n(·,d/2) + r_m(·,d/2)` (the hypotheses of that corollary), along every
schedule with `n, m ≥ 2` and `n∧m → ∞`, the estimator at level `δ_{n,m} = 1/(n∧m)` converges in probability to `α⋆ = TV(P,Q)`: for every `e > 0`
there are measurable events `E_i ⊆ {|α̂_i − α⋆| ≤ e}` whose probabilities tend to `1`. -/
def consistency_schedule : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (τ τA : ℕ → ℕ → ℝ → ℝ → ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ → StatFormal.Distances.tvDist P Q < 1 →
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → ∀ d : ℝ, 0 < d → d < 1 →
      StatFormal.Wave30tu.ValidThreshold φ n m d (τ n m d) ∧
        (∀ α ∈ Ico (0 : ℝ) 1, τ n m d α ≤ StatFormal.TrimmedMMD.tau κ α d n m) ∧
        StatFormal.Wave30tu.LowerTool φ P Q n m d (τA n m d) ∧
        ∀ α ∈ Ico (0 : ℝ) 1, τA n m d α ≤ StatFormal.TrimmedMMD.tau κ α d n m) →
    (∀ i, 2 ≤ n i) → (∀ i, 2 ≤ m i) → Tendsto (fun i => min (n i) (m i)) l atTop →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | |StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
            (τ (n i) (m i) (deltaSched (n i) (m i))) - StatFormal.Distances.tvDist P Q| ≤ e}) ∧
        Tendsto (fun i => ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) (E i))
          l (𝓝 1)

/-- (b) for the paper's threshold `τ = min(τ^P, τ^{P'}, τ^A)` (general kernel, `Wave30tu.Full.tauFull`, `D` any bound on `‖φ x − φ x′‖` with
`D ≤ 2κ`, the form of the certified `cor_consistency_full`): under (A1)–(A3) and `α⋆ = TV(P,Q) < 1`, along every schedule with `n, m ≥ 2` and
`n∧m → ∞`, `α̂_{n,m}` at level `δ_{n,m} = 1/(n∧m)` converges in probability to `α⋆`. -/
def consistency_schedule_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D : ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → D ≤ 2 * κ →
    Characteristic φ → StatFormal.Distances.tvDist P Q < 1 →
    (∀ i, 2 ≤ n i) → (∀ i, 2 ≤ m i) → Tendsto (fun i => min (n i) (m i)) l atTop →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | |StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
            (fun α => tauFull κ D α (deltaSched (n i) (m i)) (n i) (m i)) - StatFormal.Distances.tvDist P Q| ≤ e}) ∧
        Tendsto (fun i => ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) (E i))
          l (𝓝 1)

/-- (b) the same for the paper's threshold in its coupled form (kernels with `k ≥ 0` and `k(x,x) ≡ κ²`, the sharper candidate `τ^{P'}` being the
coupled supremum: `Wave31ta.tauV2Cpl = min(τ^A, τ^P, τ^{cpl}_{P'})`). -/
def consistency_schedule_cpl : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D : ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → D ≤ 2 * κ →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    Characteristic φ → StatFormal.Distances.tvDist P Q < 1 →
    (∀ i, 2 ≤ n i) → (∀ i, 2 ≤ m i) → Tendsto (fun i => min (n i) (m i)) l atTop →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | |StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
            (fun α => StatFormal.Wave31ta.tauV2Cpl κ D α (deltaSched (n i) (m i)) (n i) (m i)) -
          StatFormal.Distances.tvDist P Q| ≤ e}) ∧
        Tendsto (fun i => ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) (E i))
          l (𝓝 1)

/-! ### G7 `prose:n-of-a` (`03_analytic.tex:222-229`) -/

/-- (a) the generic reason: if, for every sample size `n ≥ 1`, the threshold `a ↦ τ_n(a)` is nondecreasing on `[0,1)` with `τ_n(0) > 0`, and the
path `D` is continuous on `[0,α⋆]` with `D(α⋆) = 0` (`0 < α⋆ < 1`), then for every `N ∈ ℕ` there is `a_N ∈ [0,α⋆)` such that `n(a) > N` for every
`a ∈ [a_N, α⋆)`, where `n(a) = min{n ≥ 1 : τ_n(a) < D(a)} ∈ ℕ ∪ {∞}` (`sizeNeeded`); i.e. `n(a)` grows without bound as `a ↑ α⋆`. -/
def n_of_a_generic : Prop :=
  ∀ (τ : ℕ → ℝ → ℝ) (D : ℝ → ℝ) (αs : ℝ), 0 < αs → αs < 1 →
    (∀ n, 1 ≤ n → MonotoneOn (τ n) (Ico 0 1)) → (∀ n, 1 ≤ n → 0 < τ n 0) →
    ContinuousOn D (Icc 0 αs) → D αs = 0 →
      ∀ N : ℕ, ∃ aN ∈ Ico 0 αs, ∀ a ∈ Ico aN αs, (N : ℕ∞) < sizeNeeded τ D a

/-- (b) "The size `n(a)` grows without bound as `a ↑ α⋆`" at the paper's threshold (general kernel, `Wave30tu.Full.tauFull`, `D` any bound on
`‖φ x − φ x′‖`): under (A1)–(A2), `0 < α⋆ = TV(P,Q) < 1`, `δ ∈ (0,1)`, `κ > 0` and `D > 0` (a non-degenerate feature map), for every `N ∈ ℕ` there
is `a_N ∈ [0,α⋆)` such that `n(a) = min{n ≥ 1 : τ_{n,n}(a,δ) < D_a(P,Q)} > N` for every `a ∈ [a_N, α⋆)`. -/
def n_of_a_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < κ → 0 < D →
    0 < δ → δ < 1 → 0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      ∀ N : ℕ, ∃ aN ∈ Ico 0 (StatFormal.Distances.tvDist P Q), ∀ a ∈ Ico aN (StatFormal.Distances.tvDist P Q),
        (N : ℕ∞) < sizeNeeded (fun n a => tauFull κ D a δ n n) (Dpop φ P Q) a

/-- (b) the same at the paper's threshold in its coupled form (kernels with `k ≥ 0` and `k(x,x) ≡ κ²`, `Wave31ta.tauV2Cpl`). -/
def n_of_a_cpl : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) → 0 < κ → 0 < D →
    0 < δ → δ < 1 → 0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      ∀ N : ℕ, ∃ aN ∈ Ico 0 (StatFormal.Distances.tvDist P Q), ∀ a ∈ Ico aN (StatFormal.Distances.tvDist P Q),
        (N : ℕ∞) < sizeNeeded (fun n a => StatFormal.Wave31ta.tauV2Cpl κ D a δ n n) (Dpop φ P Q) a

/-! ### G8 `prose:no-uniform-rate` (`03_analytic.tex:202-203`, `thm:impossible` `04_split.tex:141-148`) -/

/-- "no estimator of `TV` has a rate uniform over all pairs" (the core): fix `n, m ≥ 1`, `δ ∈ (0,½)` and a radius `r < ½` (the binding target takes
`r ∈ [0,½)`; here every real `r < ½` is allowed, a negative `r` making the event empty; `r < ½` is sharp, since `T̂ ≡ ½` is within `½` of every
`TV ∈ [0,1]`). For every measurable, possibly randomised estimator
`T̂ = T̂(X_{1:n}, Y_{1:m}, ξ)` with values in `ℝ`, it is false that `Pr_{P,Q}(|T̂ − TV(P,Q)| ≤ r) ≥ 1 − δ` for every `(P,Q) ∈ 𝒫₂` (pairs of
probability measures on `[0,1]` with Lebesgue densities bounded by `2`, `Wave31ta.Density2`). -/
def no_uniform_accuracy : Prop :=
  ∀ (n m : ℕ) (δ r : ℝ) (Ξ : Type) [MeasurableSpace Ξ] (R : Measure Ξ) [IsProbabilityMeasure R]
    (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
    1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 / 2 → r < 1 / 2 → Measurable T →
    ¬ ∀ P Q : Measure ℝ, StatFormal.Wave31ta.Density2 P → StatFormal.Wave31ta.Density2 Q →
        1 - δ ≤ (StatFormal.TrimmedMMD.Impossible.dataLaw n m P Q R).real
          {z | |T z - StatFormal.Distances.tvDist P Q| ≤ r}

/-- Binding target (not printed): "hence no radius sequence `r_{n,m} → 0` is attained uniformly over `𝒫₂`, and so none over all pairs of laws on
`[0,1]`". For every `δ ∈ (0,½)` and every radius array `r_{n,m}` with `r_{n,m} → 0` as `n, m → ∞`, there is `N` such that for all `n, m ≥ N` and
every measurable, possibly randomised estimator `T̂` at sizes `(n,m)`, it is false that `Pr_{P,Q}(|T̂ − TV(P,Q)| ≤ r_{n,m}) ≥ 1 − δ` for all
`(P,Q) ∈ 𝒫₂`, and false for all pairs of laws on `[0,1]` (`Law01`). `N` does not depend on the estimator. The printed "all pairs" is read as all
pairs of laws on the sample space `[0,1] ⊂ ℝ` of `thm:impossible` (on a finite sample space a plug-in estimator of `TV` has a uniform rate, so some
richness of the sample space is implicit in the printed sentence); the second conjunct follows from the first because `Density2 ⊂ Law01`. -/
def no_uniform_rate : Prop :=
  ∀ (δ : ℝ) (r : ℕ → ℕ → ℝ), 0 < δ → δ < 1 / 2 → Tendsto (fun p : ℕ × ℕ => r p.1 p.2) atTop (𝓝 0) →
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → 1 ≤ n → 1 ≤ m →
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (R : Measure Ξ) [IsProbabilityMeasure R]
        (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ), Measurable T →
      (¬ ∀ P Q : Measure ℝ, StatFormal.Wave31ta.Density2 P → StatFormal.Wave31ta.Density2 Q →
          1 - δ ≤ (StatFormal.TrimmedMMD.Impossible.dataLaw n m P Q R).real
            {z | |T z - StatFormal.Distances.tvDist P Q| ≤ r n m}) ∧
      (¬ ∀ P Q : Measure ℝ, Law01 P → Law01 Q →
          1 - δ ≤ (StatFormal.TrimmedMMD.Impossible.dataLaw n m P Q R).real
            {z | |T z - StatFormal.Distances.tvDist P Q| ≤ r n m})

/-! ### G6 `prose:strict-overlap` (`07_data.tex:8-11`) -/

/-- "strict overlap, a propensity score in `[η, 1−η]`, bounds every `f`-divergence between the covariate laws of the arms by a constant free of the
dimension (for arms of equal size, `TV(P,Q) ≤ 1 − 2η`)": for probability measures `P`, `Q` on any measurable space (the covariate laws of the two arms),
`η ∈ (0,½]` and strict overlap for arms of equal size (`StrictOverlap`: `η ≤ p/(p+q) ≤ 1 − η` `(P+Q)`-a.e. where `p + q > 0`, `p = dP/d(P+Q)`,
`q = dQ/d(P+Q)`): (i) `TV(P,Q) ≤ 1 − 2η`; (ii) `P ≪ Q ≪ P` with `η/(1−η) ≤ dP/dQ ≤ (1−η)/η` (and, by symmetry, the same for `dQ/dP`), and
for every convex `f : [0,∞) → ℝ` with `f(1) = 0`, `D_f(P‖Q) = ∫ f(dP/dQ) dQ` and `D_f(Q‖P)` exist and are at most `max{f(η/(1−η)), f((1−η)/η)}`,
a constant that depends on `η` and `f` only, not on the space or its dimension (`FDivBound` in both orders). Arms of equal size only (see the
module docstring, Not covered); the reverse order `D_f(Q‖P)`, `Q ≪ P` and the integrability are additions to the binding target; the constant
`max{f(a), f(b)}` (`a = η/(1−η)`, `b = (1−η)/η`) is valid but not the sharpest (the chord bound gives `((b−1)f(a) + (1−a)f(b))/(b−a)`). -/
def strict_overlap : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (η : ℝ),
    0 < η → η ≤ 1 / 2 → StrictOverlap P Q η →
      StatFormal.Distances.tvDist P Q ≤ 1 - 2 * η ∧ FDivBound P Q η ∧ FDivBound Q P η

end Claims

end StatFormal.Wave31tf
