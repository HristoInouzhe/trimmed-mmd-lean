import StatFormal.Wave31tf.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31ti: trimmed-mmd (jmlr) **v3 revision of 2026-11-17**: `lem:pathconvex`, the polynomial `ass:margin`, `thm:rate`, `lem:marginexists`, `prop:rategeneral`

Printed source: the working tree of `trimmed-mmd/jmlr/v3/` on 2026-11-17 (uncommitted on top of trimmed-mmd `5e17fad`; the revision is
red text, `\rev{}`/`revblock`; read-only, read 2026-11-17). sha256 of the files read:
`sections/03_analytic.tex` `1d3360b7827698fce51e27bf8215e422eb7a922c84d95229344f8ad55d35d437`,
`appendix/B_analytic.tex` `b0e9849a9c13b7241f9f88cc66b15ed0e902487fcdcf11d8f652468911a3a2c9`,
`sections/02_regions.tex` `8c3985ee6342637cdae3398107f390f70dace632577b9c1176a800ab5ea11461`,
`sections/05_trimming.tex` `d418a839f402427505bc231fbc61e484296781710ce8a20ff9e9525af20260be`.
Printed numbers (from `main.aux` of the same build): Assumption 1 `ass:regularity`, Assumption 2 `ass:margin`, Lemma 7 `lem:pathconvex`,
Theorem 8 `thm:rate`, Lemma 24 `lem:marginexists`, Proposition 25 `prop:rategeneral`.

* `ass:margin` (Assumption 2, "Polynomial margin", `03_analytic.tex:178-182`): "There are constants `c₀ > 0` and `γ ≥ 1` such that
  `D_{α⋆−ε}(P,Q) ≥ c₀ε^γ` for all `ε ∈ [0,α⋆]`." Encoded as the definition `PolyMargin φ P Q c₀ γ`.
* `lem:pathconvex` (Lemma 7, "Convexity of the path", `03_analytic.tex:197-212`, proof `B_analytic.tex:423-477`): "Let Assumption 1
  hold, let `P,Q` be any probability measures on `𝒳`, empirical measures included, and put `u(α) := (1−α)D_α(P,Q)` for `α ∈ [0,1)`.
  Then `u` is convex and nonincreasing. If moreover `0 < α⋆ < 1`, then: (i) `u` is strictly decreasing on `[0,α⋆]`, and for all
  `0 ≤ α₁ < α₂ < α⋆`, `α⋆ ≥ α₂ + (α₂−α₁)u(α₂)/(u(α₁)−u(α₂))`; (ii) `ε ↦ u(α⋆−ε)/ε` is nondecreasing on `(0,α⋆]`, so it has a limit
  `s ≥ 0` as `ε ↓ 0`, and `D_{α⋆−ε}(P,Q) ≤ D₀(P,Q)ε/{α⋆(1−α⋆)}` for all `ε ∈ [0,α⋆]`. Assumption 2 holds with `γ = 1` if and only if
  `s > 0`, and then it holds with `c₀ = s`."
  The prose after it (`03_analytic.tex:214-219`): "By (ii) the path leaves zero in one of two ways: with a kink, a positive slope at
  `α⋆`, and then the margin is linear, or tangentially, and then no linear margin holds and Assumption 2 needs `γ > 1`. … Since the lemma
  applies to `P_n` and `Q_m` as well, the rescaled empirical path `α ↦ (1−α)D̂_α` is convex too."
* `lem:marginexists` (Lemma 24, "A margin always exists", `B_analytic.tex:371-381`): "Let Assumption 1 hold with `0 < α⋆ < 1`, and for
  `ε ∈ [0,α⋆]` put `m(ε) := min_{ε′∈[ε,α⋆]} D_{α⋆−ε′}(P,Q)`, `ω(ε) := (ε/α⋆) m(ε)`. Then `ω` is continuous and strictly increasing on
  `[0,α⋆]`, `ω(0) = 0`, and `D_{α⋆−ε}(P,Q) ≥ ω(ε)` for every `ε ∈ [0,α⋆]`."
* `prop:rategeneral` (Proposition 25, `B_analytic.tex:406-415`) is the former `thm:rate` verbatim (general `ω`); it is the certified
  `Wave30tu.rate` (with `rate_eps`, and `Wave30tu.Full.rate_full` at the paper's `τ`): no new claim here. The sentence after it
  (`B_analytic.tex:417-419`): "Theorem 8 is the case `ω(ε) = c₀ε^γ`, which is strictly increasing and continuous with `ω(0) = 0`; then
  `t_{n,m} ≤ c₀(α⋆)^γ = ω(α⋆)` and `ε_{n,m} = (t_{n,m}/c₀)^{1/γ}`" is `poly_is_general`.
* `thm:rate` (Theorem 8, "Rate under the margin condition", `03_analytic.tex:241-252`, proof `B_analytic.tex:482-505`): "Let
  Assumptions 1 and 2 hold, let `δ,δ′ ∈ (0,1)`, put `t_{n,m} = τ(α⋆) + τ^A(α⋆,δ′)`, …, and suppose that `n,m` are large enough that
  `t_{n,m} ≤ c₀(α⋆)^γ`. Then with probability at least `1−δ−δ′`, `α̂ ≤ α⋆` and
  `|α̂ − α⋆| ≤ (t_{n,m}/c₀)^{1/γ} = O((κ/(c₀(1−α⋆)) √((1+log(1/δ)+log(1/δ′))/(n∧m)))^{1/γ})`."
* The linear-kernel pair "satisfies Assumption 2 with `c₀ = 3/2` and `γ = 1`" (`05_trimming.tex:85`): `linear_poly`.

Reuses (imported, not copied): `TrimmedMMD.Unconditional.Dpop`/`Demp` (the regions' distance `D_α(P,Q)`, `eq:setdist`, equal to the printed
infimum over trimmings by the certified `Wave8a.georep_dist`; `D̂_α = D_α(P_n,Q_m)`), `TrimmedMMD.Concentration.region`/`empirical`,
`TrimmedMMD.ZeroSet.Characteristic` ((A3)), `Distances.tvDist`, `Wave30tu.ValidThreshold`, `LowerTool`, `Margin` (the general margin of
`prop:rategeneral`), `TrimmedMMD.alphaHat`, `TrimmedMMD.tau` (`r_n + r_m`), `Wave30tu.Full.tauFull` (the paper's `τ_{n,m}`),
`Wave30tr.tauA` (`eq:tauA`), `Wave31td.phiLin`, `Plin`, `Qlin` (the linear-kernel pair).

Encodings:
* (A1)–(A2) as in every earlier trimmed-mmd wave: `H` a real complete separable inner-product space, `φ : 𝒳 → H` strongly measurable with
  `‖φ x‖ ≤ κ` (the canonical feature map); (A3) is `Characteristic φ`. (A3) is assumed only where the proof needs `D_α > 0` below `α⋆`
  (`eq:zeroeq`): `pathconvex_i` and `marginexists`; it is dropped elsewhere (generalisation; `pathconvex_ii` and `pathconvex_tangent` need
  only `D_{α⋆} = 0`, which holds without (A3) by the certified `ZeroSet.zero_of_tv_le`).
* `α⋆ = TV(P,Q)` is `tvDist P Q`. `u(α) = (1−α)D_α(P,Q)` is `uPath φ P Q α`; its empirical counterpart `(1−α)D̂_α` is `uEmp φ x y α`.
  "convex and nonincreasing" on `[0,1)`: `ConvexOn ℝ (Ico 0 1)` and `AntitoneOn … (Ico 0 1)`.
* "`P,Q` any probability measures, empirical measures included": the claims are for all probability measures; `pathconvex_emp` states the
  empirical case (`empirical x` with `n ≥ 1` points) explicitly.
* (ii): `r(ε) = u(α⋆−ε)/ε`; "nondecreasing on `(0,α⋆]`" is `MonotoneOn r (Ioc 0 α⋆)`; "it has a limit `s ≥ 0` as `ε ↓ 0`" is
  `∃ s, Tendsto r (𝓝[>] 0) (𝓝 s)`, and every such limit `s` is `≥ 0` and satisfies the equivalence and the `c₀ = s` clause.
* `ass:margin` is `PolyMargin φ P Q c₀ γ`: `0 < c₀`, `1 ≤ γ`, `c₀ ε^γ ≤ D_{α⋆−ε}(P,Q)` for `ε ∈ [0,α⋆]` (`ε^γ` is `Real.rpow`, genuine for
  `ε ≥ 0`, `0^γ = 0` as `γ ≥ 1`). "Assumption 2 holds with `γ = 1`" is `∃ c₀, PolyMargin φ P Q c₀ 1`.
* `m(ε) = min_{ε′∈[ε,α⋆]} D_{α⋆−ε′}` is `mRun` (the `sInf` of the image of `[ε,α⋆]`); that the minimum is attained (so `m` is well defined as a
  minimum) is part of `marginexists`. `ω(ε) = (ε/α⋆)m(ε)` is `omegaRun` (`α⋆ > 0`, no division by zero).
* `thm:rate`: as in the certified `Wave30tu.rate_poly`, the threshold `τ` is any valid threshold at level `δ` (`ValidThreshold`, the hypothesis
  of `lem:oneevent`) and `τ^A(·,δ′)` any lower two-sided tool at level `δ′` (`LowerTool`, the event `E⁻` of `thm:twosided`) — a declared
  generalisation; the paper's `τ_{n,m}` and `τ^A_{n,m}` are instantiated in `rate_v3_full`. `α⋆ < 1` is assumed (the printed theorem
  evaluates `τ(α⋆)`, defined on `[0,1)`). "With probability at least `1−δ−δ′`" is a measurable event of that probability inside the claimed
  set. The `O(·)`: in `rate_v3`, with `τ, τ^A ≤ r_n + r_m` at `α⋆`, the explicit constant 24 of `Wave30tu.rate_poly`; in `rate_v3_full`,
  the printed proof's bound `t ≤ 2κ(1−α⋆)^{-1}(2√2 + 4 + √log(1/δ) + √log(1/δ′))/√(n∧m)` for `Δ_φ ≤ 2κ`, and the `O(·)` with the
  explicit constant 14.
* Junk values: `Dpop` is evaluated only at levels in `[0,1)` (by `α⋆ < 1`), where the `1/(1−α)` inside `region` is genuine; `r(ε)` divides by
  `ε` only on `(0,α⋆]` (its values elsewhere do not enter: `𝓝[>] 0` is eventually in `(0,α⋆]`); the secant bound divides by
  `u(α₁) − u(α₂)`, positive by the strict decrease in the same claim (and stated only for `α₁ < α₂ < α⋆`); `D₀ε/(α⋆(1−α⋆))` has a positive
  denominator; `(t/c₀)^{1/γ}` has `c₀ > 0`, `γ ≥ 1`, `t ≥ 0`; `log(1/δ)` with `δ ∈ (0,1)`; `min n m ≥ 1`.

Covered elsewhere (no new claim): `ex:separated` (Example 1) now concludes "Assumption 2 holds with `γ = 1` and `c₀ = 2/‖f‖`"; the certified
`Wave31tb.separated` already states `‖f‖ > 0` and `2/‖f‖ · ε^1 ≤ D_{α⋆−ε}(P,Q)` on `[0,α⋆]`, i.e. `PolyMargin φ P Q (2/‖f‖) 1`. "Exponents
below `1` are excluded because no path can satisfy them" (`03_analytic.tex:186-187`, `B_analytic.tex:474-476`) is the certified
`Wave31tf.gamma_ge_one` (under (A1)–(A2), `0 < α⋆ < 1`, `c₀ > 0`, `γ > 0`: the bound `c₀ε^γ ≤ D_{α⋆−ε}` on `[0,α⋆]` forces `γ ≥ 1`); the
reason given now (the upper bound of (ii)) is another proof of it.
Not covered: "The rate is `(n∧m)^{-1/(2γ)}`" (a reading of the `O(·)`), "a larger `γ` allows a flatter contact, which is harder to detect"
(informal), and the prose "extrapolating it to zero never overshoots" beyond what `pathconvex_i` states (the secant bound itself).
FROZEN 2026-11-17 before any proof, after an independent critic's pre-freeze review (10 claims: 8 ACCEPT, 1 ACCEPT-WITH-NOTE
(`pathconvex_ii`: (A3) not needed), 1 REVISE non-blocking (`rate_v3_full`: add the printed `O(·)` at the paper's thresholds); none false;
verdict READY TO FREEZE; it typechecked the draft, back-translated blind, checked hashes and `main.aux` numbers, and re-derived the
secant bound, the limit `s`, the equivalence, the `D₀` bound and the `τ^A` bound. Applied: five line numbers, (A3) dropped from
`pathconvex_ii` and `pathconvex_tangent`, the constant-14 conjunct of `rate_v3_full`, the coverage of `ex:separated` and of "exponents below
1 are excluded" (`Wave31tf.gamma_ge_one`), the Not-covered list). Hashed in `certify/statements.lock` (with its imports); AI agents must not
edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave31ti

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet StatFormal.Wave30tu

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `ass:margin` (v3, Assumption 2, polynomial margin): `c₀ > 0`, `γ ≥ 1`, and `D_{α⋆−ε}(P,Q) ≥ c₀ε^γ` for every `ε ∈ [0,α⋆]`,
`α⋆ = TV(P,Q)`. -/
def PolyMargin (φ : 𝒳 → H) (P Q : Measure 𝒳) (c₀ γ : ℝ) : Prop :=
  0 < c₀ ∧ 1 ≤ γ ∧ ∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
    c₀ * e ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)

/-- The rescaled population path `u(α) = (1−α) D_α(P,Q)` (`lem:pathconvex`). -/
def uPath (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : ℝ := (1 - α) * Dpop φ P Q α

/-- The rescaled empirical path `(1−α) D̂_α`, `D̂_α = D_α(P_n,Q_m)`. -/
def uEmp (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (α : ℝ) : ℝ := (1 - α) * Demp φ x y α

/-- The running minimum `m(ε) = min_{ε′ ∈ [ε,α⋆]} D_{α⋆−ε′}(P,Q)` of `lem:marginexists`, as the `sInf` of the image of `[ε,α⋆]`. -/
def mRun (φ : 𝒳 → H) (P Q : Measure 𝒳) (ε : ℝ) : ℝ :=
  sInf ((fun e' => Dpop φ P Q (StatFormal.Distances.tvDist P Q - e')) '' Icc ε (StatFormal.Distances.tvDist P Q))

/-- `ω(ε) = (ε/α⋆) m(ε)` of `lem:marginexists`. -/
def omegaRun (φ : 𝒳 → H) (P Q : Measure 𝒳) (ε : ℝ) : ℝ :=
  ε / StatFormal.Distances.tvDist P Q * mRun φ P Q ε

end Defs

namespace Claims

/-! ### `lem:pathconvex` (Lemma 7) -/

/-- `lem:pathconvex`, first sentence: for any probability measures `P, Q` (under (A1)–(A2); (A3) is not needed), `u(α) = (1−α)D_α(P,Q)`
is convex and nonincreasing on `[0,1)`. -/
def pathconvex : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
      ConvexOn ℝ (Ico 0 1) (uPath φ P Q) ∧ AntitoneOn (uPath φ P Q) (Ico 0 1)

/-- `lem:pathconvex` for empirical measures, and the sentence after it ("Since the lemma applies to `P_n` and `Q_m` as well, the rescaled
empirical path `α ↦ (1−α)D̂_α` is convex too"): for every realization with `n, m ≥ 1`, `(1−α)D̂_α` is convex and nonincreasing on
`[0,1)`. -/
def pathconvex_emp : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        ConvexOn ℝ (Ico 0 1) (uEmp φ x y) ∧ AntitoneOn (uEmp φ x y) (Ico 0 1)

/-- `lem:pathconvex` (i): under (A1)–(A3) with `0 < α⋆ = TV(P,Q) < 1`, `u` is strictly decreasing on `[0,α⋆]`, and for all
`0 ≤ α₁ < α₂ < α⋆`, `α⋆ ≥ α₂ + (α₂ − α₁)u(α₂)/(u(α₁) − u(α₂))` (the secant through two points of `u` below `α⋆` reaches zero at or before
`α⋆`). -/
def pathconvex_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      StrictAntiOn (uPath φ P Q) (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧
      ∀ α₁ α₂ : ℝ, 0 ≤ α₁ → α₁ < α₂ → α₂ < StatFormal.Distances.tvDist P Q →
        α₂ + (α₂ - α₁) * uPath φ P Q α₂ / (uPath φ P Q α₁ - uPath φ P Q α₂) ≤ StatFormal.Distances.tvDist P Q

/-- `lem:pathconvex` (ii): under (A1)–(A2) ((A3) is not needed) with `0 < α⋆ = TV(P,Q) < 1`, with `r(ε) = u(α⋆−ε)/ε`: `r` is nondecreasing on `(0,α⋆]`; it
has a limit as `ε ↓ 0`; every such limit `s` is `≥ 0`, Assumption 2 holds with `γ = 1` (for some `c₀`) if and only if `s > 0`, and if
`s > 0` it holds with `c₀ = s`; and `D_{α⋆−ε}(P,Q) ≤ D₀(P,Q)ε/(α⋆(1−α⋆))` for every `ε ∈ [0,α⋆]`. -/
def pathconvex_ii : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      MonotoneOn (fun e => uPath φ P Q (StatFormal.Distances.tvDist P Q - e) / e)
          (Ioc 0 (StatFormal.Distances.tvDist P Q)) ∧
      (∃ s : ℝ, Tendsto (fun e => uPath φ P Q (StatFormal.Distances.tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 s)) ∧
      (∀ s : ℝ, Tendsto (fun e => uPath φ P Q (StatFormal.Distances.tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 s) →
        0 ≤ s ∧ ((∃ c₀ : ℝ, PolyMargin φ P Q c₀ 1) ↔ 0 < s) ∧ (0 < s → PolyMargin φ P Q s 1)) ∧
      ∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
        Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) ≤
          Dpop φ P Q 0 * e / (StatFormal.Distances.tvDist P Q * (1 - StatFormal.Distances.tvDist P Q))

/-- The prose after `lem:pathconvex` (`03_analytic.tex:214-216`): "or tangentially, and then no linear margin holds and Assumption 2
needs `γ > 1`": under (A1)–(A2) with `0 < α⋆ < 1`, if the limit `s` of `u(α⋆−ε)/ε` as `ε ↓ 0` is `0`, then no `c₀` gives Assumption 2
with `γ = 1`, and every `(c₀, γ)` satisfying Assumption 2 has `γ > 1`. -/
def pathconvex_tangent : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      Tendsto (fun e => uPath φ P Q (StatFormal.Distances.tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 0) →
        (¬ ∃ c₀ : ℝ, PolyMargin φ P Q c₀ 1) ∧ ∀ c₀ γ : ℝ, PolyMargin φ P Q c₀ γ → 1 < γ

/-! ### `lem:marginexists` (Lemma 24) -/

/-- `lem:marginexists`: under (A1)–(A3) with `0 < α⋆ = TV(P,Q) < 1`, for every `ε ∈ [0,α⋆]` the minimum `m(ε)` of `D_{α⋆−ε′}` over
`ε′ ∈ [ε,α⋆]` is attained; `ω(ε) = (ε/α⋆)m(ε)` is continuous and strictly increasing on `[0,α⋆]`, `ω(0) = 0`, and
`D_{α⋆−ε}(P,Q) ≥ ω(ε)` for every `ε ∈ [0,α⋆]`; in particular `ω` is a margin in the sense of `prop:rategeneral` (`Wave30tu.Margin`). -/
def marginexists : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      (∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
        IsLeast ((fun e' => Dpop φ P Q (StatFormal.Distances.tvDist P Q - e')) ''
          Icc ε (StatFormal.Distances.tvDist P Q)) (mRun φ P Q ε)) ∧
      ContinuousOn (omegaRun φ P Q) (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧
      StrictMonoOn (omegaRun φ P Q) (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧
      omegaRun φ P Q 0 = 0 ∧
      (∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
        omegaRun φ P Q ε ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε)) ∧
      Margin φ P Q (omegaRun φ P Q)

/-! ### `prop:rategeneral` (Proposition 25) and `thm:rate` (Theorem 8) -/

/-- The sentence after `prop:rategeneral` (`B_analytic.tex:417-419`): the polynomial margin is a margin in the general sense,
`ω(ε) = c₀ε^γ` being strictly increasing and continuous on `[0,α⋆]` with `ω(0) = 0`; and for `0 ≤ t ≤ c₀(α⋆)^γ = ω(α⋆)`,
`ε = (t/c₀)^{1/γ}` lies in `[0,α⋆]` and solves `ω(ε) = t`. -/
def poly_is_general : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (c₀ γ : ℝ),
    PolyMargin φ P Q c₀ γ →
      Margin φ P Q (fun e => c₀ * e ^ γ) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ c₀ * StatFormal.Distances.tvDist P Q ^ γ →
        (t / c₀) ^ (1 / γ) ∈ Icc 0 (StatFormal.Distances.tvDist P Q) ∧ c₀ * ((t / c₀) ^ (1 / γ)) ^ γ = t

/-- `thm:rate` (v3, Theorem 8), any valid threshold `τ` at level `δ` and any lower two-sided tool `τ^A` at level `δ′`: under (A1)–(A2),
`α⋆ = TV(P,Q) < 1` and Assumption 2 (`PolyMargin`, `c₀ > 0`, `γ ≥ 1`), if `t = τ(α⋆) + τ^A(α⋆) ≤ c₀(α⋆)^γ`, then on one measurable event of
probability `≥ 1 − δ − δ′`, `α̂ ≤ α⋆` and `|α̂ − α⋆| ≤ (t/c₀)^{1/γ}`; and when `τ`, `τ^A` are at most `r_n + r_m` at `α⋆` (`eq:tauA`),
`(t/c₀)^{1/γ} ≤ (24κ/(c₀(1−α⋆)) · √((1 + log(1/δ) + log(1/δ′))/min(n,m)))^{1/γ}` (the `O(·)`, explicit constant 24). -/
def rate_v3 : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' c₀ γ : ℝ) (τ τA : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → PolyMargin φ P Q c₀ γ →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → LowerTool φ P Q n m δ' τA →
    τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q) ≤
      c₀ * StatFormal.Distances.tvDist P Q ^ γ →
      (∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q ∧
              |alphaHat (Demp φ z.1 z.2) τ - StatFormal.Distances.tvDist P Q| ≤
                ((τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q)) / c₀) ^ (1 / γ)}) ∧
      (τ (StatFormal.Distances.tvDist P Q) ≤ tau κ (StatFormal.Distances.tvDist P Q) δ n m →
        τA (StatFormal.Distances.tvDist P Q) ≤ tau κ (StatFormal.Distances.tvDist P Q) δ' n m →
        ((τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q)) / c₀) ^ (1 / γ) ≤
          (24 * κ / (c₀ * (1 - StatFormal.Distances.tvDist P Q)) *
            √((1 + Real.log (1 / δ) + Real.log (1 / δ')) / (min n m : ℕ))) ^ (1 / γ))

/-- `thm:rate` (v3, Theorem 8) at the paper's thresholds: `τ = τ_{n,m}(·,δ)` (`Wave30tu.Full.tauFull`, the minimum of `τ^A`, `τ^P`,
`τ^{P′}`) and `τ^A = τ^A_{n,m}(·,δ′)` of `eq:tauA` (`Wave30tr.tauA`), any `Δ_φ = D` with `‖φ x − φ x′‖ ≤ D`: under (A1)–(A2),
`α⋆ < 1` and Assumption 2, if `t_{n,m} = τ_{n,m}(α⋆,δ) + τ^A_{n,m}(α⋆,δ′) ≤ c₀(α⋆)^γ`, then on one measurable event of probability
`≥ 1 − δ − δ′`, `α̂ ≤ α⋆` and `|α̂ − α⋆| ≤ (t_{n,m}/c₀)^{1/γ}`; and if `D ≤ 2κ`,
`t_{n,m} ≤ 2κ(1−α⋆)^{-1}(2√2 + 4 + √log(1/δ) + √log(1/δ′))/√(n∧m)` (the bound of the printed proof) and, by Cauchy–Schwarz,
`(t_{n,m}/c₀)^{1/γ} ≤ (14κ/(c₀(1−α⋆)) · √((1 + log(1/δ) + log(1/δ′))/(n∧m)))^{1/γ}` (the printed `O(·)`, explicit constant 14). -/
def rate_v3_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' c₀ γ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    StatFormal.Distances.tvDist P Q < 1 → PolyMargin φ P Q c₀ γ →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    StatFormal.Wave30tu.Full.tauFull κ D (StatFormal.Distances.tvDist P Q) δ n m +
        StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m ≤
      c₀ * StatFormal.Distances.tvDist P Q ^ γ →
      (∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ D α δ n m) ≤
                StatFormal.Distances.tvDist P Q ∧
              |alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ D α δ n m) -
                  StatFormal.Distances.tvDist P Q| ≤
                ((StatFormal.Wave30tu.Full.tauFull κ D (StatFormal.Distances.tvDist P Q) δ n m +
                    StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m) / c₀) ^ (1 / γ)}) ∧
      (D ≤ 2 * κ →
        StatFormal.Wave30tu.Full.tauFull κ D (StatFormal.Distances.tvDist P Q) δ n m +
            StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m ≤
          2 * κ / (1 - StatFormal.Distances.tvDist P Q) *
            (2 * √2 + 4 + √(Real.log (1 / δ)) + √(Real.log (1 / δ'))) / √((min n m : ℕ) : ℝ)) ∧
      (D ≤ 2 * κ →
        ((StatFormal.Wave30tu.Full.tauFull κ D (StatFormal.Distances.tvDist P Q) δ n m +
            StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m) / c₀) ^ (1 / γ) ≤
          (14 * κ / (c₀ * (1 - StatFormal.Distances.tvDist P Q)) *
            √((1 + Real.log (1 / δ) + Real.log (1 / δ')) / (min n m : ℕ))) ^ (1 / γ))

/-! ### The linear-kernel pair under the polynomial margin (`05_trimming.tex:85`) -/

/-- "the pair also satisfies Assumption 2 with `c₀ = 3/2` and `γ = 1`" (the linear kernel on `[−1,1]`, `P = U[−½,1]`, `Q = U[−1,½]`). -/
def linear_poly : Prop :=
  PolyMargin StatFormal.Wave31td.phiLin StatFormal.Wave31td.Plin StatFormal.Wave31td.Qlin (3 / 2) 1

end Claims

end StatFormal.Wave31ti
