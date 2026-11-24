import StatFormal.Wave30tu.Statements
import StatFormal.Wave30tv.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tj: trimmed-mmd (jmlr) **v3 revision of 2026-11-17**: Algorithm 1 (`alg:bisect`, bisection for `α̂`) and `rem:batch0grid` (Remark 30)

Printed source: the working tree of `trimmed-mmd/jmlr/v3/` on 2026-11-17 (uncommitted on top of trimmed-mmd `5e17fad`; red text;
read-only, read 2026-11-17). sha256: `sections/03_analytic.tex` `1d3360b7827698fce51e27bf8215e422eb7a922c84d95229344f8ad55d35d437`,
`appendix/B_analytic.tex` `b0e9849a9c13b7241f9f88cc66b15ed0e902487fcdcf11d8f652468911a3a2c9`,
`appendix/C_split.tex` `e2db7656ba1fb9c91ec575069982c50f92e4875a2fd342bbe621d4cc137b4ae2`,
`sections/04_split.tex` `8a187adb8dde02a44279cc08f63927038ee64716688c69f2fb51203b516c220c`,
`sections/07_data.tex` `ef1aa08a2869e91af8d3d2f8fdcac6a022eb50130131467950fd68424d9d0330`.

* Algorithm 1 (`alg:bisect`, "Bisection for the analytic estimator `α̂`", `B_analytic.tex:259-278`, with the sentence before it
  `:256-257`: "by Lemma 22 the levels it rejects are exactly those below `α̂`, so it brackets `α̂` at every step"):
  "Say that `α` is rejected when `D̂_α > τ(α)`. If `0` is not rejected, return `α̂ = 0` and no rejected level. `ℓ ← 0` (largest
  level known to be rejected); `u ←` the smallest `α` with `τ(α) ≥ Δ_φ` (accepted, as `D̂_α ≤ Δ_φ`); `a ← α₀` if `ℓ < α₀ < u`, else
  `(ℓ+u)/2`; while `u − ℓ > ε` and fewer than `J` levels tested: if `a` is rejected then `ℓ ← a` else `u ← a`; `a ← (ℓ+u)/2`.
  Return `α_last = ℓ` and `u`; then `α̂ ∈ (ℓ,u]` and `α⋆ > ℓ` with probability at least `1−δ`."
* The prose of §3.2 (`03_analytic.tex:139-147`): "Since every level below `α̂` is rejected and every level from `α̂` on is accepted,
  `α̂` can be found by bisection. Each step tests the midpoint of an interval known to contain `α̂` and halves the interval, so a
  tolerance `ε` costs about `log₂(1/ε)` convex solves, seven for `ε = 0.01` … The first test is at a level `α₀` chosen by the user,
  `½` by default, or a guess from earlier data. We report the largest rejected level visited, `α_last`, which is within `ε` of `α̂`.
  On the event of Lemma 5 every rejected level is below `α⋆`, so `α⋆ > α_last` with probability at least `1−δ`, however the levels
  were chosen. The same holds for a grid of levels read upward, as in Section 7." and `07_data.tex:36-38` (Table 3): "bisection: the
  largest level rejected after bisecting between `α_last` and the first accepted grid level to width 0.0125, valid on the same event".
* `rem:batch0grid` (Remark 30, "A grid chosen from batch 0", `C_split.tex:168-178`): "Corollary 11 holds, with the same proof, when
  the grid `α₁ < ⋯ < α_J` is a measurable function of batch 0 instead of being fixed in advance. Given batch 0 the grid is fixed, …
  the conditional bound of Theorem 10 gives `P(H_{0,α_{i₀}} rejected | batch 0) ≤ δ`; integrating over batch 0 gives the claim." and
  `04_split.tex:161-163`: "The grid may also be chosen from batch 0 … because Theorem 10 holds conditionally on batch 0".

Reuses (imported, not copied): `TrimmedMMD.Unconditional.Demp` (`D̂_α`), `TrimmedMMD.alphaHat`, `TrimmedMMD.crossSet`,
`Wave30tu.ValidThreshold` (the hypothesis of `lem:oneevent`), `Wave30tu.tauRight` (`τ(0+)`), the frozen Wave 30tv betting framework
(`IsBatchPairing`, `IsBatchRule`, `seqReject`; `IsBatchBetRule` is generalised here to a level that depends on `u`), and
`TrimmedMMD.Lower.alphaLo` (`eq:downclosed`).

Encodings:
* (A1)–(A2) as in every earlier trimmed-mmd wave (`φ` strongly measurable, `‖φ‖ ≤ κ`, `H` complete separable); no (A3).
* "`α` is rejected": `rejected D̂ τ α :≡ τ α < D̂ α` with `D̂ = Demp φ x y` for the realization `(x, y)`.
* The algorithm: `bisectLoop rej ε J ℓ u a` runs the while loop from `(ℓ, u)` with first test point `a`, at most `J` tests, and returns
  `(ℓ, u, number of tests)`; `bisectAlg rej α₀ u₀ ε J` is Algorithm 1 with `u = u₀`: `none` ("return `α̂ = 0` and no rejected level")
  if `0` is not rejected, else the loop from `(0, u₀)` with first test `α₀` if `0 < α₀ < u₀`, else `u₀/2`. The printed choice of `u₀`
  ("the smallest `α` with `τ(α) ≥ Δ_φ`") is replaced by any accepted level `u₀ ∈ (0,1)` (generalisation); `alg_start` covers the
  printed choice. The test of level `0` is not counted among the `J` tests (the printed "fewer than `J` levels tested" leaves this open;
  the count of `alg_cost`, "seven for `ε = 0.01`", is that of the bisection tests).
* Corrected reading (declared): the printed `α̂ ∈ (ℓ,u]` is frozen as `ℓ ≤ α̂ ≤ u`, with `ℓ < α̂` whenever `ℓ > 0`. When `ℓ = 0` the
  strict inequality can fail if `τ` jumps at `0` (`τ(0) < τ(0+)`, which `lem:crossing` allows): then `0` may be rejected while
  `α̂ = 0`. Likewise "every level from `α̂` on is accepted" holds for levels above `α̂`, and at `α̂` itself when `α̂ > 0`
  (certified `Wave30tu.crossing`).
* "with probability at least `1 − δ`, however the levels were chosen": one measurable event of probability `≥ 1 − δ` (that of
  `lem:oneevent`) on which every rejected level in `[0,1)` is `< α⋆`, and the output `ℓ` of every run of the loop and of the algorithm
  (any `α₀`, `u₀`, `ε`, `J`, start, possibly chosen from the data) is `< α⋆`.
* `rem:batch0grid`: in the frozen Wave 30tv framework, batch 0 is `batchZero lx ly ω = (u, (x_i)_{lx i = 0}, (y_j)_{ly j = 0})` (the
  auxiliary randomness `u` and the observations of batch 0). The grid is `α j u x y`, jointly measurable, `≥ 0`, and a function of
  `u` and batch 0 only (it agrees for samples that agree on batch 0); not necessarily increasing (a generalisation). The fractions at
  level `j` are capped by `c/(1 + α_j)` at that level (`IsBatchBetRuleU`). The conditional form is for every value `(u, x₀, y₀)` of
  batch 0, as the frozen `Wave30tv.thm_betting_cond` (batch 0 replaced by `withBatchZero`).
* Junk values: `Demp` is evaluated by the claims at levels in `[0,1)` only where it matters (every tested level lies in `(ℓ₀, u₀) ⊆ [0,1)`);
  `alphaHat` is the `sInf` of a nonempty set bounded below (the accepted `u₀` lies in it); `(1/2)^k` and `ε > 0` are genuine.
FROZEN 2026-11-17 before any proof, after an independent critic's pre-freeze review (7 claims: alg_bracket, alg_loop, alg_cost,
alg_start, alg_event ACCEPT; batch0grid_cond, batch0grid REVISE, true as drafted; none false; verdict READY TO FREEZE after the changes).
It confirmed the corrected reading (the printed `α̂ ∈ (ℓ,u]` fails when `τ(0) < τ(0+)`: `τ(0) = 0`, `τ = c` on `(0,1)`, `D̂₀ ∈ (0,c]`).
Applied: two line numbers, and the grid of `rem:batch0grid` as a function of `(u, batch 0 of x, batch 0 of y)` (`Batch0Grid`) with the
conditional form over `withBatchZero`, mirroring `Wave30tv.thm_betting_cond`, instead of a function of `u` alone. Hashed in
`certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave31tj

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tu StatFormal.Wave30tv StatFormal.Wave30tq

/-- `α` is rejected by the test `eq:test`: `D̂_α > τ(α)`. -/
def rejected (Dh τ : ℝ → ℝ) (α : ℝ) : Prop := τ α < Dh α

open Classical in
/-- The while loop of Algorithm 1 from the bracket `(ℓ, u)` with next test point `a`, at most `k` tests: returns
`(ℓ, u, number of tests performed)`. -/
def bisectLoop (rej : ℝ → Prop) (ε : ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ
  | 0, l, u, _ => (l, u, 0)
  | k + 1, l, u, a =>
    if u - l ≤ ε then (l, u, 0)
    else
      let r := if rej a then bisectLoop rej ε k a u ((a + u) / 2) else bisectLoop rej ε k l a ((l + a) / 2)
      (r.1, r.2.1, r.2.2 + 1)

/-- The first test point: `α₀` if `ℓ < α₀ < u`, else `(ℓ + u)/2`. -/
def startPoint (α₀ l u : ℝ) : ℝ := if l < α₀ ∧ α₀ < u then α₀ else (l + u) / 2

open Classical in
/-- Algorithm 1 with the accepted upper level `u₀`: `none` if `0` is not rejected (return `α̂ = 0`), else the loop from `(0, u₀)`. -/
def bisectAlg (rej : ℝ → Prop) (α₀ u₀ ε : ℝ) (J : ℕ) : Option (ℝ × ℝ × ℕ) :=
  if rej 0 then some (bisectLoop rej ε J 0 u₀ (startPoint α₀ 0 u₀)) else none

/-- Predictable betting fractions at a level `α(u, x, y)` that may depend on batch 0: as `Wave30tv.IsBatchBetRule`, with the cap
`c/(1 + α(u, x, y))`. -/
def IsBatchBetRuleU {𝒳 U : Type*} [MeasurableSpace 𝒳] [MeasurableSpace U] {n m N : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (bat : Fin N → ℕ) (α : U → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (c : ℝ)
    (lam : (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) : Prop :=
  ∀ k : Fin N,
    Measurable (fun p : (U × ((Fin n → 𝒳) × (Fin m → 𝒳))) × (Fin k → ℝ) => lam k p.1.1 p.1.2.1 p.1.2.2 p.2) ∧
    (∀ u x y z, 0 ≤ lam k u x y z ∧ lam k u x y z ≤ c / (1 + α u x y)) ∧
    (∀ u x x' y y', (∀ i, lx i < bat k → x i = x' i) → (∀ j, ly j < bat k → y j = y' j) →
      lam k u x y = lam k u x' y')

/-- A grid chosen from batch 0: each level `α_j(u, x, y) ≥ 0` is jointly measurable and depends on the sample only through
batch 0 (`lx i = 0`, `ly j = 0`). -/
def Batch0Grid {𝒳 U : Type*} [MeasurableSpace 𝒳] [MeasurableSpace U] {n m J : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (α : Fin J → U → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) : Prop :=
  ∀ j, Measurable (fun ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) => α j ω.1 ω.2.1 ω.2.2) ∧ (∀ u x y, 0 ≤ α j u x y) ∧
    ∀ u x x' y y', (∀ i, lx i = 0 → x i = x' i) → (∀ i, ly i = 0 → y i = y' i) → α j u x y = α j u x' y'

namespace Claims

/-! ### Algorithm 1 -/

/-- Algorithm 1, deterministic guarantee (every realization; `τ ≥ 0` nondecreasing on `[0,1)` and continuous on `(0,1)`, the
hypotheses of `lem:crossing`; any accepted `u₀ ∈ (0,1)`, any `α₀`, `ε`, `J`): the algorithm returns `none` exactly when `0` is not
rejected, and then `α̂ = 0`; otherwise its output `(ℓ, u, t)` has `ℓ` rejected, `u` accepted, `0 ≤ ℓ < u ≤ u₀`, `ℓ ≤ α̂ ≤ u` with
`ℓ < α̂` when `ℓ > 0`, at most `J` tests, and, if fewer than `J` tests were made, `u − ℓ ≤ ε`, so `α̂ − ℓ ≤ ε`. -/
def alg_bracket : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → ContinuousOn τ (Ioo 0 1) →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (α₀ u₀ ε : ℝ) (J : ℕ),
        u₀ ∈ Ioo (0 : ℝ) 1 → ¬ rejected (Demp φ x y) τ u₀ →
          (bisectAlg (rejected (Demp φ x y) τ) α₀ u₀ ε J = none ↔ ¬ rejected (Demp φ x y) τ 0) ∧
          (¬ rejected (Demp φ x y) τ 0 → alphaHat (Demp φ x y) τ = 0) ∧
          ∀ p : ℝ × ℝ × ℕ, bisectAlg (rejected (Demp φ x y) τ) α₀ u₀ ε J = some p →
            rejected (Demp φ x y) τ p.1 ∧ ¬ rejected (Demp φ x y) τ p.2.1 ∧
            0 ≤ p.1 ∧ p.1 < p.2.1 ∧ p.2.1 ≤ u₀ ∧
            p.1 ≤ alphaHat (Demp φ x y) τ ∧ alphaHat (Demp φ x y) τ ≤ p.2.1 ∧
            (0 < p.1 → p.1 < alphaHat (Demp φ x y) τ) ∧
            p.2.2 ≤ J ∧ (p.2.2 < J → p.2.1 - p.1 ≤ ε ∧ alphaHat (Demp φ x y) τ - p.1 ≤ ε)

/-- The loop from any bracket (the bisection of Table 3 "between `α_last` and the first accepted grid level"; the sentence before
Algorithm 1, "it brackets `α̂` at every step"): from a rejected `ℓ₀ ≥ 0`, an accepted `u₀ ∈ (ℓ₀, 1)` and a first test point in
`(ℓ₀, u₀)`, the output `(ℓ, u, t)` has `ℓ` rejected, `u` accepted, `ℓ₀ ≤ ℓ < u ≤ u₀`, `ℓ ≤ α̂ ≤ u` with `ℓ < α̂` when `ℓ > 0`,
`t ≤ J`, and `u − ℓ ≤ ε` if `t < J`. -/
def alg_loop : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → ContinuousOn τ (Ioo 0 1) →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (l₀ u₀ a₀ ε : ℝ) (J : ℕ),
        0 ≤ l₀ → l₀ < u₀ → u₀ < 1 → rejected (Demp φ x y) τ l₀ → ¬ rejected (Demp φ x y) τ u₀ → a₀ ∈ Ioo l₀ u₀ →
          rejected (Demp φ x y) τ (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).1 ∧
          ¬ rejected (Demp φ x y) τ (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).2.1 ∧
          l₀ ≤ (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).1 ∧
          (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).1 < (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).2.1 ∧
          (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).2.1 ≤ u₀ ∧
          (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).1 ≤ alphaHat (Demp φ x y) τ ∧
          alphaHat (Demp φ x y) τ ≤ (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).2.1 ∧
          (0 < (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).1 →
            (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).1 < alphaHat (Demp φ x y) τ) ∧
          (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).2.2 ≤ J ∧
          ((bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).2.2 < J →
            (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).2.1 -
              (bisectLoop (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀).1 ≤ ε)

/-- The cost (`03_analytic.tex:140-143`, "Each step tests the midpoint … and halves the interval, so a tolerance `ε` costs about
`log₂(1/ε)` convex solves, seven for `ε = 0.01`"): with the default start `α₀ = ½` and `u₀ ≤ 1`, for every rule of rejection, the
output `(ℓ, u, t)` of Algorithm 1 has `u − ℓ ≤ 2^{−t}`, and `t ≤ k` for every `k` with `2^{−k} ≤ ε`; in particular `t ≤ 7` when
`ε = 0.01`. -/
def alg_cost : Prop :=
  ∀ (rej : ℝ → Prop) (u₀ ε : ℝ) (J : ℕ) (p : ℝ × ℝ × ℕ), 0 < u₀ → u₀ ≤ 1 → 0 < ε →
    bisectAlg rej (1 / 2) u₀ ε J = some p →
      p.2.1 - p.1 ≤ (1 / 2 : ℝ) ^ p.2.2 ∧ (∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ ε → p.2.2 ≤ k) ∧
      (ε = 1 / 100 → p.2.2 ≤ 7)

/-- The upper end of the bracket (`B_analytic.tex:269`, "`u ←` the smallest `α` with `τ(α) ≥ Δ_φ`, accepted, as `D̂_α ≤ Δ_φ`"): for
any `D ≥ ‖φ x − φ x′‖` (`Δ_φ`), every `α ∈ [0,1)` with `τ(α) ≥ D` is accepted; if `τ → ∞` as `α → 1`, such levels exist in `(0,1)`;
and if moreover `τ(0+) < D` (`tauRight τ 0`) and `τ` is nondecreasing on `[0,1)` and continuous on `(0,1)`, the smallest one exists
and is positive. -/
def alg_start : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 1 ≤ n → 1 ≤ m →
      (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), ∀ α ∈ Ico (0 : ℝ) 1, D ≤ τ α → ¬ rejected (Demp φ x y) τ α) ∧
      (Tendsto τ (𝓝[<] 1) atTop → ∃ α ∈ Ioo (0 : ℝ) 1, D ≤ τ α) ∧
      (Tendsto τ (𝓝[<] 1) atTop → (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → ContinuousOn τ (Ioo 0 1) →
        tauRight τ 0 < D → ∃ u, 0 < u ∧ IsLeast {α | α ∈ Ico (0 : ℝ) 1 ∧ D ≤ τ α} u)

/-- The probability guarantee (`03_analytic.tex:145-147`, Algorithm 1's last line, `07_data.tex:36-38`): for a valid threshold at level
`δ` (the hypothesis of `lem:oneevent`) and `α⋆ = TV(P,Q) < 1`, one measurable event of probability `≥ 1 − δ` on which every rejected
level in `[0,1)` is below `α⋆`, the output `ℓ` of Algorithm 1 is below `α⋆` for every `α₀`, accepted `u₀ ∈ (0,1)`, `ε` and `J`, and
the output `ℓ` of the loop is below `α⋆` for every rejected start `ℓ₀ ∈ [0,1)`, `u₀ < 1` and first test in `(ℓ₀, u₀)` — however these
were chosen. -/
def alg_event : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → StatFormal.Distances.tvDist P Q < 1 →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | (∀ α ∈ Ico (0 : ℝ) 1, rejected (Demp φ z.1 z.2) τ α → α < StatFormal.Distances.tvDist P Q) ∧
              (∀ (α₀ u₀ ε : ℝ) (J : ℕ) (p : ℝ × ℝ × ℕ), u₀ ∈ Ioo (0 : ℝ) 1 →
                bisectAlg (rejected (Demp φ z.1 z.2) τ) α₀ u₀ ε J = some p → p.1 < StatFormal.Distances.tvDist P Q) ∧
              (∀ (l₀ u₀ a₀ ε : ℝ) (J : ℕ), 0 ≤ l₀ → u₀ < 1 → rejected (Demp φ z.1 z.2) τ l₀ → a₀ ∈ Ioo l₀ u₀ →
                (bisectLoop (rejected (Demp φ z.1 z.2) τ) ε J l₀ u₀ a₀).1 < StatFormal.Distances.tvDist P Q)}

/-! ### `rem:batch0grid` (Remark 30) -/

/-- `rem:batch0grid`, conditional form ("Given batch 0 the grid is fixed, … `P(H_{0,α_{i₀}}` rejected `| batch 0) ≤ δ`"): for every
value `(u, x₀, y₀)` of batch 0, with the other batches drawn from `P^{⊗n} ⊗ Q^{⊗m}`, `P(α̂_lo > TV(P,Q)) ≤ δ`. -/
def batch0grid_cond : Prop :=
  ∀ (𝒳 U : Type) [MeasurableSpace 𝒳] [MeasurableSpace U] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (n m N J : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α : Fin J → U → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (δ c : ℝ)
    (g : Fin J → ℕ → U → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : Fin J → (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    IsBatchPairing lx ly bat A B → 0 < δ → δ < 1 → 0 < c → c ≤ 1 → Batch0Grid lx ly α →
    (∀ j, IsBatchRule lx ly bat (g j)) → (∀ j, IsBatchBetRuleU lx ly bat (α j) c (lam j)) →
      ∀ (u : U) (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳),
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
          {ω | StatFormal.Distances.tvDist P Q < StatFormal.TrimmedMMD.Lower.alphaLo
              (fun j => α j u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2))
              (fun j => seqReject (lam j) (g j) bat A B (α j u (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)) δ u
                (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2))}
            ≤ ENNReal.ofReal δ

/-- `rem:batch0grid` ("`cor:lower` holds, with the same proof, when the grid is a measurable function of batch 0"; "integrating over
batch 0 gives the claim"): under `ν ⊗ P^{⊗n} ⊗ Q^{⊗m}`, with a grid chosen from batch 0, `P(α̂_lo > TV(P,Q)) ≤ δ` for all sample sizes
and every pair `(P,Q)`. -/
def batch0grid : Prop :=
  ∀ (𝒳 U : Type) [MeasurableSpace 𝒳] [MeasurableSpace U] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ν : Measure U) [IsProbabilityMeasure ν]
    (n m N J : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α : Fin J → U → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (δ c : ℝ)
    (g : Fin J → ℕ → U → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : Fin J → (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    IsBatchPairing lx ly bat A B → 0 < δ → δ < 1 → 0 < c → c ≤ 1 → Batch0Grid lx ly α →
    (∀ j, IsBatchRule lx ly bat (g j)) → (∀ j, IsBatchBetRuleU lx ly bat (α j) c (lam j)) →
      (ν.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
        {ω | StatFormal.Distances.tvDist P Q < StatFormal.TrimmedMMD.Lower.alphaLo (fun j => α j ω.1 ω.2.1 ω.2.2)
            (fun j => seqReject (lam j) (g j) bat A B (α j ω.1 ω.2.1 ω.2.2) δ ω.1 ω.2.1 ω.2.2)}
          ≤ ENNReal.ofReal δ

end Claims

end StatFormal.Wave31tj
