import StatFormal.Wave30tz.Statements
import StatFormal.Wave31ti.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tl: trimmed-mmd (jmlr) **v3 of 2026-11-19**: `thm:lorate` (rate of the split-sample lower bound `α̂_lo` under the margin condition) and the prose that rides on it

Printed source: `trimmed-mmd/jmlr/v3/` at trimmed-mmd commit `5e51f65` ("JMLR v3: split-sample rate and trimming corollary …"; read-only,
read 2026-11-19 from `git show 5e51f65:…`). sha256 of the files read:
`appendix/C_split.tex` `04089c47637336218a115c1c660829cbdfe3a8b26d47fa4af171846ffd7feda1`,
`sections/04_split.tex` `790e687bc511c0c918b821ce8f24e56e6f916f1e9f8fb0516c6baaaa24ea153e`,
`sections/03_analytic.tex` `f47ebecd68ce035e3b59bf1d50189a89bdd60587498eef7b22bb04f6fce9e220`,
`sections/02_regions.tex` `8c3985ee6342637cdae3398107f390f70dace632577b9c1176a800ab5ea11461` (context: `ass:regularity`,
`α⋆ := TV(P,Q)`, `κ`, `Δ_φ = sup‖φ(x) − φ(x′)‖ ≤ 2κ`),
`appendix/B_analytic.tex` `012c79c858499552dddb0649afca4752bce816a1f0e76b2fa34aa5349fcca8da` (context: Proposition 26 `prop:rategeneral`,
`:407-416`, the general margin `ω` used by `lorate_general`).
Printed numbers (`main.aux` of the build of 2026-11-19 18:48): Theorem 33 `thm:lorate` (Appendix C.6 `sec:lorate`), display (28)
`eq:loconst`, Proposition 12 `prop:loconsistency`, Corollary 11 `cor:lower`, Theorem 8 `thm:rate`, Assumption 2 `ass:margin`,
Proposition 26 `prop:rategeneral`, Section 4.2 `sec:betting` (the batches), Section 4.3 `sec:lower`.

* `thm:lorate` (Theorem 33, "Rate of the lower bound under the margin condition", `C_split.tex:303-340`, proof `:350-460`): "Let
  Assumptions 1 and 2 hold with `α⋆ < 1`, and compute `α̂_lo` as in Proposition 12: on a grid `α_1 < ⋯ < α_J` fixed in advance, with a
  witness fitted at each level by a minimizer of (qp) on the batches before the one bet on, cut points satisfying (cutrank), and the
  fractions (fractions) with `λ_max = ½`, `σ₀² ≤ 4` and the running variance floored at a constant `σ²_min ∈ (0,4]`. Let `B` be the number
  of batches bet on, `N` the number of pairs and `r₁ = 1/n_{<1} + 1/m_{<1}`, where `n_{<1}, m_{<1}` are the sizes of batch 0, and suppose
  `r₁ ≤ 1`. Put `β⋆ = (1−α⋆)⁻¹`, `L_δ = log(1/δ)` and, for `η ∈ (0,1)` and `J′ ≥ 1`,
  `T_fit(η) = 8[2(1+√2)κ + Δ_φ √(½ log(4B/η))]√r₁`,
  `T_bet(η,J′) = 2Δ_φ √(2/N) [(1 + 16/σ²_min)√L_δ + (2/σ_min)√(log(2J′/η))]` (28).
  For `ε ∈ (0,α⋆]` let `a_ε = max({0} ∪ {α_j : α_j ≤ α⋆ − ε})`, let `h₀` be the smallest gap between consecutive grid levels (`h₀ = ∞` if
  `J = 1`), and let `J_ε = min{J, 2(1+ε/h₀)}`. (i) If `c₀ε^γ ≥ β⋆ max{T_fit(η), T_bet(η,J_ε)}`, then `P(α̂_lo < a_ε) ≤ η`.
  (ii) Let `t_{n,m} = β⋆ max{T_fit(η), T_bet(η,J)}` and let `h = sup_{a∈[0,α⋆]}(a − max{g ∈ {0,α_1,…,α_J} : g ≤ a})` be the mesh of the
  grid below `α⋆`. Then, with probability at least `1−δ−η`, `α⋆ − h − (t_{n,m}/c₀)^{1/γ} ≤ α̂_lo ≤ α⋆`. (iii) With the batches of
  Section 4.2, their boundaries rounded to the nearest integers, and `n∧m ≥ 10`, one has `r₁ ≤ min{1, 12/(n∧m)}` and `N ≥ (n∧m)/2`, so
  that, with an absolute constant in the `O`, `(t_{n,m}/c₀)^{1/γ} = O((κ/(c₀(1−α⋆)σ²_min) √((1+log(1/δ)+log(J/η))/(n∧m)))^{1/γ})`."
* The paragraph after it (`C_split.tex:342-348`): "… part (i) removes [the factor `log J`] when the grid is not finer than the rate: if
  `h₀ ≥ ε′_{n,m} = (β⋆ max{T_fit(η), T_bet(η,4)}/c₀)^{1/γ}`, then `J_{ε′_{n,m}} ≤ 4`, and with probability at least `1−δ−η`,
  `α⋆ − h − ε′_{n,m} ≤ α̂_lo ≤ α⋆`, with no `log J`." (`lorate_nologJ`)
* The paragraph after the proof (`C_split.tex:462-464`): "With a general margin `D_{α⋆−ε} ≥ ω(ε)` as in Proposition 26, part (ii) holds
  with `ω^{-1}(t_{n,m})` in place of `(t_{n,m}/c₀)^{1/γ}` when `t_{n,m} ≤ ω(α⋆)`" (`lorate_general`).
* The display after Proposition 12 (`04_split.tex:181-192`): "Under the margin condition … the lower bound converges at the rate of
  Theorem 8: for every `η ∈ (0,1)`, with probability at least `1−δ−η`,
  `α⋆ − h − O((κ/(c₀(1−α⋆)σ²_min) √((1+log(1/δ)+log(J/η))/(n∧m)))^{1/γ}) ≤ α̂_lo ≤ α⋆`, where `h` is the mesh of the grid below `α⋆` and
  `J` the number of its levels" (`lorate_O`).
* The sentence after Theorem 8 (`03_analytic.tex:256-257`): "The split-sample bound of Section 4 has the same rate (Section 4.3)"
  (`same_rate`: the exponent `(n∧m)^{-1/(2γ)}` of Theorem 8, with a constant free of `n, m`, the grid values and the run, up to the mesh).
  The same reading covers "The exponent is that of Theorem 8, `(n∧m)^{-1/(2γ)}`" (`C_split.tex:342`) and "The exponent is that of `α̂`"
  (`04_split.tex:191`).

Reuses (imported, not copied): `Wave30tz` (`LoRun`, `LoRun.IsWitnessRun` — per-level exact QP minimizers, cut points in (cutrank), the
fractions (fractions) through their bounds `lamLo ≤ λ_k ≤ lamHi`, admissibility —, `LoRun.alphaLo` = `eq:downclosed`, `IsGrid`, `fitCard`),
`Wave31ti.PolyMargin` (`ass:margin`), `Wave30tu.Margin` (the general margin of Proposition 26), `Wave30tq.beta`, `Wave30tp.sampleLaw`,
`TrimmedMMD.Unconditional.Dpop`, `Distances.tvDist`.

Encodings:
* (A1)–(A2) as in every trimmed-mmd wave: `H` a real complete separable inner-product space, `φ : 𝒳 → H` strongly measurable with
  `‖φ x‖ ≤ κ`; `Δ_φ` is any `Dφ` with `‖φ x − φ x′‖ ≤ Dφ ≤ 2κ` (the printed `Δ_φ`, the least such bound, is one; the constants increase
  with `κ` and `Dφ`, so this is a generalisation). (A3) is not assumed (the printed paragraph after the theorem: "it does not use (A3)";
  `α⋆ = TV(P,Q)` is `tvDist P Q`). `ass:margin` is `PolyMargin φ P Q c₀ γ` (`c₀ > 0`, `γ ≥ 1`).
* "computed as in Proposition 12 … with `λ_max = ½`, `σ₀² ≤ 4`, floor `σ²_min ∈ (0,4]`": `R.IsWitnessRun φ α δ (1/2) s2` with
  `0 < s2 ≤ 4` (the certified `Wave30tz.fractions_bounds` shows that the printed fractions satisfy its bounds); the grid is `IsGrid α`
  (`0 ≤ α_1 < ⋯ < α_J < 1`), `J ≥ 1`.
* `B` (batches bet on): every pair lies in a batch `≤ B` (pairs never lie in batch 0, `IsBatchPairing`); `N = R.N`. `r₁` is `rOne`, with
  batch 0 nonempty on both sides (`fitCard … 1 ≥ 1`; the printed `r₁` is finite); `N ≥ 1` (the printed `T_bet` has `2/N`).
* `σ_min = √σ²_min`; `L_δ = log(1/δ)`, `δ ∈ (0,1)`; `η ∈ (0,1)`.
* `h₀`: any `h0 > 0` bounding the gaps between consecutive levels from below (`GapsGe`); the printed `h₀` is one when `J ≥ 2`, and when
  `J = 1` every `h0 > 0` gives `J_ε = 1 = J`, as `h₀ = ∞` does. `J_ε` is `Jeps J ε h0` (decreasing in `h0`, so this is a generalisation).
* `a_ε` is `gridFloor α (α⋆ − ε)`; the mesh `h` below `α⋆` enters through any upper bound `h` of `a − gridFloor α a` on `[0,α⋆]`
  (`MeshBelowLe`; the printed supremum is the least one, and the bounds are monotone in `h`).
* "with probability at least `1−δ−η`": a measurable event of that probability inside the claimed set.
* (iii) "the batches of Section 4.2, their boundaries rounded to the nearest integers": batch 0 = indices `< b₁`, batch 1 = `[b₁, b₂)`,
  batch 2 = `≥ b₂` with `|b₁ − n/4| ≤ ½`, `|b₂ − n/2| ≤ ½` (any tie-breaking), likewise for `m` (`defaultLabel`, `NearestCuts`); `N` is
  the printed number of pairs `min(n_[1], m_[1]) + min(n_[2], m_[2])` (`defaultPairs`; `IsDefaultRun` for a run). The `O(·)` is an explicit
  bound with the absolute constant 1000 (inside the power, as for Theorem 8 in Wave 31ti; `(1000X)^{1/γ} ≤ 1000X^{1/γ}`), together with the
  printed proof's `t_{n,m} ≤ C β⋆κσ_min^{-2}√((1+L_δ+log(J/η))/(n∧m))`. The order of the observations: Section 4.2 puts each sample in a
  random order drawn once; the index order used here is an order fixed in advance (`C_split.tex:94`), equivalent in law for i.i.d. data.
* `lorate_O`, `same_rate`: the size condition `n∧m ≥ 10` of (iii) is dropped (generalisation; the display after Proposition 12 states
  none): for `n∧m ≤ 9` the bound term is at least `α⋆`, because `c₀(α⋆)^γ ≤ D₀ ≤ 2κ` while its base is at least `1000κ/(12c₀)`, so the
  lower inequality holds trivially there; only `n, m ≥ 1` is assumed (junk values below).
* `same_rate`: "the same rate" as Theorem 8 (`(n∧m)^{-1/(2γ)}`) is read as: for fixed laws, kernel bound, margin constants, `δ`, `η`, `σ²_min`
  and `J`, a constant `C` such that for all `n, m ≥ 1`, every grid with `J` levels and every run with the default batches, with probability
  `≥ 1−δ−η`, `α⋆ − h − C(n∧m)^{-1/(2γ)} ≤ α̂_lo ≤ α⋆`.
* Junk values: `Real.log (4B/η)` with `B ≥ 1` (every pair lies in a batch `1 ≤ bat k ≤ B`, `N ≥ 1`) and `η ∈ (0,1)`; `log(2J′/η)` with
  `J′ ≥ 1` (`J ≥ 1`, so `J_ε ≥ 1`); `√(2/N)` with `N ≥ 1`; `1/n_{<1}`, `1/m_{<1}` with nonempty batch 0; `16/s2`, `2/√s2` with `s2 > 0`;
  `(t/c₀)^{1/γ}` with `c₀ > 0`, `γ ≥ 1`, `t ≥ 0`; `ε/h0` with `h0 > 0`; `(n∧m)^{-1/(2γ)}` and `√(·/(n∧m))` with `n, m ≥ 1` (at `n∧m = 0` Lean's
  `0^{-a} = 0` and `x/0 = 0` would make the bound false, so `1 ≤ n`, `1 ≤ m` are assumed); `beta α⋆` with `α⋆ < 1`; `Dpop` only at levels
  in `[0,1)`; `gridFloor` is a `max` over a finite set with `0` adjoined.

Not covered (declared): "A feasible point of (qp) with relative Frank–Wolfe gap at most `ρ < 1` serves in place of a minimizer, with
`(1−ρ/2)c₀`" (`C_split.tex:464-467`; the frozen witness rule of Wave 30tz takes exact minimizers); "the kernel is fixed in advance … a
bandwidth computed from batch 0 is not covered" (a scope remark); "The proof needs no density of the witness at the cut points … and it
does not use (A3)" (meta; consistent with the claims, which assume neither); "the constants, which treat the fractions in the worst case,
are far from sharp" (informal); the comparison of the factors (`h`, `1/σ²_min`, `log J`) in prose beyond what the claims state.
FROZEN 2026-11-19 before any proof, after an independent critic's pre-freeze review (9 claims of waves 31tl and 31tm: 6 ACCEPT,
3 ACCEPT-WITH-NOTE; none false, no undeclared conditionalisation; every printed step of the proofs of Theorem 33 and Corollary 17
re-derived, no wrong step; hashes, `main.aux` numbers and line ranges checked; verdict READY TO FREEZE after R1). Applied: R1 the
batches are those of Section 4.2 (was "4.1", eight places), R2 the hashes of `02_regions.tex` and `B_analytic.tex` and the number of
Proposition 26, R3 the dropped size condition of `lorate_O`/`same_rate` declared, R5 the order of the observations; the two "exponent"
sentences listed under `same_rate`. No Lean term changed.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tl

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.TrimmedMMD.Unconditional

/-! ### The constants of `eq:loconst` and the grid quantities -/

/-- `T_fit(η) = 8[2(1+√2)κ + Δ_φ √(½ log(4B/η))] √r₁` (`eq:loconst`). -/
def Tfit (κ Dφ η r1 : ℝ) (B : ℕ) : ℝ :=
  8 * (2 * (1 + √2) * κ + Dφ * √(1 / 2 * Real.log (4 * B / η))) * √r1

/-- `T_bet(η, J′) = 2Δ_φ √(2/N) [(1 + 16/σ²_min)√L_δ + (2/σ_min)√(log(2J′/η))]` (`eq:loconst`), `σ_min = √σ²_min`, `L = L_δ`. -/
def Tbet (Dφ s2 L η J' : ℝ) (N : ℕ) : ℝ :=
  2 * Dφ * √(2 / N) * ((1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)))

open Classical in
/-- `max({0} ∪ {α_j : α_j ≤ x})`, the largest point of `{0, α_1, …, α_J}` at most `x` when `x ≥ 0` (so `a_ε = gridFloor α (α⋆ − ε)`). -/
def gridFloor {J : ℕ} (α : Fin J → ℝ) (x : ℝ) : ℝ :=
  if h : (Finset.univ.filter fun j => α j ≤ x).Nonempty then max 0 ((Finset.univ.filter fun j => α j ≤ x).sup' h α) else 0

/-- `J_ε = min{J, 2(1 + ε/h₀)}`. -/
def Jeps (J : ℕ) (ε h0 : ℝ) : ℝ := min (J : ℝ) (2 * (1 + ε / h0))

/-- `h0` bounds the gaps between consecutive grid levels from below: `α_j + h0 ≤ α_{j+1}`. -/
def GapsGe {J : ℕ} (α : Fin J → ℝ) (h0 : ℝ) : Prop :=
  ∀ (j : Fin J) (hj : j.1 + 1 < J), α j + h0 ≤ α ⟨j.1 + 1, hj⟩

/-- `h` bounds the mesh of the grid below `a⋆`: `a − max{g ∈ {0, α_1, …, α_J} : g ≤ a} ≤ h` for every `a ∈ [0, a⋆]`. -/
def MeshBelowLe {J : ℕ} (α : Fin J → ℝ) (aStar h : ℝ) : Prop :=
  ∀ a ∈ Icc (0 : ℝ) aStar, a - gridFloor α a ≤ h

/-- `r₁ = 1/n_{<1} + 1/m_{<1}`, `n_{<1}, m_{<1}` the sizes of batch 0. -/
def rOne {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) : ℝ := 1 / (fitCard lx 1 : ℝ) + 1 / (fitCard ly 1 : ℝ)

/-- `t_{n,m} = β⋆ max{T_fit(η), T_bet(η, J)}`, `β⋆ = (1 − α⋆)⁻¹`, `L_δ = log(1/δ)`. -/
def tNM (κ Dφ αs s2 δ η r1 : ℝ) (B J N : ℕ) : ℝ :=
  beta αs * max (Tfit κ Dφ η r1 B) (Tbet Dφ s2 (Real.log (1 / δ)) η J N)

/-! ### The batches of Section 4.2 -/

/-- The batch of index `i` when the boundaries are `b₁ ≤ b₂`: batch 0 = `i < b₁`, batch 1 = `b₁ ≤ i < b₂`, batch 2 = `i ≥ b₂`. -/
def defaultLabel (b1 b2 i : ℕ) : ℕ := if i < b1 then 0 else if i < b2 then 1 else 2

/-- The boundaries are the nearest integers to `n/4` and `n/2` (any tie-breaking). -/
def NearestCuts (n b1 b2 : ℕ) : Prop := |(b1 : ℝ) - n / 4| ≤ 1 / 2 ∧ |(b2 : ℝ) - n / 2| ≤ 1 / 2

open Classical in
/-- The size `n_[b]` of batch `b`. -/
def batchCount {p : ℕ} (l : Fin p → ℕ) (b : ℕ) : ℕ := (Finset.univ.filter fun i => l i = b).card

/-- The number of pairs of the default batches, `N = min(n_[1], m_[1]) + min(n_[2], m_[2])`. -/
def defaultPairs {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) : ℕ :=
  min (batchCount lx 1) (batchCount ly 1) + min (batchCount lx 2) (batchCount ly 2)

/-- A run with the batches of Section 4.2 (boundaries rounded to the nearest integers) and `N` the printed number of pairs. -/
def IsDefaultRun {𝒳 : Type*} {J n m : ℕ} (R : LoRun 𝒳 J n m) : Prop :=
  ∃ bn1 bn2 bm1 bm2 : ℕ, NearestCuts n bn1 bn2 ∧ NearestCuts m bm1 bm2 ∧
    (∀ i : Fin n, R.lx i = defaultLabel bn1 bn2 i) ∧ (∀ j : Fin m, R.ly j = defaultLabel bm1 bm2 j) ∧
    R.N = defaultPairs R.lx R.ly

namespace Claims

/-- **`thm:lorate` (i)** (Theorem 33): under (A1)–(A2), `Δ_φ ≤ 2κ`, Assumption 2 (`PolyMargin`, `c₀ > 0`, `γ ≥ 1`) with `α⋆ = TV(P,Q) < 1`,
a run of Proposition 12 on a grid of `J ≥ 1` levels with `λ_max = ½` and floor `σ²_min ∈ (0,4]`, pairs in batches `≤ B`, batch 0 nonempty
with `r₁ ≤ 1`, `N ≥ 1`, `η ∈ (0,1)`, `h₀ > 0` below every consecutive gap, and `ε ∈ (0,α⋆]`: if
`β⋆ max{T_fit(η), T_bet(η,J_ε)} ≤ c₀ε^γ`, then `P(α̂_lo < a_ε) ≤ η`. -/
def lorate_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h0 ε : ℝ) (R : LoRun 𝒳 J n m) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ (1 / 2) s2 →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → 0 < h0 → GapsGe α h0 → 0 < ε → ε ≤ StatFormal.Distances.tvDist P Q →
    beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N) ≤ c₀ * ε ^ γ →
      sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < gridFloor α (StatFormal.Distances.tvDist P Q - ε)} ≤
        ENNReal.ofReal η

/-- **`thm:lorate` (ii)** (Theorem 33): under the hypotheses of (i) without `ε` and `h₀`, for every upper bound `h` of the mesh of the grid
below `α⋆`, on a measurable event of probability `≥ 1 − δ − η`, `α⋆ − h − (t_{n,m}/c₀)^{1/γ} ≤ α̂_lo ≤ α⋆`,
`t_{n,m} = β⋆ max{T_fit(η), T_bet(η,J)}`. -/
def lorate_ii : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun 𝒳 J n m) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ (1 / 2) s2 →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {ω | StatFormal.Distances.tvDist P Q - h -
              (tNM κ Dφ (StatFormal.Distances.tvDist P Q) s2 δ η (rOne R.lx R.ly) B J R.N / c₀) ^ (1 / γ) ≤
                R.alphaLo α δ ω.1 ω.2 ∧
            R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- **`thm:lorate` (iii)**, first half: with the batches of Section 4.2 (boundaries at nearest integers to `n/4`, `n/2` and `m/4`, `m/2`)
and `n∧m ≥ 10`: batch 0 is nonempty on both sides, `r₁ ≤ min{1, 12/(n∧m)}` and `N = min(n_[1],m_[1]) + min(n_[2],m_[2]) ≥ (n∧m)/2`. -/
def lorate_batches : Prop :=
  ∀ (n m bn1 bn2 bm1 bm2 : ℕ), 10 ≤ min n m → NearestCuts n bn1 bn2 → NearestCuts m bm1 bm2 →
    1 ≤ fitCard (fun i : Fin n => defaultLabel bn1 bn2 i) 1 ∧ 1 ≤ fitCard (fun j : Fin m => defaultLabel bm1 bm2 j) 1 ∧
    rOne (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j) ≤
      min 1 (12 / ((min n m : ℕ) : ℝ)) ∧
    ((min n m : ℕ) : ℝ) / 2 ≤ (defaultPairs (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j) : ℝ)

/-- **`thm:lorate` (iii)**, the `O(·)`: for `0 ≤ Δ_φ ≤ 2κ`, `c₀ > 0`, `γ ≥ 1`, `α⋆ ∈ [0,1)`, `σ²_min ∈ (0,4]`, `δ, η ∈ (0,1)`, `J ≥ 1`,
the batches of Section 4.2 (so `B = 2`) and `n∧m ≥ 10`, with `L_δ = log(1/δ)`:
`t_{n,m} ≤ 1000 β⋆κσ_min^{-2} √((1 + L_δ + log(J/η))/(n∧m))` and
`(t_{n,m}/c₀)^{1/γ} ≤ (1000 κ/(c₀(1−α⋆)σ²_min) · √((1 + L_δ + log(J/η))/(n∧m)))^{1/γ}`. -/
def lorate_iii : Prop :=
  ∀ (κ Dφ c₀ γ αs s2 δ η : ℝ) (J n m bn1 bn2 bm1 bm2 : ℕ),
    0 ≤ Dφ → Dφ ≤ 2 * κ → 0 < c₀ → 1 ≤ γ → 0 ≤ αs → αs < 1 → 0 < s2 → s2 ≤ 4 → 0 < δ → δ < 1 → 0 < η → η < 1 →
    1 ≤ J → 10 ≤ min n m → NearestCuts n bn1 bn2 → NearestCuts m bm1 bm2 →
      tNM κ Dφ αs s2 δ η (rOne (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j)) 2 J
          (defaultPairs (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j)) ≤
        1000 * beta αs * κ / s2 * √((1 + Real.log (1 / δ) + Real.log (J / η)) / ((min n m : ℕ) : ℝ)) ∧
      (tNM κ Dφ αs s2 δ η (rOne (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j)) 2 J
          (defaultPairs (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j)) / c₀) ^ (1 / γ) ≤
        (1000 * κ / (c₀ * (1 - αs) * s2) *
          √((1 + Real.log (1 / δ) + Real.log (J / η)) / ((min n m : ℕ) : ℝ))) ^ (1 / γ)

/-- **The display after `prop:loconsistency`** (`04_split.tex:181-192`; Theorem 33 (ii)+(iii)): under (A1)–(A2), Assumption 2 with
`α⋆ < 1`, a run of Proposition 12 with the batches of Section 4.2 (`λ_max = ½`, floor `σ²_min ∈ (0,4]`) on a grid of `J ≥ 1` levels,
`n, m ≥ 1`, `η ∈ (0,1)` and any upper bound `h` of the mesh below `α⋆`: on a measurable event of probability `≥ 1 − δ − η`,
`α⋆ − h − (1000 κ/(c₀(1−α⋆)σ²_min) · √((1 + log(1/δ) + log(J/η))/(n∧m)))^{1/γ} ≤ α̂_lo ≤ α⋆` (the `O(·)` with the constant 1000). -/
def lorate_O : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ (1 / 2) s2 → IsDefaultRun R →
    1 ≤ n → 1 ≤ m → 0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {ω | StatFormal.Distances.tvDist P Q - h -
              (1000 * κ / (c₀ * (1 - StatFormal.Distances.tvDist P Q) * s2) *
                √((1 + Real.log (1 / δ) + Real.log (J / η)) / ((min n m : ℕ) : ℝ))) ^ (1 / γ) ≤
                R.alphaLo α δ ω.1 ω.2 ∧
            R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- **The sentence after `thm:rate`** (`03_analytic.tex:256-257`, "The split-sample bound of Section 4 has the same rate"): for fixed laws,
`κ`, margin constants (Assumption 2, `α⋆ < 1`), `δ, η ∈ (0,1)`, `σ²_min ∈ (0,4]` and `J ≥ 1` there is a constant `C ≥ 0` such that for all
`n, m ≥ 1`, every grid of `J` levels, every run of Proposition 12 with the batches of Section 4.2 (`λ_max = ½`, floor `σ²_min`) and every
upper bound `h` of the mesh below `α⋆`: with probability `≥ 1 − δ − η`, `α⋆ − h − C (n∧m)^{-1/(2γ)} ≤ α̂_lo ≤ α⋆` (Theorem 8's rate
`(n∧m)^{-1/(2γ)}`, up to the mesh). -/
def same_rate : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J : ℕ) (δ s2 η : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ) (α : Fin J → ℝ) (R : LoRun 𝒳 J n m) (h : ℝ),
        IsGrid α → R.IsWitnessRun φ α δ (1 / 2) s2 → IsDefaultRun R → 1 ≤ n → 1 ≤ m →
        MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
            E ⊆ {ω | StatFormal.Distances.tvDist P Q - h - C * ((min n m : ℕ) : ℝ) ^ (-(1 / (2 * γ))) ≤
                    R.alphaLo α δ ω.1 ω.2 ∧
                R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- **The paragraph after `thm:lorate`** (`C_split.tex:342-346`, no `log J` when the grid is not finer than the rate): under the hypotheses
of (i) without `ε`, with `ε′ = (β⋆ max{T_fit(η), T_bet(η,4)}/c₀)^{1/γ}` and any upper bound `h` of the mesh below `α⋆`: if `ε′ ≤ h₀`, then
`J_{ε′} ≤ 4`, and on a measurable event of probability `≥ 1 − δ − η`, `α⋆ − h − ε′ ≤ α̂_lo ≤ α⋆`. -/
def lorate_nologJ : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h0 h : ℝ) (R : LoRun 𝒳 J n m) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ (1 / 2) s2 →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → 0 < h0 → GapsGe α h0 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
    (beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η 4 R.N) / c₀) ^ (1 / γ) ≤ h0 →
      Jeps J ((beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η 4 R.N) / c₀) ^ (1 / γ)) h0 ≤ 4 ∧
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {ω | StatFormal.Distances.tvDist P Q - h -
              (beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
                (Tbet Dφ s2 (Real.log (1 / δ)) η 4 R.N) / c₀) ^ (1 / γ) ≤ R.alphaLo α δ ω.1 ω.2 ∧
            R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- **The paragraph after the proof of `thm:lorate`** (`C_split.tex:462-464`, a general margin): under the hypotheses of (ii) with the
general margin of Proposition 26 (`Wave30tu.Margin φ P Q ω`: `ω` strictly increasing, continuous, `ω(0) = 0`, `0 ≤ ω ≤ D_{α⋆−·}` on
`[0,α⋆]`) in place of Assumption 2: for every `e ∈ [0,α⋆]` with `ω(e) = t_{n,m}` (i.e. `e = ω^{-1}(t_{n,m})`, which exists when
`t_{n,m} ≤ ω(α⋆)`), on a measurable event of probability `≥ 1 − δ − η`, `α⋆ − h − e ≤ α̂_lo ≤ α⋆`. -/
def lorate_general : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ω : ℝ → ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h e : ℝ) (R : LoRun 𝒳 J n m) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave30tu.Margin φ P Q ω → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ (1 / 2) s2 →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
    e ∈ Icc 0 (StatFormal.Distances.tvDist P Q) →
    ω e = tNM κ Dφ (StatFormal.Distances.tvDist P Q) s2 δ η (rOne R.lx R.ly) B J R.N →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q - h - e ≤ R.alphaLo α δ z.1 z.2 ∧
            R.alphaLo α δ z.1 z.2 ≤ StatFormal.Distances.tvDist P Q}

end Claims

end StatFormal.Wave31tl
