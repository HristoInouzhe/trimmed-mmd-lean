import StatFormal.Wave31tl.Statements
import StatFormal.Wave31ta.Statements
import StatFormal.Wave30tu.Full.Statements
import StatFormal.Archive.Wave8a.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tn: trimmed-mmd, **Annals of Statistics version of 2026-11-20**: `prop:lower2pt` (two-point Le Cam lower bound, one sample perturbed), `lem:twopointmargin`, `cor:minimax` (i)–(iii), `prose:nouniformrate`

Printed source: the frozen statements of the AoS version, `~/projects/tmmd-aos-brief/NEW_STATEMENTS.md` (frozen 2026-11-20, read
2026-11-20), sections S1–S4 (all four in the AoS main text, Section 5): its first 120 lines (preamble and S1–S4) have sha256
`23660a336c7b7498c8804106718fdd6db6f8feb724d36e0ac51f82892039866c` (the whole file as first read); S5–S7 were appended later the same
day (whole file then `467357fecbacc9c72c39ae6c212daab755171b462decd15baf209ccd3d854162`, lines 1–120 unchanged) and are frozen
separately in `StatFormal/Wave31tn/Referee/Statements.lean`. Setting and notation of `jmlr/v3` Section 2 (trimmed-mmd `b41ea67`). The
hand-written proof routes in that file are not part of the specification. Printed-notation note (2026-11-20): the paper now writes
`n∧m` (and `n_1`) where S3 writes `N` (and `N₁`); `N` below is `n∧m` throughout (not the number of betting pairs, which is `R.N`).

* S1 `prop:lower2pt` (a) `lower2pt_tv`: `TV(P_a,Q_a) = a`, `TV(P_{a,h},Q_a) = TV(P_a,Q_{a,h}) = a + h`; (b) `lower2pt`: the two Le Cam
  bounds `P_{P_{a,h},Q_a}(TV − α̃ ≥ h) ≥ 1 − δ − h√(n/(2a(1−a)))` and the same with `Q` perturbed and `m`, for every measurable possibly
  randomised `α̃` with `P_{P_a,Q_a}(α̃ > a) ≤ δ`; (c) `lower2pt_c`: at `h = ((1−δ)/2)√(2a(1−a)/N)`, `N = n∧m`, when `h < 1 − a`, the pair
  whose perturbed sample is the smaller has `P(TV − α̃ ≥ h) ≥ (1−δ)/2`.
* S2 `lem:twopointmargin` `twopointmargin`: both perturbed pairs satisfy `D_{α⋆−ε} ≥ ε/‖f‖` on `[0,α⋆]`, `α⋆ = a + h`, i.e.
  `ass:margin` with `γ = 1`, `c₀ = 1/‖f‖`.
* S3 `cor:minimax` (i) `minimax_i` (lower bound over `𝓜`), (ii) `minimax_ii` (the analytic `α̂` attains `N^{-1/2}` uniformly over `𝓜`),
  (iii) `minimax_iii` (the split-sample `α̂_lo` on the grid `{jN^{-1/2}} ∩ (0,1)` attains it). The prose sentence printed after S3
  ("`(n∧m)^{-1/2}` is the minimax rate … both `α̂` and `α̂_lo` attain it") is the conjunction of the three; no separate claim.
* S4 `prose:nouniformrate` `nouniformrate`: no lower confidence bound valid over `𝒫₂` has a uniform rate `r < 1` over `𝒫₂`.

Reuses (imported, not copied): `Distances.tvDist`, `TrimmedMMD.Unconditional.Dpop` (`D_α`, the regions' distance) and `Wave8a.dTrim`
(the printed infimum of MMD over `R_α(P) × R_α(Q)`), `Wave31ti.PolyMargin` (`ass:margin`), `Wave30tp.sampleLaw`, `TrimmedMMD.alphaHat`
with `Wave30tu.Full.tauFull` (the analytic `α̂` at the paper's `τ_{n,m}`, general kernel), `Wave30tz.LoRun` (`alphaLo`, `IsWitnessRun`),
`Wave31tl.IsDefaultRun` (the batches of Section 4.2), `Wave31ta.Density2` (`𝒫₂`), `TrimmedMMD.Impossible.dataLaw`.

Encodings:
* (A1)–(A2) as in every trimmed-mmd wave: `H` a real complete inner-product space (separable where the certified rate results need it),
  `φ : 𝒳 → H` strongly measurable with `‖φ x‖ ≤ κ`, `k(x,x′) = ⟪φ x, φ x′⟫`, `f(x) = ⟪f, φ x⟫`. (A3) is used by none of the proofs and
  is not assumed (generalisation); separability is dropped in S2 and S3 (i) (generalisation). `Δ_φ` is any `Dφ` with
  `‖φ x − φ x′‖ ≤ Dφ ≤ 2κ` (the least such bound is the printed `Δ_φ`). `InM` and `PolyMargin` use `Dpop`, equal to the printed
  `D_α` (infimum over trimmings, `dTrim`) by the certified `Wave8a.georep_dist`.
* S1 (b): `δ` is any real (generalisation of `δ ∈ [0,1]`; the bound is trivial for `δ ≥ 1`). S1 (c): when `n = m` both conjuncts hold
  (stronger than "at one of the two pairs").
* S2 (strengthenings, all printed or implicit): the conclusion also states `‖f‖ > 0`, `α⋆ = a + h` for both pairs, the bound for both
  `dTrim` and `Dpop`, and `PolyMargin` with `c₀ = 1/‖f‖`, `γ = 1`.
* `P_a = (1−a)R + aP₀` is `mixAt R P₀ a`, `P_{a,h} = (1−a−h)R + (a+h)P₀` is `mixAt R P₀ (a + h)` (likewise `Q` with `Q₀`); "concentrated
  on pairwise disjoint measurable sets": `R S_Rᶜ = 0`, `P₀ S_Pᶜ = 0`, `Q₀ S_Qᶜ = 0`, the sets measurable and pairwise disjoint.
* Randomised estimators (S1, S3 (i), S4, as in the certified `thm:impossible`): a measurable `T` of `((X_{1:n}, Y_{1:m}), U)`, `U` from
  any probability space `(Ξ, ρ)` independent of the data; the law of `((X,Y),U)` is `(sampleLaw P Q n m).prod ρ` (S4: `dataLaw`, the same
  on `ℝ`). Probabilities are `Measure.real` (S1, S3 (i), S4) or `ℝ≥0∞` bounds `≤ ofReal ·` (S3 (ii), (iii), as in the certified sources).
* `𝓜(a₀,a₁,c₀)` is `InM φ a₀ a₁ c₀ P Q`. "`sup_𝓜 P(·) ≤ c`" is `∀ (P,Q) ∈ 𝓜, P(·) ≤ c`; "`sup_𝓜 P(·) ≥ c`" (S3 (i)) is the stronger
  `∃ (P,Q) ∈ 𝓜, P(·) ≥ c`. "There are `C, N₁` depending only on …": `∃ C N₁` placed after exactly those parameters and before `𝒳`, `φ`,
  `n`, `m`, the pair and the run. `N^{-1/2}` is `1/√N`, `N = n∧m` (`(min n m : ℕ)` cast to `ℝ`).
* S3 (i): the three points and `f` enter only through `⟪f, φ x₁⟫ = 1`, `⟪f, φ x₂⟫ = 0`, `⟪f, φ x₃⟫ = −1` (distinctness follows).
  S3 (ii), (iii) do not use the points, `f` or `c₀ ≤ 1/‖f‖` (dropped: generalisation).
* S3 (iii): the grid `{jN^{-1/2} : j ≥ 1} ∩ (0,1)` is `rootGrid N : Fin (rootLevels N) → ℝ`, `j ↦ (j+1)/√N`, with
  `rootLevels N = ⌈√N⌉ − 1` levels (exactly the `j ≥ 1` with `j/√N < 1`); "computed as in prop:loconsistency / thm:lorate (default
  batches, …, `λ_max = ½`, `σ₀² ≤ 4`, floor `σ²_min ∈ (0,4]`) at level `δ`" is `R.IsWitnessRun φ (rootGrid N) δ (1/2) s2 ∧ IsDefaultRun R`
  with `0 < s2 ≤ 4`, exactly as in the certified `Wave31tl.lorate_O`. Inherited generalisations (Wave 30tz/31tl): any cut points
  satisfying (C) in place of `eq:cutrank`, any fractions within `[lamLo, lamHi]` (and `0` when there is no bet) in place of
  `eq:fractions`. `R.N` is the number of betting pairs, not `N = n∧m`. That some run satisfies `IsWitnessRun ∧ IsDefaultRun` is not
  certified here (inherited from `lorate_O`; non-vacuity needs a measurable choice of QP minimisers and cut points).
* S4: `r ∈ [0,1)` is relaxed to `r < 1` (generalisation); `δ, δ′ > 0`, `δ + δ′ < 1`.
* Junk values: `mixAt` uses `ofReal (1−t)`, `ofReal t` only at `t ∈ (0,1)` (`a ∈ (0,1)`, `0 ≤ h < 1−a`), where they are the printed
  weights; `√(n/(2a(1−a)))` with `a ∈ (0,1)`; S1 (c) and S3 (i): `√(2a(1−a)/N)` and `c_lo/√N` with `N ≥ 1` (S1 (c) assumes `n, m ≥ 1`: at
  `N = 0` the printed `h` is infinite, Lean's `x/0 = 0` would make it `0`; in S3 (i) `N ≥ c_lo²/(a₁−a₀)² > 0` forces `N ≥ 1`); S3 (ii),
  (iii): `C/√N` with `N ≥ max(N₁, 1)` resp. `N ≥ 10` (`N₁` is existential; (ii) can fail at `N = 0`, where
  `C/√0 = 0` and `Demp ≡ 0`, so a valid witness has `N₁ ≥ 1`, which forces `n, m ≥ 1`); `rootGrid` divides by `√N > 0`; `ε/‖f‖` with `‖f‖ > 0` (part of the conclusion of S2); `Dpop`/`dTrim` evaluated only at
  levels in `[0,1)`; `tvDist` of probability measures only (genuine, in `[0,1]`); `PolyMargin` with `γ = 1` (`ε ^ (1:ℝ) = ε`); no
  `Measure.map`, no `klDiv`, no `iSup` beyond `tvDist`; `⌈√N⌉₊ − 1` is ℕ subtraction, `≥ 3` for `N ≥ 10`.

Not covered (declared): the prose half of S4 ("validity and consistency of both estimators hold for every pair", certified earlier as
`thm:consistency`, `cor:lower`, `prop:loconsistency`; "a condition on the laws, here ass:margin, is needed for any rate", informal);
the interpolation remark in S3 ("such an `f` exists whenever `k` is strictly positive definite", certified as `Wave31tg.interpolation`
for finite sets); the remark in S2 that at `h = 0` the bound is weaker than `ex:separated` (a comparison of constants, `1/‖f‖ ≤ 2/‖f‖`);
the proof routes.
FROZEN 2026-11-20 before any proof, after an independent critic's pre-freeze review (8 claims: 4 ACCEPT — `lower2pt_tv`,
`lower2pt_c`, `twopointmargin`, `nouniformrate` —, 4 ACCEPT-WITH-NOTE — `lower2pt`, `minimax_i`, `minimax_ii`, `minimax_iii` —; none
false; every claim re-derived, including the exact constant `h√(n/(2a(1−a)))` of S1 (b) via `χ² = h²/(a(1−a))`, Pinsker and
tensorisation; verdict READY TO FREEZE after R1–R5, all header/docstring-only). Applied: R1 provenance of the appended S5–S7 (lines
1–120 unchanged), R2 the S1 (b) and S2 generalisations/strengthenings moved to the Encodings, `InM` uses `Dpop` = `dTrim`, R3 the
inherited run generalisations and the non-vacuity remark for S3 (iii), R4 the `N₁ ≥ 1` junk-value remark for S3 (ii), R5 "(A1),
separability not assumed" in two docstrings. Not applied: R6 (optional non-vacuity claim for the run predicate). No Lean term changed.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tn

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The mixture `(1−t)R + tP₀` (`P_a = mixAt R P₀ a`, `P_{a,h} = mixAt R P₀ (a + h)`; Mathlib measure sum and `ℝ≥0∞` scaling). -/
def mixAt (R P₀ : Measure 𝒳) (t : ℝ) : Measure 𝒳 := ENNReal.ofReal (1 - t) • R + ENNReal.ofReal t • P₀

/-- The perturbation of S1 (c), `h = ((1−δ)/2)·√(2a(1−a)/N)`. -/
def hStar (δ a : ℝ) (N : ℕ) : ℝ := (1 - δ) / 2 * √(2 * a * (1 - a) / N)

/-- The constant of S3 (i), `c_lo = ((1−δ)/2)·√(2a₀(1−a₀))`. -/
def clo (δ a₀ : ℝ) : ℝ := (1 - δ) / 2 * √(2 * a₀ * (1 - a₀))

/-- The class `𝓜(a₀,a₁,c₀)` of S3: probability measures `P, Q` with `a₀ ≤ TV(P,Q) ≤ a₁` satisfying `ass:margin` with `γ = 1` and `c₀`. -/
def InM (φ : 𝒳 → H) (a₀ a₁ c₀ : ℝ) (P Q : Measure 𝒳) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧ a₀ ≤ StatFormal.Distances.tvDist P Q ∧
    StatFormal.Distances.tvDist P Q ≤ a₁ ∧ StatFormal.Wave31ti.PolyMargin φ P Q c₀ 1

/-- The number of levels of the grid `{jN^{-1/2} : j ≥ 1} ∩ (0,1)`: `⌈√N⌉ − 1`. -/
def rootLevels (N : ℕ) : ℕ := ⌈√(N : ℝ)⌉₊ - 1

/-- The grid `{jN^{-1/2} : j ≥ 1} ∩ (0,1)` in increasing order: level `j` (from `0`) is `(j+1)/√N`. -/
def rootGrid (N : ℕ) : Fin (rootLevels N) → ℝ := fun j => ((j : ℕ) + 1 : ℝ) / √(N : ℝ)

end Defs

namespace Claims

/-! ### S1 `prop:lower2pt` -/

/-- **S1 (a)**: `R, P₀, Q₀` probability measures concentrated on pairwise disjoint measurable `S_R, S_P, S_Q`, `a ∈ (0,1)`,
`h ∈ [0, 1−a)`: `TV(P_a,Q_a) = a`, `TV(P_{a,h},Q_a) = a + h`, `TV(P_a,Q_{a,h}) = a + h`. -/
def lower2pt_tv : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure Q₀] (SR SP SQ : Set 𝒳) (a h : ℝ),
    MeasurableSet SR → MeasurableSet SP → MeasurableSet SQ →
    Disjoint SR SP → Disjoint SR SQ → Disjoint SP SQ →
    R SRᶜ = 0 → P₀ SPᶜ = 0 → Q₀ SQᶜ = 0 →
    0 < a → a < 1 → 0 ≤ h → h < 1 - a →
      StatFormal.Distances.tvDist (mixAt R P₀ a) (mixAt R Q₀ a) = a ∧
      StatFormal.Distances.tvDist (mixAt R P₀ (a + h)) (mixAt R Q₀ a) = a + h ∧
      StatFormal.Distances.tvDist (mixAt R P₀ a) (mixAt R Q₀ (a + h)) = a + h

/-- **S1 (b)**: in the setting of (a), for `n, m ∈ ℕ`, a randomiser `U ∼ ρ` on any probability space `Ξ` and any measurable
`α̃ = T((X,Y),U)` with `P_{P_a,Q_a}(α̃ > a) ≤ δ`: for every `h ∈ (0, 1−a)`,
`P_{P_{a,h},Q_a}(TV(P_{a,h},Q_a) − α̃ ≥ h) ≥ 1 − δ − h√(n/(2a(1−a)))` and
`P_{P_a,Q_{a,h}}(TV(P_a,Q_{a,h}) − α̃ ≥ h) ≥ 1 − δ − h√(m/(2a(1−a)))`. (`δ` any real: generalisation of `δ ∈ [0,1]`.) -/
def lower2pt : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure Q₀] (SR SP SQ : Set 𝒳) (a δ : ℝ) (n m : ℕ) (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] (T : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Ξ → ℝ),
    MeasurableSet SR → MeasurableSet SP → MeasurableSet SQ →
    Disjoint SR SP → Disjoint SR SQ → Disjoint SP SQ →
    R SRᶜ = 0 → P₀ SPᶜ = 0 → Q₀ SQᶜ = 0 →
    0 < a → a < 1 → Measurable T →
    ((sampleLaw (mixAt R P₀ a) (mixAt R Q₀ a) n m).prod ρ).real {z | a < T z} ≤ δ →
      ∀ h : ℝ, 0 < h → h < 1 - a →
        1 - δ - h * √(n / (2 * a * (1 - a))) ≤
          ((sampleLaw (mixAt R P₀ (a + h)) (mixAt R Q₀ a) n m).prod ρ).real
            {z | h ≤ StatFormal.Distances.tvDist (mixAt R P₀ (a + h)) (mixAt R Q₀ a) - T z} ∧
        1 - δ - h * √(m / (2 * a * (1 - a))) ≤
          ((sampleLaw (mixAt R P₀ a) (mixAt R Q₀ (a + h)) n m).prod ρ).real
            {z | h ≤ StatFormal.Distances.tvDist (mixAt R P₀ a) (mixAt R Q₀ (a + h)) - T z}

/-- **S1 (c)**: in the setting of (b) with `n, m ≥ 1`, `δ ∈ [0,1]`, `N = n∧m` and `h = ((1−δ)/2)√(2a(1−a)/N) < 1 − a`: if `n ≤ m`
(the `X`-sample is the smaller) then `P_{P_{a,h},Q_a}(TV − α̃ ≥ h) ≥ (1−δ)/2`, and if `m ≤ n` then `P_{P_a,Q_{a,h}}(TV − α̃ ≥ h) ≥ (1−δ)/2`. -/
def lower2pt_c : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure Q₀] (SR SP SQ : Set 𝒳) (a δ : ℝ) (n m : ℕ) (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] (T : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Ξ → ℝ),
    MeasurableSet SR → MeasurableSet SP → MeasurableSet SQ →
    Disjoint SR SP → Disjoint SR SQ → Disjoint SP SQ →
    R SRᶜ = 0 → P₀ SPᶜ = 0 → Q₀ SQᶜ = 0 →
    0 < a → a < 1 → 0 ≤ δ → δ ≤ 1 → 1 ≤ n → 1 ≤ m → Measurable T →
    ((sampleLaw (mixAt R P₀ a) (mixAt R Q₀ a) n m).prod ρ).real {z | a < T z} ≤ δ →
    hStar δ a (min n m) < 1 - a →
      (n ≤ m → (1 - δ) / 2 ≤
          ((sampleLaw (mixAt R P₀ (a + hStar δ a (min n m))) (mixAt R Q₀ a) n m).prod ρ).real
            {z | hStar δ a (min n m) ≤
              StatFormal.Distances.tvDist (mixAt R P₀ (a + hStar δ a (min n m))) (mixAt R Q₀ a) - T z}) ∧
      (m ≤ n → (1 - δ) / 2 ≤
          ((sampleLaw (mixAt R P₀ a) (mixAt R Q₀ (a + hStar δ a (min n m))) n m).prod ρ).real
            {z | hStar δ a (min n m) ≤
              StatFormal.Distances.tvDist (mixAt R P₀ a) (mixAt R Q₀ (a + hStar δ a (min n m))) - T z})

/-! ### S2 `lem:twopointmargin` -/

/-- **S2**: (A1) (`φ` strongly measurable into a real Hilbert space, `‖φ x‖ ≤ κ`; separability not assumed), the setting of S1 (a), and `f ∈ 𝓗` with
`f = 0` on `S_R`, `1` on `S_P`, `−1` on `S_Q`: `‖f‖ > 0`, and each of the pairs `(P_{a,h},Q_a)`, `(P_a,Q_{a,h})` has `α⋆ = a + h` and
`D_{α⋆−ε} ≥ ε/‖f‖` for every `ε ∈ [0,α⋆]` (for `D_α` the printed infimum over trimmings, `dTrim`, and the regions' distance `Dpop`),
i.e. `ass:margin` with `γ = 1` and `c₀ = 1/‖f‖` (`PolyMargin`). -/
def twopointmargin : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure Q₀] (SR SP SQ : Set 𝒳) (a h : ℝ) (f : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    MeasurableSet SR → MeasurableSet SP → MeasurableSet SQ →
    Disjoint SR SP → Disjoint SR SQ → Disjoint SP SQ →
    R SRᶜ = 0 → P₀ SPᶜ = 0 → Q₀ SQᶜ = 0 →
    0 < a → a < 1 → 0 ≤ h → h < 1 - a →
    (∀ x ∈ SR, ⟪f, φ x⟫_ℝ = 0) → (∀ x ∈ SP, ⟪f, φ x⟫_ℝ = 1) → (∀ x ∈ SQ, ⟪f, φ x⟫_ℝ = -1) →
      0 < ‖f‖ ∧
      StatFormal.Distances.tvDist (mixAt R P₀ (a + h)) (mixAt R Q₀ a) = a + h ∧
      StatFormal.Distances.tvDist (mixAt R P₀ a) (mixAt R Q₀ (a + h)) = a + h ∧
      (∀ ε ∈ Icc (0 : ℝ) (a + h),
        ε / ‖f‖ ≤ StatFormal.Wave8a.dTrim φ (mixAt R P₀ (a + h)) (mixAt R Q₀ a) (a + h - ε) ∧
        ε / ‖f‖ ≤ Dpop φ (mixAt R P₀ (a + h)) (mixAt R Q₀ a) (a + h - ε) ∧
        ε / ‖f‖ ≤ StatFormal.Wave8a.dTrim φ (mixAt R P₀ a) (mixAt R Q₀ (a + h)) (a + h - ε) ∧
        ε / ‖f‖ ≤ Dpop φ (mixAt R P₀ a) (mixAt R Q₀ (a + h)) (a + h - ε)) ∧
      StatFormal.Wave31ti.PolyMargin φ (mixAt R P₀ (a + h)) (mixAt R Q₀ a) (1 / ‖f‖) 1 ∧
      StatFormal.Wave31ti.PolyMargin φ (mixAt R P₀ a) (mixAt R Q₀ (a + h)) (1 / ‖f‖) 1

/-! ### S3 `cor:minimax` -/

/-- **S3 (i)** (lower bound): (A1) (separability not assumed), three points with `f(x₁) = 1`, `f(x₂) = 0`, `f(x₃) = −1` (`f(x) = ⟪f, φ x⟫`),
`0 < a₀ < a₁ < 1`, `0 < c₀ ≤ 1/‖f‖`, `δ ∈ (0,1)`, `N = n∧m ≥ c_lo²/(a₁ − a₀)²`: every measurable, possibly randomised `α̃` with
`P_{P,Q}(α̃ > TV(P,Q)) ≤ δ` for every `(P,Q) ∈ 𝓜(a₀,a₁,c₀)` has, at some `(P,Q) ∈ 𝓜`, `P_{P,Q}(TV(P,Q) − α̃ ≥ c_lo N^{-1/2}) ≥ (1−δ)/2`
(so the supremum over `𝓜` is at least `(1−δ)/2`). -/
def minimax_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (x₁ x₂ x₃ : 𝒳) (f : H) (a₀ a₁ c₀ δ : ℝ) (n m : ℕ)
    (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (T : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Ξ → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    ⟪f, φ x₁⟫_ℝ = 1 → ⟪f, φ x₂⟫_ℝ = 0 → ⟪f, φ x₃⟫_ℝ = -1 →
    0 < a₀ → a₀ < a₁ → a₁ < 1 → 0 < c₀ → c₀ ≤ 1 / ‖f‖ → 0 < δ → δ < 1 →
    clo δ a₀ ^ 2 / (a₁ - a₀) ^ 2 ≤ ((min n m : ℕ) : ℝ) → Measurable T →
    (∀ P Q : Measure 𝒳, InM φ a₀ a₁ c₀ P Q →
      ((sampleLaw P Q n m).prod ρ).real {z | StatFormal.Distances.tvDist P Q < T z} ≤ δ) →
      ∃ P Q : Measure 𝒳, InM φ a₀ a₁ c₀ P Q ∧
        (1 - δ) / 2 ≤ ((sampleLaw P Q n m).prod ρ).real
          {z | clo δ a₀ / √((min n m : ℕ) : ℝ) ≤ StatFormal.Distances.tvDist P Q - T z}

/-- **S3 (ii)** (upper bound, analytic estimator): for `κ, Δ_φ`, `0 < a₀ < a₁ < 1`, `c₀ > 0`, `δ, δ′ ∈ (0,1)` there are `C, N₁` such
that for every (A1)–(A2) feature map with `‖φ‖ ≤ κ`, `‖φ x − φ x′‖ ≤ Δ_φ ≤ 2κ`, all `n, m` with `N = n∧m ≥ N₁` and every
`(P,Q) ∈ 𝓜(a₀,a₁,c₀)`, the analytic `α̂` (`eq:alphaest` at the paper's `τ_{n,m}(·,δ)`) has `P(α̂ > TV(P,Q)) ≤ δ` and
`P(TV(P,Q) − α̂ > C N^{-1/2}) ≤ δ + δ′`. -/
def minimax_ii : Prop :=
  ∀ (κ Dφ a₀ a₁ c₀ δ δ' : ℝ), 0 < a₀ → a₀ < a₁ → a₁ < 1 → 0 < c₀ → 0 < δ → δ < 1 → 0 < δ' → δ' < 1 →
    ∃ C N₁ : ℝ, ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (n m : ℕ) (P Q : Measure 𝒳),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
      N₁ ≤ ((min n m : ℕ) : ℝ) → InM φ a₀ a₁ c₀ P Q →
        sampleLaw P Q n m {z | StatFormal.Distances.tvDist P Q <
            alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ Dφ α δ n m)} ≤ ENNReal.ofReal δ ∧
        sampleLaw P Q n m {z | C / √((min n m : ℕ) : ℝ) < StatFormal.Distances.tvDist P Q -
            alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ Dφ α δ n m)} ≤ ENNReal.ofReal (δ + δ')

/-- **S3 (iii)** (upper bound, split-sample estimator): for `κ, Δ_φ`, `0 < a₁ < 1`, `c₀ > 0`, `σ²_min ∈ (0,4]`, `δ, η ∈ (0,1)` there
are `C, N₁` such that for every `a₀ ∈ (0, a₁)`, every (A1)–(A2) feature map with `‖φ‖ ≤ κ`, `‖φ x − φ x′‖ ≤ Δ_φ ≤ 2κ`, all `n, m` with
`N = n∧m ≥ max(N₁, 10)`, every `(P,Q) ∈ 𝓜(a₀,a₁,c₀)` and every run of Proposition 12 with the batches of Section 4.2 (`λ_max = ½`, floor
`σ²_min`) at level `δ` on the grid `{jN^{-1/2}} ∩ (0,1)`: `P(α̂_lo > TV(P,Q)) ≤ δ` and `P(TV(P,Q) − α̂_lo > C N^{-1/2}) ≤ η`. -/
def minimax_iii : Prop :=
  ∀ (κ Dφ a₁ c₀ s2 δ η : ℝ), 0 < a₁ → a₁ < 1 → 0 < c₀ → 0 < s2 → s2 ≤ 4 → 0 < δ → δ < 1 → 0 < η → η < 1 →
    ∃ C N₁ : ℝ, ∀ (a₀ : ℝ) (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (n m : ℕ) (P Q : Measure 𝒳)
      (R : LoRun 𝒳 (rootLevels (min n m)) n m),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
      0 < a₀ → a₀ < a₁ → max N₁ 10 ≤ ((min n m : ℕ) : ℝ) → InM φ a₀ a₁ c₀ P Q →
      R.IsWitnessRun φ (rootGrid (min n m)) δ (1 / 2) s2 → IsDefaultRun R →
        sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q < R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} ≤
          ENNReal.ofReal δ ∧
        sampleLaw P Q n m {ω | C / √((min n m : ℕ) : ℝ) <
            StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} ≤ ENNReal.ofReal η

/-! ### S4 `prose:nouniformrate` -/

/-- **S4**: fix `n, m ≥ 1`, `δ, δ′ > 0` with `δ + δ′ < 1` and `r < 1`. No measurable, possibly randomised `α̃ = T((X,Y),U)` has both
`P_{P,Q}(α̃ > TV(P,Q)) ≤ δ` and `P_{P,Q}(TV(P,Q) − α̃ > r) ≤ δ′` for every `(P,Q) ∈ 𝒫₂` (laws on `[0,1]` with densities bounded by 2). -/
def nouniformrate : Prop :=
  ∀ (n m : ℕ) (δ δ' r : ℝ) (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
    1 ≤ n → 1 ≤ m → 0 < δ → 0 < δ' → δ + δ' < 1 → r < 1 → Measurable T →
      ¬ ((∀ P Q : Measure ℝ, StatFormal.Wave31ta.Density2 P → StatFormal.Wave31ta.Density2 Q →
            (StatFormal.TrimmedMMD.Impossible.dataLaw n m P Q ρ).real {z | StatFormal.Distances.tvDist P Q < T z} ≤ δ) ∧
          (∀ P Q : Measure ℝ, StatFormal.Wave31ta.Density2 P → StatFormal.Wave31ta.Density2 Q →
            (StatFormal.TrimmedMMD.Impossible.dataLaw n m P Q ρ).real
              {z | r < StatFormal.Distances.tvDist P Q - T z} ≤ δ'))

end Claims

end StatFormal.Wave31tn
