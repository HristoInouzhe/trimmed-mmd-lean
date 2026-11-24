import StatFormal.Wave30tu.Statements
import StatFormal.Archive.Wave8a.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tb: trimmed-mmd (jmlr) **v3**, `ex:separated` (separated supports satisfy the margin with `γ = 1`)

Printed source: `trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md`, section `ex:separated` (the statement frozen 2026-11-12 for the v3 clarity
revision of `jmlr/v2`; an Example of the main text §3 after Assumption 2 `ass:margin`, proof in Appendix B; read-only, read 2026-11-12,
sha256 `6b4825f20f0253ee1dfff276ed801cfcbb906e5bafca87a16106b2ce3557c238`; `jmlr/v3/` is not yet committed in trimmed-mmd, whose master is
at `d5cdddb`). Notation as in `jmlr/v2` §2 (`jmlr/v2/sections/02_regions.tex` at `d5cdddb`, sha256 `1cf7137b…`, `eq:trimset`,
`eq:trimMMDpop`, `ass:regularity`, `eq:region`) and `ass:margin` (`jmlr/v2/sections/03_analytic.tex:180-184` at `d5cdddb`, sha256
`8e52b514…`), both restated in the header of `NEW_STATEMENTS.md`; the uncommitted `jmlr/v3/sections/` copies (still being edited) carry the
same definitions, and `jmlr/v3/sections/03_analytic.tex` (read 2026-11-12, label `ex:separated` at line 147, proof
`jmlr/v3/appendix/B_analytic.tex`, subsection "Proof of Example") prints the same statement without the parenthetical "(the polynomial case
`γ = 1`)". Label `ex:separated (v3)`.

The printed statement: let (A1) and (A2) hold; let `R, P₀, Q₀` be probability measures concentrated on pairwise disjoint measurable sets
`S_R, S_P, S_Q`, let `α⋆ ∈ (0,1)`, and put `P = (1−α⋆)R + α⋆P₀`, `Q = (1−α⋆)R + α⋆Q₀`. Then `TV(P,Q) = α⋆`. If moreover some `f ∈ ℋ` takes
the value `0` on `S_R`, `1` on `S_P` and `−1` on `S_Q`, then for every `α ∈ [0,α⋆]`,
`D_α(P,Q) ≥ 2(α⋆ − α)/((1−α)‖f‖_ℋ) ≥ 2(α⋆ − α)/‖f‖_ℋ`, so Assumption 2 holds with `ω(ε) = c₀ε`, `c₀ = 2/‖f‖_ℋ` (the polynomial case `γ = 1`).
The paragraph after it (existence of such `f` for finite supports and strictly positive definite kernels, or for Matérn kernels on
`ℝ^d`) is prose and is not formalised.

Covered here (1 claim): `separated`.

Reuses (imported, not copied): `Distances.tvDist` (`TV`), `Wave8a.trimSet` (`R_α`, `eq:trimset`, literal: probability measures
`P' ≪ P` with `dP'/dP ≤ (1−α)⁻¹` `P`-a.s.), `Wave8a.dTrim` (`D_α`, `eq:trimMMDpop`, literal: the infimum of `MMD(P',Q') = ‖μ_{P'} − μ_{Q'}‖`
over `R_α(P) × R_α(Q)`), `TrimmedMMD.Unconditional.Dpop` (the distance between the trimmed regions `𝒞_α(P)`, `𝒞_α(Q)`, `eq:setdist`; equal
to `dTrim` by the certified `Wave8a.georep_dist`; it is the `D_α` of every certified estimator claim), `Wave30tu.Margin` (`ass:margin` at
`α⋆ = TV(P,Q)`, the hypothesis of the certified `Wave30tu.rate`, stated with `Dpop`); the polynomial-case hypothesis of the certified
`Wave30tu.rate_poly` (`c₀ε^γ ≤ D_{α⋆−ε}` on `[0,α⋆]`, real power `γ`).

Encodings (see the card `certify/cards/wave31tb.md`):
* (A1)–(A2) as in the reused waves: `𝓗` a real Hilbert space (complete; separability is not used by this claim and is dropped —
  generalisation), `φ : 𝒳 → 𝓗` strongly measurable with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ(x)‖² ≤ κ²`); an element `f ∈ 𝓗` acts as the function
  `x ↦ ⟪f, φ x⟫` (reproducing property) and `‖f‖_ℋ` is `‖f‖`. For the RKHS itself (`φ(x) = k(x,·)`) this is literal.
* "concentrated on `S`": the complement is null (`R S_Rᶜ = 0`, …); "pairwise disjoint measurable": `MeasurableSet` and `Disjoint`.
* The mixtures: `P = ofReal(1−α⋆)•R + ofReal(α⋆)•P₀` (Mathlib measure sum and `ℝ≥0∞` scaling), and the same for `Q`.
* "`f` takes the value `0` on `S_R`, `1` on `S_P`, `−1` on `S_Q`": `⟪f, φ x⟫ = 0, 1, −1` for every `x` in the respective set.
* The bound is stated for both `dTrim` (the printed `D_α`) and `Dpop` (the regions' distance; equal by `prop:georep`).
* "Assumption 2 holds with `ω(ε) = c₀ε`": `Wave30tu.Margin φ P Q (fun ε => 2/‖f‖ * ε)`; "the polynomial case `γ = 1`": the hypothesis of
  `Wave30tu.rate_poly` with `c₀ = 2/‖f‖ > 0` and `γ = 1` (`ε ^ (1 : ℝ)`). `0 < ‖f‖` is part of the conclusion (no division by zero).
FROZEN 2026-11-12 after an independent critic's pre-freeze review (1 claim, ACCEPT-WITH-NOTE, every conjunct true, verdict READY TO FREEZE;
it back-translated the claim blind, typechecked a witness of the hypotheses (the three-point laws with a rank-one kernel), and checked the
bound numerically on the three-point Gaussian example, where it is attained, and on 349 random Gaussian configurations, never violated;
applied: the provenance lines above). Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tb

open StatFormal.TrimmedMMD.Unconditional StatFormal.Wave8a StatFormal.Wave30tu

namespace Claims

/-- `ex:separated (v3)` (`jmlr/v3/NEW_STATEMENTS.md`, section `ex:separated`). (A1)–(A2): `φ` strongly measurable into a real Hilbert space,
`‖φ x‖ ≤ κ`. `R, P₀, Q₀` probability measures concentrated on the pairwise disjoint measurable sets `S_R, S_P, S_Q`, `α⋆ ∈ (0,1)`,
`P = (1−α⋆)R + α⋆P₀`, `Q = (1−α⋆)R + α⋆Q₀`. Then `TV(P,Q) = α⋆`; and for every `f ∈ 𝓗` with `f = 0` on `S_R`, `f = 1` on `S_P`, `f = −1` on
`S_Q` (`f(x) = ⟪f, φ x⟫`): `‖f‖ > 0`; for every `α ∈ [0,α⋆]`,
`D_α(P,Q) ≥ 2(α⋆ − α)/((1−α)‖f‖)` (for `D_α` the infimum of MMD over `R_α(P) × R_α(Q)`, `dTrim`, and for the regions' distance `Dpop`)
and `2(α⋆ − α)/((1−α)‖f‖) ≥ 2(α⋆ − α)/‖f‖`; Assumption 2 (`ass:margin`, `Wave30tu.Margin`) holds with `ω(ε) = (2/‖f‖)ε`; and
`c₀ = 2/‖f‖ > 0`, `c₀ε^γ ≤ D_{α⋆−ε}(P,Q)` for every `ε ∈ [0, TV(P,Q)]` with `γ = 1` (the hypothesis of the polynomial case of `thm:rate`,
`Wave30tu.rate_poly`). The first bound is attained, e.g. for the three-point laws (`R = δ_{x₂}`, `P₀ = δ_{x₁}`, `Q₀ = δ_{x₃}`,
`α⋆ = 1/2`) with the Gaussian kernel and the interpolating `f`, and for a rank-one kernel. -/
def separated : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (R P₀ Q₀ P Q : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure Q₀] (SR SP SQ : Set 𝒳) (αs : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    MeasurableSet SR → MeasurableSet SP → MeasurableSet SQ →
    Disjoint SR SP → Disjoint SR SQ → Disjoint SP SQ →
    R SRᶜ = 0 → P₀ SPᶜ = 0 → Q₀ SQᶜ = 0 →
    0 < αs → αs < 1 →
    P = ENNReal.ofReal (1 - αs) • R + ENNReal.ofReal αs • P₀ →
    Q = ENNReal.ofReal (1 - αs) • R + ENNReal.ofReal αs • Q₀ →
      StatFormal.Distances.tvDist P Q = αs ∧
      ∀ f : H, (∀ x ∈ SR, ⟪f, φ x⟫_ℝ = 0) → (∀ x ∈ SP, ⟪f, φ x⟫_ℝ = 1) → (∀ x ∈ SQ, ⟪f, φ x⟫_ℝ = -1) →
        0 < ‖f‖ ∧
        (∀ α ∈ Icc 0 αs,
          2 * (αs - α) / ((1 - α) * ‖f‖) ≤ dTrim φ P Q α ∧
          2 * (αs - α) / ((1 - α) * ‖f‖) ≤ Dpop φ P Q α ∧
          2 * (αs - α) / ‖f‖ ≤ 2 * (αs - α) / ((1 - α) * ‖f‖)) ∧
        Margin φ P Q (fun ε => 2 / ‖f‖ * ε) ∧
        (0 < 2 / ‖f‖ ∧ ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
          2 / ‖f‖ * ε ^ (1 : ℝ) ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε))

end Claims

end StatFormal.Wave31tb
