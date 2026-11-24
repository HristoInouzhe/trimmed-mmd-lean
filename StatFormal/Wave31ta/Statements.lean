import StatFormal.Wave30tx.Statements
import StatFormal.Wave30tw.Statements
import StatFormal.Wave30tv.Statements
import StatFormal.Archive.TrimmedMMD.Impossible.Statements
import StatFormal.Archive.Wave17a.Statements
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# FROZEN STATEMENTS — wave 31ta: trimmed-mmd (jmlr) **v2 short**, the statements not implied by earlier certified claims

Printed source: `trimmed-mmd/jmlr/v2/` at trimmed-mmd master `3bad3e7` (the 50-page JMLR version; read-only, read 2026-11-08; sha256
`sections/02_regions.tex` `1cf7137b…`, `sections/03_analytic.tex` `4075baa8…`, `sections/04_split.tex` `5091bcf4…`,
`sections/05_trimming.tex` `96f95270…`, `appendix/A_regions.tex` `8901e245…`, `appendix/B_analytic.tex` `e160b84a…`,
`appendix/C_split.tex` `a3a7389e…`, `appendix/D_trimming.tex` `10a4d944…`; full hashes and the statement-by-statement coverage
map on `certify/cards/wave31ta_map.md`). Every other numbered statement of v2 is exact or implied by claims certified in earlier
waves (map). Labels `<label> (v2 short)`.

Covered here (13 claims):
* `prop:bangbang` (`05_trimming.tex:17-35`): `bangbang_v2`, the printed form with one level `α ∈ [0,1)` in the RKHS setting, including
  (i)'s "namely the element of minimal norm of `𝒞_α(P_n) − 𝒞_α(Q_m)`, and `‖d̂‖ = D̂_α`" and (ii) at `n_α = n` (the printed convention
  `d̂_{(n+1)} = +∞`: every weight at its cap; symmetrically for `m_α = m`).
* `lem:continuity` (`A_regions.tex:74-81`): `continuity_v2`, the printed `ᾱ ∈ [0,1)` form (the frozen `Wave18b.continuity_lip` has
  `η = 1 − ᾱ ∈ (0,1)`, which excludes `ᾱ = 0`).
* `eq:distmax` (`C_split.tex:32-37`): `distmax`.
* `cor:uniform` (`D_trimming.tex:345-357`): `uniform_event`, with the event named as printed,
  `{sup_{g∈𝒢}|(P_n − P)g| ≤ 4κ/√n + κ√(2log(2/δ)/n)}`, `𝒢 = {x ↦ (f(x) − t)_+ : f ∈ B_𝓗, t ∈ [−κ,κ]}`.
* `rem:sharper` (`03_analytic.tex:66-72`), "a smaller threshold": `sharp_le_plugin` (`τ^{P'} ≤ τ^P` for the general-kernel `τ^{P'}`,
  and for the coupled supremum when `D_φ = √2κ`), and `sharp_cpl_counterexample` (the coupled supremum of `B_analytic.tex:144-147` can
  exceed `τ^P` when `D_φ < √2κ`: a defect of the printed sentence for those kernels).
* `eq:sharptau` (`B_analytic.tex:128-140`): `pinelis_h_form`, the Pinelis term in the printed form `2exp(−(b²/a²)h(ta/b²))`.
* The paper's threshold `τ = min(τ^P, τ^{P'}, τ^A)` for kernels with `k ≥ 0` and constant diagonal, where `τ^{P'}` is the coupled
  supremum (`03_analytic.tex:87-90`, `B_analytic.tex:144-147`): `tauV2Cpl_facts` (valid, nondecreasing, `≤ τ^A`, `≤ r_n + r_m`,
  continuous on `(0,1)`, `→ ∞`, every clause of `lem:crossing` and of the paragraph after `eq:alphaest`), so that the generic §3
  results (Wave30tu) apply to it.
* `cor:lower` (`04_split.tex:119-132`), the second sentence: `cor_lower_v2` (the event "`H_{0,α̂_lo}` is rejected and
  `TV(P,Q) ≤ α̂_lo`" is measurable and has probability `≤ δ`), with the first sentence restated.
* `thm:impossible` (`04_split.tex:170-177`): `impossible_two`, coverage required only over `𝒫₂` (densities bounded by 2).
* `cor:trimrate` (`05_trimming.tex:83-98`): `cor_trimrate_v2`, with the printed sample-size clause ("the sample size from which the
  bounds apply depends on `(P,Q,k,α)` and `r_Q`": `N` is chosen before the density constants and the quantiles), `t_α` any
  `(1−α)`-quantile at which (Q) holds.
* Encoding check for `thm:trimrate`, `cor:trimrate`: `quantile_of_QDensity` (a `p`-quantile at which the law has a density bounded
  below near it is the lower quantile `quantileAt` used by the frozen `Wave30tx` claims).
* `eq:samplesize` (`03_analytic.tex:253-262`) with the sentence `:61-62`: `samplesize`.

Reuses (imported, not copied): `TrimmedMMD/Concentration` (`region`, `empirical`), `TrimmedMMD/Unconditional` (`Dpop`, `Demp`, `setDist`),
`TrimmedMMD/BangBang` (`capped`, `cap`, `kfloor`, `ord`, `qp`), `TrimmedMMD/Projection` (`IsMinNorm`), `TrimmedMMD/Lower` (`alphaLo`),
`TrimmedMMD/Impossible` (`dataLaw`), `TrimmedMMD` (`rn`, `tau`), `Wave4b` (`witness`), `Wave12c` (`witFn`, `quantileAt`, `QDensity`,
`QDensityLower`, `tHat`), `Wave17a` (`sepVal`), `Wave30tp` (`tauP`, `sampleLaw`), `Wave30tr` (`tauA`), `Wave30ts` (`psiPin`, `tauPs`,
`tauCpl`), `Wave30tu` (`ValidThreshold`), `Wave30tu.Full` (`tauFull`), `Wave30tw` (`CrossingFacts`), `Wave30tx` (`IsQuantile`,
`plugDensityFn`), `Wave30tv` (`IsBatchPairing`, `IsBatchRule`, `IsBatchBetRule`, `seqReject`), `Distances.tvDist`.

Encodings (see the card `certify/cards/wave31ta.md`): as in the reused waves. (A1)–(A2): `𝓗` a real Hilbert space (separable where the
printed proof needs it), `φ` strongly measurable, `‖φ x‖ ≤ κ`; `D_φ` any bound `D` on `‖φ(x) − φ(x')‖`. `𝒫₂`: probability measures on `ℝ`
with `P ≤ 2·λ|_{[0,1]}` (density bounded by 2, vanishing off `[0,1]`). "`H_{0,α̂_lo}` is rejected": `α̂_lo` equals a grid level whose test
rejected. The `O_P` statements in the explicit form of the frozen `Wave30tx.cor_trimrate`.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (13 claims: 8 ACCEPT, 5 ACCEPT-WITH-NOTE, none false, verdict READY TO
FREEZE; applied: docstring notes on `bangbang_v2`, `sharp_le_plugin`, `sharp_cpl_counterexample`, `cor_trimrate_v2`, `samplesize`).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31ta

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.Wave12c StatFormal.Wave4b

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The parameters of the class `𝒢 = {x ↦ (f(x) − t)_+ : f ∈ B_𝓗, t ∈ [−κ,κ]}` of `cor:uniform`. -/
def gPar (H : Type*) [NormedAddCommGroup H] (κ : ℝ) : Set (H × ℝ) := {p | ‖p.1‖ ≤ 1 ∧ |p.2| ≤ κ}

/-- `sup_{g ∈ 𝒢} |(P_n − P) g|`, `(P_n − P)g = n⁻¹ Σ_i g(x_i) − ∫ g dP`, `g(x) = (⟨f, φ(x)⟩ − t)_+` (a real `⨆`; the class is nonempty
and uniformly bounded when `‖φ‖ ≤ κ`). -/
def gDev (P : Measure 𝒳) (φ : 𝒳 → H) (κ : ℝ) {n : ℕ} (x : Fin n → 𝒳) : ℝ :=
  ⨆ p : gPar H κ, |(n : ℝ)⁻¹ * ∑ i, max (⟪p.1.1, φ (x i)⟫_ℝ - p.1.2) 0 - ∫ y, max (⟪p.1.1, φ y⟫_ℝ - p.1.2) 0 ∂P|

end Defs

/-- The paper's `τ_{n,m}(α,δ) = min(τ^A, τ^P, τ^{P'})` for a kernel with `k ≥ 0` and constant diagonal, where `τ^{P'}` is the coupled
supremum `τ^{cpl}_{P'}` (`B_analytic.tex:144-147`), `v = √min(κ², D²/2)` and `ρ̄ = D` in `τ^P`. -/
def tauV2Cpl (κ D α δ : ℝ) (n m : ℕ) : ℝ :=
  min (StatFormal.Wave30tr.tauA κ D α δ n m)
    (min (StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m) (StatFormal.Wave30ts.tauCpl D κ α δ n m))

/-- The class `𝒫₂` of `thm:impossible`: a probability measure on `ℝ` with `P ≤ 2·λ|_{[0,1]}`, i.e. concentrated on `[0,1]` with a
density bounded by `2`. -/
def Density2 (P : Measure ℝ) : Prop :=
  IsProbabilityMeasure P ∧ P ≤ (2 : ℝ≥0∞) • volume.restrict (Set.Icc (0 : ℝ) 1)

namespace Claims

/-! ### `prop:bangbang (v2 short)` -/

/-- `prop:bangbang (v2 short)` (`05_trimming.tex:17-35`), one level `α ∈ [0,1)` for both samples: the set `𝒯_α` of minimisers of
`eq:qp` over `Δ_α(n) × Δ_α(m)` is nonempty, convex and compact; (i) at every `(w,v) ∈ 𝒯_α` the witness `d̂ = Σ w_iφ(X_i) − Σ v_jφ(Y_j)` is
the element of minimal norm of `𝒞_α(P_n) − 𝒞_α(Q_m)`, `‖d̂‖ = D̂_α`, and it is the same at every minimiser; (ii) if `D̂_α > 0`, with
`d̂(x) = ⟨d̂, φ(x)⟩`: when `n_α = ⌊n(1−α)⌋ < n`, `w_i = c_α` if `d̂(X_i) < d̂_{(n_α+1)}`, `w_i = 0` if `d̂(X_i) > d̂_{(n_α+1)}`, and the ties
carry `1 − c_α #{i : d̂(X_i) < d̂_{(n_α+1)}}`; when `n_α = n` (the convention `d̂_{(n+1)} = +∞`) every `w_i = c_α`; symmetrically for `v`
with the `(m_α+1)`-th largest value; (iii) if `D̂_α = 0`, `𝒯_α` is the set of feasible pairs with `Σ w_iφ(X_i) = Σ v_jφ(Y_j)`. At
`n_α = n` (only at `α = 0`) the printed tie clause is vacuous (no ties at `+∞`, remaining mass `1 − c_α n = 0`) and is omitted. -/
def bangbang_v2 : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (α : ℝ) (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳),
    StronglyMeasurable φ → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m →
      let T : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
        {p | p ∈ capped n α ×ˢ capped m α ∧
          IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m α) p}
      (T.Nonempty ∧ Convex ℝ T ∧ IsCompact T) ∧
      (∀ p ∈ T, IsMinNorm (region φ α (empirical x) - region φ α (empirical y)) (witness φ x y p) ∧
        ‖witness φ x y p‖ = Demp φ x y α) ∧
      (∀ p ∈ T, ∀ p' ∈ T, witness φ x y p = witness φ x y p') ∧
      (0 < Demp φ x y α → ∀ p ∈ T,
        let dx : Fin n → ℝ := fun i => ⟪witness φ x y p, φ (x i)⟫_ℝ
        let dy : Fin m → ℝ := fun j => ⟪witness φ x y p, φ (y j)⟫_ℝ
        (kfloor n α < n →
          (∀ i, dx i < ord dx (kfloor n α) → p.1 i = cap n α) ∧
          (∀ i, ord dx (kfloor n α) < dx i → p.1 i = 0) ∧
          ∑ i ∈ Finset.univ.filter (fun i => dx i = ord dx (kfloor n α)), p.1 i =
            1 - cap n α * (Finset.univ.filter (fun i => dx i < ord dx (kfloor n α))).card) ∧
        (kfloor n α = n → ∀ i, p.1 i = cap n α) ∧
        (kfloor m α < m →
          (∀ j, ord dy (m - kfloor m α - 1) < dy j → p.2 j = cap m α) ∧
          (∀ j, dy j < ord dy (m - kfloor m α - 1) → p.2 j = 0) ∧
          ∑ j ∈ Finset.univ.filter (fun j => dy j = ord dy (m - kfloor m α - 1)), p.2 j =
            1 - cap m α * (Finset.univ.filter (fun j => ord dy (m - kfloor m α - 1) < dy j)).card) ∧
        (kfloor m α = m → ∀ j, p.2 j = cap m α)) ∧
      (Demp φ x y α = 0 →
        T = {p | p ∈ capped n α ×ˢ capped m α ∧ ∑ i, p.1 i • φ (x i) = ∑ j, p.2 j • φ (y j)})

/-! ### `lem:continuity (v2 short)` and `eq:distmax (v2 short)` -/

/-- `lem:continuity (v2 short)` (`A_regions.tex:74-81`): for every `ᾱ ∈ [0,1)` and `α, α' ∈ [0, ᾱ]`,
`|D_α(P,Q) − D_{α'}(P,Q)| ≤ 4κ(1−ᾱ)⁻²|α − α'|`, for any probability measures (so also for `P_n`, `Q_m`). -/
def continuity_v2 : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ αbar α α' : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ αbar → αbar < 1 → α ∈ Icc 0 αbar → α' ∈ Icc 0 αbar →
      |Dpop φ P Q α - Dpop φ P Q α'| ≤ 4 * κ / (1 - αbar) ^ 2 * |α - α'|

/-- `eq:distmax (v2 short)` (`C_split.tex:32-37`): for nonempty convex weakly compact `A, B ⊆ 𝓗`,
`dist(A, B) = max_{f ∈ B_𝓗} sep(f; A, B)` (`sep` in `EReal`, `Wave17a.sepVal`), the maximum being attained at `f = 0` when
`dist(A,B) = 0` and at `f* = (a* − b*)/‖a* − b*‖` for any nearest points `a*, b*` when `dist(A,B) > 0`. -/
def distmax : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (A B : Set H),
    A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
    IsCompact (toWeakSpace ℝ H '' A) → IsCompact (toWeakSpace ℝ H '' B) →
      IsGreatest ((fun f => StatFormal.Wave17a.sepVal f A B) '' Metric.closedBall (0 : H) 1) (setDist A B : EReal) ∧
      (setDist A B = 0 → StatFormal.Wave17a.sepVal 0 A B = (setDist A B : EReal)) ∧
      ∀ a ∈ A, ∀ b ∈ B, 0 < setDist A B → ‖a - b‖ = setDist A B →
        StatFormal.Wave17a.sepVal ((‖a - b‖⁻¹) • (a - b)) A B = (setDist A B : EReal)

/-! ### `cor:uniform (v2 short)` -/

/-- `cor:uniform (v2 short)` (`D_trimming.tex:345-357`): under (A1)–(A2), for every `n ≥ 1` and `δ ∈ (0,1)`, the event
`E = {sup_{g∈𝒢}|(P_n − P)g| ≤ 4κ/√n + κ√(2log(2/δ)/n)}` (not depending on `α`) is measurable, has probability `≥ 1 − δ`, and on it
`d_H(𝒞_α(P_n), 𝒞_α(P)) ≤ r_n(α,δ) = κ(1−α)⁻¹[4/√n + √(2log(2/δ)/n)]` for every `α ∈ [0,1)`. -/
def uniform_event : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ δ : ℝ) (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 0 < δ → δ < 1 →
      MeasurableSet {x : Fin n → 𝒳 | gDev P φ κ x ≤ 4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n)} ∧
      1 - δ ≤ (Measure.pi fun _ : Fin n => P).real
        {x : Fin n → 𝒳 | gDev P φ κ x ≤ 4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n)} ∧
      ∀ x : Fin n → 𝒳, gDev P φ κ x ≤ 4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n) →
        ∀ α, 0 ≤ α → α < 1 →
          Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤ rn κ α δ n

/-! ### `rem:sharper (v2 short)` and `eq:sharptau (v2 short)` -/

/-- `rem:sharper (v2 short)` (`03_analytic.tex:66-72`), "a smaller threshold": (1) for kernel constants `D > 0`, `v, ρ̄ ≥ 0`,
`τ^{P'}(α,δ) ≤ τ^P(α,δ)` at every `α ∈ [0,1)`; (2) the same at the paper's constants `v = √min(κ², D²/2)`, `ρ̄ = D`, for every `D ≥ 0`;
(3) for the coupled supremum `τ^{cpl}_{P'}` with `D_φ = √2κ` (the Gaussian kernel on `ℝ^d`), `τ^{cpl}_{P'} ≤ τ^P` at the paper's
constants (`v = κ`, `ρ̄ = √2κ`). "Smaller" is read as `≤` (equality occurs, e.g. at `α = 0` when Pinelis' term does not bind). The
case `D = 0` of (2) is the junk identity `0 ≤ 0`: the printed `Ψ_H` is undefined at `D_φ = 0`; in Lean `Ψ_H = 1 > δ`, the admissible
sets are empty and `τ^{P'} = sInf ∅ = 0 = τ^P`. -/
def sharp_le_plugin : Prop :=
  (∀ (D v ρbar α δ : ℝ) (n m : ℕ), 0 < D → 0 ≤ v → 0 ≤ ρbar → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      StatFormal.Wave30ts.tauPs D v ρbar α δ n m ≤ StatFormal.Wave30tp.tauP D v ρbar α δ n m) ∧
    (∀ (κ D α δ : ℝ) (n m : ℕ), 0 ≤ D → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      StatFormal.Wave30ts.tauPs D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m ≤
        StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m) ∧
    ∀ (κ α δ : ℝ) (n m : ℕ), 0 < κ → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      StatFormal.Wave30ts.tauCpl (√2 * κ) κ α δ n m ≤
        StatFormal.Wave30tp.tauP (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) α δ n m

/-- The printed "smaller" fails for the coupled supremum of `B_analytic.tex:144-147` when `D_φ < √2κ`: a kernel with `k ≥ 0` and
constant diagonal `κ² = 1` on two points (e.g. a Gaussian kernel restricted to two points) with `D_φ = 1/10`, at `α = δ = 1/2`,
`n = m = 1`, has `τ^P(α,δ) < τ^{cpl}_{P'}(α,δ)` (paper's constants `v = √min(κ², D_φ²/2)`, `ρ̄ = D_φ` in `τ^P`). Route:
`τ^{cpl}_{P'} ≥ τ^{P'}(u = 0) ≥ κ√(βs) = 2` (below `√(b²)` the McDiarmid term is `1` and Pinelis' term is `≥ 2e^{−1} > ηδ`), while
`τ^P ≈ 0.855`. Not an artefact of `δ = 1/2`: the same kernel at `δ = 0.05`, `n = m = 100`, `α = 1/2` has `τ^P ≈ 0.103 < 0.2 ≤ τ^{cpl}_{P'}`
(critic's numerics). A remedy for the paper: in the coupled version use `v² = min(κ² − u, D_φ²/2)` and `ρ̄ = min(√(κ²+u), D_φ)` (still
valid, and by monotonicity at most the general `τ^{P'}`). The paper's `τ = min(…)` and its validity are unaffected. -/
def sharp_cpl_counterexample : Prop :=
  (∃ φ : Bool → EuclideanSpace ℝ (Fin 2), (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) ∧ (∀ x, ⟪φ x, φ x⟫_ℝ = 1) ∧
      (∀ x x', ‖φ x - φ x'‖ ≤ 1 / 10) ∧ ‖φ true - φ false‖ = 1 / 10) ∧
    StatFormal.Wave30tp.tauP (1 / 10) (√(min (1 ^ 2) ((1 / 10) ^ 2 / 2))) (1 / 10) (1 / 2) (1 / 2) 1 1 <
      StatFormal.Wave30ts.tauCpl (1 / 10) 1 (1 / 2) (1 / 2) 1 1

/-- `eq:sharptau (v2 short)` (`B_analytic.tex:128-136`): the Pinelis term in the printed form, for `a, b² > 0`:
`2exp(t/a − (t/a + b²/a²)log(1 + ta/b²)) = 2exp(−(b²/a²)h(ta/b²))`, `h(x) = (1+x)log(1+x) − x`. -/
def pinelis_h_form : Prop :=
  ∀ a b2 t : ℝ, 0 < a → 0 < b2 →
    StatFormal.Wave30ts.psiPin a b2 t =
      2 * Real.exp (-(b2 / a ^ 2) * ((1 + t * a / b2) * Real.log (1 + t * a / b2) - t * a / b2))

/-! ### The paper's threshold for kernels with `k ≥ 0` and constant diagonal -/

/-- The v2-short `τ_{n,m} = min(τ^A, τ^P, τ^{cpl}_{P'})` (kernel with `k ≥ 0`, `k(x,x) ≡ κ²`, `D` any bound on `‖φ(x) − φ(x')‖`):
valid and nondecreasing (`Wave30tu.ValidThreshold`), `≤ τ^A`, `≤ r_n(·,δ/2) + r_m(·,δ/2)` when `D ≤ 2κ`, continuous on `(0,1)`,
`→ ∞` as `α → 1` when `D, κ > 0`, and every clause of `lem:crossing` and of the paragraph after `eq:alphaest`
(`Wave30tw.CrossingFacts`). -/
def tauV2Cpl_facts : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    Nonempty 𝒳 → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      StatFormal.Wave30tu.ValidThreshold φ n m δ (fun α => tauV2Cpl κ D α δ n m) ∧
      (∀ α ∈ Ico (0 : ℝ) 1, tauV2Cpl κ D α δ n m ≤ StatFormal.Wave30tr.tauA κ D α δ n m) ∧
      (D ≤ 2 * κ → ∀ α ∈ Ico (0 : ℝ) 1, tauV2Cpl κ D α δ n m ≤ tau κ α δ n m) ∧
      ContinuousOn (fun α => tauV2Cpl κ D α δ n m) (Ioo 0 1) ∧
      (0 < D → 0 < κ → Tendsto (fun α => tauV2Cpl κ D α δ n m) (𝓝[<] 1) atTop) ∧
      StatFormal.Wave30tw.CrossingFacts φ κ n m (fun α => tauV2Cpl κ D α δ n m)

/-! ### `cor:lower (v2 short)` -/

/-- `cor:lower (v2 short)` (`04_split.tex:119-132`, proof `C_split.tex:131-139`): a grid `α_1 < ⋯ < α_J` (`α_j ≥ 0`) fixed in advance,
each `H_{0,α_j}` tested by the betting test of `thm:betting` on the same batches and pairs, with any fitting rule and fractions at each
level, `α̂_lo` by `eq:downclosed`. Then the event "`H_{0,α̂_lo}` is rejected (`α̂_lo` is a grid level whose test rejected) and
`TV(P,Q) ≤ α̂_lo`" is measurable with probability `≤ δ`, and `P(α̂_lo > TV(P,Q)) ≤ δ`, for all sample sizes and every pair. -/
def cor_lower_v2 : Prop :=
  ∀ (𝒳 U : Type) [MeasurableSpace 𝒳] [MeasurableSpace U] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ν : Measure U) [IsProbabilityMeasure ν]
    (n m N J : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α : Fin J → ℝ) (δ c : ℝ)
    (g : Fin J → ℕ → U → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : Fin J → (k : ℕ) → U → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    StatFormal.Wave30tv.IsBatchPairing lx ly bat A B → 0 < δ → δ < 1 → 0 < c → c ≤ 1 → StrictMono α →
    (∀ j, 0 ≤ α j) → (∀ j, StatFormal.Wave30tv.IsBatchRule lx ly bat (g j)) →
    (∀ j, StatFormal.Wave30tv.IsBatchBetRule lx ly bat (α j) c (lam j)) →
      MeasurableSet {ω : U × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
          (∃ j, StatFormal.TrimmedMMD.Lower.alphaLo α
              (fun j => StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2) = α j ∧
            StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2) ∧
          StatFormal.Distances.tvDist P Q ≤ StatFormal.TrimmedMMD.Lower.alphaLo α
            (fun j => StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2)} ∧
      (ν.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
        {ω | (∃ j, StatFormal.TrimmedMMD.Lower.alphaLo α
              (fun j => StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2) = α j ∧
            StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2) ∧
          StatFormal.Distances.tvDist P Q ≤ StatFormal.TrimmedMMD.Lower.alphaLo α
            (fun j => StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2)}
          ≤ ENNReal.ofReal δ ∧
      (ν.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
        {ω | StatFormal.Distances.tvDist P Q < StatFormal.TrimmedMMD.Lower.alphaLo α
            (fun j => StatFormal.Wave30tv.seqReject (lam j) (g j) bat A B (α j) δ ω.1 ω.2.1 ω.2.2)}
          ≤ ENNReal.ofReal δ

/-! ### `thm:impossible (v2 short)` -/

/-- `thm:impossible (v2 short)` (`04_split.tex:170-177`): fix `n, m ≥ 1`, `δ ∈ (0,1)`; if a measurable, possibly randomised `Û` has
`Pr_{P,Q}(TV(P,Q) ≤ Û) ≥ 1 − δ` for every pair `(P,Q) ∈ 𝒫₂` (densities on `[0,1]` bounded by `2`), then
`Pr_{P_u,P_u}(Û ≥ 1) ≥ 1 − δ`, `P_u` the uniform law on `[0,1]`. -/
def impossible_two : Prop :=
  ∀ (n m : ℕ) (δ : ℝ) (Ξ : Type) [MeasurableSpace Ξ] (R : Measure Ξ) [IsProbabilityMeasure R]
    (U : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
    1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 → Measurable U →
    (∀ P Q : Measure ℝ, Density2 P → Density2 Q →
      1 - δ ≤ (StatFormal.TrimmedMMD.Impossible.dataLaw n m P Q R).real
        {z | StatFormal.Distances.tvDist P Q ≤ U z}) →
      1 - δ ≤ (StatFormal.TrimmedMMD.Impossible.dataLaw n m (volume.restrict (Set.Icc (0 : ℝ) 1))
          (volume.restrict (Set.Icc (0 : ℝ) 1)) R).real {z | 1 ≤ U z}

/-! ### `thm:trimrate`, `cor:trimrate (v2 short)` -/

/-- Encoding check for `thm:trimrate` and `cor:trimrate` (`05_trimming.tex:50-69`): if `t` is a `p`-quantile of `f` under `P`
(`P(f < t) ≤ p ≤ P(f ≤ t)`) and the law of `f` has a density bounded below by `c > 0` on `[t − ρ, t + ρ]`, `ρ > 0`, then `t` is the
lower quantile `quantileAt P f p = inf{s : P(f ≤ s) ≥ p}` (the `t_α` of the frozen `Wave30tx` claims); in particular such a quantile
is unique. -/
def quantile_of_QDensity : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] (f : 𝒳 → ℝ) (p t ρ c : ℝ),
    Measurable f → 0 < ρ → 0 < c → StatFormal.Wave30tx.IsQuantile P f p t → QDensityLower P f t ρ c →
      quantileAt P f p = t

/-- `cor:trimrate (v2 short)` (`05_trimming.tex:83-98`, printed as a Theorem), in the explicit form of `Wave30tx.cor_trimrate` with the
printed sample-size clause: for every `ε ∈ (0,1)` there is `Λ` (depending on `ε` only) such that for every `(P,Q,k,α)` with (A1)–(A2),
`α ∈ (0,1)`, `D = D_α(P,Q) > 0`, population witness `d*` and window half-width `r_Q = ρ > 0` there is `N` — chosen before the
quantiles `t_α`, `u_α` and the density constants `c_f, C_f, c'_f` — such that whenever (Q) holds at a `(1−α)`-quantile `t_α` of `d*(X)`
with `c_f, C_f` and (Q′) at an `α`-quantile `u_α` of `d*(Y)` with `c'_f`, for all `n, m ≥ N` there is a measurable event of probability
`≥ 1 − ε` on which, at every minimiser of `eq:qp`, `D̂ > 0`, `‖d̂/D̂ − d*/D‖ ≤ ΛV_α/(D√(n∧m))`, `‖d̂ − d*‖ ≤ ΛV_α/√(n∧m)`, and
`P(Â_n △ A*)`, `(1−α)∫|ĝ_n − g*| dP` (all tie functions) are `≤ ΛC_f(κV_α + c_f⁻¹)/√(n∧m)`, `V_α = κ(1−α)⁻¹ + [(1−α)min(c_f,c'_f)]^{−1/2}`,
`A* = {d* < t_α}`, `Â_n = {d̂ < t̂_n}`. `N` may depend on `κ` (printed: a function of `k`) and `d*` (unique, a function of
`(P,Q,k,α)`); it does not depend on `t_α, u_α` (unique under (Q), (Q′): `quantile_of_QDensity`) or on `c_f, C_f, c'_f` (route: the
best constants, essential infimum and supremum of the density on the window, are admissible and every bound is monotone in them). -/
def cor_trimrate_v2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Λ : ℝ, 0 < Λ ∧
    ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α ρ : ℝ) (dstar : H),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < α → α < 1 → 0 < Dpop φ P Q α →
      IsMinNorm (region φ α P - region φ α Q) dstar → 0 < ρ →
        ∃ N : ℕ, ∀ (tα uα cf Cf cf' : ℝ), 0 < cf → 0 < cf' →
          StatFormal.Wave30tx.IsQuantile P (witFn dstar φ) (1 - α) tα →
          QDensity P (witFn dstar φ) tα ρ cf Cf →
          StatFormal.Wave30tx.IsQuantile Q (witFn dstar φ) α uα → QDensityLower Q (witFn dstar φ) uα ρ cf' →
          ∀ n m : ℕ, N ≤ n → N ≤ m →
            ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
              ENNReal.ofReal (1 - ε) ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
              ∀ z ∈ E, ∀ pr ∈ capped n α ×ˢ capped m α,
                IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
                  let D := Dpop φ P Q α
                  let V := κ / (1 - α) + 1 / √((1 - α) * min cf cf')
                  let q := √((min n m : ℕ) : ℝ)
                  let dh := witness φ z.1 z.2 pr
                  let Dh := Demp φ z.1 z.2 α
                  let th := tHat φ dh α z.1
                  0 < Dh ∧
                  ‖Dh⁻¹ • dh - D⁻¹ • dstar‖ ≤ Λ * (V / (D * q)) ∧
                  ‖dh - dstar‖ ≤ Λ * (V / q) ∧
                  P (symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα}) ≤
                    ENNReal.ofReal (Λ * (Cf * (κ * V + 1 / cf) / q)) ∧
                  ∀ ϑ ϑh : 𝒳 → ℝ, (∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1 / (1 - α)) → (∀ x, 0 ≤ ϑh x ∧ ϑh x ≤ 1 / (1 - α)) →
                    (1 - α) * ∫ x, |StatFormal.Wave30tx.plugDensityFn α ϑh (witFn dh φ) th x -
                      StatFormal.Wave30tx.plugDensityFn α ϑ (witFn dstar φ) tα x| ∂P ≤
                        Λ * (Cf * (κ * V + 1 / cf) / q)

/-! ### `eq:samplesize (v2 short)` -/

/-- `eq:samplesize (v2 short)` (`03_analytic.tex:253-262`) and `:61-62`: for the Gaussian constants (`‖φ‖ ≤ κ`, `D_φ = √2κ`, so
`v = √min(κ², D_φ²/2) = κ`) and `n = m`, `τ^P_{n,n}(0,δ) = C₀√(2/n)` with `C₀ = κ[1 + √log(1/δ)]`; hence `τ_{n,n}(0,δ) ≤ C₀√(2/n)` for the
paper's `τ` (general kernel `min(τ^A, τ^P, τ^{P'})` and coupled `min(τ^A, τ^P, τ^{cpl}_{P'})`), and every value `D̂₀ > 0` with
`n > 2(C₀/D̂₀)²` exceeds both, so the test rejects `H_{0,0}` (`τ(0) < D̂₀`). The numeral `C₀ ≈ 2.73` at `δ = 0.05`, `κ = 1` is not
covered. -/
def samplesize : Prop :=
  ∀ (κ δ Dh : ℝ) (n : ℕ), 0 < κ → 0 < δ → δ < 1 → 1 ≤ n →
    StatFormal.Wave30tp.tauP (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) 0 δ n n =
        κ * (1 + √(Real.log (1 / δ))) * √(2 / n) ∧
      StatFormal.Wave30tu.Full.tauFull κ (√2 * κ) 0 δ n n ≤ κ * (1 + √(Real.log (1 / δ))) * √(2 / n) ∧
      tauV2Cpl κ (√2 * κ) 0 δ n n ≤ κ * (1 + √(Real.log (1 / δ))) * √(2 / n) ∧
      (0 < Dh → 2 * (κ * (1 + √(Real.log (1 / δ))) / Dh) ^ 2 < n →
        StatFormal.Wave30tu.Full.tauFull κ (√2 * κ) 0 δ n n < Dh ∧ tauV2Cpl κ (√2 * κ) 0 δ n n < Dh)

end Claims
end StatFormal.Wave31ta
