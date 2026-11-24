import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import Mathlib.Order.Filter.ENNReal

/-!
# FROZEN STATEMENTS — trimmed MMD: the downward-closed lower confidence bound `α̂_lo`

Source: `trimmed-mmd/paper.tex` (verbatim in `inventory/extracted/trimmed-mmd.md`): `cor:lower` (l.1175) with
`eq:downclosed` (l.1181), the null `H_{0,α} : TV(P,Q) ≤ α` (l.723) and `thm:split` (l.1160, used only as a
hypothesis). Repaired once (`REVISION_LEDGER.md` I24/F17: downward-closed rule, `≤` in the null).

Covered:
* `downclosed_pathwise`: the "no multiplicity correction" logic — for any rejection pattern and any `t ≥ 0`,
  `α̂_lo > t` forces the existence of a smallest grid level `≥ t` and its rejection;
* `downclosed_measurable_le`: finite-sample form — the event `{α̂_lo > t}` is measurable and has probability
  at most that of rejecting the smallest grid level `≥ t` (and it is empty when every level is `< t`);
* `cor_lower`: `cor:lower` — at `t = TV(P,Q)`, if every test of a *true* null `H_{0,α_j}` has asymptotic
  level `δ` (`limsup_N P_N(reject H_{0,α_j}) ≤ δ`, i.e. `thm:split` as a hypothesis), then
  `limsup_N P_N(α̂_lo > TV(P,Q)) ≤ δ`, with no multiplicity correction.
Not covered (declared): `thm:split` itself (asymptotic normality of `T̂`, bootstrap consistency, the level of
the single test); "rejection certifies `TV > α`" (`lem:separation` + `eq:zeroeq`); the two-sided interval
combining `cor:lower` with `prop:upper`.

Encodings (see card):
* the grid is `α : Fin J → ℝ`, fixed (independent of `N` and of the data); `cor_lower` assumes the paper's
  `α_1 < … < α_J` in `[0,1)` (unused by the proof), the two auxiliary claims assume neither (generalisation):
  "the smallest grid level `≥ t`" is the first index `j₀` with `t ≤ α j₀` (all earlier levels `< t`), which
  for an increasing grid is the smallest level `≥ t` (the paper's "exceeding", strict, also follows: every
  index between `j₀` and the end of the rejected prefix is rejected);
* junk-value audit: no division, `sSup` or `ℕ` subtraction; `δ ∈ (0,1)` is assumed but unused;
* "`H_{0,α_i}` rejected" is membership in a measurable rejection event `R j`; `α̂_lo` is defined pathwise from
  the rejection pattern by `eq:downclosed`, as a `Finset.sup'` (a genuine maximum), with the paper's value `0`
  when no prefix is rejected (no `sSup ∅` junk);
* the asymptotics: experiments indexed by `N : ℕ` on probability spaces `(Ω N, P_N)` (the sample sizes grow
  with `N`); "asymptotically at most `δ`" is `limsup` in `ℝ≥0∞` (no boundedness junk);
* `TV(P,Q)` is `StatFormal.Distances.tvDist` (`sup_A |P(A) − Q(A)|`), for probability measures `P, Q` on the
  sample space, as in `TrimmedMMD/ZeroSet`;
* every probability is of a measurable event (measurability is part of the conclusion);
* what is certified: the pathwise inclusion `{α̂_lo > TV} ⊆ R_{j₀}` plus monotonicity of `limsup`, with
  `thm:split` (per-level asymptotic validity) as a hypothesis; "rejection certifies `TV > α`" is not used.
Hash-lock: DRAFT, not yet in `certify/statements.lock`; on approval this becomes `Lower/Statements.lean`.
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped ENNReal

namespace StatFormal.TrimmedMMD.Lower

open Classical in
/-- `eq:downclosed`: `α̂_lo = max{α_j : H_{0,α_i} rejected for every i ≤ j}`, and `0` if no such `j`
(i.e. if `H_{0,α_1}` is not rejected). -/
def alphaLo {J : ℕ} (α : Fin J → ℝ) (rej : Fin J → Prop) : ℝ :=
  if h : (univ.filter fun j : Fin J => ∀ i ≤ j, rej i).Nonempty then
    (univ.filter fun j : Fin J => ∀ i ≤ j, rej i).sup' h α
  else 0

namespace Claims

/-- The logical core of `cor:lower`: if `α̂_lo > t ≥ 0`, there is a first grid index `j₀` with `t ≤ α_{j₀}`,
and every such first index was rejected. -/
def downclosed_pathwise : Prop :=
  ∀ (J : ℕ) (α : Fin J → ℝ) (rej : Fin J → Prop) (t : ℝ), 0 ≤ t → t < alphaLo α rej →
    (∃ j₀ : Fin J, t ≤ α j₀ ∧ ∀ i < j₀, α i < t) ∧
      ∀ j₀ : Fin J, t ≤ α j₀ → (∀ i < j₀, α i < t) → rej j₀

/-- Finite-sample form: `{α̂_lo > t}` is measurable, contained in the rejection of the smallest grid level
`≥ t` (so its probability is at most that one test's), and empty if every grid level is `< t`. -/
def downclosed_measurable_le : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (J : ℕ) (α : Fin J → ℝ) (R : Fin J → Set Ω) (t : ℝ),
    (∀ j, MeasurableSet (R j)) → 0 ≤ t →
      MeasurableSet {ω | t < alphaLo α (fun j => ω ∈ R j)} ∧
      (∀ j₀ : Fin J, t ≤ α j₀ → (∀ i < j₀, α i < t) →
        P {ω | t < alphaLo α (fun j => ω ∈ R j)} ≤ P (R j₀)) ∧
      ((∀ j, α j < t) → {ω | t < alphaLo α (fun j => ω ∈ R j)} = ∅)

/-- `cor:lower`: if each test of a true null `H_{0,α_j} : TV(P,Q) ≤ α_j` has asymptotic level `δ`
(`thm:split`), then `P_N(α̂_lo > TV(P,Q))` is asymptotically at most `δ`, with no multiplicity correction. -/
def cor_lower : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J : ℕ) (α : Fin J → ℝ) (δ : ℝ)
    (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (PN : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (PN N)]
    (R : ∀ N, Fin J → Set (Ω N)),
    StrictMono α → (∀ j, α j ∈ Ico (0 : ℝ) 1) → 0 < δ → δ < 1 →
    (∀ N j, MeasurableSet (R N j)) →
    (∀ j, StatFormal.Distances.tvDist P Q ≤ α j →
      limsup (fun N => PN N (R N j)) atTop ≤ ENNReal.ofReal δ) →
      (∀ N, MeasurableSet {ω | StatFormal.Distances.tvDist P Q < alphaLo α (fun j => ω ∈ R N j)}) ∧
      limsup (fun N => PN N {ω | StatFormal.Distances.tvDist P Q < alphaLo α (fun j => ω ∈ R N j)}) atTop
        ≤ ENNReal.ofReal δ

end Claims
end StatFormal.TrimmedMMD.Lower
