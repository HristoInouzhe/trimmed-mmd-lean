import StatFormal.Archive.RobustEquality.Coverage.Statements
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# FROZEN STATEMENTS — robust equality (JASA): `thm:coverage`, random folds (unconditional)

Source: `thm:coverage` (`jasa/main.tex:484`), proof in `jasa/supp_proofs.tex:523-545`; folds as in
`supp_proofs.tex:35-41`. Complements the frozen `RobustEquality/Coverage` statements (`coverage_general` and
the per-fold Hoeffding bound conditional on the fold): here the fold points are themselves random.

Covered: the sample `X_1, …, X_N` i.i.d. `P` is split by a fixed partition into folds; for fold `v`,
`ρ̂_v = OT_ε(P̂_v, P̂_{−v}) + B_c √(log(V/a)/(2 m_v))` with `P̂_{−v}` the empirical law of the `m_v` points
outside fold `v`; then `Pr[OT_ε(P̂, P) ≤ Σ_v w_v ρ̂_v] ≥ 1 − a`.
Not covered (declared): `prop:allpairs` (the all-pairs empirical-Bernstein term); random fold sizes.

Encodings (see card): as in `Coverage/Statements.lean` (labelled atoms, surjection `fold`, enumerations
`e v`, weights `1/N`, `1/n v`, `w_v = n v / N`, ball membership = `OT_ε(P̂,P) ≤ r̂`). Additionally:
* the cost `c : K → K → ℝ` is jointly measurable and bounded, with oscillation `c(x,y) − c(x,y') ≤ B_c`
  (`B_c > 0`): `B_c` is any bound on the cost's oscillation over all of `K` — the paper's `B_c = sup c`
  qualifies since `c ≥ 0`; no topology on `K` is needed (the paper: compact `K`, continuous `c`);
* every fold has a nonempty complement (`m_v ≥ 1`, i.e. `V ≥ 2`), as the radius requires;
* "with probability `≥ 1 − a`" is the existence of a measurable event of that probability inside the
  coverage event (inner-measure form; the outer-measure form would be weaker);
* `OT_ε(P̂_v, P̂_{−v})` enters through `.toReal`; it is always finite (product coupling), so nothing is lost.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.RobustEquality.CoverageRandom

open StatFormal.RobustEquality.SemidualStrong

/-- Empirical law of the points indexed by a finite type (the held-out points of a fold). -/
def empOn {K ι : Type*} [MeasurableSpace K] [Fintype ι] (y : ι → K) : Measure K :=
  ∑ j, ENNReal.ofReal (1 / Fintype.card ι) • Measure.dirac (y j)

/-- The fold-`v` radius `ρ̂_v = OT_ε(P̂_v, P̂_{−v}) + B_c √(log(V/a)/(2 m_v))`. -/
def rhoHat {K : Type*} [MeasurableSpace K] {N V : ℕ} {fold : Fin N → Fin V} {n : Fin V → ℕ}
    (ε : ℝ) (c : K → K → ℝ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (Bc a : ℝ) (v : Fin V)
    (X : Fin N → K) : ℝ :=
  (OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j)))
      (empOn fun i : {i // ¬ fold i = v} => X i)).toReal +
    Bc * √(Real.log (V / a) / (2 * Fintype.card {i // ¬ fold i = v}))

namespace Claims

/-- `thm:coverage` with random folds. -/
def coverage_random_folds : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P : Measure K) [IsProbabilityMeasure P] (N V : ℕ)
    (fold : Fin N → Fin V) (n : Fin V → ℕ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v})
    (c : K → K → ℝ) (B Bc ε a : ℝ),
    Function.Surjective fold → (∀ v, ∃ i, ¬ fold i = v) → Measurable (Function.uncurry c) →
    (∀ x y, |c x y| ≤ B) → 0 < ε → 0 < Bc → (∀ x y y', c x y - c x y' ≤ Bc) → 0 < a → a < 1 → 0 < N →
      ∃ E : Set (Fin N → K), MeasurableSet E ∧ ENNReal.ofReal (1 - a) ≤ Measure.pi (fun _ : Fin N => P) E ∧
        E ⊆ {X : Fin N → K | OTdisc ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (X i)) P ≤
          ((∑ v, ((n v : ℝ) / N) * rhoHat ε c e Bc a v X : ℝ) : EReal)}

end Claims
end StatFormal.RobustEquality.CoverageRandom
