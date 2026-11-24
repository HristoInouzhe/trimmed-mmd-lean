import StatFormal.Archive.RobustEquality.Semidual.Statements
import StatFormal.Lib.Distances.TV

/-!
# FROZEN STATEMENTS — robust equality (JASA): `lem:semidual` (i) strong duality, (iii), (iv)

Source (verbatim in `inventory/extracted/robust-equality-jasa.md`): `lem:semidual`
(`jasa/supp_proofs.tex:63-105`), notation `supp_proofs.tex:35-45`. Builds on the frozen
`RobustEquality/Semidual/Statements.lean` (definitions `gsoft`, `muDisc`; weak duality and increments are
certified there).

Covered:
* (i) strong duality `Θ(Q) = max_f J_Q(f)` with the infimum over couplings attained; every maximiser
  satisfies the first-order condition `e^{−f*_i/ε} = ∫ e^{(g_{f*} − c_i)/ε} dQ` and lies in
  `F_W = {f : f_i − f_j ≤ sup_K (c_i − c_j)}`;
* (iii) subgradient: `Θ(Q') ≥ Θ(Q) + ∫ g̃ d(Q' − Q)` with `g̃ = g_{f*}` for any maximiser `f*` at `Q`;
* (iv) convexity of `Q ↦ Θ(Q)` and `|Θ(Q) − Θ(Q')| ≤ b ‖Q − Q'‖_TV`.
Not covered (declared): weak continuity of `Θ` on `𝒫(K)` (iv, last clause).

Encodings (see card):
* `Θ(Q) = OT_ε(μ, Q)` is the infimum, in `EReal`, of `E_γ c + ε KL(γ ‖ μ⊗Q)` over couplings `γ` of
  `(μ, Q)` on `Fin k × K` (`KL` = the paper's `klRef`), defined here (`OTdisc`);
* `J_Q(f) = ⟨a, f⟩ + ∫ g_f dQ` (`Jdual`);
* `sup_K (c_i − c_j)` enters as any upper bound `B'` of `c_i − c_j` on `K`; `b` as any bound on the
  oscillations `c_i(y) − c_i(y')`;
* setting: any measurable `K`, bounded measurable `c_i` (the paper: compact `K`, continuous `c`) — a
  declared generalisation (the argument is finite-dimensional);
* (iii) is stated with `Θ(Q)` itself on the left (critic: with `J_Q(f*)` it would only restate weak
  duality at `Q'`);
* `‖Q − Q'‖_TV` is `StatFormal.Distances.tvDist` (`sup_A |Q(A) − Q'(A)|`, the paper's convention); the
  mixture `θQ + (1−θ)Q'` uses `ENNReal.ofReal` weights.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.RobustEquality.SemidualStrong

open StatFormal.RobustEquality.Semidual

/-- `OT_ε(μ, Q)` for the discrete first marginal `μ = Σ_i a_i δ_i`, as an infimum over couplings. -/
def OTdisc {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) : EReal :=
  sInf {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
    γ.map Prod.snd = Q ∧
    v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) + (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod Q)}

/-- The semi-dual objective `J_Q(f) = ⟨a, f⟩ + ∫ g_f dQ`. -/
def Jdual {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) (f : Fin k → ℝ) : ℝ :=
  ∑ i, a i * f i + ∫ y, gsoft ε a f c y ∂Q

/-- The standing hypotheses of the lemma. -/
def Setting {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) :
    Prop :=
  0 < ε ∧ (∀ i, 0 < a i) ∧ ∑ i, a i = 1 ∧ (∀ i, Measurable (c i)) ∧ ∃ B, ∀ i y, |c i y| ≤ B

namespace Claims

/-- (i) strong duality: a maximiser `f*` of `J_Q` exists, `Θ(Q) = J_Q(f*)`, and the infimum over
couplings is attained. -/
def strong_duality : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) [IsProbabilityMeasure Q],
    Setting ε a c →
      ∃ fs : Fin k → ℝ, (∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) ∧
        OTdisc ε a c Q = (Jdual ε a c Q fs : EReal) ∧
        ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
          γ.map Prod.snd = Q ∧
          ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) +
              (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod Q) =
            OTdisc ε a c Q

/-- (i) every maximiser satisfies `e^{−f*_i/ε} = ∫ e^{(g_{f*} − c_i)/ε} dQ` and lies in `F_W`. -/
def maximiser_foc : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) [IsProbabilityMeasure Q] (fs : Fin k → ℝ),
    Setting ε a c → (∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) →
      (∀ i, Real.exp (-fs i / ε) = ∫ y, Real.exp ((gsoft ε a fs c y - c i y) / ε) ∂Q) ∧
      (∀ i j (B' : ℝ), (∀ y, c i y - c j y ≤ B') → fs i - fs j ≤ B')

/-- (iii) subgradient: `Θ(Q') ≥ Θ(Q) + ∫ g̃ dQ' − ∫ g̃ dQ`, `g̃ = g_{f*}`, `f*` any maximiser at `Q`. -/
def subgradient : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q Q' : Measure K) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (fs : Fin k → ℝ),
    Setting ε a c → (∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) →
      OTdisc ε a c Q + ((∫ y, gsoft ε a fs c y ∂Q' - ∫ y, gsoft ε a fs c y ∂Q : ℝ) : EReal) ≤
        OTdisc ε a c Q'

/-- (iv) convexity of `Q ↦ Θ(Q)`. -/
def convex : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q Q' : Measure K) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (θ : ℝ),
    Setting ε a c → 0 ≤ θ → θ ≤ 1 →
      OTdisc ε a c (ENNReal.ofReal θ • Q + ENNReal.ofReal (1 - θ) • Q') ≤
        (θ : EReal) * OTdisc ε a c Q + ((1 - θ : ℝ) : EReal) * OTdisc ε a c Q'

/-- (iv) total-variation Lipschitz bound `|Θ(Q) − Θ(Q')| ≤ b ‖Q − Q'‖_TV` (both values finite). -/
def tv_lipschitz : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q Q' : Measure K) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (b : ℝ),
    Setting ε a c → (∀ i y y', c i y - c i y' ≤ b) →
      ∃ t t' : ℝ, OTdisc ε a c Q = t ∧ OTdisc ε a c Q' = t' ∧
        |t - t'| ≤ b * StatFormal.Distances.tvDist Q Q'

end Claims
end StatFormal.RobustEquality.SemidualStrong
