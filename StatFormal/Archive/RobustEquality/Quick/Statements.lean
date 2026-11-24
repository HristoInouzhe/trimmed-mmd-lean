import StatFormal.Archive.RobustEquality.Certificate.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# FROZEN STATEMENTS — robust equality (JASA): `lem:ranges`, `prop:aniso`, `prop:cs-carry`

Sources: `jasa/supp_computation.tex:17-35` (`lem:ranges`), `jasa/supp_common_shift.tex:302-330`
(`prop:aniso`, error J2 once) and `:363-385` (`prop:cs-carry`, error J1 once: the factor `‖A‖²_op` alone is
false for contractions; correct factor `max(1, L²)`).

Scope / encodings (see card):
* `lem:ranges`: `K` a set in a real inner-product space, `c(x₀,x) = ‖x − x₀‖²`, `f_h(x₀,x) = (h x − h x₀)²`;
  "osc_K(h)" via bounds `a ≤ h ≤ b` on `K`; ranges stated pointwise on `K` (the paper: `ν`-a.e.).
* `prop:aniso`: stated for `M ≻ 0` (paper: "for `M ≻ 0` simply `c_M = (x'−x)ᵀM⁻¹(x'−x)`"); the singular case
  with the Moore–Penrose inverse is NOT covered. Sets `B = {Q : inf_{γ ∈ Π(P,Q)} E_γ c_M ≤ β}` on `ℝᵈ`.
* `prop:cs-carry`: `OT_ε` and `W^ν_ε` with Mathlib's `klDiv` (`ℝ≥0∞`), for probability references `ν`
  (the sub-probability convention is NOT covered); `T` `L`-Lipschitz.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti InformationTheory Matrix
open scoped ENNReal

namespace StatFormal.RobustEquality.Quick

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- Anisotropic cost `c_M(x,x') = (x'−x)ᵀ M⁻¹ (x'−x)` (for `M ≻ 0`). -/
def cM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x x' : E d) : ℝ :=
  dotProduct (WithLp.equiv 2 _ (x' - x)) (M⁻¹ *ᵥ WithLp.equiv 2 _ (x' - x))

/-- The anisotropic set's membership: `inf_{γ ∈ Π(P,Q)} E_γ c_M ≤ β` (in `ℝ≥0∞`). -/
def InAniso {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (β : ℝ) (P Q : Measure (E d)) : Prop :=
  (⨅ (γ : Measure ((E d) × (E d))) (_ : IsCoupling γ P Q),
      ∫⁻ z, ENNReal.ofReal (cM M z.1 z.2) ∂γ) ≤ ENNReal.ofReal β

/-- Entropic transport cost `OT_ε(μ,P)` with reference `ν` in the KL term (`W^ν_ε`; `ν = P` gives `OT_ε`). -/
def entCost {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] (ε : ℝ) (μ P ν : Measure X) : ℝ≥0∞ :=
  ⨅ (γ : Measure (X × X)) (_ : IsCoupling γ μ P),
    ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂γ + ENNReal.ofReal ε * klDiv γ (μ.prod ν)

namespace Claims

/-- `lem:ranges` (i)–(iii): a-priori ranges `U ≤ R` for `U(x) = exp{(f_h(x₀,x) − λ c(x₀,x))/(λε)}`. -/
def ranges : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (K : Set F) (h : F → ℝ) (x₀ : F)
    (lam ε : ℝ), 0 < lam → 0 < ε → x₀ ∈ K →
    let U : F → ℝ := fun x => Real.exp (((h x - h x₀) ^ 2 - lam * ‖x - x₀‖ ^ 2) / (lam * ε))
    -- (i) oscillation range
    (∀ a b : ℝ, (∀ x ∈ K, a ≤ h x ∧ h x ≤ b) → ∀ x ∈ K, U x ≤ Real.exp ((b - a) ^ 2 / (lam * ε))) ∧
    -- (ii) Lipschitz range
    (∀ L : ℝ, L ^ 2 ≤ lam → ∀ x ∈ K, |h x - h x₀| ≤ L * ‖x - x₀‖ → U x ≤ 1) ∧
    -- (iii) shell-wise range
    (∀ (J : ℕ) (δ I : ℕ → ℝ) (hJ : 1 ≤ J), δ 0 = 0 → StrictMonoOn δ (Set.Icc 0 J) →
      (∀ x ∈ K, ‖x - x₀‖ ≤ δ J) →
      (∀ j ∈ Finset.Icc 1 J, ∀ x ∈ K, ‖x - x₀‖ ≤ δ j → |h x - h x₀| ≤ I j) →
        ∀ x ∈ K, U x ≤ Real.exp ((Finset.Icc 1 J).sup' (Finset.nonempty_Icc.2 hJ)
          (fun j => I j ^ 2 - lam * δ (j - 1) ^ 2) / (lam * ε)))

/-- `prop:aniso` (i) for `M ≻ 0`: for a linear rule `h = ⟨w,·⟩`, every `Q` in the anisotropic set around
`P` has `W₂²(h#P, h#Q) ≤ β wᵀMw`, and the bound is attained (translation by `t M w`) when `P` is an
empirical centre. -/
def aniso_i : Prop :=
  ∀ (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) (w : E d) (β : ℝ), M.PosDef → 0 ≤ β →
    (∀ (P Q : Measure (E d)), IsProbabilityMeasure P → IsProbabilityMeasure Q → InAniso M β P Q →
      wassersteinEDist 2 (P.map (fun x => inner ℝ w x)) (Q.map (fun x => inner ℝ w x)) ^ 2 ≤
        ENNReal.ofReal (β * dotProduct (WithLp.equiv 2 _ w) (M *ᵥ WithLp.equiv 2 _ w))) ∧
    (∀ (n : ℕ) (x : Fin n → E d), 0 < n →
      ∃ Q : Measure (E d), IsProbabilityMeasure Q ∧ InAniso M β (StatFormal.RobustEquality.Certificate.centre x) Q ∧
        wassersteinEDist 2 ((StatFormal.RobustEquality.Certificate.centre x).map (fun z => inner ℝ w z))
            (Q.map (fun z => inner ℝ w z)) ^ 2 =
          ENNReal.ofReal (β * dotProduct (WithLp.equiv 2 _ w) (M *ᵥ WithLp.equiv 2 _ w)))

/-- `prop:aniso` (ii) for `M ≻ 0`: if `M = E_π uuᵀ` (`u = X' − X`) for a coupling `π` of `P, P'` with finite
second moments, then `E_π c_M(X,X') = d` (`= rank M`), so `P'` is in the set at every `β ≥ d`; and (iii)
`wᵀMw = E_π⟨w,u⟩²`. -/
def aniso_ii_iii : Prop :=
  ∀ (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) (π : Measure ((E d) × (E d))) [IsProbabilityMeasure π],
    M.PosDef → (∀ i j, Integrable (fun z => (z.2 - z.1) i * (z.2 - z.1) j) π) →
    (∀ i j, M i j = ∫ z, (z.2 - z.1) i * (z.2 - z.1) j ∂π) →
      ∫ z, cM M z.1 z.2 ∂π = d ∧
      (∀ β : ℝ, (d : ℝ) ≤ β → InAniso M β (π.map Prod.fst) (π.map Prod.snd)) ∧
      ∀ w : E d, dotProduct (WithLp.equiv 2 _ w) (M *ᵥ WithLp.equiv 2 _ w) =
        ∫ z, (inner ℝ w (z.2 - z.1)) ^ 2 ∂π

/-- `prop:cs-carry`: for `T` `L`-Lipschitz and probability `μ, P, ν`,
`OT_ε(T#μ, T#P) ≤ max(1, L²) OT_ε(μ, P)` and `W^{T#ν}_ε(T#μ, T#P) ≤ max(1, L²) W^ν_ε(μ, P)`. -/
def cs_carry : Prop :=
  ∀ (d d' : ℕ) (T : (E d) → (E d')) (L : NNReal) (ε : ℝ) (μ P ν : Measure (E d)),
    IsProbabilityMeasure μ → IsProbabilityMeasure P → IsProbabilityMeasure ν → 0 < ε →
    LipschitzWith L T →
      entCost ε (μ.map T) (P.map T) (P.map T) ≤ ENNReal.ofReal (max 1 ((L : ℝ) ^ 2)) * entCost ε μ P P ∧
      entCost ε (μ.map T) (P.map T) (ν.map T) ≤ ENNReal.ofReal (max 1 ((L : ℝ) ^ 2)) * entCost ε μ P ν

end Claims
end StatFormal.RobustEquality.Quick
