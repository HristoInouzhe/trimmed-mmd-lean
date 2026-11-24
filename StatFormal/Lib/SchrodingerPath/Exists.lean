import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

/-!
# Existence and uniqueness of the static Schrödinger minimiser (generic reference)

For a finite reference measure `R` on `X × Y` and a finite source measure `μ` (arbitrary measurable spaces):
* `static_exists_iff`: a coupling of finite relative entropy that minimises `KL(· ‖ R)` over `Π(μ, ν)` exists iff
  the Schrödinger value `inf_{π ∈ Π(μ,ν)} KL(π ‖ R)` is finite (Tau Ceti
  `exists_isCoupling_klDiv_eq_schroedingerValue`: Csiszár's `L¹`-Cauchy argument from quantitative strict convexity
  plus Fatou);
* `static_unique`: there is at most one such minimiser (Tau Ceti `IsCoupling.eq_of_klDiv_eq_schroedingerValue`,
  strict convexity of `KL`);
* `static_val`: its relative entropy is the Schrödinger value.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory InformationTheory TauCeti
open scoped ENNReal

namespace StatFormal.SchrodingerPath

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {R : Measure (X × Y)} {μ : Measure X}
  {ν : Measure Y}

/-- A static minimiser: a coupling of finite relative entropy minimising `KL(· ‖ R)` over `Π(μ, ν)`. -/
def IsStaticMin (R : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) (π : Measure (X × Y)) : Prop :=
  IsCoupling π μ ν ∧ klDiv π R ≠ ∞ ∧ ∀ π' : Measure (X × Y), IsCoupling π' μ ν → klDiv π R ≤ klDiv π' R

lemma static_val {π : Measure (X × Y)} (h : IsStaticMin R μ ν π) : klDiv π R = schroedingerValue R μ ν :=
  le_antisymm (le_schroedingerValue h.2.2) (schroedingerValue_le_klDiv h.1 R)

theorem static_exists_iff [IsFiniteMeasure μ] [IsFiniteMeasure R] :
    (∃ π, IsStaticMin R μ ν π) ↔ schroedingerValue R μ ν ≠ ∞ := by
  constructor
  · rintro ⟨π, hπ⟩
    exact ne_top_of_le_ne_top hπ.2.1 (schroedingerValue_le_klDiv hπ.1 R)
  · intro h
    obtain ⟨π, hπ, hval⟩ := exists_isCoupling_klDiv_eq_schroedingerValue h
    exact ⟨π, hπ, hval ▸ h, fun π' h' => hval ▸ schroedingerValue_le_klDiv h' R⟩

theorem static_unique [IsFiniteMeasure μ] [IsFiniteMeasure R] {π π' : Measure (X × Y)}
    (h : IsStaticMin R μ ν π) (h' : IsStaticMin R μ ν π') : π = π' :=
  h.1.eq_of_klDiv_eq_schroedingerValue h'.1 (static_val h) (static_val h')
    ((static_val h) ▸ h.2.1)

end StatFormal.SchrodingerPath
