import StatFormal.Lib.Distances.Product

/-!
# Le Cam's two-point method

Library component F.H (part 3). Untrusted library code.

Conventions: `tvDist` is the usual total-variation distance `sup_A |μ A − ν A|` (values in
`[0,1]` for probability measures); `P^m` is `Measure.pi fun _ : Fin m => P`. Probabilities are
real-valued (`Measure.real`).

## Main results

* `lecam_event`: `P₁(A) − TV(P₀, P₁) ≤ P₀(A)` for measurable `A`;
* `lecam_of_highProb`: if `P₁(A) ≥ 1 − δ` then `P₀(A) ≥ 1 − δ − TV(P₀, P₁)` — the shape of the
  JASA `eq:twopoint` step (take `A = {ρ̂ − OT(μ,P₀) ≥ OT(μ,P₁) − OT(μ,P₀)}`);
* `lecam_test`: `P₀(A) + P₁(Aᶜ) ≥ 1 − TV(P₀, P₁)` (sum of type-I/II errors of any test);
* `one_sub_two_mul_le_tvDist`: if `P₀(A₀) ≥ 1 − δ`, `P₁(A₁) ≥ 1 − δ` and `A₀ ∩ A₁ = ∅`, then
  `1 − 2δ ≤ TV(P₀, P₁)` ("no procedure is valid at both points");
* `m`-sample versions with `TV(P₀^m, P₁^m) ≤ m·TV(P₀,P₁)` and `≤ √(m·KL(P₀‖P₁)/2)`:
  `lecam_of_highProb_pi`, `lecam_of_highProb_pi_kl`, `one_sub_two_mul_le_pi`,
  `one_sub_two_mul_le_sqrt_klDiv_pi`.
-/

noncomputable section
open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace StatFormal.Distances

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {P₀ P₁ : Measure Ω}

/-- **Le Cam event bound.** -/
theorem lecam_event [IsFiniteMeasure P₀] [IsFiniteMeasure P₁] {A : Set Ω}
    (hA : MeasurableSet A) : P₁.real A - tvDist P₀ P₁ ≤ P₀.real A :=
  measureReal_ge_sub_tvDist hA

/-- **Two-point transfer** (`eq:twopoint` shape): an event of `P₁`-probability at least `1 − δ`
has `P₀`-probability at least `1 − δ − TV(P₀, P₁)`. -/
theorem lecam_of_highProb [IsFiniteMeasure P₀] [IsFiniteMeasure P₁] {A : Set Ω}
    (hA : MeasurableSet A) {δ : ℝ} (h : 1 - δ ≤ P₁.real A) :
    1 - δ - tvDist P₀ P₁ ≤ P₀.real A := by
  have := lecam_event (P₀ := P₀) (P₁ := P₁) hA
  linarith

/-- **Le Cam testing bound**: for every test (measurable rejection region `Aᶜ` under `P₀`),
`P₀(A) + P₁(Aᶜ) ≥ 1 − TV(P₀, P₁)`. -/
theorem lecam_test [IsFiniteMeasure P₀] [IsProbabilityMeasure P₁] {A : Set Ω}
    (hA : MeasurableSet A) : 1 - tvDist P₀ P₁ ≤ P₀.real A + P₁.real Aᶜ := by
  have h1 := lecam_event (P₀ := P₀) (P₁ := P₁) hA
  have h2 : P₁.real A + P₁.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hA, probReal_univ]
  linarith

/-- **No procedure is valid at both points**: if `A₀` and `A₁` are disjoint, `P₀(A₀) ≥ 1 − δ`
and `P₁(A₁) ≥ 1 − δ`, then `1 − 2δ ≤ TV(P₀, P₁)`. -/
theorem one_sub_two_mul_le_tvDist [IsFiniteMeasure P₀] [IsProbabilityMeasure P₁]
    {A₀ A₁ : Set Ω} (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁) (hdisj : Disjoint A₀ A₁)
    {δ : ℝ} (h₀ : 1 - δ ≤ P₀.real A₀) (h₁ : 1 - δ ≤ P₁.real A₁) :
    1 - 2 * δ ≤ tvDist P₀ P₁ := by
  have hsum : P₁.real A₀ + P₁.real A₁ ≤ 1 := by
    rw [← measureReal_union hdisj hA₁]
    exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have h := abs_measureReal_sub_le_tvDist (μ := P₀) (ν := P₁) hA₀
  have h' := le_abs_self (P₀.real A₀ - P₁.real A₀)
  linarith

/-! ### `m`-sample versions -/

variable {P Q : Measure α}

/-- `m`-sample two-point transfer with the hybrid bound `TV(P^m, Q^m) ≤ m · TV(P, Q)`. -/
theorem lecam_of_highProb_pi [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (m : ℕ)
    {A : Set (Fin m → α)} (hA : MeasurableSet A) {δ : ℝ}
    (h : 1 - δ ≤ (Measure.pi fun _ : Fin m => Q).real A) :
    1 - δ - m * tvDist P Q ≤ (Measure.pi fun _ : Fin m => P).real A := by
  have h1 := lecam_of_highProb (P₀ := Measure.pi fun _ : Fin m => P) hA h
  have h2 := tvDist_pi_le P Q m
  linarith

/-- `m`-sample two-point transfer with the Pinsker bound `TV(P^m, Q^m) ≤ √(m · KL(P‖Q) / 2)`. -/
theorem lecam_of_highProb_pi_kl [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (m : ℕ)
    (hkl : klDiv P Q ≠ ∞) {A : Set (Fin m → α)} (hA : MeasurableSet A) {δ : ℝ}
    (h : 1 - δ ≤ (Measure.pi fun _ : Fin m => Q).real A) :
    1 - δ - √(m * (klDiv P Q).toReal / 2) ≤ (Measure.pi fun _ : Fin m => P).real A := by
  have h1 := lecam_of_highProb (P₀ := Measure.pi fun _ : Fin m => P) hA h
  have h2 := tvDist_pi_le_sqrt_klDiv P Q m hkl
  linarith

/-- `m`-sample "no procedure valid at both points", hybrid form: `1 − 2δ ≤ m · TV(P, Q)`. -/
theorem one_sub_two_mul_le_pi [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (m : ℕ)
    {A₀ A₁ : Set (Fin m → α)} (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hdisj : Disjoint A₀ A₁) {δ : ℝ}
    (h₀ : 1 - δ ≤ (Measure.pi fun _ : Fin m => P).real A₀)
    (h₁ : 1 - δ ≤ (Measure.pi fun _ : Fin m => Q).real A₁) :
    1 - 2 * δ ≤ m * tvDist P Q :=
  (one_sub_two_mul_le_tvDist hA₀ hA₁ hdisj h₀ h₁).trans (tvDist_pi_le P Q m)

/-- `m`-sample "no procedure valid at both points", Pinsker form:
`1 − 2δ ≤ √(m · KL(P‖Q) / 2)`. -/
theorem one_sub_two_mul_le_sqrt_klDiv_pi [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m : ℕ) (hkl : klDiv P Q ≠ ∞)
    {A₀ A₁ : Set (Fin m → α)} (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hdisj : Disjoint A₀ A₁) {δ : ℝ}
    (h₀ : 1 - δ ≤ (Measure.pi fun _ : Fin m => P).real A₀)
    (h₁ : 1 - δ ≤ (Measure.pi fun _ : Fin m => Q).real A₁) :
    1 - 2 * δ ≤ √(m * (klDiv P Q).toReal / 2) :=
  (one_sub_two_mul_le_tvDist hA₀ hA₁ hdisj h₀ h₁).trans (tvDist_pi_le_sqrt_klDiv P Q m hkl)

end StatFormal.Distances
