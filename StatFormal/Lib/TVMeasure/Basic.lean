import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import StatFormal.Lib.Distances.TV

/-!
# The total variation measure `|P − Q|`, `P ∧ Q` and densities (library, untrusted)

For finite measures `P, Q` on any measurable space, the total variation measure of the signed measure `P − Q` is
`(P − Q) + (Q − P)` (measure subtraction; Mathlib's `toJordanDecomposition_toSignedMeasure_sub`). When `P, Q` have densities
`p, q ≥ 0` with respect to a common measure `μ`:

* `P − Q = (p − q)₊ · μ` (`sub_eq_withDensity_ofReal`);
* `|P − Q| = |p − q| · μ` (`totalVariation_eq_withDensity_abs`);
* `P ∧ Q = min(p, q) · μ` (`inf_eq_withDensity_min`, from `withDensity_inf`: the infimum in the lattice of measures of two
  measures with densities has the pointwise minimum as density);
* `P − P ∧ Q = P − Q` (`sub_inf_eq_sub_of_withDensity`).

Every pair of finite measures has such densities with respect to `μ = P + Q` (`eq_withDensity_ofReal_rnDeriv`), so the
identities `P − P ∧ Q = P − Q` (`sub_inf_eq_sub`), `|P − Q| = (P − P ∧ Q) + (Q − P ∧ Q)` hold in general, and for probability
measures `|P − Q|(𝒳) = 2·TV(P, Q)`, `(P ∧ Q)(𝒳) = 1 − TV(P, Q)` (`totalVariation_univ_eq`, `inf_univ_eq`).

Reference: Halmos, *Measure Theory*, §29 (Jordan decomposition and its minimality); the density formulas are the standard
`|P − Q| = |p − q| dμ` (e.g. Tsybakov, *Introduction to Nonparametric Estimation*, Lemma 2.1).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace StatFormal.TVMeasure

variable {α : Type*} [MeasurableSpace α]

/-- The total variation measure of `P − Q` is `(P − Q) + (Q − P)` (measure subtraction). -/
theorem totalVariation_sub_eq (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (P.toSignedMeasure - Q.toSignedMeasure).totalVariation = (P - Q) + (Q - P) := by
  rw [SignedMeasure.totalVariation, Measure.toJordanDecomposition_toSignedMeasure_sub]
  rfl

/-- The infimum (in the complete lattice of measures) of `f · μ` and `g · μ` is `(f ⊓ g) · μ`. -/
theorem withDensity_inf (μ : Measure α) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity f ⊓ μ.withDensity g = μ.withDensity (f ⊓ g) := by
  refine le_antisymm ?_ (le_inf (withDensity_mono (Eventually.of_forall fun x => inf_le_left))
    (withDensity_mono (Eventually.of_forall fun x => inf_le_right)))
  refine Measure.le_iff.2 fun s hs => ?_
  set t := {x | f x ≤ g x} with ht_def
  have ht : MeasurableSet t := measurableSet_le hf hg
  rw [← measure_inter_add_sdiff s ht, withDensity_apply _ hs, ← lintegral_inter_add_sdiff _ s ht]
  gcongr
  · refine (Measure.le_iff'.1 inf_le_left _).trans ?_
    rw [withDensity_apply _ (hs.inter ht)]
    refine le_of_eq (setLIntegral_congr_fun (hs.inter ht) fun x hx => ?_)
    have : f x ≤ g x := hx.2
    simp [Pi.inf_apply, inf_eq_left.2 this]
  · refine (Measure.le_iff'.1 inf_le_right _).trans ?_
    rw [withDensity_apply _ (hs.diff ht)]
    refine le_of_eq (setLIntegral_congr_fun (hs.diff ht) fun x hx => ?_)
    have : g x ≤ f x := le_of_lt (not_le.1 hx.2)
    simp [Pi.inf_apply, inf_eq_right.2 this]

/-- A finite measure `μ ≪ ν` is `ν.withDensity` of the real version of its Radon–Nikodym derivative. -/
theorem eq_withDensity_ofReal_rnDeriv (μ ν : Measure α) [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (h : μ ≪ ν) :
    μ = ν.withDensity (fun x => ENNReal.ofReal (μ.rnDeriv ν x).toReal) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ν h]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
  rw [ENNReal.ofReal_toReal hx]

/-- For finite `P, Q`, `P = (P + Q).withDensity (dP/d(P+Q))` (real version). -/
theorem eq_withDensity_add_left (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    P = (P + Q).withDensity (fun x => ENNReal.ofReal (P.rnDeriv (P + Q) x).toReal) :=
  eq_withDensity_ofReal_rnDeriv P (P + Q) (Measure.AbsolutelyContinuous.rfl.add_right Q)

/-- For finite `P, Q`, `Q = (P + Q).withDensity (dQ/d(P+Q))` (real version). -/
theorem eq_withDensity_add_right (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Q = (P + Q).withDensity (fun x => ENNReal.ofReal (Q.rnDeriv (P + Q) x).toReal) :=
  eq_withDensity_ofReal_rnDeriv Q (P + Q) (Measure.AbsolutelyContinuous.rfl.add_right' P)

section Densities

variable {μ P Q : Measure α} {p q : α → ℝ}

/-- `P − Q = (p − q)₊ · μ` when `P = p · μ`, `Q = q · μ` (`Q` finite, `q ≥ 0`). -/
theorem sub_eq_withDensity_ofReal [IsFiniteMeasure Q] (hp : Measurable p) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (q x))) :
    P - Q = μ.withDensity (fun x => ENNReal.ofReal (p x - q x)) := by
  subst hP hQ
  rw [← Measure.withDensity_sub (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  simp [ENNReal.ofReal_sub _ (hq0 x)]

/-- `|P − Q| = |p − q| · μ` when `P = p · μ`, `Q = q · μ` (finite, `p, q ≥ 0`). -/
theorem totalVariation_eq_withDensity_abs [IsFiniteMeasure P] [IsFiniteMeasure Q] (hp : Measurable p)
    (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (q x))) :
    (P.toSignedMeasure - Q.toSignedMeasure).totalVariation = μ.withDensity (fun x => ENNReal.ofReal |p x - q x|) := by
  rw [totalVariation_sub_eq, sub_eq_withDensity_ofReal hp hq hq0 hP hQ, sub_eq_withDensity_ofReal hq hp hp0 hQ hP,
    ← withDensity_add_left (by fun_prop)]
  congr 1
  ext x
  simp only [Pi.add_apply]
  rcases le_total (p x) (q x) with h | h
  · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_add, abs_of_nonpos (by linarith), neg_sub]
  · rw [ENNReal.ofReal_of_nonpos (p := q x - p x) (by linarith), add_zero, abs_of_nonneg (by linarith)]

/-- `P ∧ Q = min(p, q) · μ` when `P = p · μ`, `Q = q · μ`. -/
theorem inf_eq_withDensity_min (hp : Measurable p) (hq : Measurable q)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (q x))) :
    P ⊓ Q = μ.withDensity (fun x => ENNReal.ofReal (min (p x) (q x))) := by
  subst hP hQ
  rw [withDensity_inf μ (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  simp [Pi.inf_apply, ENNReal.ofReal_min]

/-- `P − P ∧ Q = P − Q` when `P = p · μ`, `Q = q · μ` (finite, `p, q ≥ 0`). -/
theorem sub_inf_eq_sub_of_withDensity [IsFiniteMeasure P] [IsFiniteMeasure Q] (hp : Measurable p)
    (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (q x))) :
    P - P ⊓ Q = P - Q := by
  have : IsFiniteMeasure (P ⊓ Q) := isFiniteMeasure_of_le P inf_le_left
  rw [sub_eq_withDensity_ofReal hp (hp.min hq) (fun x => le_min (hp0 x) (hq0 x)) hP
      (inf_eq_withDensity_min hp hq hP hQ), sub_eq_withDensity_ofReal hp hq hq0 hP hQ]
  congr 1
  ext x
  rcases le_total (p x) (q x) with h | h
  · rw [min_eq_left h, sub_self, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos (by linarith)]
  · rw [min_eq_right h]

/-- If `p ≤ q` `μ`-a.e. on a measurable `S`, then `(P − Q)(S) = 0`. -/
theorem sub_apply_eq_zero_of_ae_le [IsFiniteMeasure Q] (hp : Measurable p) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (q x)))
    {S : Set α} (hS : MeasurableSet S) (hle : ∀ᵐ x ∂μ, x ∈ S → p x ≤ q x) : (P - Q) S = 0 := by
  rw [sub_eq_withDensity_ofReal hp hq hq0 hP hQ, withDensity_apply _ hS]
  rw [setLIntegral_congr_fun_ae (g := fun _ => 0) hS
    (hle.mono fun x hx hxS => ENNReal.ofReal_of_nonpos (sub_nonpos.2 (hx hxS)))]
  simp

/-- `∫ h d(w · μ) = ∫ h w dμ` for a measurable density `w ≥ 0`. -/
theorem integral_withDensity_ofReal {w : α → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (h : α → ℝ) :
    ∫ x, h x ∂μ.withDensity (fun x => ENNReal.ofReal (w x)) = ∫ x, h x * w x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  ext x
  rw [ENNReal.toReal_ofReal (hw0 x), smul_eq_mul, mul_comm]

end Densities

/-- For finite measures, `P − P ∧ Q = P − Q`. -/
theorem sub_inf_eq_sub (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] : P - P ⊓ Q = P - Q :=
  sub_inf_eq_sub_of_withDensity (Measure.measurable_rnDeriv _ _).ennreal_toReal
    (Measure.measurable_rnDeriv _ _).ennreal_toReal (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (eq_withDensity_add_left P Q) (eq_withDensity_add_right P Q)

/-- For finite measures, `|P − Q| = (P − P ∧ Q) + (Q − P ∧ Q)`. -/
theorem totalVariation_eq_sub_inf (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (P.toSignedMeasure - Q.toSignedMeasure).totalVariation = (P - P ⊓ Q) + (Q - P ⊓ Q) := by
  rw [totalVariation_sub_eq, sub_inf_eq_sub, inf_comm, sub_inf_eq_sub]

/-- For probability measures, `|P − Q|(univ) = 2·TV(P, Q)`. -/
theorem totalVariation_univ_eq (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (P.toSignedMeasure - Q.toSignedMeasure).totalVariation univ = ENNReal.ofReal (2 * Distances.tvDist P Q) := by
  rw [Distances.tvDist_eq_totalVariation_div_two_of_prob, mul_div_cancel₀ _ two_ne_zero,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- For probability measures, `(P ∧ Q)(univ) = 1 − TV(P, Q)`. -/
theorem inf_univ_eq (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (P ⊓ Q) univ = ENNReal.ofReal (1 - Distances.tvDist P Q) := by
  have hfin : IsFiniteMeasure (P ⊓ Q) := isFiniteMeasure_of_le P inf_le_left
  have hm1 : (P ⊓ Q) univ ≤ 1 := by
    calc (P ⊓ Q) univ ≤ P univ := Measure.le_iff'.1 inf_le_left _
      _ = 1 := measure_univ
  have hP : (P - P ⊓ Q) univ = 1 - (P ⊓ Q) univ := by
    rw [Measure.sub_apply MeasurableSet.univ inf_le_left, measure_univ]
  have hQ : (Q - P ⊓ Q) univ = 1 - (P ⊓ Q) univ := by
    rw [Measure.sub_apply MeasurableSet.univ inf_le_right, measure_univ]
  have h := totalVariation_univ_eq P Q
  rw [totalVariation_eq_sub_inf, Measure.add_apply, hP, hQ] at h
  set m := (P ⊓ Q) univ with hm
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hm1
  have hr : ((1 - m) + (1 - m)).toReal = (ENNReal.ofReal (2 * Distances.tvDist P Q)).toReal := by rw [h]
  rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_sub_of_le hm1 ENNReal.one_ne_top,
    ENNReal.toReal_ofReal (by have := Distances.tvDist_nonneg P Q; positivity)] at hr
  simp only [ENNReal.toReal_one] at hr
  rw [← ENNReal.ofReal_toReal hmt]
  congr 1
  linarith

end StatFormal.TVMeasure
