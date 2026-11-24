import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Extreme quantiles of a bounded measurable function

Library component (trimmed-mmd, the printed cuts `t⋆` (smallest `(1−α)`-quantile) and `u⋆` (largest `α`-quantile)). Untrusted
library code.

A `p`-quantile of `f` under a probability measure `μ` is a `q` with `μ{f < q} ≤ p ≤ μ{f ≤ q}`.

## Main results

* `exists_isLeast_quantile`: for a bounded measurable `f` and `0 < p ≤ 1`, the `p`-quantiles have a least element,
  `t = inf{q : p ≤ μ{f ≤ q}}` (continuity of `μ` from above gives `p ≤ μ{f ≤ t}`, from below `μ{f < t} ≤ p`);
* `quantile_iff_neg`: `q` is a `p`-quantile of `f` iff `−q` is a `(1−p)`-quantile of `−f`;
* `exists_isGreatest_quantile`: for `0 ≤ p < 1`, the `p`-quantiles have a greatest element.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.ExcessRamp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `p`-quantiles of `f` under `μ`. -/
def quantileSet (μ : Measure Ω) (f : Ω → ℝ) (p : ℝ) : Set ℝ :=
  {q | μ.real {x | f x < q} ≤ p ∧ p ≤ μ.real {x | f x ≤ q}}

/-- **The least `p`-quantile exists** for a bounded measurable function and `0 < p ≤ 1`. -/
theorem exists_isLeast_quantile (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : ∃ t, IsLeast (quantileSet μ f p) t := by
  set S : Set ℝ := {q | p ≤ μ.real {x | f x ≤ q}} with hS
  have hmono : ∀ q q', q ≤ q' → q ∈ S → q' ∈ S := fun q q' hqq' hq =>
    hq.trans (measureReal_mono fun x (hx : f x ≤ q) => (hx.trans hqq' : f x ≤ q'))
  have hCS : C ∈ S := by
    have : {x | f x ≤ C} = univ := eq_univ_of_forall fun x => (le_abs_self _).trans (hC x)
    simp only [hS, mem_ofPred_eq, this, probReal_univ]; exact hp1
  have hlow : ∀ q ∈ S, -C ≤ q := by
    intro q hq
    by_contra hlt
    push_neg at hlt
    have : {x | f x ≤ q} = ∅ := eq_empty_of_forall_notMem fun x (hx : f x ≤ q) => by
      linarith [neg_abs_le (f x), hC x]
    simp only [hS, mem_ofPred_eq, this, measureReal_empty] at hq
    linarith
  have hne : S.Nonempty := ⟨C, hCS⟩
  have hbdd : BddBelow S := ⟨-C, hlow⟩
  set t := sInf S with ht
  have hmeas : ∀ q : ℝ, MeasurableSet {x | f x ≤ q} := fun q => measurableSet_le hf measurable_const
  -- `t ∈ S` by continuity from above
  have htS : t ∈ S := by
    have hsn : ∀ n : ℕ, t + 1 / (n + 1 : ℝ) ∈ S := fun n => by
      have hlt : t < t + 1 / (n + 1 : ℝ) := lt_add_of_pos_right _ (by positivity)
      obtain ⟨q, hq, hqlt⟩ := exists_lt_of_csInf_lt hne hlt
      exact hmono q _ hqlt.le hq
    set s : ℕ → Set Ω := fun n => {x | f x ≤ t + 1 / (n + 1 : ℝ)} with hs
    have hanti : Antitone s := fun m n hmn x (hx : f x ≤ t + 1 / (n + 1 : ℝ)) => by
      change f x ≤ t + 1 / (m + 1 : ℝ)
      have : 1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
      linarith
    have hinter : (⋂ n, s n) = {x | f x ≤ t} := by
      ext x
      simp only [mem_iInter, hs, mem_ofPred_eq]
      constructor
      · intro h
        by_contra hgt
        push_neg at hgt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
        linarith [h n]
      · intro h n
        linarith [show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity]
    have htend := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hmeas _).nullMeasurableSet) hanti
      ⟨0, measure_ne_top μ _⟩
    rw [hinter] at htend
    have htend' : Tendsto (fun n => μ.real (s n)) atTop (𝓝 (μ.real {x | f x ≤ t})) :=
      (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend
    exact ge_of_tendsto' htend' fun n => hsn n
  -- `μ{f < t} ≤ p` by continuity from below
  have hlt : μ.real {x | f x < t} ≤ p := by
    have hrn : ∀ n : ℕ, μ.real {x | f x ≤ t - 1 / (n + 1 : ℝ)} < p := fun n => by
      have hlt : t - 1 / (n + 1 : ℝ) < t := sub_lt_self _ (by positivity)
      by_contra hge
      push_neg at hge
      have := csInf_le hbdd (show t - 1 / (n + 1 : ℝ) ∈ S from hge)
      linarith
    set r : ℕ → Set Ω := fun n => {x | f x ≤ t - 1 / (n + 1 : ℝ)} with hr
    have hmon : Monotone r := fun m n hmn x (hx : f x ≤ t - 1 / (m + 1 : ℝ)) => by
      change f x ≤ t - 1 / (n + 1 : ℝ)
      have : 1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
      linarith
    have hunion : (⋃ n, r n) = {x | f x < t} := by
      ext x
      simp only [mem_iUnion, hr, mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn⟩
        linarith [show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity]
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact ⟨n, by linarith⟩
    have htend := tendsto_measure_iUnion_atTop (μ := μ) hmon
    rw [hunion] at htend
    have htend' : Tendsto (fun n => μ.real (r n)) atTop (𝓝 (μ.real {x | f x < t})) :=
      (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend
    exact le_of_tendsto' htend' fun n => (hrn n).le
  refine ⟨t, ⟨hlt, htS⟩, fun q hq => csInf_le hbdd hq.2⟩

/-- `q` is a `p`-quantile of `f` iff `−q` is a `(1−p)`-quantile of `−f`. -/
theorem quantile_iff_neg (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (p q : ℝ) :
    q ∈ quantileSet μ f p ↔ -q ∈ quantileSet μ (fun x => -f x) (1 - p) := by
  have e1 : {x | -f x < -q} = {x | f x ≤ q}ᶜ := by ext x; simp
  have e2 : {x | -f x ≤ -q} = {x | f x < q}ᶜ := by ext x; simp
  simp only [quantileSet, mem_ofPred_eq, e1, e2, probReal_compl_eq_one_sub (measurableSet_le hf measurable_const),
    probReal_compl_eq_one_sub (measurableSet_lt hf measurable_const)]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **The greatest `p`-quantile exists** for a bounded measurable function and `0 ≤ p < 1`. -/
theorem exists_isGreatest_quantile (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : ∃ u, IsGreatest (quantileSet μ f p) u := by
  obtain ⟨t, ht⟩ := exists_isLeast_quantile μ (f := fun x => -f x) hf.neg (C := C) (fun x => by
      rw [abs_neg]; exact hC x)
    (p := 1 - p) (by linarith) (by linarith)
  refine ⟨-t, ?_, fun q hq => ?_⟩
  · rw [quantile_iff_neg μ hf, neg_neg]; exact ht.1
  · have := ht.2 ((quantile_iff_neg μ hf p q).1 hq)
    linarith

end StatFormal.ExcessRamp
