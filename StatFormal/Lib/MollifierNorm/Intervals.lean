import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Translation bounds for finite unions of intervals on `ℝ` (library, untrusted)

For an order-connected set `I ⊆ ℝ` (an interval of any type, bounded or not, possibly empty) and `h ∈ ℝ`, the symmetric difference
`I △ (I + h)` has Lebesgue measure at most `2|h|`: the points of `I` that leave `I` under a translation by `t` lie within `|t|` of each
other, so they form a set of diameter at most `|t|` (`Real.volume_le_diam`). For a union of `N` such sets (not necessarily disjoint),
`(⋃ Iᵢ) △ (⋃ (Iᵢ + h)) ⊆ ⋃ (Iᵢ △ (Iᵢ + h))` and subadditivity give `Leb(E △ (E + h)) ≤ 2N|h|`. Here `E + h` is written
`(· - h) ⁻¹' E`.
-/

noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal

namespace StatFormal.MollifierNorm

/-- Two points of an order-connected `I ⊆ ℝ` whose translates by `t` both leave `I` are within `|t|` of each other. -/
theorem dist_le_of_translate_notMem {I : Set ℝ} (hI : I.OrdConnected) {t x y : ℝ}
    (hx : x ∈ I) (hxt : x + t ∉ I) (hy : y ∈ I) (hyt : y + t ∉ I) : dist x y ≤ |t| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [dist_comm]; exact this hy hyt hx hxt (le_of_not_ge hxy)
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy)]
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    exact hxt (hI.out hx hy ⟨by linarith, by linarith⟩)
  · rw [abs_of_neg ht]
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    exact hyt (hI.out hx hy ⟨by linarith, by linarith⟩)

/-- The points of an order-connected `I ⊆ ℝ` whose translate by `t` leaves `I` form a set of measure at most `|t|`. -/
theorem volume_translate_exit_le {I : Set ℝ} (hI : I.OrdConnected) (t : ℝ) :
    volume {x | x ∈ I ∧ x + t ∉ I} ≤ ENNReal.ofReal |t| := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun x hx y hy => ?_)
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_le_of_translate_notMem hI hx.1 hx.2 hy.1 hy.2)

/-- **One interval**: `Leb(I △ (I + h)) ≤ 2|h|` for an order-connected `I ⊆ ℝ`, with `I + h = (· - h) ⁻¹' I`. -/
theorem volume_symmDiff_translate_le {I : Set ℝ} (hI : I.OrdConnected) (h : ℝ) :
    volume (I ∆ ((· - h) ⁻¹' I)) ≤ ENNReal.ofReal (2 * |h|) := by
  have h1 : I \ ((· - h) ⁻¹' I) = {x | x ∈ I ∧ x + (-h) ∉ I} := by
    ext x; simp [sub_eq_add_neg]
  have h2 : ((· - h) ⁻¹' I) \ I = (· + -h) ⁻¹' {y | y ∈ I ∧ y + h ∉ I} := by
    ext x; simp [sub_eq_add_neg]
  rw [Set.symmDiff_def]
  refine (measure_union_le _ _).trans ?_
  rw [h1, h2, measure_preimage_add_right volume (-h), show 2 * |h| = |-h| + |h| by rw [abs_neg]; ring,
    ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  · exact add_le_add (volume_translate_exit_le hI (-h)) (volume_translate_exit_le hI h)

/-- **Finite unions of intervals** (`Π = 2N`): for `N` order-connected sets `Iᵢ ⊆ ℝ` (not necessarily disjoint) and
`E = ⋃ Iᵢ`, `Leb(E △ (E + h)) ≤ 2N|h|`. -/
theorem volume_symmDiff_iUnion_translate_le (N : ℕ) (I : Fin N → Set ℝ) (hI : ∀ i, (I i).OrdConnected) (h : ℝ) :
    volume ((⋃ i, I i) ∆ ((· - h) ⁻¹' (⋃ i, I i))) ≤ ENNReal.ofReal (2 * N * |h|) := by
  rw [Set.preimage_iUnion]
  calc volume ((⋃ i, I i) ∆ (⋃ i, (· - h) ⁻¹' I i))
      ≤ volume (⋃ i, I i ∆ ((· - h) ⁻¹' I i)) := measure_mono iUnion_symmDiff_iUnion_subset
    _ ≤ ∑ i, volume (I i ∆ ((· - h) ⁻¹' I i)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin N, ENNReal.ofReal (2 * |h|) := Finset.sum_le_sum fun i _ => volume_symmDiff_translate_le (hI i) h
    _ = ENNReal.ofReal (2 * N * |h|) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      ring_nf

end StatFormal.MollifierNorm
