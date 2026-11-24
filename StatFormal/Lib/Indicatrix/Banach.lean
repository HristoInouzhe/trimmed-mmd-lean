import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Basic.Real.ENatENNReal

set_option linter.style.longLine false

/-!
# Banach's indicatrix: the inequality half

For `h : ℝ → ℝ` continuous on `[a,b]`, Banach's counting function (the *indicatrix*)
`N(s) = #{x ∈ [a,b] : h x = s} ∈ [0,∞]` is Borel measurable and `∫⁻ N ≤ V_{[a,b]}(h)`
(Banach 1925; Natanson, *Theory of Functions of a Real Variable*, Ch. VIII §5).

## Route (dyadic counting functions)

* `dyIdx a b k x = min ⌊(x − a)2^k/(b − a)⌋₊ (2^k − 1)`: the index of the dyadic piece of `[a,b]` of
  generation `k` containing `x` (half-open pieces, the last one closed); it is monotone in `x`.
* `dyCount h a b k s = #(dyIdx '' {x ∈ [a,b] : h x = s})`: the number of pieces whose image under `h`
  contains `s`. It is a finite sum of indicators of the intervals `h(piece)` (`dyCount_eq_sum`), so it
  is measurable, and `∫⁻ dyCount = Σ |h(piece)| ≤ Σ V_{piece}(h) ≤ V_{[a,b]}(h)`
  (`lintegral_dyCount_le`; diameters are bounded by the variation, `eVariationOn.add_le_union`).
* `dyCount ≤ N` (an image has at most as many points), and for any finite set of level points the
  dyadic index is eventually injective on it, so `N = liminf_k dyCount_k` (`bcount_eq_liminf`).
* Measurability by `Measurable.liminf`, the inequality by Fatou's lemma (`lintegral_liminf_le`).

## Main results

* `measurable_bcount`, `lintegral_bcount_le`.
* General helpers: `sum_eVariationOn_fibers_le` (the variations on the fibres of a monotone index
  add up to at most the variation), `ediam_image_le_eVariationOn`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Indicatrix

/-- Banach's counting function `N(s) = #{x ∈ [a,b] : h x = s}` in `[0,∞]`. -/
def bcount (h : ℝ → ℝ) (a b s : ℝ) : ℝ≥0∞ :=
  ENat.toENNReal ({x | x ∈ Icc a b ∧ h x = s} : Set ℝ).encard

/-- The dyadic index of generation `k` on `[a,b]`: `min ⌊(x − a)2^k/(b − a)⌋₊ (2^k − 1)`. -/
def dyIdx (a b : ℝ) (k : ℕ) (x : ℝ) : ℕ := min ⌊(x - a) * 2 ^ k / (b - a)⌋₊ (2 ^ k - 1)

/-- The dyadic piece number `i` of generation `k` of `[a,b]`. -/
def dyPiece (a b : ℝ) (k i : ℕ) : Set ℝ := Icc a b ∩ dyIdx a b k ⁻¹' {i}

/-- The dyadic counting function: the number of dyadic pieces of generation `k` whose image under
`h` contains `s`. -/
def dyCount (h : ℝ → ℝ) (a b : ℝ) (k : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ENat.toENNReal (dyIdx a b k '' {x | x ∈ Icc a b ∧ h x = s}).encard

/-! ### General facts on variation -/

/-- The diameter of the image is at most the variation. -/
theorem ediam_image_le_eVariationOn {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) (S : Set ℝ) :
    Metric.ediam (f '' S) ≤ eVariationOn f S := by
  refine Metric.ediam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact eVariationOn.edist_le f hx hy

/-- For a monotone index `g : ℝ → ℕ`, the variations of `f` on the fibres `S ∩ g⁻¹{i}`, `i < m`, add up
to at most the variation on `S ∩ {g < m}`. -/
theorem sum_eVariationOn_fibers_le {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) (S : Set ℝ)
    {g : ℝ → ℕ} (hg : Monotone g) (m : ℕ) :
    ∑ i ∈ Finset.range m, eVariationOn f (S ∩ g ⁻¹' {i}) ≤ eVariationOn f (S ∩ {x | g x < m}) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc _ ≤ eVariationOn f (S ∩ {x | g x < m}) + eVariationOn f (S ∩ g ⁻¹' {m}) := by gcongr
      _ ≤ eVariationOn f ((S ∩ {x | g x < m}) ∪ (S ∩ g ⁻¹' {m})) := by
          refine eVariationOn.add_le_union f ?_
          rintro x ⟨_, hx⟩ y ⟨_, hy⟩
          by_contra hxy
          have h1 := hg (not_le.1 hxy).le
          simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff] at hx hy
          omega
      _ ≤ _ := by
          refine eVariationOn.mono f ?_
          rintro x (⟨hxS, hx⟩ | ⟨hxS, hx⟩) <;> refine ⟨hxS, ?_⟩ <;>
            simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff] at hx ⊢ <;> omega

/-- The fibres of a monotone map `ℝ → ℕ` are order-connected. -/
theorem ordConnected_fiber {g : ℝ → ℕ} (hg : Monotone g) (i : ℕ) : (g ⁻¹' {i}).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  simp only [mem_preimage, mem_singleton_iff] at hx hy ⊢
  exact le_antisymm (hy ▸ hg hz.2) (hx ▸ hg hz.1)

/-! ### The dyadic index -/

variable {a b : ℝ}

theorem dyIdx_mono (hab : a ≤ b) (k : ℕ) : Monotone (dyIdx a b k) := by
  intro x y hxy
  unfold dyIdx
  refine min_le_min (Nat.floor_le_floor ?_) le_rfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (sub_le_sub_right hxy a)
    (by positivity)) (sub_nonneg.2 hab)

theorem dyIdx_lt (k : ℕ) (x : ℝ) : dyIdx a b k x < 2 ^ k :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (pow_pos two_pos k) one_pos)

/-- Points of `[a,b]` more than `(b − a)/2^k` apart have distinct dyadic indices. -/
theorem dyIdx_lt_of_gap (hab : a < b) {k : ℕ} {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x + (b - a) / 2 ^ k < y) : dyIdx a b k x < dyIdx a b k y := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set tx := (x - a) * 2 ^ k / (b - a) with htx
  set ty := (y - a) * 2 ^ k / (b - a) with hty
  have htx0 : 0 ≤ tx := div_nonneg (mul_nonneg (sub_nonneg.2 hx.1) h2k.le) hba.le
  have hty1 : ty ≤ 2 ^ k := by
    rw [hty, div_le_iff₀ hba]
    nlinarith [hy.2]
  have hgap : tx + 1 < ty := by
    have h1 : (b - a) / 2 ^ k < y - x := by linarith
    rw [div_lt_iff₀ h2k] at h1
    have h2 : (y - a) * 2 ^ k = (x - a) * 2 ^ k + (y - x) * 2 ^ k := by ring
    rw [htx, hty, div_add_one hba.ne', div_lt_div_iff_of_pos_right hba]
    linarith
  have hfl : ⌊tx⌋₊ + 1 ≤ ⌊ty⌋₊ := by
    rw [← Nat.floor_add_one htx0]
    exact Nat.floor_le_floor hgap.le
  have hcast : (((2 ^ k - 1 : ℕ)) : ℝ) = 2 ^ k - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hlt : ⌊tx⌋₊ < 2 ^ k - 1 := by
    have h1 : (⌊tx⌋₊ : ℝ) < ((2 ^ k - 1 : ℕ) : ℝ) := by
      rw [hcast]; linarith [Nat.floor_le htx0]
    exact_mod_cast h1
  unfold dyIdx
  rw [← htx, ← hty, min_eq_left hlt.le]
  exact lt_min (by omega) hlt

/-- For a finite set of points of `[a,b]`, the dyadic index is eventually injective on it. -/
theorem eventually_injOn_dyIdx (hab : a ≤ b) (F : Finset ℝ) (hF : (F : Set ℝ) ⊆ Icc a b) :
    ∀ᶠ k in atTop, Set.InjOn (dyIdx a b k) F := by
  rcases hab.eq_or_lt with heq | hlt
  · refine Eventually.of_forall fun k x hx y hy _ => ?_
    have h1 := hF hx; have h2 := hF hy
    rw [← heq, Icc_self, mem_singleton_iff] at h1 h2
    rw [h1, h2]
  · have hlim : Tendsto (fun k : ℕ => (b - a) * (1 / 2 : ℝ) ^ k) atTop (𝓝 ((b - a) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul (b - a)
    rw [mul_zero] at hlim
    have hall : ∀ᶠ k in atTop, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → (b - a) * (1 / 2 : ℝ) ^ k < |p.1 - p.2| := by
      rw [eventually_all_finset]
      intro p _
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun _ h => absurd hp h
      · exact (hlim.eventually (gt_mem_nhds (abs_pos.2 (sub_ne_zero.2 hp)))).mono fun _ h _ => h
    filter_upwards [hall] with k hk
    intro x hx y hy hxy
    by_contra hne
    have hk' := hk (x, y) (Finset.mem_product.2 ⟨hx, hy⟩) hne
    have hpow : (b - a) * (1 / 2 : ℝ) ^ k = (b - a) / 2 ^ k := by
      rw [one_div_pow, mul_one_div]
    rw [hpow] at hk'
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm, abs_of_pos (sub_pos.2 h)] at hk'
      exact absurd hxy (dyIdx_lt_of_gap hlt (hF hx) (hF hy) (by linarith)).ne
    · rw [abs_of_pos (sub_pos.2 h)] at hk'
      exact absurd hxy (dyIdx_lt_of_gap hlt (hF hy) (hF hx) (by linarith)).ne'

/-! ### The dyadic counting functions -/

variable {h : ℝ → ℝ}

theorem dyCount_le_bcount (k : ℕ) (s : ℝ) : dyCount h a b k s ≤ bcount h a b s :=
  ENat.toENNReal_le.2 (encard_image_le _ _)

theorem ordConnected_image_dyPiece (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) (k i : ℕ) :
    (h '' dyPiece a b k i).OrdConnected := by
  have hc : (dyPiece a b k i).OrdConnected :=
    ordConnected_Icc.inter (ordConnected_fiber (dyIdx_mono hab k) i)
  exact (hc.isPreconnected.image h (hh.mono inter_subset_left)).ordConnected

theorem dyCount_eq_sum (k : ℕ) (s : ℝ) :
    dyCount h a b k s = ∑ i ∈ Finset.range (2 ^ k), (h '' dyPiece a b k i).indicator 1 s := by
  classical
  set S := dyIdx a b k '' {x | x ∈ Icc a b ∧ h x = s} with hS
  have hmem : ∀ i, s ∈ h '' dyPiece a b k i ↔ i ∈ S := by
    intro i
    simp only [hS, dyPiece, mem_image, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨hx, hi⟩, hs⟩; exact ⟨x, ⟨hx, hs⟩, hi⟩
    · rintro ⟨x, ⟨hx, hs⟩, hi⟩; exact ⟨x, ⟨hx, hi⟩, hs⟩
  have hT : ((Finset.range (2 ^ k)).filter (· ∈ S) : Set ℕ) = S := by
    ext i
    simp only [Finset.coe_filter, Finset.mem_range, mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro hi
      obtain ⟨x, _, rfl⟩ := hi
      exact ⟨dyIdx_lt k x, ⟨x, by assumption, rfl⟩⟩
  have hsum : ∑ i ∈ Finset.range (2 ^ k), (h '' dyPiece a b k i).indicator (1 : ℝ → ℝ≥0∞) s =
      ∑ i ∈ Finset.range (2 ^ k), if i ∈ S then (1 : ℝ≥0∞) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      rw [indicator_of_mem ((hmem i).2 hi)]; rfl
    · simp only [hi, ↓reduceIte]
      rw [indicator_of_notMem (fun h => hi ((hmem i).1 h))]
  have hcard : S.encard = (((Finset.range (2 ^ k)).filter (· ∈ S)).card : ℕ∞) := by
    conv_lhs => rw [← hT]
    exact encard_coe_eq_coe_finsetCard _
  rw [hsum, Finset.sum_boole, dyCount, ← hS, hcard, ENat.toENNReal_coe]

theorem measurable_dyCount (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) (k : ℕ) :
    Measurable (dyCount h a b k) := by
  have : dyCount h a b k = fun s =>
      ∑ i ∈ Finset.range (2 ^ k), (h '' dyPiece a b k i).indicator (1 : ℝ → ℝ≥0∞) s :=
    funext (dyCount_eq_sum k)
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.indicator (ordConnected_image_dyPiece hab hh k i).measurableSet

theorem lintegral_dyCount_le (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) (k : ℕ) :
    ∫⁻ s, dyCount h a b k s ≤ eVariationOn h (Icc a b) := by
  simp_rw [dyCount_eq_sum]
  rw [lintegral_finsetSum (f := fun i s => (h '' dyPiece a b k i).indicator (1 : ℝ → ℝ≥0∞) s) _
    fun i _ => measurable_const.indicator (ordConnected_image_dyPiece hab hh k i).measurableSet]
  calc ∑ i ∈ Finset.range (2 ^ k), ∫⁻ s, (h '' dyPiece a b k i).indicator 1 s
        = ∑ i ∈ Finset.range (2 ^ k), volume (h '' dyPiece a b k i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact lintegral_indicator_one (ordConnected_image_dyPiece hab hh k i).measurableSet
    _ ≤ ∑ i ∈ Finset.range (2 ^ k), eVariationOn h (dyPiece a b k i) :=
          Finset.sum_le_sum fun i _ =>
            (Real.volume_le_diam _).trans (ediam_image_le_eVariationOn h _)
    _ ≤ eVariationOn h (Icc a b ∩ {x | dyIdx a b k x < 2 ^ k}) :=
          sum_eVariationOn_fibers_le h (Icc a b) (dyIdx_mono hab k) (2 ^ k)
    _ ≤ eVariationOn h (Icc a b) := eVariationOn.mono h inter_subset_left

/-- Every finite set of level points is eventually counted: `|F| ≤ liminf_k dyCount_k(s)`. -/
theorem card_le_liminf_dyCount (hab : a ≤ b) (s : ℝ) (F : Finset ℝ)
    (hF : (F : Set ℝ) ⊆ {x | x ∈ Icc a b ∧ h x = s}) :
    (F.card : ℝ≥0∞) ≤ liminf (fun k => dyCount h a b k s) atTop := by
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_injOn_dyIdx hab F (fun x hx => (hF hx).1)] with k hk
  have h1 : (dyIdx a b k '' (F : Set ℝ)).encard = F.card := by
    rw [hk.encard_image, encard_coe_eq_coe_finsetCard]
  have h2 := encard_le_encard (image_mono (f := dyIdx a b k) hF)
  rw [h1] at h2
  have := ENat.toENNReal_le.2 h2
  rwa [ENat.toENNReal_coe] at this

theorem bcount_le_liminf (hab : a ≤ b) (s : ℝ) :
    bcount h a b s ≤ liminf (fun k => dyCount h a b k s) atTop := by
  set Z : Set ℝ := {x | x ∈ Icc a b ∧ h x = s} with hZ
  by_cases hfin : Z.Finite
  · have := card_le_liminf_dyCount (h := h) hab s hfin.toFinset hfin.coe_toFinset.subset
    rwa [bcount, ← hZ, hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
  · refine le_of_eq_of_le (b := ⊤) ?_ ?_
    · rw [bcount, ← hZ, encard_eq_top_iff.2 hfin, ENat.toENNReal_top]
    · refine top_le_iff.2 (ENNReal.eq_top_of_forall_nnreal_le fun r => ?_)
      obtain ⟨N, hN⟩ := exists_nat_gt (r : ℝ)
      obtain ⟨F, hFZ, hFc⟩ := Set.Infinite.exists_subset_card_eq hfin N
      have := card_le_liminf_dyCount (h := h) hab s F hFZ
      rw [hFc] at this
      refine le_trans ?_ this
      have : (r : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hN.le
      exact this

theorem bcount_eq_liminf (hab : a ≤ b) (s : ℝ) :
    bcount h a b s = liminf (fun k => dyCount h a b k s) atTop :=
  le_antisymm (bcount_le_liminf hab s)
    (liminf_le_of_frequently_le' (Frequently.of_forall fun k => dyCount_le_bcount k s))

/-! ### Banach's indicatrix: measurability and the inequality -/

/-- **Banach's indicatrix is measurable**: for `h` continuous on `[a,b]`, `s ↦ #{x ∈ [a,b] : h x = s}` is
Borel measurable. -/
theorem measurable_bcount (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) :
    Measurable (bcount h a b) := by
  have : bcount h a b = fun s => liminf (fun k => dyCount h a b k s) atTop :=
    funext (bcount_eq_liminf hab)
  rw [this]
  exact Measurable.liminf (measurable_dyCount hab hh)

/-- **Banach's indicatrix inequality**: for `h` continuous on `[a,b]`,
`∫⁻ #{x ∈ [a,b] : h x = s} ds ≤ V_{[a,b]}(h)`. -/
theorem lintegral_bcount_le (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) :
    ∫⁻ s, bcount h a b s ≤ eVariationOn h (Icc a b) := by
  calc ∫⁻ s, bcount h a b s = ∫⁻ s, liminf (fun k => dyCount h a b k s) atTop :=
        lintegral_congr fun s => bcount_eq_liminf hab s
    _ ≤ liminf (fun k => ∫⁻ s, dyCount h a b k s) atTop :=
        lintegral_liminf_le (measurable_dyCount hab hh)
    _ ≤ eVariationOn h (Icc a b) :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun k => lintegral_dyCount_le hab hh k)

end StatFormal.Indicatrix
