import StatFormal.Wave30tz.RouteOrder
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Order statistics: regularity, junk ranks, and the extreme empirical quantiles (library)

Library component (untrusted). For values `h : Fin k → ℝ` and the order statistic `h_(r)` (`Wave30tz.ordStat`, the least `v`
with at least `r` values `≤ v`):

* junk ranks: `ordStat h 0 = 0` and `ordStat h r = 0` for `r > k` (the infimum of `ℝ`, resp. of `∅`);
* `ordStat_lipschitz`: for `1 ≤ r ≤ k`, `h ↦ h_(r)` is 1-Lipschitz for the sup metric of `Fin k → ℝ`;
* `measurable_ordStat`: `h ↦ h_(r)` is measurable for every rank `r` (constant at the junk ranks);
* `isEmpQuantile_ordStat_ceil`, `isEmpQuantile_ordStat_floor`: the order statistics of ranks `max 1 ⌈kp⌉` and
  `min k (⌊kp⌋ + 1)` are empirical `p`-quantiles (`#{h_i < q} ≤ kp ≤ #{h_i ≤ q}`) for `p ∈ [0,1]`;
* `ordStat_ceil_le_of_isEmpQuantile` (`p > 0`): the first is the smallest empirical `p`-quantile;
  `le_ordStat_floor_of_isEmpQuantile` (`⌊kp⌋ + 1 ≤ k`): the second is the largest.

The counting facts used are those of `StatFormal.Wave30tz.RouteOrder` (`ordStat_le_iff`, `card_lt_ordStat_lt`, …).
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.PaperRun

open StatFormal.Wave30tz

variable {k : ℕ}

/-- Junk rank `0`: every `v` has at least `0` values below it, so `h_(0) = sInf ℝ = 0`. -/
theorem ordStat_zero (h : Fin k → ℝ) : ordStat h 0 = 0 := by
  unfold ordStat
  have : {v : ℝ | 0 ≤ (univ.filter fun i => h i ≤ v).card} = Set.univ := by
    ext v; simp
  rw [this]
  exact Real.sInf_of_not_bddBelow (fun ⟨b, hb⟩ => by
    have := hb (Set.mem_univ (b - 1)); linarith)

/-- Junk ranks above `k`: no `v` has more than `k` values below it, so `h_(r) = sInf ∅ = 0`. -/
theorem ordStat_of_lt (h : Fin k → ℝ) {r : ℕ} (hr : k < r) : ordStat h r = 0 := by
  unfold ordStat
  have : {v : ℝ | r ≤ (univ.filter fun i => h i ≤ v).card} = ∅ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_le_of_lt (card_filter_le_n h (fun t => t ≤ v)) hr
  rw [this, Real.sInf_empty]

/-- For `1 ≤ r ≤ k` the order statistic is 1-Lipschitz for the sup metric: shifting every value by at most `ε` shifts `h_(r)`
by at most `ε` (`Wave30tz.ordStat_sub_le` in both directions). -/
theorem ordStat_lipschitz {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    LipschitzWith 1 (fun h : Fin k → ℝ => ordStat h r) := by
  refine LipschitzWith.of_dist_le_mul fun h h' => ?_
  simp only [NNReal.coe_one, one_mul]
  have hi : ∀ i, |h i - h' i| ≤ dist h h' := fun i => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist h h' i
  have h1 := ordStat_sub_le (h := h) (h' := h') (ε := dist h h')
    (fun i => by have := (abs_le.mp (hi i)).2; linarith) hr1 hrk
  have h2 := ordStat_sub_le (h := h') (h' := h) (ε := dist h h')
    (fun i => by have := (abs_le.mp (hi i)).1; linarith) hr1 hrk
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- `h ↦ h_(r)` is measurable for every rank `r`: continuous (Lipschitz) for `1 ≤ r ≤ k`, constant `0` otherwise. -/
theorem measurable_ordStat (r : ℕ) : Measurable (fun h : Fin k → ℝ => ordStat h r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · simp only [ordStat_zero]; exact measurable_const
  rcases le_or_gt r k with hrk | hrk
  · exact (ordStat_lipschitz hr1 hrk).continuous.measurable
  · simp only [ordStat_of_lt _ hrk]; exact measurable_const

/-- The rank `max 1 ⌈kp⌉` lies in `[1, k]` for `k ≥ 1`, `p ≤ 1`. -/
theorem ceil_rank_le {p : ℝ} (hk : 1 ≤ k) (hp1 : p ≤ 1) : max 1 ⌈(k : ℝ) * p⌉₊ ≤ k := by
  refine max_le hk (Nat.ceil_le.mpr ?_)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- The order statistic of rank `max 1 ⌈kp⌉` is an empirical `p`-quantile (`k ≥ 1`, `p ∈ [0,1]`). -/
theorem isEmpQuantile_ordStat_ceil (h : Fin k → ℝ) {p : ℝ} (hk : 1 ≤ k) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsEmpQuantile h p (ordStat h (max 1 ⌈(k : ℝ) * p⌉₊)) := by
  set r := max 1 ⌈(k : ℝ) * p⌉₊ with hr
  have hr1 : 1 ≤ r := le_max_left _ _
  have hrk : r ≤ k := ceil_rank_le hk hp1
  have hkp : 0 ≤ (k : ℝ) * p := mul_nonneg (Nat.cast_nonneg k) hp0
  constructor
  · have hlt := card_lt_ordStat_lt h hr1 hrk
    have hle : ((univ.filter fun i => h i < ordStat h r).card : ℝ) + 1 ≤ r := by exact_mod_cast hlt
    have hrle : (r : ℝ) ≤ (k : ℝ) * p + 1 := by
      rw [hr, Nat.cast_max, Nat.cast_one]
      exact max_le (by linarith) (Nat.ceil_lt_add_one hkp).le
    linarith
  · have := card_le_ordStat h hr1 hrk
    have h1 : (k : ℝ) * p ≤ ⌈(k : ℝ) * p⌉₊ := Nat.le_ceil _
    have h2 : (⌈(k : ℝ) * p⌉₊ : ℝ) ≤ r := by exact_mod_cast le_max_right _ _
    have h3 : (r : ℝ) ≤ (univ.filter fun i => h i ≤ ordStat h r).card := by exact_mod_cast this
    linarith

/-- The order statistic of rank `min k (⌊kp⌋ + 1)` is an empirical `p`-quantile (`k ≥ 1`, `p ∈ [0,1]`). -/
theorem isEmpQuantile_ordStat_floor (h : Fin k → ℝ) {p : ℝ} (hk : 1 ≤ k) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsEmpQuantile h p (ordStat h (min k (⌊(k : ℝ) * p⌋₊ + 1))) := by
  set r := min k (⌊(k : ℝ) * p⌋₊ + 1) with hr
  have hr1 : 1 ≤ r := le_min hk (by omega)
  have hrk : r ≤ k := min_le_left _ _
  have hkp : 0 ≤ (k : ℝ) * p := mul_nonneg (Nat.cast_nonneg k) hp0
  constructor
  · have hlt := card_lt_ordStat_lt h hr1 hrk
    have hle : (univ.filter fun i => h i < ordStat h r).card ≤ ⌊(k : ℝ) * p⌋₊ := by
      have : r ≤ ⌊(k : ℝ) * p⌋₊ + 1 := min_le_right _ _
      omega
    calc ((univ.filter fun i => h i < ordStat h r).card : ℝ) ≤ ⌊(k : ℝ) * p⌋₊ := by exact_mod_cast hle
      _ ≤ (k : ℝ) * p := Nat.floor_le hkp
  · have h3 : (r : ℝ) ≤ (univ.filter fun i => h i ≤ ordStat h r).card := by
      exact_mod_cast card_le_ordStat h hr1 hrk
    have hkr : (k : ℝ) * p ≤ r := by
      rw [hr, Nat.cast_min]
      refine le_min ?_ ?_
      · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      · push_cast; exact (Nat.lt_floor_add_one _).le
    linarith

/-- For `p > 0`, the order statistic of rank `⌈kp⌉` is below every empirical `p`-quantile: at least `kp` values are `≤ q`, hence at
least `⌈kp⌉`. -/
theorem ordStat_ceil_le_of_isEmpQuantile (h : Fin k → ℝ) {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hk : 1 ≤ k)
    (hq : IsEmpQuantile h p q) : ordStat h ⌈(k : ℝ) * p⌉₊ ≤ q := by
  have hkp : 0 < (k : ℝ) * p := mul_pos (by exact_mod_cast hk) hp0
  have hr1 : 1 ≤ ⌈(k : ℝ) * p⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hkp).ne'
  have hrk : ⌈(k : ℝ) * p⌉₊ ≤ k := le_trans (le_max_right _ _) (ceil_rank_le hk hp1)
  rw [ordStat_le_iff h hr1 hrk]
  exact Nat.ceil_le.mpr hq.2

/-- If `⌊kp⌋ + 1 ≤ k`, every empirical `p`-quantile is below the order statistic of rank `⌊kp⌋ + 1`: otherwise at least
`⌊kp⌋ + 1 > kp` values would be `< q`. -/
theorem le_ordStat_floor_of_isEmpQuantile (h : Fin k → ℝ) {p q : ℝ} (hp0 : 0 ≤ p) (hr : ⌊(k : ℝ) * p⌋₊ + 1 ≤ k)
    (hq : IsEmpQuantile h p q) : q ≤ ordStat h (⌊(k : ℝ) * p⌋₊ + 1) := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have hkp : 0 ≤ (k : ℝ) * p := mul_nonneg (Nat.cast_nonneg k) hp0
  have hc := card_le_ordStat h (by omega : 1 ≤ ⌊(k : ℝ) * p⌋₊ + 1) hr
  have hsub : (univ.filter fun i => h i ≤ ordStat h (⌊(k : ℝ) * p⌋₊ + 1)) ⊆ univ.filter fun i => h i < q := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    linarith
  have h1 := le_trans hc (card_le_card hsub)
  have h2 : ((⌊(k : ℝ) * p⌋₊ + 1 : ℕ) : ℝ) ≤ (univ.filter fun i => h i < q).card := by exact_mod_cast h1
  have h3 := hq.1
  push_cast at h2
  linarith [Nat.lt_floor_add_one ((k : ℝ) * p)]

end StatFormal.PaperRun
