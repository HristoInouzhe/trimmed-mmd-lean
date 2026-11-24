import StatFormal.Wave31tr.Statements
import StatFormal.Lib.PaperRun.OrdStat


/-!
# Order statistics at data-dependent ranks, and the median heuristic (library)

Library component (untrusted). For values `h : Fin k → ℝ` and the order statistic `h_(r)` (`Wave30tz.ordStat`):

* `measurable_ordStat_rank`: `ω ↦ h(ω)_(r(ω))` is measurable when the values `h` and the rank `r : Ω → ℕ` are (the rank takes
  countably many values; for each fixed rank the order statistic is measurable, `PaperRun.measurable_ordStat`);
* `measurable_card_filter`: the number of indices `p` with `ω ∈ E p`, for measurable events `E p`, is a measurable `ℕ`-valued map;
  in particular `measurable_zeroCount` (the number of zero values);
* `ordStat_nonneg`: order statistics of nonnegative values are nonnegative (at every rank, the junk ranks giving `0`);
* `ordStat_pos_of_zeroCount_lt`: for nonnegative values, the order statistics of ranks above the number of zeros are positive;
* `measurable_medianBw`, `medianBw_pos` (T49 (b) (i)): the median heuristic `Wave31tr.medianBw ρ` of the pair distances is a
  measurable, positive function of the points, for any measurable nonnegative `ρ`. Symmetry of `ρ` and `ρ(a,a) = 0` (which make
  the count of positive distances even, so that both ranks used are those of positive distances) are not needed for positivity:
  the second rank `c + ⌊(k² − c)/2⌋ + 1` always lies in `(c, k²]` when some distance is positive, and the first order
  statistic is at least `0`.
-/

set_option linter.style.longLine false


noncomputable section
open MeasureTheory Finset

namespace StatFormal.KernelRun

open StatFormal.Wave30tz StatFormal.PaperRun StatFormal.Wave31tr

section OrdStat

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

/-- The order statistic at a measurable rank of measurable values is measurable. -/
theorem measurable_ordStat_rank {h : Ω → Fin k → ℝ} {r : Ω → ℕ} (hh : Measurable h) (hr : Measurable r) :
    Measurable fun ω => ordStat (h ω) (r ω) := by
  have hF : Measurable fun q : (Fin k → ℝ) × ℕ => ordStat q.1 q.2 :=
    measurable_from_prod_countable_left fun r => measurable_ordStat r
  exact hF.comp (hh.prodMk hr)

/-- The number of indices whose event holds is a measurable `ℕ`-valued map. -/
theorem measurable_card_filter {N : ℕ} {E : Fin N → Set Ω} (hE : ∀ p, MeasurableSet (E p))
    [∀ ω, DecidablePred fun p => ω ∈ E p] :
    Measurable fun ω => (univ.filter fun p => ω ∈ E p).card := by
  classical
  have hb : Measurable fun ω => fun p : Fin N => decide (ω ∈ E p) := by
    refine Measurable.of_eval fun p => measurable_to_bool ?_
    have : (fun ω => decide (ω ∈ E p)) ⁻¹' {true} = E p := by
      ext ω; simp
    rw [this]; exact hE p
  have e : (fun ω => (univ.filter fun p => ω ∈ E p).card) =
      (fun s : Fin N → Bool => (univ.filter fun p => s p = true).card) ∘ fun ω p => decide (ω ∈ E p) := by
    funext ω
    simp only [Function.comp_apply, decide_eq_true_eq]
  rw [e]
  exact (measurable_of_countable _).comp hb

/-- The number of zero values is measurable. -/
theorem measurable_zeroCount (N : ℕ) : Measurable fun d : Fin N → ℝ => zeroCount d := by
  classical
  have := measurable_card_filter (Ω := Fin N → ℝ) (E := fun p => {d | d p = 0})
    fun p => measurableSet_eq_fun (measurable_pi_apply p) measurable_const
  convert this using 2 with d
  unfold zeroCount
  rfl

/-- Order statistics of nonnegative values are nonnegative, at every rank. -/
theorem ordStat_nonneg {h : Fin k → ℝ} (h0 : ∀ i, 0 ≤ h i) (r : ℕ) : 0 ≤ ordStat h r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · rw [ordStat_zero]
  rcases le_or_gt r k with hrk | hrk
  · exact le_ordStat_of_forall_le h hr1 hrk h0
  · rw [ordStat_of_lt _ hrk]

/-- For nonnegative values, the order statistic of a rank above the number of zeros (and at most `k`) is positive. -/
theorem ordStat_pos_of_zeroCount_lt {h : Fin k → ℝ} (h0 : ∀ i, 0 ≤ h i) {r : ℕ} (hr : zeroCount h < r) (hrk : r ≤ k) :
    0 < ordStat h r := by
  classical
  have hr1 : 1 ≤ r := by omega
  rw [lt_ordStat_iff h hr1 hrk]
  have e : (univ.filter fun i => h i ≤ 0).card = zeroCount h := by
    unfold zeroCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hi => le_antisymm hi (h0 i), fun hi => hi.le⟩
  rw [e]
  exact hr

/-- The number of zero values is at most the number of values. -/
theorem zeroCount_le (h : Fin k → ℝ) : zeroCount h ≤ k := by
  classical
  unfold zeroCount
  exact (Finset.card_filter_le _ _).trans (by simp)

end OrdStat

section Median

variable {E : Type*} [MeasurableSpace E] {ρ : E → E → ℝ}

/-- The pair distances are a measurable function of the points. -/
theorem measurable_pairDist (hρ : Measurable fun p : E × E => ρ p.1 p.2) (k : ℕ) :
    Measurable fun z : Fin k → E => pairDist ρ z :=
  Measurable.of_eval fun p => by
    unfold pairDist
    have h2 : Measurable fun z : Fin k → E => (z (finProdFinEquiv.symm p).1, z (finProdFinEquiv.symm p).2) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact hρ.comp h2

/-- **The median heuristic is measurable** in the points, for a measurable `ρ`. -/
theorem measurable_medianBw (hρ : Measurable fun p : E × E => ρ p.1 p.2) (k : ℕ) :
    Measurable fun z : Fin k → E => medianBw ρ z := by
  classical
  have hd := measurable_pairDist hρ k
  have hc : Measurable fun z : Fin k → E => zeroCount (pairDist ρ z) := (measurable_zeroCount _).comp hd
  have hF : Measurable fun q : (Fin (k * k) → ℝ) × ℕ =>
      if q.2 = k * k then (1 : ℝ) else
        (ordStat q.1 (q.2 + (k * k - q.2) / 2) + ordStat q.1 (q.2 + (k * k - q.2) / 2 + 1)) / 2 :=
    measurable_from_prod_countable_left fun c => by
      by_cases hck : c = k * k
      · simp only [hck, ite_true]; exact measurable_const
      · simp only [hck, ite_false]
        exact ((measurable_ordStat _).add (measurable_ordStat _)).div_const _
  exact hF.comp (hd.prodMk hc)

omit [MeasurableSpace E] in
/-- **The median heuristic is positive**, for a nonnegative `ρ`. -/
theorem medianBw_pos (hρ0 : ∀ a b, 0 ≤ ρ a b) {k : ℕ} (z : Fin k → E) : 0 < medianBw ρ z := by
  unfold medianBw
  split_ifs with hall
  · exact one_pos
  · set d := pairDist ρ z with hd
    have hd0 : ∀ p, 0 ≤ d p := fun p => hρ0 _ _
    have hle := zeroCount_le d
    have hlt : zeroCount d < k * k := lt_of_le_of_ne hle hall
    have h1 := ordStat_nonneg hd0 (zeroCount d + (k * k - zeroCount d) / 2)
    have h2 := ordStat_pos_of_zeroCount_lt hd0 (r := zeroCount d + (k * k - zeroCount d) / 2 + 1) (by omega)
      (by omega)
    linarith

end Median

end StatFormal.KernelRun
