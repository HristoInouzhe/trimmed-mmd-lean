import StatFormal.Lib.Donsker.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Data.Finset.Sum

/-!
# Exponential nets: bounded sets in finite dimension, products, disjoint unions (untrusted library code)

* `hasExpNets_of_isBounded`: a bounded `S ⊆ F`, `dim F = d < ∞`. Volume argument: if `T ⊆ S ⊆ B̄(0, R)` is
  `ε`-separated, the balls `B(t, ε/2)` are disjoint and lie in `B(0, R + ε/2)`, so with an additive Haar measure
  (`Measure.addHaar_ball_of_pos`) `|T| (ε/2)^d ≤ (R + ε/2)^d`. A separated `T` of maximal cardinality (`Nat.findGreatest`)
  is an `ε`-net (otherwise add the uncovered point). With `ε = 2^{-j}`: `|T| ≤ (2R 2^j + 1)^d ≤ (2R + 1)^d (2^d)^j`.
* `HasExpNets.prod`: products of nets (the sup metric), `C = C₁C₂`, `A = A₁A₂`.
* `HasExpNets.sum`: disjoint unions of nets, for Mathlib's (non-instance) metric `Metric.metricSpaceSum` on
  `X ⊕ Y` (activated locally; the injections are isometries), `C = |C₁| + |C₂|`, `A = max |A₁| |A₂|`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Metric Set Module

namespace StatFormal.Foundations.Donsker

section Bounded
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Volume bound for an `ε`-separated finite subset of `S ⊆ B̄(0, R)`. -/
lemma card_mul_le_of_separated {S : Set F} {R ε : ℝ} (hR0 : 0 ≤ R) (hR : S ⊆ closedBall 0 R) (hε : 0 < ε)
    (T : Finset S) (hT : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ε ≤ dist t t') :
    (T.card : ℝ) * (ε / 2) ^ finrank ℝ F ≤ (R + ε / 2) ^ finrank ℝ F := by
  let _ : MeasurableSpace F := borel F
  have _ : BorelSpace F := ⟨rfl⟩
  set μ : Measure F := Measure.addHaar
  have hε2 : 0 < ε / 2 := by linarith
  have hdisj : PairwiseDisjoint (↑T) (fun t : S => ball (t : F) (ε / 2)) := by
    intro t ht t' ht' hne
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have h1 := hT t ht t' ht' hne
    rw [mem_ball] at hx hx'
    have h2 : dist (t : F) t' ≤ dist x t + dist x t' := dist_triangle_left _ _ _
    rw [Subtype.dist_eq] at h1
    linarith
  have hsub : (⋃ t ∈ T, ball (t : F) (ε / 2)) ⊆ ball 0 (R + ε / 2) := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨t, -, hx⟩ := hx
    have h1 : dist (t : F) 0 ≤ R := hR t.2
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle x (t : F) 0]
  have hle := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun t _ => measurableSet_ball)] at hle
  simp_rw [Measure.addHaar_ball_of_pos μ _ hε2] at hle
  rw [Finset.sum_const, nsmul_eq_mul, Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < R + ε / 2),
    ← mul_assoc] at hle
  have hpos : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hfin : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hpos hfin).1 hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- An `ε`-net of `S ⊆ B̄(0, R)` of cardinality `≤ (2R/ε + 1)^d`. -/
lemma exists_net_of_subset_closedBall {S : Set F} {R : ℝ} (hR0 : 0 ≤ R) (hR : S ⊆ closedBall 0 R) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T : Finset S, (T.card : ℝ) ≤ (2 * R / ε + 1) ^ finrank ℝ F ∧ ∀ x : S, ∃ t ∈ T, dist x t ≤ ε := by
  classical
  set d := finrank ℝ F
  let Sep : Finset S → Prop := fun T => ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ε < dist t t'
  have hbound : ∀ T, Sep T → (T.card : ℝ) ≤ (2 * R / ε + 1) ^ d := by
    intro T hT
    have h := card_mul_le_of_separated hR0 hR hε T (fun t ht t' ht' hne => (hT t ht t' ht' hne).le)
    have e : (R + ε / 2) ^ d = (2 * R / ε + 1) ^ d * (ε / 2) ^ d := by
      rw [← mul_pow]; congr 1; field_simp
    rw [e] at h
    exact le_of_mul_le_mul_right h (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 * R / ε + 1) ^ d)
  have hP0 : ∃ T, Sep T ∧ T.card = 0 := ⟨∅, by simp [Sep], rfl⟩
  obtain ⟨T, hT, hTk⟩ : ∃ T, Sep T ∧ T.card = Nat.findGreatest (fun k => ∃ T, Sep T ∧ T.card = k) N :=
    Nat.findGreatest_spec (P := fun k => ∃ T, Sep T ∧ T.card = k) (Nat.zero_le N) hP0
  refine ⟨T, hbound T hT, fun x => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxT : x ∉ T := fun hx => by have := hcon x hx; rw [dist_self] at this; linarith
  have hsep : Sep (insert x T) := by
    intro t ht t' ht' hne
    rw [Finset.mem_insert] at ht ht'
    rcases ht with rfl | ht <;> rcases ht' with rfl | ht'
    · exact absurd rfl hne
    · exact hcon t' ht'
    · rw [dist_comm]; exact hcon t ht
    · exact hT t ht t' ht' hne
  have hcard : (insert x T).card = T.card + 1 := Finset.card_insert_of_notMem hxT
  have hle : T.card + 1 ≤ N := by
    have h := hbound _ hsep
    rw [hcard] at h
    exact_mod_cast h.trans hN
  have := Nat.le_findGreatest (P := fun k => ∃ T, Sep T ∧ T.card = k) hle ⟨_, hsep, hcard⟩
  omega

/-- Bounded subsets of a finite-dimensional normed space have exponential nets. -/
theorem hasExpNets_of_isBounded {S : Set F} (hS : Bornology.IsBounded S) : HasExpNets S := by
  obtain ⟨R0, hR0⟩ := hS.subset_closedBall 0
  set R := max R0 0 with hRdef
  have hRnn : 0 ≤ R := le_max_right _ _
  have hR : S ⊆ closedBall 0 R := hR0.trans (closedBall_subset_closedBall (le_max_left _ _))
  set d := finrank ℝ F
  refine ⟨(2 * R + 1) ^ d, 2 ^ d, fun j => ?_⟩
  obtain ⟨T, hT, hnet⟩ := exists_net_of_subset_closedBall hRnn hR (ε := (1 / 2 : ℝ) ^ j) (by positivity)
  refine ⟨T, hT.trans ?_, hnet⟩
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h2 : 2 * R / (1 / 2 : ℝ) ^ j + 1 ≤ (2 * R + 1) * 2 ^ j := by
    rw [one_div, inv_pow, div_inv_eq_mul]
    nlinarith
  have h0 : 0 ≤ 2 * R / (1 / 2 : ℝ) ^ j + 1 := by
    have : 0 ≤ 2 * R / (1 / 2 : ℝ) ^ j := div_nonneg (by linarith) (by positivity)
    linarith
  calc (2 * R / (1 / 2 : ℝ) ^ j + 1) ^ d ≤ ((2 * R + 1) * 2 ^ j) ^ d := pow_le_pow_left₀ h0 h2 d
    _ = (2 * R + 1) ^ d * (2 ^ d) ^ j := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j d]

end Bounded

/-- Products (sup metric) of spaces with exponential nets have exponential nets. -/
theorem HasExpNets.prod {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (hX : HasExpNets X)
    (hY : HasExpNets Y) : HasExpNets (X × Y) := by
  obtain ⟨C1, A1, h1⟩ := hX
  obtain ⟨C2, A2, h2⟩ := hY
  refine ⟨C1 * C2, A1 * A2, fun j => ?_⟩
  obtain ⟨T1, hc1, hn1⟩ := h1 j
  obtain ⟨T2, hc2, hn2⟩ := h2 j
  refine ⟨T1 ×ˢ T2, ?_, fun x => ?_⟩
  · rw [Finset.card_product, Nat.cast_mul, mul_pow]
    calc (T1.card : ℝ) * T2.card ≤ (C1 * A1 ^ j) * (C2 * A2 ^ j) :=
          mul_le_mul hc1 hc2 (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hc1)
      _ = C1 * C2 * (A1 ^ j * A2 ^ j) := by ring
  · obtain ⟨t1, ht1, d1⟩ := hn1 x.1
    obtain ⟨t2, ht2, d2⟩ := hn2 x.2
    exact ⟨(t1, t2), Finset.mem_product.2 ⟨ht1, ht2⟩, by rw [Prod.dist_eq]; exact max_le d1 d2⟩

attribute [local instance] Metric.metricSpaceSum in
/-- Disjoint unions (Mathlib's `Metric.metricSpaceSum`, the injections isometric) of spaces with exponential
nets have exponential nets. -/
theorem HasExpNets.sum {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hX : HasExpNets X) (hY : HasExpNets Y) :
    HasExpNets (X ⊕ Y) := by
  obtain ⟨C1, A1, h1⟩ := hX
  obtain ⟨C2, A2, h2⟩ := hY
  set M := max |A1| |A2|
  refine ⟨|C1| + |C2|, M, fun j => ?_⟩
  obtain ⟨T1, hc1, hn1⟩ := h1 j
  obtain ⟨T2, hc2, hn2⟩ := h2 j
  refine ⟨T1.disjSum T2, ?_, ?_⟩
  · rw [Finset.card_disjSum, Nat.cast_add]
    have e1 : C1 * A1 ^ j ≤ |C1| * M ^ j := (le_abs_self _).trans (by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) j) (abs_nonneg _))
    have e2 : C2 * A2 ^ j ≤ |C2| * M ^ j := (le_abs_self _).trans (by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) j) (abs_nonneg _))
    linarith
  · rintro (a | b)
    · obtain ⟨t, ht, hd⟩ := hn1 a
      exact ⟨Sum.inl t, Finset.inl_mem_disjSum.2 ht, by rw [Metric.isometry_inl.dist_eq]; exact hd⟩
    · obtain ⟨t, ht, hd⟩ := hn2 b
      exact ⟨Sum.inr t, Finset.inr_mem_disjSum.2 ht, by rw [Metric.isometry_inr.dist_eq]; exact hd⟩

end StatFormal.Foundations.Donsker
