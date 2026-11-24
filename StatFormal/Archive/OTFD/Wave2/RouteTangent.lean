import StatFormal.Archive.OTFD.Wave2.Statements
import StatFormal.Archive.OTFD.Bands.Proofs
import StatFormal.Archive.OTFD.Bands2.RouteSaturation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Order.Compact

/-!
# Route: T `prop:caps` (`eq:dual`, `eq:caps`, `eq:polytope`, `eq:leadcaps`, knapsack)
-/

noncomputable section
open Finset Matrix

namespace StatFormal.OTFD.Wave2

open StatFormal.OTFD.Bands StatFormal.OTFD.Bands2

variable {n K : ℕ}

/-! ### Shared lemmas -/

lemma dot_le_eucl (x y : Fin K → ℝ) : x ⬝ᵥ y ≤ eucl x * eucl y := by
  unfold eucl
  rw [← Real.sqrt_mul (by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))]
  apply le_trans (le_abs_self _)
  apply Real.abs_le_sqrt
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simp only [dotProduct]
  simpa [sq] using this

lemma eucl_nonneg (x : Fin K → ℝ) : 0 ≤ eucl x := Real.sqrt_nonneg _

lemma gap_le_at {a : Fin n → ℝ} {b : Fin n → Fin K → ℝ} {A : Set (Fin K → ℝ)} (j : Fin n)
    {u : Fin K → ℝ} (hu : u ∈ A) : gap a b A j ≤ (⨆ k, score a b k u) - score a b j u := by
  have : Nonempty (Fin n) := ⟨j⟩
  refine csInf_le ⟨0, ?_⟩ ⟨u, hu, rfl⟩
  rintro _ ⟨u', _, rfl⟩
  exact sub_nonneg.mpr (le_ciSup (Finite.bddAbove_range (fun k => score a b k u')) j)

lemma softmax_mem_simplex (hn : 0 < n) (x : Fin n → ℝ) : (fun j => softmax x j) ∈ simplex n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpos : 0 < ∑ k, Real.exp (x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  refine ⟨fun j => div_nonneg (Real.exp_pos _).le hpos.le, ?_⟩
  unfold softmax
  rw [← Finset.sum_div, div_self hpos.ne']

lemma mem_region_of_mem {E : Type*} [AddCommGroup E] [Module ℝ E] {κ q : Fin n → ℝ}
    (v : Fin n → E) (h : q ∈ cappedSimplex κ) : ∑ j, q j • v j ∈ tangentRegion κ v :=
  ⟨q, h, rfl⟩

/-! ### Claims -/

theorem tangent_dual : Claims.tangent_dual := by
  intro n K a b A j w σA hA hw hσ
  exact band_dual_cert n K a b A j w σA hA hw hσ

theorem tangent_caps_entropic : Claims.tangent_caps_entropic := by
  intro n K E _ _ a b A ε δlow v u hn hε hu hδ
  have hmem : entWeights a b ε u ∈ cappedSimplex (fun j => Real.exp (-δlow j / ε)) :=
    ⟨softmax_mem_simplex hn _, fun j =>
      band_cap_entropic n K a b ε (δlow j) j u hε ((hδ j).trans (gap_le_at j hu))⟩
  exact ⟨hmem, mem_region_of_mem v hmem⟩

theorem tangent_caps_quadratic : Claims.tangent_caps_quadratic := by
  intro n K E _ _ a b A lam δlow v u q hlam hu hδ hq
  have hq' : IsSimplexProj (fun k => score a b k u / (lam / ((1 : ℕ) : ℝ))) q := by
    simpa using hq
  have hmem : q ∈ cappedSimplex (fun j => max 0 (1 - δlow j / lam)) := by
    refine ⟨hq.1, fun j => ?_⟩
    have := band_cap_quadratic n K 1 a b lam (δlow j) j u q hlam one_pos
      ((hδ j).trans (gap_le_at j hu)) hq'
    simpa using this
  exact ⟨hmem, mem_region_of_mem v hmem⟩

theorem tangent_lead_caps : Claims.tangent_lead_caps := by
  intro n K E _ _ a b A ε ρ δlow v u hn hε hρ hu hδ
  have hlead : ∀ j, entWeights a b ε u j ≤ leadCap ε a b ρ j := by
    intro j
    apply sat_cap_entropic n K a b ε (leadGap a b ρ j) j u hε
    intro l _
    unfold score leadGap
    have h1 := dot_le_eucl (b j - b l) u
    have h2 : eucl (b j - b l) * eucl u ≤ ρ * eucl (b j - b l) := by
      rw [mul_comm ρ]
      exact mul_le_mul_of_nonneg_left (hρ u hu) (eucl_nonneg _)
    rw [sub_dotProduct] at h1
    linarith
  have hent := (tangent_caps_entropic n K E a b A ε δlow v u hn hε hu hδ).1
  have hmem : entWeights a b ε u ∈
      cappedSimplex (fun j => min (Real.exp (-δlow j / ε)) (leadCap ε a b ρ j)) :=
    ⟨hent.1, fun j => le_min (hent.2 j) (hlead j)⟩
  exact ⟨hlead, hmem, mem_region_of_mem v hmem⟩

/-! ### Knapsack -/

lemma greedy_opt {κ c q q' : Fin n → ℝ} (hq : IsGreedyFill κ c q) (hq' : q' ∈ cappedSimplex κ) :
    ∑ j, q' j * c j ≤ ∑ j, q j * c j := by
  obtain ⟨⟨⟨_, hs⟩, _⟩, τ, hτ⟩ := hq
  obtain ⟨⟨h0', hs'⟩, hκ'⟩ := hq'
  have key : ∑ j, q j * c j - ∑ j, q' j * c j = ∑ j, (q j - q' j) * (c j - τ) := by
    have e : ∀ j, (q j - q' j) * (c j - τ) = q j * c j - q' j * c j - τ * q j + τ * q' j :=
      fun j => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hs']
    ring
  have hterm : ∀ j, 0 ≤ (q j - q' j) * (c j - τ) := by
    intro j
    rcases lt_trichotomy (c j) τ with h | h | h
    · rw [(hτ j).2 h]
      nlinarith [h0' j]
    · rw [h, sub_self, mul_zero]
    · rw [(hτ j).1 h]
      exact mul_nonneg (by linarith [hκ' j]) (by linarith)
  have := Finset.sum_nonneg fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hterm j
  linarith

theorem tangent_knapsack : Claims.tangent_knapsack := by
  intro n κ c q
  refine ⟨fun hq => ⟨⟨q, hq.1, rfl⟩, ?_⟩, fun hq => ⟨⟨q, hq.1, rfl⟩, ?_⟩⟩
  · rintro _ ⟨q', hq', rfl⟩
    exact greedy_opt hq hq'
  · rintro _ ⟨q', hq', rfl⟩
    have := greedy_opt hq hq'
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at this
    exact this

lemma cappedSimplex_compact (κ : Fin n → ℝ) : IsCompact (cappedSimplex κ) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h1 : IsClosed {q : Fin n → ℝ | ∀ i, 0 ≤ q i} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {q : Fin n → ℝ | ∑ i, q i = 1} :=
      isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
    have h3 : IsClosed {q : Fin n → ℝ | ∀ j, q j ≤ κ j} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
    have : cappedSimplex κ =
        ({q : Fin n → ℝ | ∀ i, 0 ≤ q i} ∩ {q | ∑ i, q i = 1}) ∩ {q | ∀ j, q j ≤ κ j} := by
      ext q; simp [cappedSimplex, simplex]
    rw [this]
    exact (h1.inter h2).inter h3
  · apply (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset
    intro q ⟨⟨h0, hs⟩, _⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 i)]
    rw [← hs]
    exact Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ i)

theorem tangent_knapsack_exists : Claims.tangent_knapsack_exists := by
  intro n κ c hne
  have hcont : Continuous fun q' : Fin n → ℝ => ∑ j, q' j * c j := by fun_prop
  obtain ⟨q, hq, hmax⟩ := (cappedSimplex_compact κ).exists_isMaxOn hne hcont.continuousOn
  obtain ⟨⟨h0, hs⟩, hκ⟩ := hq
  -- the positive support is nonempty
  have hpos : (Finset.univ.filter fun k => 0 < q k).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    have : ∑ i, q i = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (not_lt.mp (h (Finset.mem_univ i))) (h0 i)
    rw [hs] at this; exact one_ne_zero this
  obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image _ c hpos
  have hk0p : 0 < q k0 := (Finset.mem_filter.mp hk0).2
  refine ⟨q, ⟨⟨h0, hs⟩, hκ⟩, c k0, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · by_contra hne'
    have hlt : q j < κ j := lt_of_le_of_ne (hκ j) hne'
    have hjk : j ≠ k0 := by rintro rfl; exact lt_irrefl _ hj
    set t := min (κ j - q j) (q k0) with ht
    have htpos : 0 < t := lt_min (by linarith) hk0p
    set q' : Fin n → ℝ := fun i => q i + (if i = j then t else 0) - (if i = k0 then t else 0)
      with hq'
    have hmem : q' ∈ cappedSimplex κ := by
      refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
      · simp only [hq']
        by_cases hi : i = k0
        · subst hi; simp only [hjk.symm, if_false, if_true]
          linarith [min_le_right (κ j - q j) (q i)]
        · simp only [hi, if_false, sub_zero]
          split_ifs <;> linarith [h0 i]
      · simp only [hq', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        linarith
      · simp only [hq']
        by_cases hi : i = j
        · subst hi; simp only [hjk, if_false, if_true, sub_zero]
          linarith [min_le_left (κ i - q i) (q k0)]
        · simp only [hi, if_false, add_zero]
          split_ifs <;> linarith [hκ i]
    have hobj : ∑ i, q' i * c i = ∑ i, q i * c i + t * (c j - c k0) := by
      simp only [hq', add_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have := hmax hmem
    simp only [Set.mem_setOf_eq] at this
    rw [hobj] at this
    nlinarith
  · by_contra hne'
    have hqj : 0 < q j := lt_of_le_of_ne (h0 j) (Ne.symm hne')
    have := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hqj⟩)
    linarith

end StatFormal.OTFD.Wave2
