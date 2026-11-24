import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Powerset

/-!
# Empirical extreme trimmed means: duality, order statistics, asymptotic-linearity inequality (library)

For `v : Fin n → ℝ`, `α ∈ [0,1)`, `β = 1 − α` and the frozen capped simplex `capped n α`
(`0 ≤ w_i ≤ cap = [nβ]⁻¹`, `Σ w_i = 1`):

* `ordStat k v = min_{|S| = k} max_{i ∈ S} v_i` is the `k`-th order statistic (`ordStat_spec`: at least `k` values
  are `≤` it, fewer than `k` are `<` it, and it is one of the `v_i`);
* weak duality `trimDual_le`: `c − cap Σ_i (c − v_i)_+ ≤ Σ_i w_i v_i` for every `w ∈ capped n α` and every `c`;
* attainment `exists_capped_eq` at every empirical `β`-quantile `c`;
* the closed form `trimLo_eq`: `min_{capped} Σ w_i v_i = Ψ(ĉ)` with `ĉ = ordStat ⌈nβ⌉ v`, and measurability;
* the deterministic asymptotic-linearity inequality `al_bound`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.Foundations.TrimmedMean

open StatFormal.TrimmedMMD.BangBang

variable {n : ℕ}

/-! ### Order statistics -/

/-- `k`-th order statistic: `min` over `k`-subsets of the `max` over the subset. -/
def ordStat (k : ℕ) (v : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : Finset (Fin n) // S.card = k}, ⨆ i : S.1, v i

lemma ordStat_spec {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (v : Fin n → ℝ) :
    k ≤ (univ.filter fun j => v j ≤ ordStat k v).card ∧
      (univ.filter fun j => v j < ordStat k v).card < k ∧ ∃ j, ordStat k v = v j := by
  have hne : Nonempty {S : Finset (Fin n) // S.card = k} := by
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hkn)
    exact ⟨⟨S, hS⟩⟩
  have hSne : ∀ S : {S : Finset (Fin n) // S.card = k}, Nonempty S.1 := fun S => by
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [S.2]; omega)
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨S0, hS0⟩ := exists_eq_ciInf_of_finite (f := fun S : {S : Finset (Fin n) // S.card = k} =>
    ⨆ i : S.1, v i)
  have hmax : ∀ S : {S : Finset (Fin n) // S.card = k}, ∃ i : S.1, v i = ⨆ i : S.1, v i := fun S => by
    haveI := hSne S
    exact exists_eq_ciSup_of_finite
  have hc : ordStat k v = ⨆ i : S0.1, v i := hS0.symm
  refine ⟨?_, ?_, ?_⟩
  · have hsub : S0.1 ⊆ univ.filter fun j => v j ≤ ordStat k v := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and]
      rw [hc]
      haveI := hSne S0
      exact le_ciSup (f := fun i : S0.1 => v i) (Finite.bddAbove_range _) ⟨j, hj⟩
    calc k = S0.1.card := S0.2.symm
      _ ≤ _ := card_le_card hsub
  · by_contra hlt
    push_neg at hlt
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hlt
    obtain ⟨t, ht⟩ := hmax ⟨T, hTc⟩
    have h1 : ordStat k v ≤ ⨆ i : T, v i :=
      ciInf_le (f := fun S : {S : Finset (Fin n) // S.card = k} => ⨆ i : S.1, v i)
        (Finite.bddBelow_range _) ⟨T, hTc⟩
    have h2 : v t < ordStat k v := by
      have := hT t.2
      simpa using this
    have : (⨆ i : T, v i) = v t := ht.symm
    linarith
  · obtain ⟨i, hi⟩ := hmax S0
    exact ⟨i, by rw [hc, ← hi]⟩

lemma measurable_ordStat (k : ℕ) : Measurable fun v : Fin n → ℝ => ordStat k v := by
  unfold ordStat
  exact Measurable.iInf fun S => Measurable.iSup fun i => measurable_pi_apply _

/-! ### Duality for the capped simplex -/

/-- The dual objective `Ψ(c) = c − cap Σ_i (c − v_i)_+`. -/
def trimDual (n : ℕ) (α : ℝ) (v : Fin n → ℝ) (c : ℝ) : ℝ :=
  c - cap n α * ∑ i, max (c - v i) 0

/-- The empirical lower `β`-quantile `ĉ = v_{(⌈nβ⌉)}`. -/
def quantLo (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ := ordStat ⌈(n : ℝ) * (1 - α)⌉₊ v

lemma trimDual_le {α : ℝ} {v w : Fin n → ℝ} (hw : w ∈ capped n α) (c : ℝ) :
    trimDual n α v c ≤ ∑ i, w i * v i := by
  obtain ⟨hb, hs⟩ := hw
  have h1 : ∀ i, w i * (c - v i) ≤ cap n α * max (c - v i) 0 := fun i =>
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (hb i).1).trans
      (mul_le_mul_of_nonneg_right (hb i).2 (le_max_right _ _))
  have h2 : ∑ i, w i * v i = c - ∑ i, w i * (c - v i) := by
    have : ∑ i, w i * (c - v i) = (∑ i, w i) * c - ∑ i, w i * v i := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this, hs]; ring
  unfold trimDual
  rw [h2, mul_sum]
  linarith [sum_le_sum fun i (_ : i ∈ univ) => h1 i]

lemma cap_pos {α : ℝ} (hn : 0 < n) (hα : α < 1) : 0 < cap n α := by
  unfold cap
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < 1 - α := by linarith
  positivity

lemma cap_mul {α : ℝ} (hn : 0 < n) (hα : α < 1) : cap n α * ((n : ℝ) * (1 - α)) = 1 := by
  unfold cap
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < 1 - α := by linarith
  field_simp

lemma exists_capped_eq {α c : ℝ} {v : Fin n → ℝ} (hn : 0 < n) (hα : α < 1)
    (hlt : ((univ.filter fun i => v i < c).card : ℝ) ≤ n * (1 - α))
    (hle : (n : ℝ) * (1 - α) ≤ (univ.filter fun i => v i ≤ c).card) :
    ∃ w ∈ capped n α, ∑ i, w i * v i = trimDual n α v c := by
  set A : ℝ := ((univ.filter fun i => v i < c).card : ℝ)
  set B : ℝ := ((univ.filter fun i => v i = c).card : ℝ)
  have hcap := cap_pos hn hα
  have hcm := cap_mul hn hα
  have hAB : ((univ.filter fun i => v i ≤ c).card : ℝ) = A + B := by
    simp only [A, B, natCast_card_filter, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rcases lt_trichotomy (v i) c with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [not_le.2 h, not_lt.2 h.le, h.ne']
  set t : ℝ := (1 - cap n α * A) / B
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hcapA : cap n α * A ≤ 1 := by
    calc cap n α * A ≤ cap n α * ((n : ℝ) * (1 - α)) := mul_le_mul_of_nonneg_left hlt hcap.le
      _ = 1 := hcm
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hB0
  have htc : t ≤ cap n α := by
    rcases hB0.eq_or_lt with h | h
    · simp only [t, ← h, div_zero]; exact hcap.le
    · rw [div_le_iff₀ h]
      have : 1 ≤ cap n α * (A + B) := by
        calc (1 : ℝ) = cap n α * ((n : ℝ) * (1 - α)) := hcm.symm
          _ ≤ cap n α * (A + B) := mul_le_mul_of_nonneg_left (hAB ▸ hle) hcap.le
      linarith
  let w : Fin n → ℝ := fun i => if v i < c then cap n α else if v i = c then t else 0
  have hsum : ∑ i, w i = 1 := by
    have : ∑ i, w i = cap n α * A + t * B := by
      simp only [A, B, natCast_card_filter, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rcases lt_trichotomy (v i) c with h | h | h
      · simp [w, h, h.ne]
      · simp [w, h]
      · simp [w, not_lt.2 h.le, h.ne']
    rw [this]
    rcases hB0.eq_or_lt with h | h
    · have hA : A = (n : ℝ) * (1 - α) := le_antisymm hlt (by rw [hAB, ← h, add_zero] at hle; exact hle)
      rw [← h, mul_zero, add_zero, hA, hcm]
    · simp only [t]; field_simp; ring
  refine ⟨w, ⟨fun i => ?_, hsum⟩, ?_⟩
  · simp only [w]
    split_ifs
    · exact ⟨hcap.le, le_rfl⟩
    · exact ⟨ht0, htc⟩
    · exact ⟨le_rfl, hcap.le⟩
  · have hterm : ∀ i, w i * v i = w i * c - cap n α * max (c - v i) 0 := fun i => by
      simp only [w]
      rcases lt_trichotomy (v i) c with h | h | h
      · rw [if_pos h, max_eq_left (by linarith)]; ring
      · rw [if_neg (not_lt.2 h.ge), if_pos h, h, sub_self, max_self]; ring
      · rw [if_neg (not_lt.2 h.le), if_neg h.ne', max_eq_right (by linarith)]; ring
    rw [sum_congr rfl fun i _ => hterm i, sum_sub_distrib, ← sum_mul, hsum, ← mul_sum]
    unfold trimDual
    ring

lemma ceil_bounds {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    1 ≤ ⌈(n : ℝ) * (1 - α)⌉₊ ∧ ⌈(n : ℝ) * (1 - α)⌉₊ ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by nlinarith)).ne'
  · exact Nat.ceil_le.2 (by nlinarith)

lemma quantLo_spec {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ) :
    (n : ℝ) * (1 - α) ≤ (univ.filter fun j => v j ≤ quantLo n α v).card ∧
      ((univ.filter fun j => v j < quantLo n α v).card : ℝ) < n * (1 - α) ∧
      ∃ j, quantLo n α v = v j := by
  obtain ⟨h1, h2⟩ := ceil_bounds hn hα0 hα1
  obtain ⟨s1, s2, s3⟩ := ordStat_spec h1 h2 v
  refine ⟨?_, ?_, s3⟩
  · exact (Nat.le_ceil _).trans (by exact_mod_cast s1)
  · exact Nat.lt_ceil.1 s2

/-- If at least `nβ` values are `≤ x`, then `ĉ ≤ x`. -/
lemma quantLo_le {α x : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ)
    (h : (n : ℝ) * (1 - α) ≤ (univ.filter fun j => v j ≤ x).card) : quantLo n α v ≤ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨-, s2, -⟩ := quantLo_spec hn hα0 hα1 v
  have : (univ.filter fun j => v j ≤ x).card ≤ (univ.filter fun j => v j < quantLo n α v).card :=
    card_le_card fun j hj => by
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      linarith
  have : ((univ.filter fun j => v j ≤ x).card : ℝ) ≤ (univ.filter fun j => v j < quantLo n α v).card := by
    exact_mod_cast this
  linarith

/-- If fewer than `nβ` values are `< x`, then `x ≤ ĉ`. -/
lemma le_quantLo {α x : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ)
    (h : ((univ.filter fun j => v j < x).card : ℝ) < n * (1 - α)) : x ≤ quantLo n α v := by
  by_contra hc
  push_neg at hc
  obtain ⟨s1, -, -⟩ := quantLo_spec hn hα0 hα1 v
  have : (univ.filter fun j => v j ≤ quantLo n α v).card ≤ (univ.filter fun j => v j < x).card :=
    card_le_card fun j hj => by
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      linarith
  have : ((univ.filter fun j => v j ≤ quantLo n α v).card : ℝ) ≤ (univ.filter fun j => v j < x).card := by
    exact_mod_cast this
  linarith

lemma isLeast_trim {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ) :
    IsLeast ((fun w => ∑ i, w i * v i) '' capped n α) (trimDual n α v (quantLo n α v)) := by
  obtain ⟨s1, s2, -⟩ := quantLo_spec hn hα0 hα1 v
  obtain ⟨w, hw, hwv⟩ := exists_capped_eq hn hα1 s2.le s1
  exact ⟨⟨w, hw, hwv⟩, by rintro _ ⟨w', hw', rfl⟩; exact trimDual_le hw' _⟩

lemma trimLo_eq {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ) :
    sInf ((fun w => ∑ i, w i * v i) '' capped n α) = trimDual n α v (quantLo n α v) :=
  (isLeast_trim hn hα0 hα1 v).csInf_eq

lemma trimDual_le_trimLo {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ) (c : ℝ) :
    trimDual n α v c ≤ sInf ((fun w => ∑ i, w i * v i) '' capped n α) := by
  rw [trimLo_eq hn hα0 hα1]
  obtain ⟨⟨w, hw, hwv⟩, -⟩ := isLeast_trim hn hα0 hα1 v
  rw [← hwv]
  exact trimDual_le hw c

lemma isGreatest_trim {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ) :
    IsGreatest ((fun w => ∑ i, w i * v i) '' capped n α)
      (-trimDual n α (fun i => -v i) (quantLo n α fun i => -v i)) := by
  obtain ⟨⟨w, hw, hwv⟩, hlb⟩ := isLeast_trim hn hα0 hα1 (fun i => -v i)
  refine ⟨⟨w, hw, ?_⟩, ?_⟩
  · simp only at hwv ⊢
    rw [← hwv, ← sum_neg_distrib]
    exact sum_congr rfl fun i _ => by ring
  · rintro _ ⟨w', hw', rfl⟩
    have := hlb ⟨w', hw', rfl⟩
    simp only at this ⊢
    have e : ∑ i, w' i * -v i = -∑ i, w' i * v i := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
    linarith

lemma trimUp_eq {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ) :
    sSup ((fun w => ∑ i, w i * v i) '' capped n α) =
      -sInf ((fun w => ∑ i, w i * (fun i => -v i) i) '' capped n α) := by
  rw [(isGreatest_trim hn hα0 hα1 v).csSup_eq, trimLo_eq hn hα0 hα1]

lemma capped_zero (α : ℝ) : capped 0 α = ∅ := by
  ext w; simp [capped]

lemma measurable_trimLo {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Measurable fun v : Fin n → ℝ => sInf ((fun w => ∑ i, w i * v i) '' capped n α) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp only [capped_zero, Set.image_empty]
    exact measurable_const
  · have e : (fun v : Fin n → ℝ => sInf ((fun w => ∑ i, w i * v i) '' capped n α)) =
        fun v => trimDual n α v (quantLo n α v) := funext fun v => trimLo_eq hn hα0 hα1 v
    rw [e]
    unfold trimDual
    have hq : Measurable fun v : Fin n → ℝ => quantLo n α v := measurable_ordStat _
    refine hq.sub (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun i _ => (hq.sub (measurable_pi_apply i)).max measurable_const

lemma measurable_trimUp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Measurable fun v : Fin n → ℝ => sSup ((fun w => ∑ i, w i * v i) '' capped n α) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp only [capped_zero, Set.image_empty]
    exact measurable_const
  · have e : (fun v : Fin n → ℝ => sSup ((fun w => ∑ i, w i * v i) '' capped n α)) =
        fun v => -sInf ((fun w => ∑ i, w i * (fun i => -v i) i) '' capped n α) :=
      funext fun v => trimUp_eq hn hα0 hα1 v
    rw [e]
    exact ((measurable_trimLo (n := n) hα0 hα1).comp (measurable_pi_iff.2 fun i =>
      (measurable_pi_apply i).neg)).neg

/-! ### The deterministic asymptotic-linearity inequality -/

/-- Empirical cdf `F_n(x) = n⁻¹ #{v_i ≤ x}`. -/
def ecdf (v : Fin n → ℝ) (x : ℝ) : ℝ := (∑ i, if v i ≤ x then (1 : ℝ) else 0) / n

/-- `G_n(x) = n⁻¹ #{v_i < x}`. -/
def ecdfLt (v : Fin n → ℝ) (x : ℝ) : ℝ := (∑ i, if v i < x then (1 : ℝ) else 0) / n

/-- `P_n (c − v)_+`. -/
def emean (v : Fin n → ℝ) (c : ℝ) : ℝ := (∑ i, max (c - v i) 0) / n

lemma beta_trimDual {α : ℝ} (hn : 0 < n) (hα : α < 1) (v : Fin n → ℝ) (c : ℝ) :
    (1 - α) * trimDual n α v c = (1 - α) * c - emean v c := by
  unfold trimDual emean cap
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < 1 - α := by linarith
  field_simp

private lemma term1 {c q d x : ℝ} (hd : 0 ≤ d) (hc : q + d ≤ c) :
    (c - q - d) * (if x ≤ q + d then 1 else 0) + d * (if x ≤ q then 1 else 0) ≤
      max (c - x) 0 - max (q - x) 0 := by
  split_ifs with h1 h2 h2
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
  · linarith
  · rw [max_eq_right (by linarith : q - x ≤ 0)]
    linarith [le_max_right (c - x) 0]

private lemma term2 {c q x : ℝ} (hc : q ≤ c) :
    (c - q) * (if x ≤ q then 1 else 0) ≤ max (c - x) 0 - max (q - x) 0 := by
  split_ifs with h1
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rw [max_eq_right (by linarith : q - x ≤ 0)]
    linarith [le_max_right (c - x) 0]

private lemma term3 {c q x : ℝ} (hc : c ≤ q) :
    max (q - x) 0 - max (c - x) 0 ≤ (q - c) * (if x < q then 1 else 0) := by
  split_ifs with h1
  · rw [max_eq_left (by linarith : 0 ≤ q - x)]
    have := le_max_left (c - x) 0
    linarith
  · rw [max_eq_right (by linarith : q - x ≤ 0)]
    linarith [le_max_right (c - x) 0]

private lemma term4 {c q d x : ℝ} (hd : 0 ≤ d) (hc : c ≤ q - d) :
    max (q - x) 0 - max (c - x) 0 ≤ d * (if x < q then 1 else 0) + (q - d - c) * (if x < q - d then 1 else 0) := by
  split_ifs with h1 h2 h2
  · rw [max_eq_left (by linarith : 0 ≤ q - x)]
    have := le_max_left (c - x) 0
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ q - x)]
    have := le_max_right (c - x) 0
    linarith
  · linarith
  · rw [max_eq_right (by linarith : q - x ≤ 0)]
    linarith [le_max_right (c - x) 0]

/-- The deterministic core: for every `c`, `φ(c) = β(c − q) − (P_n g_c − P_n g_q)` is bounded by
`d((β − F_n(q))_+ + (G_n(q) − β)_+)` on the event `F_n(q+d) ≥ β`, `G_n(q−d) ≤ β`. -/
lemma phi_bound {β q d c : ℝ} (hn : 0 < n) (hd : 0 ≤ d) (v : Fin n → ℝ)
    (hF : β ≤ ecdf v (q + d)) (hG : ecdfLt v (q - d) ≤ β) :
    β * (c - q) - (emean v c - emean v q) ≤
      d * (max (β - ecdf v q) 0 + max (ecdfLt v q - β) 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiff : emean v c - emean v q = (∑ i, (max (c - v i) 0 - max (q - v i) 0)) / n := by
    unfold emean; rw [sum_sub_distrib, sub_div]
  have hm1 := le_max_left (β - ecdf v q) 0
  have hm2 := le_max_right (β - ecdf v q) 0
  have hm3 := le_max_left (ecdfLt v q - β) 0
  have hm4 := le_max_right (ecdfLt v q - β) 0
  rcases le_or_gt q c with hqc | hcq
  · rcases le_or_gt (q + d) c with hc1 | hc1
    · -- `c ≥ q + d`
      have hs : (c - q - d) * ecdf v (q + d) + d * ecdf v q ≤ emean v c - emean v q := by
        rw [hdiff]
        unfold ecdf
        rw [mul_div_assoc', mul_div_assoc', ← add_div, mul_sum, mul_sum, ← sum_add_distrib]
        exact div_le_div_of_nonneg_right (sum_le_sum fun i _ => term1 hd hc1) hn'.le
      have h1 : (c - q - d) * (β - ecdf v (q + d)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have h2 : d * (β - ecdf v q) ≤ d * max (β - ecdf v q) 0 := mul_le_mul_of_nonneg_left hm1 hd
      have h3 : 0 ≤ d * max (ecdfLt v q - β) 0 := mul_nonneg hd hm4
      nlinarith
    · -- `q ≤ c < q + d`
      have hs : (c - q) * ecdf v q ≤ emean v c - emean v q := by
        rw [hdiff]
        unfold ecdf
        rw [mul_div_assoc', mul_sum]
        exact div_le_div_of_nonneg_right (sum_le_sum fun i _ => term2 hqc) hn'.le
      have h2 : (c - q) * (β - ecdf v q) ≤ d * max (β - ecdf v q) 0 :=
        (mul_le_mul_of_nonneg_left hm1 (by linarith)).trans
          (mul_le_mul_of_nonneg_right (by linarith) hm2)
      have h3 : 0 ≤ d * max (ecdfLt v q - β) 0 := mul_nonneg hd hm4
      nlinarith
  · rcases le_or_gt c (q - d) with hc1 | hc1
    · -- `c ≤ q − d`
      have hs : emean v q - emean v c ≤ d * ecdfLt v q + (q - d - c) * ecdfLt v (q - d) := by
        have hdiff' : emean v q - emean v c = (∑ i, (max (q - v i) 0 - max (c - v i) 0)) / n := by
          unfold emean; rw [sum_sub_distrib, sub_div]
        rw [hdiff']
        unfold ecdfLt
        rw [mul_div_assoc', mul_div_assoc', ← add_div, mul_sum, mul_sum, ← sum_add_distrib]
        exact div_le_div_of_nonneg_right (sum_le_sum fun i _ => term4 hd hc1) hn'.le
      have h1 : (q - d - c) * (ecdfLt v (q - d) - β) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have h2 : d * (ecdfLt v q - β) ≤ d * max (ecdfLt v q - β) 0 := mul_le_mul_of_nonneg_left hm3 hd
      have h3 : 0 ≤ d * max (β - ecdf v q) 0 := mul_nonneg hd hm2
      nlinarith
    · -- `q − d < c < q`
      have hs : emean v q - emean v c ≤ (q - c) * ecdfLt v q := by
        have hdiff' : emean v q - emean v c = (∑ i, (max (q - v i) 0 - max (c - v i) 0)) / n := by
          unfold emean; rw [sum_sub_distrib, sub_div]
        rw [hdiff']
        unfold ecdfLt
        rw [mul_div_assoc', mul_sum]
        exact div_le_div_of_nonneg_right (sum_le_sum fun i _ => term3 hcq.le) hn'.le
      have h2 : (q - c) * (ecdfLt v q - β) ≤ d * max (ecdfLt v q - β) 0 :=
        (mul_le_mul_of_nonneg_left hm3 (by linarith)).trans
          (mul_le_mul_of_nonneg_right (by linarith) hm4)
      have h3 : 0 ≤ d * max (β - ecdf v q) 0 := mul_nonneg hd hm2
      nlinarith

/-- **Asymptotic-linearity inequality.** With `β = 1 − α`, `D = β·L_n − (βq − P_n g_q)` satisfies
`0 ≤ D ≤ d((β − F_n(q))_+ + (G_n(q) − β)_+)` whenever `F_n(q + d) ≥ β` and `G_n(q − d) ≤ β`. -/
lemma al_bound {α q d : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (hd : 0 ≤ d) (v : Fin n → ℝ)
    (hF : 1 - α ≤ ecdf v (q + d)) (hG : ecdfLt v (q - d) ≤ 1 - α) :
    0 ≤ (1 - α) * sInf ((fun w => ∑ i, w i * v i) '' capped n α) - ((1 - α) * q - emean v q) ∧
      (1 - α) * sInf ((fun w => ∑ i, w i * v i) '' capped n α) - ((1 - α) * q - emean v q) ≤
        d * (max (1 - α - ecdf v q) 0 + max (ecdfLt v q - (1 - α)) 0) := by
  have hβ : 0 < 1 - α := by linarith
  constructor
  · have := mul_le_mul_of_nonneg_left (trimDual_le_trimLo hn hα0 hα1 v q) hβ.le
    rw [beta_trimDual hn hα1] at this
    linarith
  · rw [trimLo_eq hn hα0 hα1, beta_trimDual hn hα1]
    have := phi_bound (β := 1 - α) (c := quantLo n α v) hn hd v hF hG
    linarith

end StatFormal.Foundations.TrimmedMean
