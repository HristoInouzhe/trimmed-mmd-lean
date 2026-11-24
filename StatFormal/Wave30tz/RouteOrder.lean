import StatFormal.Wave30tz.Statements
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Route: order statistics, the rank convention (C), Lemma 3 (untrusted proof material)

Proves the frozen claims `Claims.quantile_bracket`, `Claims.numpy_bracket`, `Claims.exact_quantile_bracket`,
`Claims.order_stat_shift` of `StatFormal.Wave30tz.Statements`.

Public API (for `h : Fin n → ℝ`, `1 ≤ k ≤ n`), usable by other routes:
* `ordStat_le_iff : ordStat h k ≤ v ↔ k ≤ #{i | h i ≤ v}`, `lt_ordStat_iff`, `card_le_ordStat`,
  `card_lt_ordStat_lt : #{i | h i < ordStat h k} < k`, `ordStat_lt_of_le_card_lt`;
* `exists_eq_ordStat : ∃ i, h i = ordStat h k`, `exists_ordStat_le`, `exists_le_ordStat`, `ordStat_le_of_forall_le`,
  `le_ordStat_of_forall_le`, `ordStat_le_sup'`, `inf'_le_ordStat`;
* `ordStat_mono_rank` (monotone in `k`), `ordStat_mono` (monotone in `h`), `ordStat_sub_le` (shift down by `ε`),
  `ordStat_add_const` (translation equivariance);
* ranks: `one_le_rkLo`, `rkHi_le`, `one_le_rkHi`, `rkLo_le`, `rkLo_le_rkHi`, `sub_one_le_rkLo`, `rkHi_le_add_two`;
* the criteria: `critT_sub_le`, `le_critT_sub`, `critU_sub_le`, `le_critU_sub` (slope bounds through counts).
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq

/-! ### Counting -/

section Count

variable {n : ℕ}

/-- The count `#{i : h i ≤ v}` is monotone in `v`. -/
theorem card_le_mono (h : Fin n → ℝ) {v w : ℝ} (hvw : v ≤ w) :
    (univ.filter fun i => h i ≤ v).card ≤ (univ.filter fun i => h i ≤ w).card :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact le_trans hi hvw

/-- `#{i : h i < v} + #{i : v ≤ h i} = n`. -/
theorem card_lt_add_card_ge (h : Fin n → ℝ) (v : ℝ) :
    (univ.filter fun i => h i < v).card + (univ.filter fun i => v ≤ h i).card = n := by
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => h i < v)
  simpa [not_lt] using this

/-- `#{i : h i ≤ v} + #{i : v < h i} = n`. -/
theorem card_le_add_card_gt (h : Fin n → ℝ) (v : ℝ) :
    (univ.filter fun i => h i ≤ v).card + (univ.filter fun i => v < h i).card = n := by
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => h i ≤ v)
  simpa [not_le] using this

theorem card_filter_le_n (h : Fin n → ℝ) (P : ℝ → Prop) [DecidablePred P] :
    (univ.filter fun i => P (h i)).card ≤ n := by
  simpa using card_filter_le (univ : Finset (Fin n)) (fun i => P (h i))

end Count

/-! ### Order statistics -/

section OrdStat

variable {n : ℕ}

/-- For `v ∈ {v | k ≤ #{h ≤ v}}` (`k ≥ 1`) the largest value `h j ≤ v` is in the set too. -/
theorem exists_val_of_le_card (h : Fin n → ℝ) {k : ℕ} (hk : 1 ≤ k) {v : ℝ}
    (hv : k ≤ (univ.filter fun i => h i ≤ v).card) :
    ∃ j, h j ≤ v ∧ k ≤ (univ.filter fun i => h i ≤ h j).card := by
  have hne : (univ.filter fun i => h i ≤ v).Nonempty := by
    rw [← card_pos]; omega
  obtain ⟨j, hj, hjmax⟩ := exists_max_image _ h hne
  refine ⟨j, (mem_filter.mp hj).2, le_trans hv (card_le_card ?_)⟩
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hjmax i (by simpa using hi)

/-- The defining set of `ordStat h k` has a least element, which is one of the values. -/
theorem isLeast_ordStat_set (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ i, IsLeast {v : ℝ | k ≤ (univ.filter fun i => h i ≤ v).card} (h i) := by
  classical
  -- a point of the set: the sum of the absolute values
  have hS : k ≤ (univ.filter fun i => h i ≤ ∑ j, |h j|).card := by
    have : (univ.filter fun i => h i ≤ ∑ j, |h j|) = univ := by
      apply filter_true_of_mem
      intro i _
      exact le_trans (le_abs_self _)
        (single_le_sum (f := fun j => |h j|) (fun j _ => abs_nonneg _) (mem_univ i))
    rw [this, card_univ, Fintype.card_fin]; exact hkn
  obtain ⟨j0, -, hj0⟩ := exists_val_of_le_card h hk1 hS
  have hne : (univ.filter fun i => k ≤ (univ.filter fun l => h l ≤ h i).card).Nonempty :=
    ⟨j0, by simp [hj0]⟩
  obtain ⟨i, hi, himin⟩ := exists_min_image _ h hne
  refine ⟨i, (mem_filter.mp hi).2, ?_⟩
  intro v hv
  obtain ⟨j, hjv, hj⟩ := exists_val_of_le_card h hk1 hv
  exact le_trans (himin j (by simp [hj])) hjv

/-- `ordStat h k` is the least element of its defining set. -/
theorem isLeast_ordStat (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    IsLeast {v : ℝ | k ≤ (univ.filter fun i => h i ≤ v).card} (ordStat h k) := by
  obtain ⟨i, hi⟩ := isLeast_ordStat_set h hk1 hkn
  have : ordStat h k = h i := by
    unfold ordStat
    convert hi.csInf_eq
  rw [this]; exact hi

/-- The order statistic `h_(k)` is one of the values (`1 ≤ k ≤ n`). -/
theorem exists_eq_ordStat (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ i, h i = ordStat h k := by
  obtain ⟨i, hi⟩ := isLeast_ordStat_set h hk1 hkn
  refine ⟨i, ?_⟩
  unfold ordStat
  convert hi.csInf_eq.symm

/-- At least `k` values are `≤ h_(k)`. -/
theorem card_le_ordStat (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    k ≤ (univ.filter fun i => h i ≤ ordStat h k).card :=
  (isLeast_ordStat h hk1 hkn).1

/-- **The workhorse**: `h_(k) ≤ v ↔ k ≤ #{i : h i ≤ v}` (`1 ≤ k ≤ n`). -/
theorem ordStat_le_iff (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (v : ℝ) :
    ordStat h k ≤ v ↔ k ≤ (univ.filter fun i => h i ≤ v).card :=
  ⟨fun hv => le_trans (card_le_ordStat h hk1 hkn) (card_le_mono h hv),
    fun hv => (isLeast_ordStat h hk1 hkn).2 hv⟩

/-- `v < h_(k) ↔ #{i : h i ≤ v} < k` (`1 ≤ k ≤ n`). -/
theorem lt_ordStat_iff (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (v : ℝ) :
    v < ordStat h k ↔ (univ.filter fun i => h i ≤ v).card < k := by
  rw [← not_le, ordStat_le_iff h hk1 hkn, not_le]

/-- If at least `k` values are `< v`, then `h_(k) < v` (`1 ≤ k ≤ n`). -/
theorem ordStat_lt_of_le_card_lt (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {v : ℝ}
    (hv : k ≤ (univ.filter fun i => h i < v).card) : ordStat h k < v := by
  have hne : (univ.filter fun i => h i < v).Nonempty := by
    rw [← card_pos]; omega
  obtain ⟨j, hj, hjmax⟩ := exists_max_image _ h hne
  have hjv : h j < v := (mem_filter.mp hj).2
  refine lt_of_le_of_lt ((ordStat_le_iff h hk1 hkn _).mpr (le_trans hv (card_le_card ?_))) hjv
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hjmax i (by simpa using hi)

/-- Fewer than `k` values are `< h_(k)` (`1 ≤ k ≤ n`). -/
theorem card_lt_ordStat_lt (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (univ.filter fun i => h i < ordStat h k).card < k := by
  by_contra hc
  exact lt_irrefl _ (ordStat_lt_of_le_card_lt h hk1 hkn (not_lt.mp hc))

/-- If `v ≤ h_(k)`, fewer than `k` values are `< v` (`1 ≤ k ≤ n`). -/
theorem card_lt_lt_of_le_ordStat (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {v : ℝ}
    (hv : v ≤ ordStat h k) : (univ.filter fun i => h i < v).card < k := by
  by_contra hc
  exact absurd hv (not_le.mpr (ordStat_lt_of_le_card_lt h hk1 hkn (not_lt.mp hc)))

/-- `h_(k) ≤ h i` for some `i`. -/
theorem exists_ordStat_le (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ i, ordStat h k ≤ h i := by
  obtain ⟨i, hi⟩ := exists_eq_ordStat h hk1 hkn; exact ⟨i, hi.ge⟩

/-- `h i ≤ h_(k)` for some `i`. -/
theorem exists_le_ordStat (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ i, h i ≤ ordStat h k := by
  obtain ⟨i, hi⟩ := exists_eq_ordStat h hk1 hkn; exact ⟨i, hi.le⟩

/-- An upper bound of all values bounds `h_(k)`. -/
theorem ordStat_le_of_forall_le (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {M : ℝ}
    (hM : ∀ i, h i ≤ M) : ordStat h k ≤ M := by
  obtain ⟨i, hi⟩ := exists_eq_ordStat h hk1 hkn; exact hi ▸ hM i

/-- A lower bound of all values bounds `h_(k)`. -/
theorem le_ordStat_of_forall_le (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {M : ℝ}
    (hM : ∀ i, M ≤ h i) : M ≤ ordStat h k := by
  obtain ⟨i, hi⟩ := exists_eq_ordStat h hk1 hkn; exact hi ▸ hM i

/-- `h_(k) ≤ max_i h i`. -/
theorem ordStat_le_sup' (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hne : (univ : Finset (Fin n)).Nonempty) :
    ordStat h k ≤ univ.sup' hne h :=
  ordStat_le_of_forall_le h hk1 hkn fun i => le_sup' h (mem_univ i)

/-- `min_i h i ≤ h_(k)`. -/
theorem inf'_le_ordStat (h : Fin n → ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hne : (univ : Finset (Fin n)).Nonempty) :
    univ.inf' hne h ≤ ordStat h k :=
  le_ordStat_of_forall_le h hk1 hkn fun i => inf'_le h (mem_univ i)

/-- `h_(j) ≤ h_(k)` for `1 ≤ j ≤ k ≤ n`. -/
theorem ordStat_mono_rank (h : Fin n → ℝ) {j k : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ n) :
    ordStat h j ≤ ordStat h k :=
  (ordStat_le_iff h hj1 (hjk.trans hkn) _).mpr (hjk.trans (card_le_ordStat h (hj1.trans hjk) hkn))

/-- Monotone in the values: `h' ≤ h` pointwise gives `h'_(k) ≤ h_(k)` (`1 ≤ k ≤ n`). -/
theorem ordStat_mono {h h' : Fin n → ℝ} (hle : ∀ i, h' i ≤ h i) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ordStat h' k ≤ ordStat h k := by
  rw [ordStat_le_iff h' hk1 hkn]
  refine le_trans (card_le_ordStat h hk1 hkn) (card_le_card ?_)
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact le_trans (hle i) hi

/-- Shift: `h − ε ≤ h'` pointwise gives `h_(k) − ε ≤ h'_(k)` (`1 ≤ k ≤ n`). -/
theorem ordStat_sub_le {h h' : Fin n → ℝ} {ε : ℝ} (hle : ∀ i, h i - ε ≤ h' i) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ordStat h k - ε ≤ ordStat h' k := by
  rw [sub_le_iff_le_add, ordStat_le_iff h hk1 hkn]
  refine le_trans (card_le_ordStat h' hk1 hkn) (card_le_card ?_)
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  linarith [hle i]

/-- Translation equivariance: `(h + c)_(k) = h_(k) + c` (`1 ≤ k ≤ n`). -/
theorem ordStat_add_const (h : Fin n → ℝ) (c : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ordStat (fun i => h i + c) k = ordStat h k + c := by
  apply le_antisymm
  · have := ordStat_sub_le (h := h) (h' := fun i => h i + c) (ε := -c) (fun i => by simp) hk1 hkn
    have h2 := ordStat_sub_le (h := fun i => h i + c) (h' := h) (ε := c) (fun i => by simp) hk1 hkn
    linarith
  · have := ordStat_sub_le (h := h) (h' := fun i => h i + c) (ε := -c) (fun i => by simp) hk1 hkn
    linarith

end OrdStat

/-! ### The ranks `ι⁻`, `ι⁺` -/

section Ranks

theorem one_le_rkLo (n : ℕ) (p : ℝ) : 1 ≤ rkLo n p := le_max_left _ _

theorem rkHi_le (n : ℕ) (p : ℝ) : rkHi n p ≤ n := min_le_left _ _

theorem one_le_rkHi {n : ℕ} (hn : 1 ≤ n) (p : ℝ) : 1 ≤ rkHi n p := le_min hn (by omega)

/-- `ι⁻(n,p) ≤ n` for `n ≥ 1`, `p ≤ 1`. -/
theorem rkLo_le {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : p ≤ 1) : rkLo n p ≤ n := by
  unfold rkLo
  refine max_le hn ?_
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : ⌈(n : ℝ) * p⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  omega

/-- `ι⁻(n,p) ≤ ι⁺(n,p)` for `n ≥ 1`, `p ≤ 1`. -/
theorem rkLo_le_rkHi {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : p ≤ 1) : rkLo n p ≤ rkHi n p := by
  have h1 := rkLo_le hn hp
  have h2 := Nat.ceil_le_floor_add_one ((n : ℝ) * p)
  unfold rkLo rkHi at *
  omega

/-- `np − 1 ≤ ι⁻(n,p)` (as reals). -/
theorem sub_one_le_rkLo (n : ℕ) (p : ℝ) : (n : ℝ) * p - 1 ≤ rkLo n p := by
  have h1 : (n : ℝ) * p ≤ ⌈(n : ℝ) * p⌉₊ := Nat.le_ceil _
  have h2 : ⌈(n : ℝ) * p⌉₊ ≤ rkLo n p + 1 := by unfold rkLo; omega
  have h3 : ((⌈(n : ℝ) * p⌉₊ : ℕ) : ℝ) ≤ (rkLo n p : ℝ) + 1 := by exact_mod_cast h2
  linarith

/-- `ι⁺(n,p) ≤ np + 2` (as reals, `p ≥ 0`). -/
theorem rkHi_le_add_two (n : ℕ) {p : ℝ} (hp : 0 ≤ p) : (rkHi n p : ℝ) ≤ n * p + 2 := by
  have h1 : (⌊(n : ℝ) * p⌋₊ : ℝ) ≤ n * p := Nat.floor_le (by positivity)
  have h2 : rkHi n p ≤ ⌊(n : ℝ) * p⌋₊ + 2 := min_le_right _ _
  have h3 : (rkHi n p : ℝ) ≤ (⌊(n : ℝ) * p⌋₊ : ℝ) + 2 := by exact_mod_cast h2
  linarith

end Ranks

/-! ### The criteria `T`, `U`: slope bounds through counts -/

section Crit

variable {n : ℕ}

theorem pos_diff_ge {a b x : ℝ} (hab : a ≤ b) :
    (if x ≤ a then b - a else 0) ≤ max (b - x) 0 - max (a - x) 0 := by
  split_ifs with hx
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rw [max_eq_right (a := a - x) (by linarith)]; linarith [le_max_right (b - x) 0]

theorem pos_diff_le {a b x : ℝ} (hab : a ≤ b) :
    max (b - x) 0 - max (a - x) 0 ≤ (if x < b then b - a else 0) := by
  split_ifs with hx
  · rw [max_eq_left (a := b - x) (by linarith)]; linarith [le_max_left (a - x) 0]
  · rw [max_eq_right (a := b - x) (by linarith), max_eq_right (a := a - x) (by linarith)]; simp

theorem pos_diff_ge' {a b x : ℝ} (hab : a ≤ b) :
    (if b ≤ x then b - a else 0) ≤ max (x - a) 0 - max (x - b) 0 := by
  split_ifs with hx
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rw [max_eq_right (a := x - b) (by linarith)]; linarith [le_max_right (x - a) 0]

theorem pos_diff_le' {a b x : ℝ} (hab : a ≤ b) :
    max (x - a) 0 - max (x - b) 0 ≤ (if a < x then b - a else 0) := by
  split_ifs with hx
  · rw [max_eq_left (a := x - a) (by linarith)]; linarith [le_max_left (x - b) 0]
  · rw [max_eq_right (a := x - a) (by linarith), max_eq_right (a := x - b) (by linarith)]; simp

theorem sum_ite_eq_mul_card (s : Fin n → Prop) [DecidablePred s] (c : ℝ) :
    ∑ i, (if s i then c else 0) = c * (univ.filter s).card := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_comm]

theorem critT_sub_eq (α : ℝ) (h : Fin n → ℝ) (a b : ℝ) :
    critT α h b - critT α h a = (b - a) - beta α / n * ∑ i, (max (b - h i) 0 - max (a - h i) 0) := by
  unfold critT; rw [Finset.sum_sub_distrib]; ring

theorem critU_sub_eq (α : ℝ) (h : Fin n → ℝ) (a b : ℝ) :
    critU α h b - critU α h a = (b - a) - beta α / n * ∑ i, (max (h i - a) 0 - max (h i - b) 0) := by
  unfold critU; rw [Finset.sum_sub_distrib]; ring

/-- `T(b) − T(a) ≤ (b − a)(1 − (β/n) #{h ≤ a})` for `a ≤ b`. -/
theorem critT_sub_le {α : ℝ} (hβ : 0 ≤ beta α) (h : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b) :
    critT α h b - critT α h a ≤ (b - a) * (1 - beta α / n * (univ.filter fun i => h i ≤ a).card) := by
  rw [critT_sub_eq]
  have hs : (b - a) * (univ.filter fun i => h i ≤ a).card ≤ ∑ i, (max (b - h i) 0 - max (a - h i) 0) := by
    rw [← sum_ite_eq_mul_card]
    exact Finset.sum_le_sum fun i _ => pos_diff_ge hab
  have hc : 0 ≤ beta α / n := div_nonneg hβ (Nat.cast_nonneg n)
  have := mul_le_mul_of_nonneg_left hs hc
  linarith

/-- `(b − a)(1 − (β/n) #{h < b}) ≤ T(b) − T(a)` for `a ≤ b`. -/
theorem le_critT_sub {α : ℝ} (hβ : 0 ≤ beta α) (h : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * (1 - beta α / n * (univ.filter fun i => h i < b).card) ≤ critT α h b - critT α h a := by
  rw [critT_sub_eq]
  have hs : ∑ i, (max (b - h i) 0 - max (a - h i) 0) ≤ (b - a) * (univ.filter fun i => h i < b).card := by
    rw [← sum_ite_eq_mul_card]
    exact Finset.sum_le_sum fun i _ => pos_diff_le hab
  have hc : 0 ≤ beta α / n := div_nonneg hβ (Nat.cast_nonneg n)
  have := mul_le_mul_of_nonneg_left hs hc
  linarith

/-- `U(b) − U(a) ≤ (b − a)(1 − (β/m) #{b ≤ h'})` for `a ≤ b`. -/
theorem critU_sub_le {α : ℝ} (hβ : 0 ≤ beta α) (h : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b) :
    critU α h b - critU α h a ≤ (b - a) * (1 - beta α / n * (univ.filter fun i => b ≤ h i).card) := by
  rw [critU_sub_eq]
  have hs : (b - a) * (univ.filter fun i => b ≤ h i).card ≤ ∑ i, (max (h i - a) 0 - max (h i - b) 0) := by
    rw [← sum_ite_eq_mul_card]
    exact Finset.sum_le_sum fun i _ => pos_diff_ge' hab
  have hc : 0 ≤ beta α / n := div_nonneg hβ (Nat.cast_nonneg n)
  have := mul_le_mul_of_nonneg_left hs hc
  linarith

/-- `(b − a)(1 − (β/m) #{a < h'}) ≤ U(b) − U(a)` for `a ≤ b`. -/
theorem le_critU_sub {α : ℝ} (hβ : 0 ≤ beta α) (h : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * (1 - beta α / n * (univ.filter fun i => a < h i).card) ≤ critU α h b - critU α h a := by
  rw [critU_sub_eq]
  have hs : ∑ i, (max (h i - a) 0 - max (h i - b) 0) ≤ (b - a) * (univ.filter fun i => a < h i).card := by
    rw [← sum_ite_eq_mul_card]
    exact Finset.sum_le_sum fun i _ => pos_diff_le' hab
  have hc : 0 ≤ beta α / n := div_nonneg hβ (Nat.cast_nonneg n)
  have := mul_le_mul_of_nonneg_left hs hc
  linarith

/-- `0 ≤ (β/n) k ≤ β` for `k ≤ n`. -/
theorem div_mul_card_le {β : ℝ} (hβ : 0 ≤ β) {k : ℕ} (hk : k ≤ n) : β / n * k ≤ β := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [hβ]
  · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hβ

/-- A function with slopes in `[1 − β, 1]` (`β ≥ 0`) is Lipschitz with constant `max(1, β − 1)`. -/
theorem abs_le_of_slopes {F : ℝ → ℝ} {β : ℝ}
    (hs : ∀ a b, a ≤ b → (b - a) * (1 - β) ≤ F b - F a ∧ F b - F a ≤ b - a) (t t' : ℝ) :
    |F t - F t'| ≤ max 1 (β - 1) * |t - t'| := by
  have hM1 : 1 ≤ max 1 (β - 1) := le_max_left _ _
  have hM2 : β - 1 ≤ max 1 (β - 1) := le_max_right _ _
  rcases le_total t' t with hle | hle
  · obtain ⟨h1, h2⟩ := hs t' t hle
    rw [abs_of_nonneg (by linarith : 0 ≤ t - t'), abs_le]
    constructor <;> nlinarith
  · obtain ⟨h1, h2⟩ := hs t t' hle
    rw [abs_sub_comm t t', abs_of_nonneg (by linarith : 0 ≤ t' - t), abs_sub_comm, abs_le]
    constructor <;> nlinarith

end Crit

/-! ### Lemma 3 -/

section Lemma3

theorem beta_eq {α : ℝ} : beta α = 1 / (1 - α) := rfl

theorem one_le_beta {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 ≤ beta α := by
  rw [beta_eq, le_div_iff₀ (by linarith)]; linarith

/-- Lemma 3 (a): `t` in the bracket `[h_(ι⁻(n,1−α)), h_(ι⁺(n,1−α))]` is within `(β/n) R` of `max T`. -/
theorem critT_bracket {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (h : Fin n → ℝ) {R : ℝ}
    (hR : ∀ i j, h i - h j ≤ R) {t : ℝ}
    (ht : t ∈ Set.Icc (ordStat h (rkLo n (1 - α))) (ordStat h (rkHi n (1 - α)))) (t' : ℝ) :
    critT α h t' - critT α h t ≤ beta α / n * R := by
  have hp0 : 0 < 1 - α := by linarith
  have hp1 : 1 - α ≤ 1 := by linarith
  have hβ : 0 ≤ beta α := by linarith [one_le_beta hα0 hα1]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc0 : 0 ≤ beta α / n := div_nonneg hβ hnR.le
  have hcnp : beta α / n * (n * (1 - α)) = 1 := by rw [beta_eq]; field_simp
  -- the maximizer `t* = h_(⌈np⌉)`
  have hk1 : 1 ≤ ⌈(n : ℝ) * (1 - α)⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hkn : ⌈(n : ℝ) * (1 - α)⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  set k := ⌈(n : ℝ) * (1 - α)⌉₊ with hk
  have hkge : (n : ℝ) * (1 - α) ≤ k := Nat.le_ceil _
  have hklt : (k : ℝ) < n * (1 - α) + 1 := Nat.ceil_lt_add_one (by positivity)
  set ts := ordStat h k with hts
  -- (1) `T t' ≤ T t*`
  have h1 : critT α h t' ≤ critT α h ts := by
    rcases le_total ts t' with hle | hle
    · have e := critT_sub_le hβ h hle
      have hcnt : (k : ℝ) ≤ (univ.filter fun i => h i ≤ ts).card := by
        exact_mod_cast card_le_ordStat h hk1 hkn
      have e2 := mul_le_mul_of_nonneg_left (hkge.trans hcnt) hc0
      have e3 : (t' - ts) * (1 - beta α / n * (univ.filter fun i => h i ≤ ts).card) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
    · have e := le_critT_sub hβ h hle
      have hcnt : (univ.filter fun i => h i < ts).card < k := card_lt_ordStat_lt h hk1 hkn
      have hcnt' : ((univ.filter fun i => h i < ts).card : ℝ) + 1 ≤ k := by exact_mod_cast hcnt
      have e2 := mul_le_mul_of_nonneg_left (by linarith :
        ((univ.filter fun i => h i < ts).card : ℝ) ≤ n * (1 - α)) hc0
      have e3 : 0 ≤ (ts - t') * (1 - beta α / n * (univ.filter fun i => h i < ts).card) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
  -- (2) `T t* − T t ≤ (β/n) R`
  have h2 : critT α h ts - critT α h t ≤ beta α / n * R := by
    have hLo1 := one_le_rkLo n (1 - α)
    have hLon := rkLo_le hn hp1
    have hHi1 := one_le_rkHi hn (1 - α)
    have hHin := rkHi_le n (1 - α)
    obtain ⟨i, hi⟩ := exists_eq_ordStat h hLo1 hLon
    obtain ⟨j, hj⟩ := exists_eq_ordStat h hHi1 hHin
    obtain ⟨l, hl⟩ := exists_eq_ordStat h hk1 hkn
    rcases le_total t ts with hle | hle
    · have e := critT_sub_le hβ h hle
      have hcnt : rkLo n (1 - α) ≤ (univ.filter fun i => h i ≤ t).card :=
        (ordStat_le_iff h hLo1 hLon t).mp ht.1
      have hcnt' : (n : ℝ) * (1 - α) - 1 ≤ (univ.filter fun i => h i ≤ t).card :=
        le_trans (sub_one_le_rkLo n (1 - α)) (by exact_mod_cast hcnt)
      have e2 := mul_le_mul_of_nonneg_left hcnt' hc0
      have hf : 1 - beta α / n * (univ.filter fun i => h i ≤ t).card ≤ beta α / n := by
        nlinarith
      have hR' : ts - t ≤ R := by
        have := hR l i; rw [hl, hi] at this; linarith [ht.1]
      have e3 := mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ ts - t)
      have e4 := mul_le_mul_of_nonneg_right hR' hc0
      linarith
    · have e := le_critT_sub hβ h hle
      have hcnt : (univ.filter fun i => h i < t).card < rkHi n (1 - α) :=
        card_lt_lt_of_le_ordStat h hHi1 hHin ht.2
      have hcnt' : ((univ.filter fun i => h i < t).card : ℝ) + 1 ≤ rkHi n (1 - α) := by
        exact_mod_cast hcnt
      have hhi := rkHi_le_add_two n hp0.le
      have e2 := mul_le_mul_of_nonneg_left (by linarith :
        ((univ.filter fun i => h i < t).card : ℝ) ≤ n * (1 - α) + 1) hc0
      have hf : beta α / n * (univ.filter fun i => h i < t).card - 1 ≤ beta α / n := by
        nlinarith
      have hR' : t - ts ≤ R := by
        have := hR j l; rw [hj, hl] at this; linarith [ht.2]
      have e3 := mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ t - ts)
      have e4 := mul_le_mul_of_nonneg_right hR' hc0
      nlinarith
  linarith

/-- Lemma 3 (b): `u` in the bracket `[h'_(ι⁻(m,α)), h'_(ι⁺(m,α))]` is within `(β/m) R'` of `min U`. -/
theorem critU_bracket {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (h : Fin m → ℝ) {R : ℝ}
    (hR : ∀ i j, h i - h j ≤ R) {u : ℝ}
    (hu : u ∈ Set.Icc (ordStat h (rkLo m α)) (ordStat h (rkHi m α))) (u' : ℝ) :
    critU α h u - critU α h u' ≤ beta α / m * R := by
  have hp1 : α ≤ 1 := by linarith
  have hβ : 0 ≤ beta α := by linarith [one_le_beta hα0 hα1]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc0 : 0 ≤ beta α / m := div_nonneg hβ hmR.le
  have hcnp : beta α / m * (m * (1 - α)) = 1 := by
    rw [beta_eq]; field_simp [(by linarith : (1 - α) ≠ 0)]
  -- the minimizer `u* = h'_(⌊mα⌋+1)`
  have hk1 : 1 ≤ ⌊(m : ℝ) * α⌋₊ + 1 := by omega
  have hkm : ⌊(m : ℝ) * α⌋₊ + 1 ≤ m := by
    have : ⌊(m : ℝ) * α⌋₊ < m := (Nat.floor_lt (by positivity)).mpr (by nlinarith)
    omega
  set k := ⌊(m : ℝ) * α⌋₊ + 1 with hk
  have hfl : (⌊(m : ℝ) * α⌋₊ : ℝ) ≤ m * α := Nat.floor_le (by positivity)
  have hfl' : (m : ℝ) * α < ⌊(m : ℝ) * α⌋₊ + 1 := Nat.lt_floor_add_one _
  have hkR : (k : ℝ) = ⌊(m : ℝ) * α⌋₊ + 1 := by rw [hk]; push_cast; ring
  set us := ordStat h k with hus
  -- (1) `U u* ≤ U u'`
  have h1 : critU α h us ≤ critU α h u' := by
    rcases le_total us u' with hle | hle
    · have e := le_critU_sub hβ h hle
      have hcnt : k ≤ (univ.filter fun i => h i ≤ us).card := card_le_ordStat h hk1 hkm
      have hsum := card_le_add_card_gt h us
      have hcnt' : ((univ.filter fun i => us < h i).card : ℝ) + k ≤ m := by
        have : (univ.filter fun i => us < h i).card + k ≤ m := by omega
        exact_mod_cast this
      have e2 := mul_le_mul_of_nonneg_left (by linarith :
        ((univ.filter fun i => us < h i).card : ℝ) ≤ m * (1 - α)) hc0
      have e3 : 0 ≤ (u' - us) * (1 - beta α / m * (univ.filter fun i => us < h i).card) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    · have e := critU_sub_le hβ h hle
      have hcnt : (univ.filter fun i => h i < us).card < k := card_lt_ordStat_lt h hk1 hkm
      have hsum := card_lt_add_card_ge h us
      have hcnt' : (m : ℝ) ≤ ((univ.filter fun i => us ≤ h i).card : ℝ) + ⌊(m : ℝ) * α⌋₊ := by
        have : m ≤ (univ.filter fun i => us ≤ h i).card + ⌊(m : ℝ) * α⌋₊ := by omega
        exact_mod_cast this
      have e2 := mul_le_mul_of_nonneg_left (by linarith :
        (m : ℝ) * (1 - α) ≤ ((univ.filter fun i => us ≤ h i).card : ℝ)) hc0
      have e3 : (us - u') * (1 - beta α / m * (univ.filter fun i => us ≤ h i).card) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
  -- (2) `U u − U u* ≤ (β/m) R`
  have h2 : critU α h u - critU α h us ≤ beta α / m * R := by
    have hLo1 := one_le_rkLo m α
    have hLon := rkLo_le hm hp1
    have hHi1 := one_le_rkHi hm α
    have hHin := rkHi_le m α
    obtain ⟨i, hi⟩ := exists_eq_ordStat h hLo1 hLon
    obtain ⟨j, hj⟩ := exists_eq_ordStat h hHi1 hHin
    obtain ⟨l, hl⟩ := exists_eq_ordStat h hk1 hkm
    rcases le_total us u with hle | hle
    · have e := critU_sub_le hβ h hle
      have hcnt : (univ.filter fun i => h i < u).card < rkHi m α :=
        card_lt_lt_of_le_ordStat h hHi1 hHin hu.2
      have hsum := card_lt_add_card_ge h u
      have hcnt' : (m : ℝ) + 1 ≤ ((univ.filter fun i => u ≤ h i).card : ℝ) + rkHi m α := by
        have : m + 1 ≤ (univ.filter fun i => u ≤ h i).card + rkHi m α := by omega
        exact_mod_cast this
      have hhi := rkHi_le_add_two m hα0
      have e2 := mul_le_mul_of_nonneg_left (by linarith :
        (m : ℝ) * (1 - α) - 1 ≤ ((univ.filter fun i => u ≤ h i).card : ℝ)) hc0
      have hf : 1 - beta α / m * (univ.filter fun i => u ≤ h i).card ≤ beta α / m := by
        nlinarith
      have hR' : u - us ≤ R := by
        have := hR j l; rw [hj, hl] at this; linarith [hu.2]
      have e3 := mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ u - us)
      have e4 := mul_le_mul_of_nonneg_right hR' hc0
      linarith
    · have e := le_critU_sub hβ h hle
      have hcnt : rkLo m α ≤ (univ.filter fun i => h i ≤ u).card :=
        (ordStat_le_iff h hLo1 hLon u).mp hu.1
      have hsum := card_le_add_card_gt h u
      have hcnt' : ((univ.filter fun i => u < h i).card : ℝ) + rkLo m α ≤ m := by
        have : (univ.filter fun i => u < h i).card + rkLo m α ≤ m := by omega
        exact_mod_cast this
      have hlo := sub_one_le_rkLo m α
      have e2 := mul_le_mul_of_nonneg_left (by linarith :
        ((univ.filter fun i => u < h i).card : ℝ) ≤ m * (1 - α) + 1) hc0
      have hf : beta α / m * (univ.filter fun i => u < h i).card - 1 ≤ beta α / m := by
        nlinarith
      have hR' : us - u ≤ R := by
        have := hR l i; rw [hl, hi] at this; linarith [hu.1]
      have e3 := mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ us - u)
      have e4 := mul_le_mul_of_nonneg_right hR' hc0
      nlinarith
  linarith

/-- Lemma 3 (c) for `T`: Lipschitz with constant `max(1, β − 1)` (any `n`, `α ∈ [0,1)`). -/
theorem critT_lipschitz {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (h : Fin n → ℝ) (t t' : ℝ) :
    |critT α h t - critT α h t'| ≤ max 1 (beta α - 1) * |t - t'| := by
  have hβ : 0 ≤ beta α := by linarith [one_le_beta hα0 hα1]
  refine abs_le_of_slopes (fun a b hab => ⟨?_, ?_⟩) t t'
  · have e := le_critT_sub hβ h hab
    have e2 := div_mul_card_le (n := n) hβ (card_filter_le_n h fun x => x < b)
    have e3 := mul_le_mul_of_nonneg_left (by linarith :
      1 - beta α ≤ 1 - beta α / n * (univ.filter fun i => h i < b).card) (by linarith : 0 ≤ b - a)
    linarith
  · have e := critT_sub_le hβ h hab
    have e2 : 0 ≤ beta α / n * (univ.filter fun i => h i ≤ a).card := by positivity
    have e3 := mul_le_mul_of_nonneg_left (by linarith :
      1 - beta α / n * (univ.filter fun i => h i ≤ a).card ≤ 1) (by linarith : 0 ≤ b - a)
    linarith

/-- Lemma 3 (c) for `U`: Lipschitz with constant `max(1, β − 1)` (any `m`, `α ∈ [0,1)`). -/
theorem critU_lipschitz {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (h : Fin m → ℝ) (u u' : ℝ) :
    |critU α h u - critU α h u'| ≤ max 1 (beta α - 1) * |u - u'| := by
  have hβ : 0 ≤ beta α := by linarith [one_le_beta hα0 hα1]
  refine abs_le_of_slopes (fun a b hab => ⟨?_, ?_⟩) u u'
  · have e := le_critU_sub hβ h hab
    have e2 := div_mul_card_le (n := m) hβ (card_filter_le_n h fun x => a < x)
    have e3 := mul_le_mul_of_nonneg_left (by linarith :
      1 - beta α ≤ 1 - beta α / m * (univ.filter fun i => a < h i).card) (by linarith : 0 ≤ b - a)
    linarith
  · have e := critU_sub_le hβ h hab
    have e2 : 0 ≤ beta α / m * (univ.filter fun i => b ≤ h i).card := by positivity
    have e3 := mul_le_mul_of_nonneg_left (by linarith :
      1 - beta α / m * (univ.filter fun i => b ≤ h i).card ≤ 1) (by linarith : 0 ≤ b - a)
    linarith

end Lemma3

/-! ### The frozen claims -/

theorem quantile_bracket_route : Claims.quantile_bracket := by
  intro n m α h h' R R' hα0 hα1
  refine ⟨fun hn hR t ht t' => critT_bracket hn hα0 hα1 h hR ht t',
    fun hm hR u hu u' => critU_bracket hm hα0 hα1 h' hR hu u',
    fun t t' => critT_lipschitz hα0 hα1 h t t', fun u u' => critU_lipschitz hα0 hα1 h' u u'⟩

theorem order_stat_shift_route : Claims.order_stat_shift := by
  intro n h h' ε k hk1 hkn hle
  exact ⟨ordStat_sub_le (fun i => (hle i).1) hk1 hkn, ordStat_mono (fun i => (hle i).2) hk1 hkn⟩

theorem numpy_bracket_route : Claims.numpy_bracket := by
  intro n p h hn hp0 hp1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ ((n : ℝ) - 1) * p := mul_nonneg (by linarith) hp0
  have hfl : (⌊((n : ℝ) - 1) * p⌋₊ : ℝ) ≤ ((n : ℝ) - 1) * p := Nat.floor_le hx0
  have hfl' : ((n : ℝ) - 1) * p < ⌊((n : ℝ) - 1) * p⌋₊ + 1 := Nat.lt_floor_add_one _
  have hA : ⌈(n : ℝ) * p⌉₊ - 1 ≤ ⌊((n : ℝ) - 1) * p⌋₊ + 1 := by
    have : ⌈(n : ℝ) * p⌉₊ ≤ ⌊((n : ℝ) - 1) * p⌋₊ + 2 := by
      apply Nat.ceil_le.mpr; push_cast; nlinarith
    omega
  have hB : ⌊((n : ℝ) - 1) * p⌋₊ + 2 ≤ ⌊(n : ℝ) * p⌋₊ + 2 := by
    have := Nat.floor_mono (show ((n : ℝ) - 1) * p ≤ n * p by nlinarith)
    omega
  refine ⟨hA, hB, ?_⟩
  have hlt : ⌊((n : ℝ) - 1) * p⌋₊ < n := (Nat.floor_lt hx0).mpr (by nlinarith)
  have hrlo : rkLo n p ≤ ⌊((n : ℝ) - 1) * p⌋₊ + 1 := max_le (by omega) hA
  have hrhi : min n (⌊((n : ℝ) - 1) * p⌋₊ + 2) ≤ rkHi n p := min_le_min_left _ hB
  unfold npQuantile
  generalize ⌊((n : ℝ) - 1) * p⌋₊ = F at *
  have hlo1 : 1 ≤ F + 1 := by omega
  have hlohi : F + 1 ≤ min n (F + 2) := le_min (by omega) (by omega)
  have hmono := ordStat_mono_rank h hlo1 hlohi (min_le_left _ _)
  have e1 := ordStat_mono_rank h (one_le_rkLo n p) hrlo (by omega)
  have e2 := ordStat_mono_rank h (hlo1.trans hlohi) hrhi (rkHi_le n p)
  have hf0 : 0 ≤ ((n : ℝ) - 1) * p - F := by linarith
  have hf1 : ((n : ℝ) - 1) * p - F ≤ 1 := by linarith
  constructor
  · nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hmono)]
  · nlinarith [mul_le_mul_of_nonneg_right hf1 (sub_nonneg.mpr hmono)]

theorem exact_quantile_bracket_route : Claims.exact_quantile_bracket := by
  intro n p q h hn hp0 hp1 hq ⟨i0, hi0⟩ ⟨i1, hi1⟩
  obtain ⟨hq1, hq2⟩ := hq
  constructor
  · rw [ordStat_le_iff h (one_le_rkLo n p) (rkLo_le hn hp1)]
    unfold rkLo
    refine max_le ?_ ?_
    · exact card_pos.mpr ⟨i0, by simp [hi0]⟩
    · have : ⌈(n : ℝ) * p⌉₊ ≤ (univ.filter fun i => h i ≤ q).card := Nat.ceil_le.mpr hq2
      omega
  · by_contra hlt
    rw [not_le] at hlt
    have hHi1 := one_le_rkHi hn p
    have hc : rkHi n p ≤ (univ.filter fun i => h i < q).card := by
      refine le_trans (card_le_ordStat h hHi1 (rkHi_le n p)) (card_le_card ?_)
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      linarith
    have hltn : (univ.filter fun i => h i < q).card < n := by
      have hss : (univ.filter fun i => h i < q) ⊂ univ :=
        filter_ssubset.mpr ⟨i1, mem_univ _, fun hlt' : h i1 < q => absurd hi1 (not_le.mpr hlt')⟩
      simpa using card_lt_card hss
    have hfl : (univ.filter fun i => h i < q).card ≤ ⌊(n : ℝ) * p⌋₊ := Nat.le_floor hq1
    unfold rkHi at hc
    omega

end StatFormal.Wave30tz
