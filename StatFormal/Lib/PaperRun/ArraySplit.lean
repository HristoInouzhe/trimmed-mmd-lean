import StatFormal.Wave31tr.Statements

/-!
# numpy's `array_split`: consecutive blocks of sizes differing by at most one (library)

Library component (untrusted), pure arithmetic of `ℕ`. `Wave31tr.splitStart M K l = l⌊M/K⌋ + min(l, M mod K)` is the start of
block `l` when `M` items are cut into `K` consecutive blocks (numpy's `array_split`): the first `M mod K` blocks have `⌊M/K⌋ + 1`
items and the others `⌊M/K⌋`.

* `splitStart_zero`, `splitStart_succ` (the size of block `l`), `splitStart_self` (`K ≥ 1`: the blocks cover `[0, M)`);
* `splitStart_mono`, `splitStart_strictMono` (`1 ≤ K ≤ M`: nonempty blocks), `splitStart_le`;
* `splitStart_block_size`: the sizes are `⌊M/K⌋` or `⌊M/K⌋ + 1`, so any two differ by at most one;
* `exists_block`, `block_unique`: every `r < M` lies in exactly one block `l < K`.

Also `card_filter_fin_Ico`: `#{i : Fin n | a ≤ i < b} = b − a` for `b ≤ n` (copy-adapted from `Wave31tl.Arith.card_fin_Ico`).
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.PaperRun

open StatFormal.Wave31tr

/-- `#{i : Fin n | a ≤ i < b} = b − a` for `b ≤ n` (copy-adapted from `StatFormal.Wave31tl.Arith.card_fin_Ico`). -/
theorem card_filter_fin_Ico (n a b : ℕ) (hb : b ≤ n) :
    (univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).card = b - a := by
  have e : (univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).map Fin.valEmbedding = Finset.Ico a b := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨k, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [← card_map, e, Nat.card_Ico]

theorem splitStart_zero (M K : ℕ) : splitStart M K 0 = 0 := by simp [splitStart]

/-- Block `l` has `⌊M/K⌋ + [l < M mod K]` items. -/
theorem splitStart_succ (M K l : ℕ) :
    splitStart M K (l + 1) = splitStart M K l + M / K + if l < M % K then 1 else 0 := by
  unfold splitStart
  rw [Nat.succ_mul]
  generalize l * (M / K) = t
  generalize M / K = q
  generalize M % K = r
  split_ifs with h
  · rw [min_eq_left (by omega : l + 1 ≤ r), min_eq_left (by omega : l ≤ r)]; omega
  · rw [min_eq_right (by omega : r ≤ l + 1), min_eq_right (by omega : r ≤ l)]; omega

/-- For `K ≥ 1` the `K` blocks cover `[0, M)`: `splitStart M K K = M`. -/
theorem splitStart_self (M K : ℕ) (hK : 1 ≤ K) : splitStart M K K = M := by
  unfold splitStart
  rw [min_eq_right (Nat.mod_lt M (by omega)).le]
  exact Nat.div_add_mod M K

theorem splitStart_mono (M K : ℕ) : Monotone (splitStart M K) :=
  monotone_nat_of_le_succ fun l => by
    rw [splitStart_succ]; generalize M / K = q; split_ifs <;> omega

/-- For `1 ≤ K ≤ M` every block is nonempty. -/
theorem splitStart_strictMono (M K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ M) : StrictMono (splitStart M K) :=
  strictMono_nat_of_lt_succ fun l => by
    have : 1 ≤ M / K := (Nat.one_le_div_iff (by omega)).mpr hKM
    rw [splitStart_succ]; generalize M / K = q at this; split_ifs <;> omega

theorem splitStart_le (M K : ℕ) (hK : 1 ≤ K) {l : ℕ} (hl : l ≤ K) : splitStart M K l ≤ M :=
  (splitStart_mono M K hl).trans (splitStart_self M K hK).le

/-- The size of block `l` is `⌊M/K⌋` or `⌊M/K⌋ + 1`. -/
theorem splitStart_block_size (M K l : ℕ) :
    M / K ≤ splitStart M K (l + 1) - splitStart M K l ∧ splitStart M K (l + 1) - splitStart M K l ≤ M / K + 1 := by
  rw [splitStart_succ]; generalize M / K = q; split_ifs <;> omega

/-- Every `r < M` lies in some block `l < K` (`K ≥ 1`). -/
theorem exists_block (M K : ℕ) (hK : 1 ≤ K) {r : ℕ} (hr : r < M) :
    ∃ l < K, splitStart M K l ≤ r ∧ r < splitStart M K (l + 1) := by
  classical
  have hex : ∃ l, r < splitStart M K (l + 1) := ⟨K - 1, by rw [Nat.sub_add_cancel hK, splitStart_self M K hK]; exact hr⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have := Nat.find_min' hex (show r < splitStart M K (K - 1 + 1) by
      rw [Nat.sub_add_cancel hK, splitStart_self M K hK]; exact hr)
    omega
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, splitStart_zero]; exact Nat.zero_le r
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel hpos] at hmin
      exact not_lt.mp hmin

/-- The block containing `r` is unique. -/
theorem block_unique (M K : ℕ) {r l l' : ℕ} (h1 : splitStart M K l ≤ r) (h2 : r < splitStart M K (l + 1))
    (h1' : splitStart M K l' ≤ r) (h2' : r < splitStart M K (l' + 1)) : l = l' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := splitStart_mono M K (show l + 1 ≤ l' by omega); omega
  · have := splitStart_mono M K (show l' + 1 ≤ l by omega); omega

end StatFormal.PaperRun
