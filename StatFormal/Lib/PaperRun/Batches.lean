import StatFormal.Lib.PaperRun.ArraySplit

/-!
# Batches cut at boundaries: labels, batch sizes and fitting sizes (library)

Library component (untrusted). For interior boundaries `c 1 ≤ ⋯ ≤ c nb ≤ n` (`Wave31tr.IsBoundaries nb n c`), the label of index
`i` is `cutLabel nb c i = #{b ∈ [1, nb] : c b ≤ i}`. With the extended boundaries `extBnd nb n c` (`0` at `b = 0`, `c b` on
`[1, nb]`, `n` above), batch `b ≤ nb` is the interval `[extBnd b, extBnd (b+1))`:

* `le_cutLabel_iff` (`b ∈ [1, nb]`): `b ≤ cutLabel nb c i ↔ c b ≤ i`; `le_cutLabel_iff_ext`, `cutLabel_lt_iff`, `cutLabel_eq_iff`;
* `batchCount_cutLabel`: `n_b = extBnd (b+1) − extBnd b`; `fitCard_cutLabel`: `n_{<b} = extBnd b` (`= c b` on `[1, nb]`);
* `cutLabel_batch_interval`: on `[1, nb]` the batch is `[c b, c b + n_b)`, the form used by the pairing construction.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.PaperRun

open StatFormal.Wave31tr StatFormal.Wave31tl StatFormal.Wave30tz

/-- The extended boundaries: `0` at `b = 0`, `c b` for `1 ≤ b ≤ nb`, `n` above. -/
def extBnd (nb n : ℕ) (c : ℕ → ℕ) (b : ℕ) : ℕ := if b = 0 then 0 else if b ≤ nb then c b else n

variable {nb n : ℕ} {c : ℕ → ℕ}

theorem extBnd_of_mem {b : ℕ} (hb : b ∈ Set.Icc 1 nb) : extBnd nb n c b = c b := by
  unfold extBnd; rw [ite_eq_right (by have := hb.1; omega), ite_eq_left hb.2]

theorem extBnd_le (hc : IsBoundaries nb n c) (b : ℕ) : extBnd nb n c b ≤ n := by
  unfold extBnd
  split_ifs with h0 h1
  · exact Nat.zero_le n
  · exact hc.2 b ⟨by omega, h1⟩
  · exact le_rfl

theorem extBnd_mono (hc : IsBoundaries nb n c) : Monotone (extBnd nb n c) := by
  intro a b hab
  unfold extBnd
  by_cases ha0 : a = 0
  · simp only [ha0, ite_true]; exact Nat.zero_le _
  have hb0 : b ≠ 0 := by omega
  simp only [ha0, hb0, ite_false]
  by_cases hb1 : b ≤ nb
  · have ha1 : a ≤ nb := hab.trans hb1
    simp only [ha1, hb1, ite_true]
    exact hc.1 ⟨by omega, ha1⟩ ⟨by omega, hb1⟩ hab
  · simp only [hb1, ite_false]
    split_ifs with ha1
    · exact hc.2 a ⟨by omega, ha1⟩
    · exact le_rfl

/-- The label is at most `nb`. -/
theorem cutLabel_le (c : ℕ → ℕ) (i : ℕ) : cutLabel nb c i ≤ nb := by
  unfold cutLabel
  exact (card_filter_le _ _).trans (by simp)

/-- For `b ∈ [1, nb]`: index `i` is in batch `b` or later iff `c b ≤ i` (monotone boundaries). -/
theorem le_cutLabel_iff (hc : IsBoundaries nb n c) {b : ℕ} (hb : b ∈ Set.Icc 1 nb) (i : ℕ) :
    b ≤ cutLabel nb c i ↔ c b ≤ i := by
  unfold cutLabel
  constructor
  · intro hle
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    have hsub : ((Finset.Icc 1 nb).filter fun b' => c b' ≤ i) ⊆ Finset.Ico 1 b := by
      intro b' hb'
      simp only [Finset.mem_filter, Finset.mem_Icc] at hb'
      simp only [Finset.mem_Ico]
      refine ⟨hb'.1.1, lt_of_not_ge fun hge => ?_⟩
      have := hc.1 ⟨hb.1, hb.2⟩ ⟨hb'.1.1, hb'.1.2⟩ hge
      omega
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    have := hb.1
    omega
  · intro hci
    have hsub : Finset.Icc 1 b ⊆ (Finset.Icc 1 nb).filter fun b' => c b' ≤ i := by
      intro b' hb'
      simp only [Finset.mem_Icc] at hb'
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hb'.1, hb'.2.trans hb.2⟩, (hc.1 ⟨hb'.1, hb'.2.trans hb.2⟩ ⟨hb.1, hb.2⟩ hb'.2).trans hci⟩
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    omega

/-- For `b ≤ nb + 1` and `i < n`: `b ≤ cutLabel nb c i ↔ extBnd b ≤ i`. -/
theorem le_cutLabel_iff_ext (hc : IsBoundaries nb n c) {b i : ℕ} (hb : b ≤ nb + 1) (hi : i < n) :
    b ≤ cutLabel nb c i ↔ extBnd nb n c b ≤ i := by
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · simp [extBnd]
  rcases Nat.lt_or_ge nb b with hnb | hnb
  · have hbe : b = nb + 1 := by omega
    have : extBnd nb n c b = n := by unfold extBnd; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [this]
    have := cutLabel_le (nb := nb) c i
    constructor <;> intro h <;> omega
  · rw [extBnd_of_mem ⟨hb1, hnb⟩]; exact le_cutLabel_iff hc ⟨hb1, hnb⟩ i

theorem cutLabel_lt_iff (hc : IsBoundaries nb n c) {b i : ℕ} (hb : b ≤ nb + 1) (hi : i < n) :
    cutLabel nb c i < b ↔ i < extBnd nb n c b := by
  rw [← not_le, le_cutLabel_iff_ext hc hb hi, not_le]

/-- Batch `b ≤ nb` is `[extBnd b, extBnd (b+1))`. -/
theorem cutLabel_eq_iff (hc : IsBoundaries nb n c) {b i : ℕ} (hb : b ≤ nb) (hi : i < n) :
    cutLabel nb c i = b ↔ extBnd nb n c b ≤ i ∧ i < extBnd nb n c (b + 1) := by
  rw [← le_cutLabel_iff_ext hc (by omega) hi, ← cutLabel_lt_iff hc (by omega) hi]
  omega

/-- The size of batch `b ≤ nb`. -/
theorem batchCount_cutLabel (hc : IsBoundaries nb n c) {b : ℕ} (hb : b ≤ nb) :
    batchCount (fun i : Fin n => cutLabel nb c i) b = extBnd nb n c (b + 1) - extBnd nb n c b := by
  unfold batchCount
  have e : (univ.filter fun i : Fin n => cutLabel nb c i = b) =
      univ.filter fun i : Fin n => extBnd nb n c b ≤ (i : ℕ) ∧ (i : ℕ) < extBnd nb n c (b + 1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact cutLabel_eq_iff hc hb i.isLt
  rw [e, card_filter_fin_Ico n _ _ (extBnd_le hc _)]

/-- The size of the fitting sample of batch `b ≤ nb + 1`. -/
theorem fitCard_cutLabel (hc : IsBoundaries nb n c) {b : ℕ} (hb : b ≤ nb + 1) :
    fitCard (fun i : Fin n => cutLabel nb c i) b = extBnd nb n c b := by
  unfold fitCard
  have e : (univ.filter fun i : Fin n => cutLabel nb c i < b) =
      univ.filter fun i : Fin n => 0 ≤ (i : ℕ) ∧ (i : ℕ) < extBnd nb n c b := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_le]; exact cutLabel_lt_iff hc hb i.isLt
  rw [e, card_filter_fin_Ico n _ _ (extBnd_le hc _), Nat.sub_zero]

/-- On `[1, nb]` the batch is the interval `[c b, c b + n_b)` inside `[0, n)`. -/
theorem cutLabel_batch_interval (hc : IsBoundaries nb n c) {b : ℕ} (hb : b ∈ Finset.Icc 1 nb) :
    c b + batchCount (fun i : Fin n => cutLabel nb c i) b ≤ n ∧
      ∀ i : Fin n, cutLabel nb c i = b ↔ c b ≤ (i : ℕ) ∧ (i : ℕ) < c b + batchCount (fun i : Fin n => cutLabel nb c i) b := by
  rw [Finset.mem_Icc] at hb
  have hb' : b ∈ Set.Icc 1 nb := ⟨hb.1, hb.2⟩
  rw [batchCount_cutLabel hc hb.2]
  have hm := extBnd_mono hc (Nat.le_add_right b 1)
  have hle := extBnd_le hc (b + 1)
  rw [extBnd_of_mem hb'] at hm ⊢
  refine ⟨by omega, fun i => ?_⟩
  rw [cutLabel_eq_iff hc hb.2 i.isLt, extBnd_of_mem hb']
  omega

end StatFormal.PaperRun
