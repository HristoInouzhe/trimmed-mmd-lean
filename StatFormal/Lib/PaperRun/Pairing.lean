import StatFormal.Lib.PaperRun.Batches

/-!
# The printed pairing: existence (numpy's `array_split`) and the batch-pairing properties (library)

Library component (untrusted), for any labels `lx : Fin n → ℕ`, `ly : Fin m → ℕ` whose batches `b ∈ [1, nb]` are consecutive
intervals `[ox b, ox b + n_b)`, `[oy b, oy b + m_b)` (`n_b = batchCount lx b`, `m_b = batchCount ly b`):

* counting of the pairs: `pre cnt b = Σ_{1 ≤ b′ < b} cnt b′` and the batch of pair `k`, `batOf cnt nb k = 1 + #{b ∈ [1, nb] :
  pre (b+1) ≤ k}`, characterized by `pre b ≤ k < pre (b+1)` (`batOf_eq`, `batOf_spec`) and monotone;
* `batch_clauses`: in one batch, singletons on the smaller side and `array_split` blocks on the larger side satisfy the six
  per-batch clauses of `Wave31tr.IsPrintedPairing` (used for both orientations);
* `exists_printedPairing`: a printed pairing exists, with the explicit description of `Claims.printedPairing_exists`;
* `batch_facts`, `isBatchPairing_of_printed`: every printed pairing is a `Wave30tv.IsBatchPairing` (nonempty blocks by a counting
  argument, disjoint blocks by the uniqueness clauses), and a batch with an empty side holds no pair.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.PaperRun

open StatFormal.Wave31tr StatFormal.Wave31tl StatFormal.Wave30tv StatFormal.Wave30tq

/-! ### Counting the pairs batch by batch -/

section Count

variable (cnt : ℕ → ℕ) (nb : ℕ)

/-- The number of pairs of the batches `1, …, b − 1`. -/
def pre (b : ℕ) : ℕ := ∑ b' ∈ Finset.Ico 1 b, cnt b'

/-- The batch of pair `k` (pairs numbered batch by batch). -/
def batOf (k : ℕ) : ℕ := 1 + ((Finset.Icc 1 nb).filter fun b => pre cnt (b + 1) ≤ k).card

variable {cnt nb}

theorem pre_succ {b : ℕ} (hb : 1 ≤ b) : pre cnt (b + 1) = pre cnt b + cnt b := by
  unfold pre; rw [Finset.sum_Ico_succ_top hb]

theorem pre_mono : Monotone (pre cnt) := fun _ _ hab =>
  Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hab)

theorem pre_top : pre cnt (nb + 1) = ∑ b ∈ Finset.Icc 1 nb, cnt b := by
  unfold pre; rw [Finset.Ico_add_one_right_eq_Icc]

theorem batOf_mono : Monotone (batOf cnt nb) := fun _ _ hkk' =>
  Nat.add_le_add_left (card_le_card fun b hb => by
    simp only [Finset.mem_filter] at hb ⊢; exact ⟨hb.1, hb.2.trans hkk'⟩) 1

/-- `pre b ≤ k < pre (b+1)` with `b ∈ [1, nb]` pins the batch of `k`. -/
theorem batOf_eq {b k : ℕ} (hb : b ∈ Finset.Icc 1 nb) (h1 : pre cnt b ≤ k) (h2 : k < pre cnt (b + 1)) :
    batOf cnt nb k = b := by
  rw [Finset.mem_Icc] at hb
  have e : ((Finset.Icc 1 nb).filter fun b' => pre cnt (b' + 1) ≤ k) = Finset.Ico 1 b := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1', h2'⟩, h3'⟩
      refine ⟨h1', lt_of_not_ge fun hge => ?_⟩
      have := pre_mono (cnt := cnt) (show b + 1 ≤ b' + 1 by omega)
      omega
    · rintro ⟨h1', h2'⟩
      exact ⟨⟨h1', by omega⟩, (pre_mono (cnt := cnt) (show b' + 1 ≤ b by omega)).trans h1⟩
  unfold batOf; rw [e, Nat.card_Ico]; omega

/-- Every pair `k < Σ_{b ∈ [1, nb]} cnt b` has its batch in `[1, nb]`, and `pre (batOf k) ≤ k < pre (batOf k + 1)`. -/
theorem batOf_spec {k : ℕ} (hk : k < ∑ b ∈ Finset.Icc 1 nb, cnt b) :
    1 ≤ batOf cnt nb k ∧ batOf cnt nb k ≤ nb ∧ pre cnt (batOf cnt nb k) ≤ k ∧ k < pre cnt (batOf cnt nb k + 1) := by
  classical
  rw [← pre_top] at hk
  have hex : ∃ b, k < pre cnt (b + 1) := ⟨nb, hk⟩
  set b₀ := Nat.find hex with hb₀
  have hspec : k < pre cnt (b₀ + 1) := Nat.find_spec hex
  have hle : b₀ ≤ nb := Nat.find_min' hex hk
  have hpos : 1 ≤ b₀ := by
    rcases Nat.eq_zero_or_pos b₀ with h0 | h0
    · rw [h0] at hspec; simp [pre] at hspec
    · exact h0
  have hlo : pre cnt b₀ ≤ k := by
    have hmin := Nat.find_min hex (show b₀ - 1 < b₀ by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    exact not_lt.mp hmin
  have := batOf_eq (cnt := cnt) (nb := nb) (Finset.mem_Icc.mpr ⟨hpos, hle⟩) hlo hspec
  rw [this]
  exact ⟨hpos, hle, hlo, hspec⟩

end Count

/-! ### One batch: singletons against `array_split` blocks -/

/-- The six per-batch clauses of `IsPrintedPairing` for a batch `b` whose smaller side (`K` items at offset `ox`) is paired one to
one, pair `k` getting item `ox + lk k`, with the `array_split` blocks of the larger side (`M` items at offset `oy`). Stated for one
orientation; the mirror clauses are the same lemma with the two sides exchanged. -/
theorem batch_clauses {n m N : ℕ} (bat : Fin N → ℕ) (b : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (ox oy K M : ℕ) (lk : Fin N → ℕ)
    (hK : 1 ≤ K) (hKM : K ≤ M) (hox : ox + K ≤ n) (hoy : oy + M ≤ m)
    (hlx : ∀ i : Fin n, lx i = b ↔ ox ≤ (i : ℕ) ∧ (i : ℕ) < ox + K)
    (hly : ∀ j : Fin m, ly j = b ↔ oy ≤ (j : ℕ) ∧ (j : ℕ) < oy + M)
    (hlk : ∀ k, bat k = b → lk k < K)
    (hsurj : ∀ l < K, ∃ k, bat k = b ∧ lk k = l)
    (hinj : ∀ k k', bat k = b → bat k' = b → lk k = lk k' → k = k')
    (hA : ∀ k, bat k = b → ∀ i : Fin n, i ∈ A k ↔ (i : ℕ) = ox + lk k)
    (hB : ∀ k, bat k = b → ∀ j : Fin m,
      j ∈ B k ↔ oy + splitStart M K (lk k) ≤ (j : ℕ) ∧ (j : ℕ) < oy + splitStart M K (lk k + 1)) :
    (∀ k, bat k = b → ∃ i, lx i = b ∧ A k = {i}) ∧
    (∀ i, lx i = b → (Finset.univ.filter fun k => bat k = b ∧ A k = {i}).card = 1) ∧
    (∀ k, bat k = b → ∀ j ∈ B k, ly j = b) ∧
    (∀ j, ly j = b → (Finset.univ.filter fun k => bat k = b ∧ j ∈ B k).card = 1) ∧
    (∀ k, bat k = b → ∀ j j' j'' : Fin m, j ∈ B k → j'' ∈ B k → j ≤ j' → j' ≤ j'' → j' ∈ B k) ∧
    (∀ k k', bat k = b → bat k' = b → (B k).card ≤ (B k').card + 1) := by
  have hAeq : ∀ k (hk : bat k = b), A k = {⟨ox + lk k, by have := hlk k hk; omega⟩} := fun k hk => by
    ext i; rw [hA k hk, Finset.mem_singleton, Fin.ext_iff]
  have hBeq : ∀ k, bat k = b → B k = univ.filter fun j : Fin m =>
      oy + splitStart M K (lk k) ≤ (j : ℕ) ∧ (j : ℕ) < oy + splitStart M K (lk k + 1) := fun k hk => by
    ext j; rw [hB k hk]; simp
  have hsM : ∀ k, bat k = b → splitStart M K (lk k + 1) ≤ M := fun k hk =>
    splitStart_le M K hK (hlk k hk)
  refine ⟨fun k hk => ⟨_, (hlx _).mpr ⟨by simp, by have := hlk k hk; simp; omega⟩, hAeq k hk⟩, fun i hi => ?_,
    fun k hk j hj => ?_, fun j hj => ?_, fun k hk j j' j'' h1 h2 h3 h4 => ?_, fun k k' hk hk' => ?_⟩
  · -- (2) each item of the smaller side is the singleton of exactly one pair
    obtain ⟨hi1, hi2⟩ := (hlx i).mp hi
    obtain ⟨k₀, hk₀, hl₀⟩ := hsurj ((i : ℕ) - ox) (by omega)
    rw [Finset.card_eq_one]
    refine ⟨k₀, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hAk⟩
      have hmem : i ∈ A k := by rw [hAk]; exact Finset.mem_singleton_self i
      rw [hA k hk] at hmem
      exact hinj k k₀ hk hk₀ (by omega)
    · rintro rfl
      refine ⟨hk₀, ?_⟩
      rw [hAeq k hk₀]; congr 1; ext; simp only; omega
  · -- (3) blocks lie in the batch
    rw [hB k hk] at hj
    have := hsM k hk
    exact (hly j).mpr ⟨by omega, by omega⟩
  · -- (4) each item of the larger side lies in exactly one block
    obtain ⟨hj1, hj2⟩ := (hly j).mp hj
    obtain ⟨l, hlK, hl1, hl2⟩ := exists_block M K hK (show (j : ℕ) - oy < M by omega)
    obtain ⟨k₀, hk₀, hl₀⟩ := hsurj l hlK
    rw [Finset.card_eq_one]
    refine ⟨k₀, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hjk⟩
      rw [hB k hk] at hjk
      have := block_unique M K (r := (j : ℕ) - oy) (l := lk k) (l' := l) (by omega) (by omega) hl1 hl2
      exact hinj k k₀ hk hk₀ (by omega)
    · rintro rfl
      refine ⟨hk₀, ?_⟩
      rw [hB k hk₀, hl₀]; omega
  · -- (5) blocks are order-convex
    rw [hB k hk] at h1 h2 ⊢
    rw [Fin.le_iff_val_le_val] at h3 h4
    omega
  · -- (6) block sizes differ by at most one
    rw [hBeq k hk, hBeq k' hk', card_filter_fin_Ico m _ _ (by have := hsM k hk; omega),
      card_filter_fin_Ico m _ _ (by have := hsM k' hk'; omega)]
    have h1 := splitStart_block_size M K (lk k)
    have h2 := splitStart_block_size M K (lk k')
    omega

/-! ### Existence of a printed pairing -/

/-- **A printed pairing exists** (numpy's `array_split`; T2 (a)): for labels whose batches `b ∈ [1, nb]` are the intervals
`[ox b, ox b + n_b)` and `[oy b, oy b + m_b)`, the pairs numbered batch by batch, pair `Σ_{b′<b} min(n_{b′}, m_{b′}) + l` of batch `b`
pairs item `l` of the smaller side with block `l` of the larger side. -/
theorem exists_printedPairing {n m : ℕ} (nb : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (ox oy : ℕ → ℕ)
    (hx : ∀ b ∈ Finset.Icc 1 nb, ox b + batchCount lx b ≤ n ∧
      ∀ i : Fin n, lx i = b ↔ ox b ≤ (i : ℕ) ∧ (i : ℕ) < ox b + batchCount lx b)
    (hy : ∀ b ∈ Finset.Icc 1 nb, oy b + batchCount ly b ≤ m ∧
      ∀ j : Fin m, ly j = b ↔ oy b ≤ (j : ℕ) ∧ (j : ℕ) < oy b + batchCount ly b) :
    ∃ (N : ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)),
      IsPrintedPairing nb lx ly bat A B ∧
      ∀ b ∈ Finset.Icc 1 nb, ∀ l : ℕ, l < min (batchCount lx b) (batchCount ly b) →
        ∃ k : Fin N, (k : ℕ) = (∑ b' ∈ Finset.Ico 1 b, min (batchCount lx b') (batchCount ly b')) + l ∧ bat k = b ∧
          (batchCount lx b ≤ batchCount ly b →
            (∀ i : Fin n, i ∈ A k ↔ (i : ℕ) = ox b + l) ∧
            ∀ j : Fin m, j ∈ B k ↔ oy b + splitStart (batchCount ly b) (batchCount lx b) l ≤ (j : ℕ) ∧
              (j : ℕ) < oy b + splitStart (batchCount ly b) (batchCount lx b) (l + 1)) ∧
          (batchCount ly b < batchCount lx b →
            (∀ j : Fin m, j ∈ B k ↔ (j : ℕ) = oy b + l) ∧
            ∀ i : Fin n, i ∈ A k ↔ ox b + splitStart (batchCount lx b) (batchCount ly b) l ≤ (i : ℕ) ∧
              (i : ℕ) < ox b + splitStart (batchCount lx b) (batchCount ly b) (l + 1)) := by
  set cnt : ℕ → ℕ := fun b => min (batchCount lx b) (batchCount ly b) with hcnt
  set N : ℕ := ∑ b ∈ Finset.Icc 1 nb, cnt b with hN
  let bat : Fin N → ℕ := fun k => batOf cnt nb k
  let lk : Fin N → ℕ := fun k => (k : ℕ) - pre cnt (bat k)
  let A : Fin N → Finset (Fin n) := fun k =>
    if batchCount lx (bat k) ≤ batchCount ly (bat k) then univ.filter fun i : Fin n => (i : ℕ) = ox (bat k) + lk k
    else univ.filter fun i : Fin n => ox (bat k) + splitStart (batchCount lx (bat k)) (batchCount ly (bat k)) (lk k) ≤ (i : ℕ) ∧
      (i : ℕ) < ox (bat k) + splitStart (batchCount lx (bat k)) (batchCount ly (bat k)) (lk k + 1)
  let B : Fin N → Finset (Fin m) := fun k =>
    if batchCount lx (bat k) ≤ batchCount ly (bat k) then univ.filter fun j : Fin m => oy (bat k) + splitStart (batchCount ly (bat k)) (batchCount lx (bat k)) (lk k) ≤ (j : ℕ) ∧
      (j : ℕ) < oy (bat k) + splitStart (batchCount ly (bat k)) (batchCount lx (bat k)) (lk k + 1)
    else univ.filter fun j : Fin m => (j : ℕ) = oy (bat k) + lk k
  have hspec : ∀ k : Fin N, 1 ≤ bat k ∧ bat k ≤ nb ∧ pre cnt (bat k) ≤ k ∧ (k : ℕ) < pre cnt (bat k) + cnt (bat k) :=
    fun k => by
      obtain ⟨h1, h2, h3, h4⟩ := batOf_spec (cnt := cnt) (nb := nb) k.isLt
      exact ⟨h1, h2, h3, by rwa [pre_succ h1] at h4⟩
  have hpreN : ∀ b ∈ Finset.Icc 1 nb, pre cnt b + cnt b ≤ N := fun b hb => by
    rw [Finset.mem_Icc] at hb
    rw [← pre_succ hb.1, hN, ← pre_top]; exact pre_mono (by omega)
  -- the pair `pre b + l` of batch `b`
  have hbat : ∀ b ∈ Finset.Icc 1 nb, ∀ l < cnt b, ∀ h : pre cnt b + l < N,
      bat ⟨pre cnt b + l, h⟩ = b ∧ lk ⟨pre cnt b + l, h⟩ = l := fun b hb l hl h => by
    have hb1 := (Finset.mem_Icc.mp hb).1
    have e : bat ⟨pre cnt b + l, h⟩ = b := batOf_eq hb (by simp) (by simp only; rw [pre_succ hb1]; omega)
    refine ⟨e, ?_⟩
    simp only [lk, e]; omega
  have hlk : ∀ b, ∀ k : Fin N, bat k = b → lk k < cnt b := fun b k hk => by
    have := hspec k; simp only [lk]; rw [← hk]; omega
  have hsurj : ∀ b ∈ Finset.Icc 1 nb, ∀ l < cnt b, ∃ k : Fin N, bat k = b ∧ lk k = l := fun b hb l hl =>
    ⟨⟨pre cnt b + l, by have := hpreN b hb; omega⟩, hbat b hb l hl _⟩
  have hinj : ∀ b, ∀ k k' : Fin N, bat k = b → bat k' = b → lk k = lk k' → k = k' := fun b k k' hk hk' hl => by
    have h1 := hspec k; have h2 := hspec k'
    simp only [lk] at hl
    rw [hk] at h1 hl; rw [hk'] at h2 hl
    exact Fin.ext (by omega)
  refine ⟨N, bat, A, B, ⟨rfl, fun k k' hkk' => batOf_mono (Fin.le_iff_val_le_val.mp hkk'),
    fun k => ⟨(hspec k).1, (hspec k).2.1⟩, fun b hb => ?_, fun b hb => ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩⟩, fun b hb l hl => ?_⟩
  · -- the number of pairs of batch `b`
    have e : (univ.filter fun k : Fin N => bat k = b) =
        univ.filter fun k : Fin N => pre cnt b ≤ (k : ℕ) ∧ (k : ℕ) < pre cnt b + cnt b := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro rfl; exact ⟨(hspec k).2.2.1, (hspec k).2.2.2⟩
      · rintro ⟨h1, h2⟩
        exact batOf_eq hb h1 (by rw [pre_succ (Finset.mem_Icc.mp hb).1]; exact h2)
    rw [e, card_filter_fin_Ico N _ _ (hpreN b hb)]
    simp only [hcnt]; omega
  · -- batch with `1 ≤ n_b ≤ m_b`
    have hc : cnt b = batchCount lx b := min_eq_left h2
    obtain ⟨hxb, hxl⟩ := hx b hb
    obtain ⟨hyb, hyl⟩ := hy b hb
    refine batch_clauses bat b lx ly A B (ox b) (oy b) (batchCount lx b) (batchCount ly b) lk h1 h2 hxb hyb hxl hyl
      (fun k hk => hc ▸ hlk b k hk) (fun l hl => hsurj b hb l (hc ▸ hl)) (hinj b) (fun k hk i => ?_) (fun k hk j => ?_)
    · simp only [A, hk, ite_eq_left h2, Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [B, hk, ite_eq_left h2, Finset.mem_filter, Finset.mem_univ, true_and]
  · -- batch with `1 ≤ m_b < n_b` (mirror)
    have hc : cnt b = batchCount ly b := min_eq_right h2.le
    obtain ⟨hxb, hxl⟩ := hx b hb
    obtain ⟨hyb, hyl⟩ := hy b hb
    refine batch_clauses bat b ly lx B A (oy b) (ox b) (batchCount ly b) (batchCount lx b) lk h1 h2.le hyb hxb hyl hxl
      (fun k hk => hc ▸ hlk b k hk) (fun l hl => hsurj b hb l (hc ▸ hl)) (hinj b) (fun k hk j => ?_) (fun k hk i => ?_)
    · simp only [B, hk, ite_eq_right (not_le.mpr h2), Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [A, hk, ite_eq_right (not_le.mpr h2), Finset.mem_filter, Finset.mem_univ, true_and]
  · -- the explicit description
    have hl' : l < cnt b := hl
    have hk : pre cnt b + l < N := by have := hpreN b hb; omega
    obtain ⟨e1, e2⟩ := hbat b hb l hl' hk
    refine ⟨⟨pre cnt b + l, hk⟩, rfl, e1, fun hle => ⟨fun i => ?_, fun j => ?_⟩, fun hlt => ⟨fun j => ?_, fun i => ?_⟩⟩
    · simp only [A, e1, e2, ite_eq_left hle, Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [B, e1, e2, ite_eq_left hle, Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [B, e1, e2, ite_eq_right (not_le.mpr hlt), Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [A, e1, e2, ite_eq_right (not_le.mpr hlt), Finset.mem_filter, Finset.mem_univ, true_and]

/-! ### Every printed pairing is a batch pairing -/

/-- Inside one batch whose pairs are as many as the items of the singleton side: the blocks are nonempty (the blocks of the
larger side partition its `≥ K` items into `K` blocks of sizes differing by at most one), lie in the batch, and are pairwise
disjoint. -/
theorem batch_facts {n m N : ℕ} (bat : Fin N → ℕ) (b : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (hcard : (univ.filter fun k => bat k = b).card = batchCount lx b) (hle : batchCount lx b ≤ batchCount ly b)
    (hC : (∀ k, bat k = b → ∃ i, lx i = b ∧ A k = {i}) ∧
      (∀ i, lx i = b → (Finset.univ.filter fun k => bat k = b ∧ A k = {i}).card = 1) ∧
      (∀ k, bat k = b → ∀ j ∈ B k, ly j = b) ∧
      (∀ j, ly j = b → (Finset.univ.filter fun k => bat k = b ∧ j ∈ B k).card = 1) ∧
      (∀ k, bat k = b → ∀ j j' j'' : Fin m, j ∈ B k → j'' ∈ B k → j ≤ j' → j' ≤ j'' → j' ∈ B k) ∧
      (∀ k k', bat k = b → bat k' = b → (B k).card ≤ (B k').card + 1)) :
    ∀ k, bat k = b → (A k).Nonempty ∧ (B k).Nonempty ∧ (∀ i ∈ A k, lx i = b) ∧ (∀ j ∈ B k, ly j = b) ∧
      ∀ k', bat k' = b → k ≠ k' → Disjoint (A k) (A k') ∧ Disjoint (B k) (B k') := by
  classical
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := hC
  set T := univ.filter fun k : Fin N => bat k = b with hT
  have hdisjB : ∀ k, bat k = b → ∀ k', bat k' = b → k ≠ k' → Disjoint (B k) (B k') := by
    intro k hk k' hk' hne
    rw [Finset.disjoint_left]
    intro j hj hj'
    have hlj := h3 k hk j hj
    have := Finset.card_le_one.mp (h4 j hlj).le k (by simp [hk, hj]) k' (by simp [hk', hj'])
    exact hne this
  have hunion : T.biUnion B = univ.filter fun j => ly j = b := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, hT]
    constructor
    · rintro ⟨k, hk, hj⟩; exact h3 k hk j hj
    · intro hj
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (by rw [h4 j hj]; exact Nat.one_pos)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact ⟨k, hk.1, hk.2⟩
  have hsum : ∑ k ∈ T, (B k).card = batchCount ly b := by
    rw [← Finset.card_biUnion (fun k hk k' hk' hne => hdisjB k (by simpa [hT] using hk) k' (by simpa [hT] using hk') hne),
      hunion]
    rfl
  intro k hk
  obtain ⟨i, hi, hAi⟩ := h1 k hk
  refine ⟨⟨i, by rw [hAi]; exact Finset.mem_singleton_self i⟩, ?_, fun i' hi' => ?_, h3 k hk, fun k' hk' hne => ⟨?_, hdisjB k hk k' hk' hne⟩⟩
  · -- nonempty block: otherwise every block of the batch has at most one item
    rw [Finset.nonempty_iff_ne_empty]
    intro hBk
    have hkT : k ∈ T := by simp [hT, hk]
    have hle1 : ∀ k' ∈ T.erase k, (B k').card ≤ 1 := fun k' hk' => by
      have := h6 k' k (by simpa [hT] using (Finset.mem_erase.mp hk').2) hk
      rwa [hBk, Finset.card_empty] at this
    have hs := Finset.add_sum_erase T (fun k => (B k).card) hkT
    have hb := Finset.sum_le_card_nsmul (T.erase k) (fun k => (B k).card) 1 hle1
    rw [Finset.card_erase_of_mem hkT, hcard, smul_eq_mul, mul_one] at hb
    rw [hBk, Finset.card_empty, zero_add, hsum] at hs
    have hpos : 1 ≤ batchCount lx b := by rw [← hcard]; exact Finset.card_pos.mpr ⟨k, hkT⟩
    omega
  · rw [hAi, Finset.mem_singleton] at hi'; rw [hi']; exact hi
  · obtain ⟨i', hi'l, hAi'⟩ := h1 k' hk'
    rw [hAi, hAi', Finset.disjoint_singleton]
    intro hii
    subst hii
    have := Finset.card_le_one.mp (h2 i hi).le k (by simp [hk, hAi]) k' (by simp [hk', hAi'])
    exact hne this

/-- **Every printed pairing is a batch pairing** (T2 (b)): nonempty, pairwise disjoint blocks inside the batch of the pair,
pairs numbered in the order of the batches; and a batch with an empty side holds no pair. -/
theorem isBatchPairing_of_printed {n m N nb : ℕ} {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ}
    {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)} (h : IsPrintedPairing nb lx ly bat A B) :
    IsBatchPairing lx ly bat A B ∧ (∀ b, (batchCount lx b = 0 ∨ batchCount ly b = 0) → ∀ k, bat k ≠ b) ∧
      ∀ k, (A k).Nonempty ∧ (B k).Nonempty := by
  classical
  obtain ⟨-, hmono, hrange, hcount, hbatch⟩ := h
  have hpos : ∀ k, 1 ≤ batchCount lx (bat k) ∧ 1 ≤ batchCount ly (bat k) := fun k => by
    have hb : bat k ∈ Finset.Icc 1 nb := Finset.mem_Icc.mpr (hrange k)
    have := hcount (bat k) hb
    have hp : 0 < (univ.filter fun k' => bat k' = bat k).card := Finset.card_pos.mpr ⟨k, by simp⟩
    rw [this] at hp
    exact ⟨by omega, by omega⟩
  have key : ∀ k, (A k).Nonempty ∧ (B k).Nonempty ∧ (∀ i ∈ A k, lx i = bat k) ∧ (∀ j ∈ B k, ly j = bat k) ∧
      ∀ k', bat k' = bat k → k ≠ k' → Disjoint (A k) (A k') ∧ Disjoint (B k) (B k') := by
    intro k
    have hb : bat k ∈ Finset.Icc 1 nb := Finset.mem_Icc.mpr (hrange k)
    rcases le_or_gt (batchCount lx (bat k)) (batchCount ly (bat k)) with hle | hlt
    · have hc := hcount (bat k) hb
      rw [min_eq_left hle] at hc
      exact batch_facts bat (bat k) lx ly A B hc hle ((hbatch (bat k) hb).1 (hpos k).1 hle) k rfl
    · have hc := hcount (bat k) hb
      rw [min_eq_right hlt.le] at hc
      obtain ⟨h1, h2, h3, h4, h5⟩ := batch_facts bat (bat k) ly lx B A hc hlt.le ((hbatch (bat k) hb).2 (hpos k).2 hlt) k rfl
      exact ⟨h2, h1, h4, h3, fun k' hk' hne => (h5 k' hk' hne).symm⟩
  refine ⟨⟨⟨fun k => (key k).1, fun k => (key k).2.1, fun k k' hne => ?_, fun k k' hne => ?_⟩, hmono,
    fun k => (hrange k).1, fun k => (key k).2.2.1, fun k => (key k).2.2.2.1⟩, fun b hb k hk => ?_, fun k => ⟨(key k).1, (key k).2.1⟩⟩
  · by_cases hbk : bat k' = bat k
    · exact ((key k).2.2.2.2 k' hbk hne).1
    · rw [Finset.disjoint_left]
      intro i hi hi'
      exact hbk (((key k').2.2.1 i hi').symm.trans ((key k).2.2.1 i hi))
  · by_cases hbk : bat k' = bat k
    · exact ((key k).2.2.2.2 k' hbk hne).2
    · rw [Finset.disjoint_left]
      intro j hj hj'
      exact hbk (((key k').2.2.2.1 j hj').symm.trans ((key k).2.2.2.1 j hj))
  · subst hk
    have := hpos k
    omega

end StatFormal.PaperRun
