import StatFormal.Lib.PaperRun.Pairing

/-!
# Wave 31tr, chunk A1, T2: the printed batches and pairing (untrusted route)

Proves `Claims.printedPairing_exists`, `Claims.printedPairing_batch`, `Claims.printedPairing_default` from the library
`StatFormal.Lib.PaperRun.Pairing` (construction by numpy's `array_split`, the batch-pairing properties) and
`StatFormal.Lib.PaperRun.Batches` (batches of `cutLabel` are intervals). T2 (c): nearest-integer boundaries are ordered and at most
`n` (`nearestCuts_bounds`), so `cutLabel 2` is `defaultLabel`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.Wave31tr.RouteRun

open StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.PaperRun

theorem printedPairing_exists_route : Claims.printedPairing_exists := by
  intro nb n m cx cy _ hcx hcy
  exact exists_printedPairing nb _ _ cx cy (fun b hb => cutLabel_batch_interval hcx hb)
    (fun b hb => cutLabel_batch_interval hcy hb)

theorem printedPairing_batch_route : Claims.printedPairing_batch := by
  intro nb n m N cx cy bat A B _ _ _ h
  obtain ⟨hbp, hempty, hne⟩ := isBatchPairing_of_printed h
  exact ⟨hbp, h.1, h.2.2.1, h.2.2.2.1, hempty, hne⟩

/-- Nearest-integer boundaries (any tie-breaking, any `n`): `b₁ ≤ b₂ ≤ n`. -/
theorem nearestCuts_bounds {n b1 b2 : ℕ} (hc : NearestCuts n b1 b2) : b1 ≤ b2 ∧ b2 ≤ n := by
  obtain ⟨h1, h2⟩ := hc
  rw [abs_le] at h1 h2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      have : (b1 : ℝ) < 1 := by push_cast at h1; linarith
      have : b1 = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
      omega
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      have : (b1 : ℝ) < b2 + 1 := by linarith
      exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
  · have : (b2 : ℝ) < n + 1 := by linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- With nearest-integer boundaries, the labels `cutLabel 2 c` are the default labels. -/
theorem cutLabel_two_eq_default {n : ℕ} {c : ℕ → ℕ} (hc : NearestCuts n (c 1) (c 2)) (i : ℕ) :
    cutLabel 2 c i = defaultLabel (c 1) (c 2) i := by
  obtain ⟨h12, h2n⟩ := nearestCuts_bounds hc
  have hb : IsBoundaries 2 n c := by
    refine ⟨fun a ha b hb hab => ?_, fun b hb => ?_⟩
    · obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
      interval_cases a <;> interval_cases b <;> first | exact le_rfl | exact h12 | omega
    · obtain ⟨hb1, hb2⟩ := hb
      interval_cases b <;> omega
  have l1 := le_cutLabel_iff hb (b := 1) ⟨le_rfl, by norm_num⟩ i
  have l2 := le_cutLabel_iff hb (b := 2) ⟨by norm_num, le_rfl⟩ i
  have l3 := cutLabel_le (nb := 2) c i
  unfold defaultLabel
  split_ifs with h1 h2 <;> omega

theorem printedPairing_default_route : Claims.printedPairing_default := by
  intro n m N cx cy bat A B hcx hcy
  have hsum : ∀ {N : ℕ} {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
      {B : Fin N → Finset (Fin m)}, IsPrintedPairing 2 lx ly bat A B → N = defaultPairs lx ly := by
    intro N lx ly bat A B h
    rw [h.1, defaultPairs, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton]
  refine ⟨cutLabel_two_eq_default hcx, cutLabel_two_eq_default hcy, hsum, fun 𝒳 J R hlx hly h => ?_⟩
  exact ⟨cx 1, cx 2, cy 1, cy 2, hcx, hcy, fun i => (hlx i).trans (cutLabel_two_eq_default hcx i),
    fun j => (hly j).trans (cutLabel_two_eq_default hcy j), hsum h⟩

end StatFormal.Wave31tr.RouteRun
