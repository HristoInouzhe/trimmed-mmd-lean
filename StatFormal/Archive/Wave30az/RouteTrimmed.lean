import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Proofs

/-!
# Route — trimmed MMD `lem:trimmedmean`: the minimum, sufficiency and uniqueness of the maximiser clause

* Minimum: the certified greedy point for `u = −v` along the reversed sort (`u ∘ τ` monotone), the exchange argument,
  and the reflection `Σ_{j ∈ [n−k, n)} v_(n−j) = Σ_{j < k} v_(j+1)`.
* Sufficiency: the exchange identity `Σ w v − Σ w' v = Σ (w − w')(v − θ)` vanishes termwise against the greedy point.
* Uniqueness: the certified `trimmedmean_argmax` fixes every coordinate off the tie set; with distinct values the tie
  set is a singleton and the tied sum fixes it; for `k = n`, `nc = 1` forces `w ≡ c`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.Wave30az

open StatFormal.TrimmedMMD.BangBang

theorem trimmedmean_min : Claims.trimmedmean_min := by
  intro n v α hn hα0 hα1
  obtain ⟨hc, hkc, hk1, hkn, hkn'⟩ := cap_facts hn hα0 hα1
  set k := kfloor n α with hkdef
  set τ : Equiv.Perm (Fin n) := (Fin.revPerm).trans (Tuple.sort v) with hτ
  have hmono : Monotone ((fun i => -v i) ∘ τ) := by
    intro a b hab
    simp only [Function.comp, hτ, Equiv.trans_apply, Fin.revPerm_apply, neg_le_neg_iff]
    exact Tuple.monotone_sort v (Fin.rev_le_rev.2 hab)
  obtain ⟨w', hw', hs', h1, h2, hval⟩ :=
    greedy hn hc hkc hk1 hkn hkn' (fun i => -v i) τ hmono (fun j => -ord v (n - 1 - j))
      (fun j h => by
        simp only [hτ, Equiv.trans_apply, Fin.revPerm_apply, ord]
        rw [dif_pos (by omega)]
        congr 3
        ext
        simp [Fin.val_rev]
        omega)
  have hrefl : ∑ j ∈ Ico (n - k) n, ord v (n - 1 - j) = ∑ j ∈ range k, ord v j := by
    rw [Finset.sum_Ico_eq_sum_range, show n - (n - k) = k by omega]
    rw [← Finset.sum_range_reflect (fun j => ord v j) k]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    congr 1
    omega
  have hval' : ∑ i, w' i * v i = cap n α * ∑ j ∈ range k, ord v j +
      (if k < n then (1 - k * cap n α) * ord v k else 0) := by
    have e1 : ∑ i, w' i * v i = -∑ i, w' i * (-v i) := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e1, hval, ← hrefl]
    simp only [sum_neg_distrib]
    by_cases hk : k < n
    · rw [if_pos hk, if_pos hk, show n - 1 - (n - k - 1) = k by omega]; ring
    · rw [if_neg hk, if_neg hk]; ring
  refine ⟨⟨w', ⟨hw', hs'⟩, hval'⟩, ?_⟩
  rintro _ ⟨w, ⟨hw, hs⟩, rfl⟩
  show _ ≤ _
  rw [← hval']
  have hterm := exch_term (u := fun i => -v i) hw h1 h2
  have hid := exch_sum (-v (τ ⟨n - k - 1, by omega⟩)) (fun i => -v i) w w' hs hs'
  have := Finset.sum_nonpos (fun i (_ : i ∈ univ) => hterm i)
  have e2 : ∀ u : Fin n → ℝ, ∑ i, u i * (-v i) = -∑ i, u i * v i := fun u => by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
  simp only [e2] at hid
  linarith

theorem trimmedmean_suff : Claims.trimmedmean_suff := by
  intro n v α w hn hα0 hα1 hk hw h1 h2
  obtain ⟨hc, hkc, hk1, hkn, hkn'⟩ := cap_facts hn hα0 hα1
  obtain ⟨w', hw', hs', g1, g2, hval⟩ :=
    greedy hn hc hkc hk1 hkn hkn' v (Tuple.sort v) (Tuple.monotone_sort v) (ord v)
      (fun j h => by simp [ord, h])
  have hθ : v (Tuple.sort v ⟨n - kfloor n α - 1, by omega⟩) = ord v (n - kfloor n α - 1) := by
    unfold ord; rw [dif_pos (by omega)]
  rw [hθ] at g1 g2
  have hid := exch_sum (ord v (n - kfloor n α - 1)) v w w' hw.2 hs'
  have hz : ∀ i, (w i - w' i) * (v i - ord v (n - kfloor n α - 1)) = 0 := by
    intro i
    rcases lt_trichotomy (v i) (ord v (n - kfloor n α - 1)) with h | h | h
    · rw [h2 i h, g2 i h]; ring
    · rw [h]; ring
    · rw [h1 i h, g1 i h]; ring
  rw [sum_eq_zero fun i _ => hz i] at hid
  have heq : ∑ i, w i * v i = ∑ i, w' i * v i := by linarith
  have hG := StatFormal.TrimmedMMD.BangBang.trimmedmean_value n v α hn hα0 hα1
  intro w'' hw''
  show ∑ i, w'' i * v i ≤ ∑ i, w i * v i
  rw [heq, hval]
  exact hG.2 ⟨w'', hw'', rfl⟩

theorem trimmedmean_unique : Claims.trimmedmean_unique := by
  intro n v α w w' hn hα0 hα1 hw hw' hmax hmax'
  obtain ⟨hc, hkc, hk1, hkn, hkn'⟩ := cap_facts hn hα0 hα1
  have hconst : kfloor n α = n → ∀ u ∈ capped n α, u = fun _ => 1 / (n : ℝ) := by
    intro hk u hu
    have hnc := hkn' hk
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hcap : cap n α = 1 / n := by field_simp; linarith
    have hsum : ∑ i, (cap n α - u i) = 0 := by
      rw [sum_sub_distrib, hu.2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hnc, sub_self]
    have := (sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hu.1 i).2)).1 hsum
    funext i
    have := this i (mem_univ _)
    rw [← hcap]; linarith
  have hoff : kfloor n α < n → ∀ i, v i ≠ ord v (n - kfloor n α - 1) → w i = w' i := by
    intro hk i hi
    obtain ⟨a1, a2, -⟩ := StatFormal.TrimmedMMD.BangBang.trimmedmean_argmax n v α w hn hα0 hα1 hk hmax hw
    obtain ⟨b1, b2, -⟩ := StatFormal.TrimmedMMD.BangBang.trimmedmean_argmax n v α w' hn hα0 hα1 hk hmax' hw'
    rcases lt_or_gt_of_ne hi with h | h
    · rw [a2 i h, b2 i h]
    · rw [a1 i h, b1 i h]
  refine ⟨?_, hoff, fun hk => hconst hk w hw⟩
  intro hinj
  by_cases hk : kfloor n α < n
  · funext i
    by_cases hi : v i = ord v (n - kfloor n α - 1)
    · obtain ⟨-, -, a3⟩ := StatFormal.TrimmedMMD.BangBang.trimmedmean_argmax n v α w hn hα0 hα1 hk hmax hw
      obtain ⟨-, -, b3⟩ := StatFormal.TrimmedMMD.BangBang.trimmedmean_argmax n v α w' hn hα0 hα1 hk hmax' hw'
      have hsing : univ.filter (fun j => v j = ord v (n - kfloor n α - 1)) = {i} := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hj; exact hinj (hj.trans hi.symm)
        · rintro rfl; exact hi
      simp only [hsing, sum_singleton] at a3 b3
      rw [a3, b3]
    · exact hoff hk i hi
  · have hk' : kfloor n α = n := le_antisymm hkn (not_lt.1 hk)
    rw [hconst hk' w hw, hconst hk' w' hw']

end StatFormal.Wave30az
