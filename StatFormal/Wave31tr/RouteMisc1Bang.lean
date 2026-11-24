import StatFormal.Wave31tr.Statements
import StatFormal.Wave31ta.RouteBang

/-!
# Wave 31tr, chunk M1: `bangbang_aos` (T27)

The certified `Wave31ta.bangbang_v2` in the `EReal` order-statistic wording: `t̂_n = ↑(ord dx (kfloor n α))` when `kfloor n α < n`
(`EReal.coe_lt_coe_iff`, `EReal.coe_eq_coe_iff` transport the three clauses), `⊤` when `kfloor n α = n`, which forces `α = 0`, all
weights `= cap n 0 = 1/n`, an empty tie set and remaining mass `1 − n · (1/n) = 0`; symmetrically with `⊥` on the `Y` side.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteMisc1

open StatFormal.TrimmedMMD.BangBang

/-- `⌊n(1−α)⌋ ≤ n` for `α ≥ 0`. -/
lemma kfloor_le (n : ℕ) {α : ℝ} (hα : 0 ≤ α) : kfloor n α ≤ n := by
  unfold kfloor
  refine Nat.floor_le_of_le ?_
  have : (n : ℝ) * (1 - α) ≤ n := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact this

/-- `kfloor n α = n` with `n ≥ 1`, `α ∈ [0,1)` forces `cap n α · n = 1` (`α = 0`). -/
lemma cap_mul_eq_one {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hk : kfloor n α = n) :
    cap n α * (n : ℝ) = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ n * (1 - α) := by
    have := Nat.floor_le (show 0 ≤ (n : ℝ) * (1 - α) by nlinarith)
    unfold kfloor at hk; rw [hk] at this; exact this
  have hα0 : α = 0 := by nlinarith
  subst hα0
  unfold cap; rw [sub_zero, mul_one]; field_simp

theorem bangbang_aos_route : Claims.bangbang_aos := by
  intro 𝒳 H _ _ _ _ φ α n m x y hφ hα0 hα1 hn hm
  have V := StatFormal.Wave31ta.bangbang_v2 𝒳 H φ α n m x y hφ hα0 hα1 hn hm
  obtain ⟨h1, h2, h3, h4, h5⟩ := V
  refine ⟨h1, h2, h3, ?_, h5⟩
  intro hD p hp
  obtain ⟨hxlt, hxeq, hylt, hyeq⟩ := h4 hD p hp
  set dx : Fin n → ℝ := fun i => ⟪StatFormal.Wave4b.witness φ x y p, φ (x i)⟫_ℝ with hdx
  set dy : Fin m → ℝ := fun j => ⟪StatFormal.Wave4b.witness φ x y p, φ (y j)⟫_ℝ with hdy
  have hkx := kfloor_le n hα0
  have hky := kfloor_le m hα0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hk : kfloor n α < n
    · simp only [hk, ↓reduceIte, EReal.coe_lt_coe_iff] at hi
      exact (hxlt hk).1 i hi
    · exact hxeq (by omega) i
  · intro i hi
    by_cases hk : kfloor n α < n
    · simp only [hk, ↓reduceIte, EReal.coe_lt_coe_iff] at hi
      exact (hxlt hk).2.1 i hi
    · simp only [hk, ↓reduceIte] at hi; exact absurd hi (not_lt.2 le_top)
  · by_cases hk : kfloor n α < n
    · simp only [hk, ↓reduceIte, EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff]
      exact (hxlt hk).2.2
    · have hk' : kfloor n α = n := by omega
      have e1 : (Finset.univ.filter fun i => ((dx i : ℝ) : EReal) = ⊤) = ∅ := by ext i; simp
      have e2 : (Finset.univ.filter fun i => ((dx i : ℝ) : EReal) < ⊤) = Finset.univ := by ext i; simp
      simp only [hk, ↓reduceIte]
      rw [e1, e2, Finset.sum_empty, Finset.card_univ, Fintype.card_fin, cap_mul_eq_one hn hα0 hα1 hk']; ring
  · intro j hj
    by_cases hk : kfloor m α < m
    · simp only [hk, ↓reduceIte, EReal.coe_lt_coe_iff] at hj
      exact (hylt hk).1 j hj
    · exact hyeq (by omega) j
  · intro j hj
    by_cases hk : kfloor m α < m
    · simp only [hk, ↓reduceIte, EReal.coe_lt_coe_iff] at hj
      exact (hylt hk).2.1 j hj
    · simp only [hk, ↓reduceIte] at hj; exact absurd hj (not_lt.2 bot_le)
  · by_cases hk : kfloor m α < m
    · simp only [hk, ↓reduceIte, EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff]
      exact (hylt hk).2.2
    · have hk' : kfloor m α = m := by omega
      have e1 : (Finset.univ.filter fun j => ((dy j : ℝ) : EReal) = ⊥) = ∅ := by ext j; simp
      have e2 : (Finset.univ.filter fun j => (⊥ : EReal) < ((dy j : ℝ) : EReal)) = Finset.univ := by ext j; simp
      simp only [hk, ↓reduceIte]
      rw [e1, e2, Finset.sum_empty, Finset.card_univ, Fintype.card_fin, cap_mul_eq_one hm hα0 hα1 hk']; ring

end StatFormal.Wave31tr.RouteMisc1
