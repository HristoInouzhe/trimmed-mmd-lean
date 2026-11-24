import StatFormal.Archive.Wave29d.Statements

/-!
# Route — robust equality JASA `thm:cert-chain`: `Γ_int ≤ Γ` and the subset-lattice dynamic programme (untrusted)

* `certchain_dp`: for any `T`, `dpVal T U` dominates every chain value `Σ_{l ≤ |U|} T(σ{0..l−1})` of a permutation `σ`
  with `σ{0..|U|−1} = U` (induction on the chain length), and is attained by one such `σ` (induction on `|U|`; the
  maximiser `i ∈ U` of the recursion is appended to a chain of `U ∖ {i}` by the permutation `swap (σ' |U|−1) i * σ'`).
  At `U = [r]` every permutation qualifies, and the summand vanishes on `[r]`, so the sum over `l ∈ (0, r]` is the
  sum over `l ∈ (0, r)` of `chainGamma`/`chainOsc`/`chainGammaInt`. (The step count `O(2^r r)` is not formalised.)
* `certchain_int_le`: for `t ≥ 0` the cells `[s_g, s_{g+1}) ∩ [0, t]` have lengths summing to `t` (telescoping);
  `(w(U) − m̲_g(U))_+ ≤ (w(U) − m̲_0(U))_+ = Ḡ(U)_+` and `s̄(U) ≥ 0`, so `Ā(U) ≤ s̄(U) Ḡ(U)_+` termwise.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.Wave29d

open StatFormal.Wave25a (chainSet sBar gBar chainGamma chainOsc)

section Combinatorics

variable {r : ℕ}

lemma mem_chainSet' (σ : Equiv.Perm (Fin r)) (l : ℕ) (x : Fin r) :
    x ∈ chainSet σ l ↔ ((σ.symm x : Fin r) : ℕ) < l := by
  simp [chainSet]

lemma chainSet_zero' (σ : Equiv.Perm (Fin r)) : chainSet σ 0 = ∅ := by
  ext x; simp [mem_chainSet']

lemma chainSet_self (σ : Equiv.Perm (Fin r)) : chainSet σ r = univ := by
  ext x; simp [mem_chainSet']

lemma not_mem_chainSet (σ : Equiv.Perm (Fin r)) {k : ℕ} (hk : k < r) : σ ⟨k, hk⟩ ∉ chainSet σ k := by
  simp [mem_chainSet']

lemma chainSet_succ (σ : Equiv.Perm (Fin r)) {k : ℕ} (hk : k < r) :
    chainSet σ (k + 1) = insert (σ ⟨k, hk⟩) (chainSet σ k) := by
  ext x
  rw [mem_insert, mem_chainSet', mem_chainSet']
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr h
    · left
      have : σ.symm x = ⟨k, hk⟩ := Fin.ext h
      exact (Equiv.symm_apply_eq σ).1 this
  · rintro (h | h)
    · subst h; simp
    · omega

lemma chainSet_ne_univ (σ : Equiv.Perm (Fin r)) {l : ℕ} (hl : l < r) : chainSet σ l ≠ univ := by
  intro h
  have := not_mem_chainSet σ hl
  rw [h] at this
  exact this (mem_univ _)

lemma chainSet_subset_of_agree {σ τ : Equiv.Perm (Fin r)} {l : ℕ} (h : ∀ j : Fin r, (j : ℕ) < l → σ j = τ j) :
    chainSet σ l ⊆ chainSet τ l := by
  intro x hx
  rw [mem_chainSet'] at hx ⊢
  have hx' : τ (σ.symm x) = x := by rw [← h _ hx]; simp
  have : τ.symm x = σ.symm x := by rw [Equiv.symm_apply_eq]; exact hx'.symm
  rw [this]; exact hx

lemma chainSet_congr {σ τ : Equiv.Perm (Fin r)} {l : ℕ} (h : ∀ j : Fin r, (j : ℕ) < l → σ j = τ j) :
    chainSet σ l = chainSet τ l :=
  Subset.antisymm (chainSet_subset_of_agree h) (chainSet_subset_of_agree fun j hj => (h j hj).symm)

/-- The value of the chain `σ{0}, σ{0,1}, …, σ{0..k−1}` under `T`. -/
def chainVal (T : Finset (Fin r) → ℝ) (σ : Equiv.Perm (Fin r)) (k : ℕ) : ℝ :=
  ∑ l ∈ range k, T (chainSet σ (l + 1))

lemma chainVal_congr (T : Finset (Fin r) → ℝ) {σ τ : Equiv.Perm (Fin r)} {k : ℕ}
    (h : ∀ j : Fin r, (j : ℕ) < k → σ j = τ j) : chainVal T σ k = chainVal T τ k := by
  unfold chainVal
  refine sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  rw [chainSet_congr fun j hj => h j (by omega)]

lemma dpVal_empty (T : Finset (Fin r) → ℝ) : dpVal T ∅ = 0 := by
  rw [dpVal]; simp

/-- Every chain value is dominated by the dynamic programme at its top set. -/
lemma chainVal_le_dpVal (T : Finset (Fin r) → ℝ) (σ : Equiv.Perm (Fin r)) :
    ∀ k, k ≤ r → chainVal T σ k ≤ dpVal T (chainSet σ k) := by
  intro k
  induction k with
  | zero => intro _; simp [chainVal, chainSet_zero', dpVal_empty]
  | succ k ih =>
    intro hk
    have hk' : k < r := by omega
    have hmem : σ ⟨k, hk'⟩ ∈ chainSet σ (k + 1) := by rw [chainSet_succ σ hk']; exact mem_insert_self _ _
    have hne : (chainSet σ (k + 1)).Nonempty := ⟨_, hmem⟩
    have herase : (chainSet σ (k + 1)).erase (σ ⟨k, hk'⟩) = chainSet σ k := by
      rw [chainSet_succ σ hk', erase_insert (not_mem_chainSet σ hk')]
    rw [dpVal, dif_pos hne]
    have h1 : chainVal T σ (k + 1) = chainVal T σ k + T (chainSet σ (k + 1)) := by
      simp [chainVal, sum_range_succ]
    have h2 : chainVal T σ k ≤ (chainSet σ (k + 1)).attach.sup' (attach_nonempty_iff.2 hne)
        fun i => dpVal T ((chainSet σ (k + 1)).erase i.1) := by
      refine le_trans (ih (by omega)) ?_
      refine le_sup'_of_le (fun i : {x // x ∈ chainSet σ (k + 1)} => dpVal T ((chainSet σ (k + 1)).erase i.1))
        (b := ⟨σ ⟨k, hk'⟩, hmem⟩) (mem_attach _ _) ?_
      simp only [herase, le_refl]
    linarith

/-- The dynamic programme is attained by a chain with top set `U`. -/
lemma exists_chainVal_ge (T : Finset (Fin r) → ℝ) :
    ∀ n (U : Finset (Fin r)), U.card = n → ∃ σ : Equiv.Perm (Fin r), chainSet σ n = U ∧ dpVal T U ≤ chainVal T σ n := by
  intro n
  induction n with
  | zero =>
    intro U hU
    rw [card_eq_zero] at hU
    subst hU
    exact ⟨1, chainSet_zero' _, by simp [dpVal_empty, chainVal]⟩
  | succ n ih =>
    intro U hU
    have hne : U.Nonempty := by rw [← card_pos]; omega
    have hn : n < r := by
      have := card_le_univ U
      rw [Fintype.card_fin] at this
      omega
    obtain ⟨⟨i, hi⟩, -, hmax⟩ := exists_mem_eq_sup' (attach_nonempty_iff.2 hne)
      (fun i : {x // x ∈ U} => dpVal T (U.erase i.1))
    obtain ⟨σ', hσ'U, hσ'le⟩ := ih (U.erase i) (by rw [card_erase_of_mem hi, hU]; rfl)
    set a := σ' ⟨n, hn⟩ with ha
    let σ : Equiv.Perm (Fin r) := Equiv.swap a i * σ'
    have hagree : ∀ j : Fin r, (j : ℕ) < n → σ j = σ' j := by
      intro j hj
      have hjm : σ' j ∈ U.erase i := by rw [← hσ'U, mem_chainSet']; simpa using hj
      have h1 : σ' j ≠ i := ne_of_mem_erase hjm
      have h2 : σ' j ≠ a := by
        intro h
        have : j = ⟨n, hn⟩ := σ'.injective h
        rw [this] at hj; simp at hj
      show Equiv.swap a i (σ' j) = σ' j
      exact Equiv.swap_apply_of_ne_of_ne h2 h1
    have hσn : σ ⟨n, hn⟩ = i := by
      show Equiv.swap a i (σ' ⟨n, hn⟩) = i
      rw [← ha]; exact Equiv.swap_apply_left a i
    have htop : chainSet σ (n + 1) = U := by
      rw [chainSet_succ σ hn, hσn, chainSet_congr hagree, hσ'U, insert_erase hi]
    refine ⟨σ, htop, ?_⟩
    rw [dpVal, dif_pos hne]
    simp only at hmax
    rw [hmax]
    have h1 : chainVal T σ (n + 1) = chainVal T σ n + T (chainSet σ (n + 1)) := by
      simp [chainVal, sum_range_succ]
    rw [h1, htop, chainVal_congr T hagree]
    linarith

/-- The dynamic programme at `[r]` is the maximum over all maximal chains. -/
lemma dpVal_univ (T : Finset (Fin r) → ℝ) :
    dpVal T univ = univ.sup' univ_nonempty fun σ : Equiv.Perm (Fin r) => chainVal T σ r := by
  apply le_antisymm
  · obtain ⟨σ, -, hle⟩ := exists_chainVal_ge T r univ (by simp)
    exact le_trans hle (le_sup' (fun σ : Equiv.Perm (Fin r) => chainVal T σ r) (mem_univ σ))
  · refine sup'_le _ _ fun σ _ => ?_
    have := chainVal_le_dpVal T σ r le_rfl
    rwa [chainSet_self] at this

/-- A summand vanishing on `[r]`: the chain value over `(0, r]` is the sum over `(0, r)`. -/
lemma chainVal_eq_Ioo (T f : Finset (Fin r) → ℝ) (hr : 0 < r) (hT : ∀ U, T U = if U = univ then 0 else f U)
    (σ : Equiv.Perm (Fin r)) : chainVal T σ r = ∑ l ∈ Ioo 0 r, f (chainSet σ l) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hI : Ioo 0 (n + 1) = Ico 1 (n + 1) := by ext l; simp; omega
  rw [chainVal, sum_range_succ, chainSet_self, hT univ, if_pos rfl, add_zero, hI, sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  rw [hT, if_neg (chainSet_ne_univ σ (by omega)), add_comm 1 l]

end Combinatorics

section Integral

variable {r S : ℕ}

/-- For `t ≥ 0` the cells `[s_g, s_{g+1}) ∩ [0, t]` (`s_{S+1} = ∞`) partition `[0, t]`. -/
lemma sum_segLen (s : Fin (S + 1) → ℝ) (h0 : s 0 = 0) (hs : StrictMono s) {t : ℝ} (ht : 0 ≤ t) :
    ∑ g, segLen s t g = t := by
  let a : ℕ → ℝ := fun n => if h : n < S + 1 then min (s ⟨n, h⟩) t else t
  have hnn : ∀ g, 0 ≤ s g := fun g => h0 ▸ hs.monotone (Fin.zero_le g)
  have hterm : ∀ g : Fin (S + 1), segLen s t g = a ((g : ℕ) + 1) - a g := by
    intro g
    have hag : a g = min (s g) t := by simp only [a, dif_pos g.isLt, Fin.eta]
    rw [hag, segLen, max_eq_left (hnn g)]
    by_cases h : (g : ℕ) + 1 < S + 1
    · have hlt : s g < s ⟨(g : ℕ) + 1, h⟩ := hs (show g < ⟨(g : ℕ) + 1, h⟩ from Fin.lt_def.2 (Nat.lt_succ_self _))
      have ha1 : a ((g : ℕ) + 1) = min (s ⟨(g : ℕ) + 1, h⟩) t := by simp only [a, dif_pos h]
      rw [dif_pos h, ha1]
      simp only [max_def, min_def]
      split_ifs <;> linarith
    · have ha1 : a ((g : ℕ) + 1) = t := by simp only [a, dif_neg h]
      rw [dif_neg h, ha1, min_self]
      simp only [max_def, min_def]
      split_ifs <;> linarith
  rw [Finset.sum_congr rfl fun g _ => hterm g, Fin.sum_univ_eq_sum_range (fun n => a (n + 1) - a n),
    sum_range_sub]
  have h0' : a 0 = 0 := by
    simp only [a, dif_pos (Nat.succ_pos S)]
    have : (⟨0, Nat.succ_pos S⟩ : Fin (S + 1)) = 0 := rfl
    rw [this, h0, min_eq_left ht]
  have hS : a (S + 1) = t := by simp [a]
  rw [h0', hS, sub_zero]

lemma sBar_nonneg (s : Fin (S + 1) → ℝ) (h0 : s 0 = 0) (hs : StrictMono s)
    (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) {smax : ℝ} (hsmax : 0 ≤ smax) (U : Finset (Fin r)) :
    0 ≤ sBar s mlow w smax U := by
  unfold sBar
  rw [le_fold_min]
  exact ⟨hsmax, fun g _ => h0 ▸ hs.monotone (Fin.zero_le g)⟩

lemma aBar_le (s : Fin (S + 1) → ℝ) (h0 : s 0 = 0) (hs : StrictMono s)
    (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) {smax : ℝ} (hsmax : 0 ≤ smax)
    (hmono : ∀ g U, mlow 0 U ≤ mlow g U) (U : Finset (Fin r)) :
    aBar s mlow w smax U ≤ sBar s mlow w smax U * max 0 (gBar mlow w U) := by
  unfold aBar
  calc ∑ g, max 0 (∑ i ∈ U, w i - mlow g U) * segLen s (sBar s mlow w smax U) g
      ≤ ∑ g, max 0 (gBar mlow w U) * segLen s (sBar s mlow w smax U) g := by
        refine sum_le_sum fun g _ => mul_le_mul_of_nonneg_right ?_ (le_max_left _ _)
        exact max_le_max le_rfl (by unfold gBar; linarith [hmono g U])
    _ = sBar s mlow w smax U * max 0 (gBar mlow w U) := by
        rw [← mul_sum, sum_segLen s h0 hs (sBar_nonneg s h0 hs mlow w hsmax U), mul_comm]

end Integral

theorem certchain_dp : Claims.certchain_dp := by
  intro r S s mlow w smax hr
  refine ⟨?_, ?_, ?_⟩
  · rw [dpVal_univ]
    exact sup'_congr _ rfl fun σ _ => chainVal_eq_Ioo _ _ hr (fun U => rfl) σ
  · rw [dpVal_univ]
    exact sup'_congr _ rfl fun σ _ => chainVal_eq_Ioo _ _ hr (fun U => rfl) σ
  · rw [dpVal_univ]
    exact sup'_congr _ rfl fun σ _ => chainVal_eq_Ioo _ _ hr (fun U => rfl) σ

theorem certchain_int_le : Claims.certchain_int_le := by
  intro r S s mlow w smax _ h0 hs hsmax hmono
  unfold chainGammaInt chainGamma
  refine sup'_le _ _ fun σ _ => le_sup'_of_le _ (mem_univ σ) ?_
  exact sum_le_sum fun l _ => aBar_le s h0 hs mlow w hsmax hmono _

end StatFormal.Wave29d
