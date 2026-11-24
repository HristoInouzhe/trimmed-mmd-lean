import StatFormal.Archive.ICL.Statements
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Proofs of the CPS claims (untrusted proof file)
-/

noncomputable section
open Finset

namespace StatFormal.ICL

variable {n : ℕ}

/-- Bijection `S ↦ S.erase ℓ` between `M`-subsets containing `ℓ` and `(M-1)`-subsets of `univ.erase ℓ`. -/
lemma sum_filter_mem_eq (M : ℕ) (hM : 1 ≤ M) (ℓ : Fin n) (f : Finset (Fin n) → ℝ) :
    ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∈ S), f S =
      ∑ T ∈ (univ.erase ℓ).powersetCard (M - 1), f (insert ℓ T) := by
  refine Finset.sum_nbij' (fun S => S.erase ℓ) (fun T => insert ℓ T) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS
    simp only [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · exact erase_subset_erase ℓ (subset_univ S)
    · rw [card_erase_of_mem hS.2, hS.1.2]
  · intro T hT
    simp only [mem_powersetCard] at hT
    simp only [mem_filter, mem_powersetCard, mem_insert_self, and_true, subset_univ, true_and]
    have hℓ : ℓ ∉ T := fun h => by simpa using hT.1 h
    rw [card_insert_of_notMem hℓ, hT.2]
    omega
  · intro S hS
    simp only [mem_filter] at hS
    exact insert_erase hS.2
  · intro T hT
    simp only [mem_powersetCard] at hT
    have hℓ : ℓ ∉ T := fun h => by simpa using hT.1 h
    exact erase_insert hℓ
  · intro S hS
    simp only [mem_filter] at hS
    rw [insert_erase hS.2]

lemma notMem_of_mem_erase_powerset {ℓ : Fin n} {k : ℕ} {T : Finset (Fin n)}
    (hT : T ∈ (univ.erase ℓ).powersetCard k) : ℓ ∉ T := by
  rw [mem_powersetCard] at hT
  intro h
  simpa using hT.1 h

lemma prod_insert_of_mem_erase {w : Fin n → ℝ} {ℓ : Fin n} {k : ℕ} {T : Finset (Fin n)}
    (hT : T ∈ (univ.erase ℓ).powersetCard k) :
    ∏ j ∈ insert ℓ T, w j = w ℓ * ∏ j ∈ T, w j :=
  prod_insert (notMem_of_mem_erase_powerset hT)

/-- Positivity of `esym` when there are enough nonzero nonnegative weights. -/
lemma esym_pos (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (s : Finset (Fin n)) (k : ℕ)
    (hk : k ≤ (s.filter fun j => w j ≠ 0).card) : 0 < esym w s k := by
  obtain ⟨T, hTs, hTc⟩ := exists_subset_card_eq hk
  unfold esym
  apply sum_pos'
  · intro S _
    exact prod_nonneg fun j _ => hw j
  · refine ⟨T, ?_, ?_⟩
    · rw [mem_powersetCard]
      exact ⟨hTs.trans (filter_subset _ _), hTc⟩
    · apply prod_pos
      intro j hj
      have := hTs hj
      rw [mem_filter] at this
      exact lt_of_le_of_ne (hw j) (Ne.symm this.2)

lemma esym_univ_pos {M : ℕ} {w : Fin n → ℝ} (hw : InDeltaM w M) : 0 < esym w univ M :=
  esym_pos w hw.1 univ M hw.2.2

lemma esym_erase_pos {M : ℕ} {w : Fin n → ℝ} (hw : InDeltaM w M) (ℓ : Fin n) :
    0 < esym w (univ.erase ℓ) (M - 1) := by
  apply esym_pos w hw.1
  rw [filter_erase]
  have := pred_card_le_card_erase (s := univ.filter fun j => w j ≠ 0) (a := ℓ)
  have h2 := hw.2.2
  omega

lemma incl_eq {M : ℕ} (hM : 1 ≤ M) (w : Fin n → ℝ) (ℓ : Fin n) :
    incl w M ℓ = w ℓ * esym w (univ.erase ℓ) (M - 1) / esym w univ M := by
  unfold incl cps
  rw [sum_filter_mem_eq M hM ℓ, ← sum_div]
  congr 1
  rw [esym, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  exact prod_insert_of_mem_erase hT

/-- Double counting: `Σ_ℓ Σ_{S ∋ ℓ} F S = M Σ_S F S`. -/
lemma sum_sum_filter_mem (M : ℕ) (F : Finset (Fin n) → ℝ) :
    ∑ ℓ, ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∈ S), F S =
      M * ∑ S ∈ univ.powersetCard M, F S := by
  simp_rw [sum_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, (mem_powersetCard.mp hS).2]

lemma incl_mul_Vrisk {M : ℕ} (hM : 1 ≤ M) {w : Fin n → ℝ} (hw : InDeltaM w M)
    (L : Finset (Fin n) → ℝ) (ℓ : Fin n) :
    incl w M ℓ * Vrisk w M L ℓ =
      ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∈ S), cps w univ M S * L S := by
  have ha := (esym_erase_pos hw ℓ).ne'
  have he := (esym_univ_pos hw).ne'
  rw [incl_eq hM, sum_filter_mem_eq M hM ℓ, Vrisk, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  unfold cps
  rw [prod_insert_of_mem_erase hT]
  field_simp

theorem cps_wellPosed : Claims.cps_wellPosed := by
  intro n M w hw
  have he := esym_univ_pos hw
  refine ⟨he, ?_, ?_⟩
  · intro S _
    exact div_nonneg (prod_nonneg fun j _ => hw.1 j) he.le
  · unfold cps
    rw [← sum_div]
    exact div_self he.ne'

theorem cps_incl : Claims.cps_incl := by
  intro n M w hM hw
  refine ⟨fun ℓ => incl_eq hM w ℓ, ?_⟩
  unfold incl
  rw [sum_sum_filter_mem]
  have := (cps_wellPosed n M w hw).2.2
  rw [this, mul_one]

theorem cps_conditional : Claims.cps_conditional := by
  intro n M w L hM hw
  refine ⟨?_, ?_⟩
  · intro ℓ hπ T hT
    have ha := (esym_erase_pos hw ℓ).ne'
    have he := (esym_univ_pos hw).ne'
    have hwℓ : w ℓ ≠ 0 := by
      intro h
      rw [incl_eq hM, h] at hπ
      simp at hπ
    rw [incl_eq hM]
    unfold cps
    rw [prod_insert_of_mem_erase hT]
    field_simp
  · simp_rw [incl_mul_Vrisk hM hw L]
    rw [sum_sum_filter_mem]
    rfl

theorem cps_condExp : Claims.cps_condExp := by
  intro n M w L hM hw ℓ hπ
  rw [← incl_mul_Vrisk hM hw L]
  field_simp

/-- Affine dependence on the `ℓ`-th coordinate. -/
lemma sum_update_affine (M : ℕ) (hM : 1 ≤ M) (w : Fin n → ℝ) (ℓ : Fin n)
    (g : Finset (Fin n) → ℝ) (t : ℝ) :
    ∑ S ∈ univ.powersetCard M, (∏ j ∈ S, Function.update w ℓ t j) * g S =
      t * (∑ T ∈ (univ.erase ℓ).powersetCard (M - 1), (∏ j ∈ T, w j) * g (insert ℓ T)) +
        ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∉ S), (∏ j ∈ S, w j) * g S := by
  rw [← sum_filter_add_sum_filter_not _ (fun S => ℓ ∈ S), sum_filter_mem_eq M hM ℓ, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have hℓ := notMem_of_mem_erase_powerset hT
    rw [prod_insert hℓ, Function.update_self, prod_update_of_notMem hℓ]
    ring
  · refine sum_congr rfl fun S hS => ?_
    rw [mem_filter] at hS
    rw [prod_update_of_notMem hS.2]

lemma Grisk_update (M : ℕ) (hM : 1 ≤ M) (w : Fin n → ℝ) (L : Finset (Fin n) → ℝ) (ℓ : Fin n)
    (t : ℝ) :
    Grisk (Function.update w ℓ t) M L =
      (t * (∑ T ∈ (univ.erase ℓ).powersetCard (M - 1), (∏ j ∈ T, w j) * L (insert ℓ T)) +
        ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∉ S), (∏ j ∈ S, w j) * L S) /
      (t * esym w (univ.erase ℓ) (M - 1) +
        ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∉ S), (∏ j ∈ S, w j)) := by
  have h1 := sum_update_affine M hM w ℓ (fun _ => 1) t
  simp only [mul_one] at h1
  unfold Grisk cps
  simp_rw [div_mul_eq_mul_div]
  rw [← sum_div, sum_update_affine M hM w ℓ L t]
  congr 1

lemma alg_deriv (a E AL N : ℝ) (ha : a ≠ 0) (hE : E ≠ 0) :
    a / E * (AL / a - N / E) = (AL * E - N * a) / E ^ 2 := by
  field_simp

theorem cps_gradient : Claims.cps_gradient := by
  intro n M w L hM hw
  have hincl := (cps_incl n M w hM hw)
  have hcond := (cps_conditional n M w L hM hw).2
  refine ⟨?_, ?_⟩
  · intro ℓ
    set a := esym w (univ.erase ℓ) (M - 1) with ha_def
    set AL := ∑ T ∈ (univ.erase ℓ).powersetCard (M - 1), (∏ j ∈ T, w j) * L (insert ℓ T)
      with hAL
    set BL := ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∉ S), (∏ j ∈ S, w j) * L S
    set B1 := ∑ S ∈ (univ.powersetCard M).filter (fun S => ℓ ∉ S), (∏ j ∈ S, w j)
    have ha : a ≠ 0 := (esym_erase_pos hw ℓ).ne'
    have hfun : (fun t => Grisk (Function.update w ℓ t) M L) =
        fun t => (t * AL + BL) / (t * a + B1) := by
      funext t
      exact Grisk_update M hM w L ℓ t
    have hG : Grisk w M L = (w ℓ * AL + BL) / (w ℓ * a + B1) := by
      have := Grisk_update M hM w L ℓ (w ℓ)
      rwa [Function.update_eq_self] at this
    have he : esym w univ M = w ℓ * a + B1 := by
      have := sum_update_affine M hM w ℓ (fun _ => 1) (w ℓ)
      simp only [mul_one, Function.update_eq_self] at this
      rw [esym, this]
      rfl
    have hV : Vrisk w M L ℓ = AL / a := by
      unfold Vrisk cps
      rw [hAL, sum_div]
      refine sum_congr rfl fun T _ => ?_
      rw [div_mul_eq_mul_div]
    have hE0 : w ℓ * a + B1 ≠ 0 := by rw [← he]; exact (esym_univ_pos hw).ne'
    rw [hfun, hG, he, hV]
    have hN : HasDerivAt (fun t => t * AL + BL) AL (w ℓ) := by
      simpa using HasDerivAt.add_const BL ((hasDerivAt_id (w ℓ)).mul_const AL)
    have hD : HasDerivAt (fun t => t * a + B1) a (w ℓ) := by
      simpa using HasDerivAt.add_const B1 ((hasDerivAt_id (w ℓ)).mul_const a)
    have hd := HasDerivAt.div hN hD hE0
    convert hd using 1
    exact alg_deriv a _ AL _ ha hE0
  · have hterm : ∀ ℓ, w ℓ * (esym w (univ.erase ℓ) (M - 1) / esym w univ M *
        (Vrisk w M L ℓ - Grisk w M L)) =
        incl w M ℓ * Vrisk w M L ℓ - incl w M ℓ * Grisk w M L := by
      intro ℓ
      rw [hincl.1 ℓ]
      ring
    simp_rw [hterm]
    rw [sum_sub_distrib, ← sum_mul, hcond, hincl.2]
    ring

end StatFormal.ICL
