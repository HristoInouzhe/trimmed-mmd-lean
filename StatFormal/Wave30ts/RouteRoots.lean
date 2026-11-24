import StatFormal.Wave30ts.RouteTails
import StatFormal.Wave30tp.RouteLevel

/-!
# Route: the admissible sets, the roots `t_1, t_2`, `τ_{P'}`, the grid (deterministic facts)

Untrusted proof material.

* The Hilbert admissible set `{t ≥ 0 : Σ Ψ_H ≤ δ₁}` is nonempty when `D > 0` (McDiarmid alone) or `v, ρ̄ > 0` (Pinelis alone),
  and empty for `δ₁ < 3` when `D = 0` and (`v = 0` or `ρ̄ = 0`) (then `Ψ_H ≡ 1`); so emptiness does not depend on `β`.
* The repair admissible set contains `3` (`Ψ_R(3;β,K) = 0` for `|K| ≤ 2`).
* `t_1`, `t_2` are nondecreasing in `β` (and `t_1` in `(v, ρ̄)` for positive constants); `τ_{P'}` is nondecreasing in `α`,
  including the step across `α = 0` (`sharp_tau_monotone`), and in `(v, ρ̄)` (`coupled_tau_mono`).
* The grid: `foldr max 0`, the uniform cover (`uniform_grid_cover`), `coupled_grid_bound`.
-/

noncomputable section
open MeasureTheory Real Set

namespace StatFormal.Wave30ts

open StatFormal.Wave30tp

/-! ### Sample-size constants -/

theorem one_div_pos_nat {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) < 1 / n := by
  have : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  positivity

theorem one_div_le_sNM {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) : (1 : ℝ) / n ≤ sNM n m ∧ (1 : ℝ) / m ≤ sNM n m := by
  have := one_div_pos_nat hn
  have := one_div_pos_nat hm
  unfold sNM; constructor <;> linarith

/-! ### Eventually small `Ψ_H` -/

theorem eventually_psiH_le {D v ρbar β s' c' ε : ℝ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 1 ≤ β) (hs : 0 < s')
    (hc : 0 < c') (hε : 0 < ε) (h : 0 < D ∨ (0 < v ∧ 0 < ρbar)) :
    ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → psiH D v ρbar β s' c' t ≤ ε := by
  have hβ0 : 0 < β := by linarith
  rcases h with hD | ⟨hv0, hρ0⟩
  · set L := |log (1 / ε)|
    set T := √(β * v ^ 2 * s') + β * D * √(s' * L / 2)
    refine ⟨T, by positivity, fun t ht => ?_⟩
    refine (psiH_le_McD _ _ _ _ _ _ _).trans ?_
    refine (psiMcD_le_exp hβ0 hD hs le_rfl (abs_nonneg _) ht).trans ?_
    calc exp (-L) ≤ exp (-log (1 / ε)) := exp_le_exp.2 (by linarith [le_abs_self (log (1 / ε))])
      _ = ε := by rw [exp_neg, exp_log (by positivity)]; field_simp
  · obtain ⟨T, hT0, hT⟩ := psiPin_small (a := β * ρbar * c') (b2 := β * v ^ 2 * s') (by positivity)
      (by positivity) hε
    refine ⟨T, hT0, fun t ht => (psiH_le_Pin _ _ _ _ _ _ _).trans ?_⟩
    exact (psiPin_antitone (by positivity) (by positivity) hT0 ht).trans hT

theorem psiH_eq_one {v ρbar β s' c' t : ℝ} (hρ : 0 ≤ ρbar) (hβ : 0 ≤ β) (hs : 0 ≤ s') (hc : 0 ≤ c') (ht : 0 ≤ t)
    (h : v = 0 ∨ ρbar = 0) : psiH 0 v ρbar β s' c' t = 1 := by
  rw [psiH_eq_McD hρ hβ hs hc ht h, psiMcD_D_zero]

/-! ### The admissible sets -/

/-- The Hilbert admissible set of `t_1`. -/
def setH (D v ρbar β δ1 : ℝ) (n m : ℕ) : Set ℝ := {t : ℝ | 0 ≤ t ∧ psiH3 D v ρbar β t n m ≤ δ1}

/-- The single-event admissible set of `τ_{P'}(0,δ)`. -/
def set0 (D v ρbar δ : ℝ) (n m : ℕ) : Set ℝ := {t : ℝ | 0 ≤ t ∧ psiH D v ρbar 1 (sNM n m) (cNM n m) t ≤ δ}

/-- The repair admissible set of `t_2`. -/
def setR (β δ2 : ℝ) (n m : ℕ) : Set ℝ := {t : ℝ | 0 ≤ t ∧ psiR3 β t n m ≤ δ2}

theorem rootH_eq (D v ρbar β δ1 : ℝ) (n m : ℕ) : rootH D v ρbar β δ1 n m = sInf (setH D v ρbar β δ1 n m) := rfl
theorem rootR_eq (β δ2 : ℝ) (n m : ℕ) : rootR β δ2 n m = sInf (setR β δ2 n m) := rfl

theorem bddBelow_nonneg_set {S : Set ℝ} (h : ∀ t ∈ S, 0 ≤ t) : BddBelow S := ⟨0, fun t ht => h t ht⟩

theorem sInf_nonneg_set {S : Set ℝ} (h : ∀ t ∈ S, 0 ≤ t) : 0 ≤ sInf S := Real.sInf_nonneg h

theorem psiH3_nonneg (D v ρbar β t : ℝ) (n m : ℕ) : 0 ≤ psiH3 D v ρbar β t n m := by
  unfold psiH3
  have := psiH_nonneg D v ρbar β (sNM n m) (cNM n m) t
  have := psiH_nonneg D v ρbar β (1 / (n : ℝ)) (1 / (n : ℝ)) t
  have := psiH_nonneg D v ρbar β (1 / (m : ℝ)) (1 / (m : ℝ)) t
  linarith

theorem setH_nonempty {D v ρbar β δ1 : ℝ} {n m : ℕ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 1 ≤ β) (hδ : 0 < δ1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (h : 0 < D ∨ (0 < v ∧ 0 < ρbar)) : (setH D v ρbar β δ1 n m).Nonempty := by
  have hε : 0 < δ1 / 3 := by positivity
  obtain ⟨T1, h10, h1⟩ := eventually_psiH_le (s' := sNM n m) (c' := cNM n m) hv hρ hβ (sNM_pos hn hm)
    (cNM_pos (m := m) hn) hε h
  obtain ⟨T2, h20, h2⟩ := eventually_psiH_le (s' := 1 / (n : ℝ)) (c' := 1 / (n : ℝ)) hv hρ hβ (one_div_pos_nat hn)
    (one_div_pos_nat hn) hε h
  obtain ⟨T3, h30, h3⟩ := eventually_psiH_le (s' := 1 / (m : ℝ)) (c' := 1 / (m : ℝ)) hv hρ hβ (one_div_pos_nat hm)
    (one_div_pos_nat hm) hε h
  set T := max T1 (max T2 T3)
  refine ⟨T, h10.trans (le_max_left _ _), ?_⟩
  have a1 := h1 T (le_max_left _ _)
  have a2 := h2 T ((le_max_left _ _).trans (le_max_right _ _))
  have a3 := h3 T ((le_max_right _ _).trans (le_max_right _ _))
  unfold psiH3
  linarith

theorem setH_empty {v ρbar β δ1 : ℝ} {n m : ℕ} (hρ : 0 ≤ ρbar) (hβ : 0 ≤ β) (hδ : δ1 < 3) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (h : v = 0 ∨ ρbar = 0) : setH 0 v ρbar β δ1 n m = ∅ := by
  ext t
  simp only [setH, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro ht
  unfold psiH3
  rw [psiH_eq_one hρ hβ (sNM_pos hn hm).le (cNM_pos (m := m) hn).le ht h,
    psiH_eq_one hρ hβ (one_div_pos_nat hn).le (one_div_pos_nat hn).le ht h,
    psiH_eq_one hρ hβ (one_div_pos_nat hm).le (one_div_pos_nat hm).le ht h]
  linarith

theorem set0_nonempty {D v ρbar δ : ℝ} {n m : ℕ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hδ : 0 < δ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (h : 0 < D ∨ (0 < v ∧ 0 < ρbar)) : (set0 D v ρbar δ n m).Nonempty := by
  obtain ⟨T, hT0, hT⟩ := eventually_psiH_le (s' := sNM n m) (c' := cNM n m) hv hρ le_rfl (sNM_pos hn hm)
    (cNM_pos (m := m) hn) hδ h
  exact ⟨T, hT0, hT T le_rfl⟩

theorem set0_empty {v ρbar δ : ℝ} {n m : ℕ} (hρ : 0 ≤ ρbar) (hδ : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : v = 0 ∨ ρbar = 0) : set0 0 v ρbar δ n m = ∅ := by
  ext t
  simp only [set0, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro ht
  rw [psiH_eq_one hρ zero_le_one (sNM_pos hn hm).le (cNM_pos (m := m) hn).le ht h]
  exact hδ

theorem psiR3_three {β : ℝ} (hβ : 1 ≤ β) (n m : ℕ) : psiR3 β 3 n m = 0 := by
  unfold psiR3
  rw [psiR_eq_zero hβ [n] (by norm_num), psiR_eq_zero hβ [m] (by norm_num),
    psiR_eq_zero hβ [n, m] (by norm_num)]
  ring

theorem three_mem_setR {β δ2 : ℝ} (hβ : 1 ≤ β) (hδ : 0 ≤ δ2) (n m : ℕ) : (3 : ℝ) ∈ setR β δ2 n m :=
  ⟨by norm_num, by rw [psiR3_three hβ]; exact hδ⟩

theorem psiR3_nonneg {β : ℝ} (hβ : 1 ≤ β) (t : ℝ) (n m : ℕ) : 0 ≤ psiR3 β t n m := by
  unfold psiR3
  have := psiR_nonneg hβ t [n]
  have := psiR_nonneg hβ t [m]
  have := psiR_nonneg hβ t [n, m]
  linarith

/-! ### Monotonicity of the sums -/

theorem psiH3_mono_beta {D v ρbar β β' t : ℝ} {n m : ℕ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 1 ≤ β)
    (hββ : β ≤ β') (ht : 0 ≤ t) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    psiH3 D v ρbar β t n m ≤ psiH3 D v ρbar β' t n m := by
  unfold psiH3
  have := psiH_mono_beta (D := D) hv hρ hβ hββ (sNM_pos hn hm) (cNM_pos (m := m) hn) ht
  have := psiH_mono_beta (D := D) hv hρ hβ hββ (one_div_pos_nat hn) (one_div_pos_nat hn) ht
  have := psiH_mono_beta (D := D) hv hρ hβ hββ (one_div_pos_nat hm) (one_div_pos_nat hm) ht
  linarith

theorem psiH3_mono_const {D v v' ρbar ρbar' β t : ℝ} {n m : ℕ} (hv : 0 < v) (hvv : v ≤ v') (hρ : 0 < ρbar)
    (hρρ : ρbar ≤ ρbar') (hβ : 1 ≤ β) (ht : 0 ≤ t) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    psiH3 D v ρbar β t n m ≤ psiH3 D v' ρbar' β t n m := by
  unfold psiH3
  have := psiH_mono_const (D := D) hv hvv hρ hρρ hβ (sNM_pos hn hm) (cNM_pos (m := m) hn) ht
  have := psiH_mono_const (D := D) hv hvv hρ hρρ hβ (one_div_pos_nat hn) (one_div_pos_nat hn) ht
  have := psiH_mono_const (D := D) hv hvv hρ hρρ hβ (one_div_pos_nat hm) (one_div_pos_nat hm) ht
  linarith

/-! ### The roots -/

theorem rootH_nonneg (D v ρbar β δ1 : ℝ) (n m : ℕ) : 0 ≤ rootH D v ρbar β δ1 n m :=
  sInf_nonneg_set fun _ ht => ht.1

theorem rootR_nonneg (β δ2 : ℝ) (n m : ℕ) : 0 ≤ rootR β δ2 n m := sInf_nonneg_set fun _ ht => ht.1

theorem sInf_set0_nonneg (D v ρbar δ : ℝ) (n m : ℕ) : 0 ≤ sInf (set0 D v ρbar δ n m) :=
  sInf_nonneg_set fun _ ht => ht.1

/-- Emptiness of the Hilbert set does not depend on `β` (for `0 < δ₁ < 3`). -/
theorem setH_nonempty_iff {D v ρbar β δ1 : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 1 ≤ β)
    (hδ0 : 0 < δ1) (hδ : δ1 < 3) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (setH D v ρbar β δ1 n m).Nonempty ↔ (0 < D ∨ (0 < v ∧ 0 < ρbar)) := by
  constructor
  · intro hne
    by_contra hc
    push_neg at hc
    have hD0 : D = 0 := le_antisymm hc.1 hD
    have hj : v = 0 ∨ ρbar = 0 := by
      by_contra hj; push_neg at hj
      exact absurd (hc.2 (lt_of_le_of_ne hv (Ne.symm hj.1))) (not_le.2 (lt_of_le_of_ne hρ (Ne.symm hj.2)))
    subst hD0
    rw [setH_empty hρ (by linarith) hδ hn hm hj] at hne
    exact Set.not_nonempty_empty hne
  · exact setH_nonempty hv hρ hβ hδ0 hn hm

theorem rootH_mono_beta {D v ρbar β β' δ1 : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 1 ≤ β)
    (hββ : β ≤ β') (hδ0 : 0 < δ1) (hδ : δ1 < 3) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    rootH D v ρbar β δ1 n m ≤ rootH D v ρbar β' δ1 n m := by
  rw [rootH_eq, rootH_eq]
  have hsub : setH D v ρbar β' δ1 n m ⊆ setH D v ρbar β δ1 n m := fun t ht =>
    ⟨ht.1, (psiH3_mono_beta hv hρ hβ hββ ht.1 hn hm).trans ht.2⟩
  by_cases hne : (setH D v ρbar β' δ1 n m).Nonempty
  · exact csInf_le_csInf (bddBelow_nonneg_set fun _ ht => ht.1) hne hsub
  · have hne' : ¬(setH D v ρbar β δ1 n m).Nonempty := by
      rw [setH_nonempty_iff hD hv hρ hβ hδ0 hδ hn hm]
      rwa [setH_nonempty_iff hD hv hρ (hβ.trans hββ) hδ0 hδ hn hm] at hne
    rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.not_nonempty_iff_eq_empty.1 hne']

theorem rootR_mono_beta {β β' δ2 : ℝ} {n m : ℕ} (hβ : 1 ≤ β) (hββ : β ≤ β') (hδ : 0 ≤ δ2) :
    rootR β δ2 n m ≤ rootR β' δ2 n m := by
  rw [rootR_eq, rootR_eq]
  have hsub : setR β' δ2 n m ⊆ setR β δ2 n m := fun t ht => by
    refine ⟨ht.1, le_trans ?_ ht.2⟩
    unfold psiR3
    have := psiR_mono_beta hβ hββ t [n]
    have := psiR_mono_beta hβ hββ t [m]
    have := psiR_mono_beta hβ hββ t [n, m]
    linarith
  exact csInf_le_csInf (bddBelow_nonneg_set fun _ ht => ht.1) ⟨3, three_mem_setR (hβ.trans hββ) hδ n m⟩ hsub

theorem rootH_mono_const {D v v' ρbar ρbar' β δ1 : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 < v) (hvv : v ≤ v')
    (hρ : 0 < ρbar) (hρρ : ρbar ≤ ρbar') (hβ : 1 ≤ β) (hδ0 : 0 < δ1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    rootH D v ρbar β δ1 n m ≤ rootH D v' ρbar' β δ1 n m := by
  rw [rootH_eq, rootH_eq]
  have hsub : setH D v' ρbar' β δ1 n m ⊆ setH D v ρbar β δ1 n m := fun t ht =>
    ⟨ht.1, (psiH3_mono_const hv hvv hρ hρρ hβ ht.1 hn hm).trans ht.2⟩
  exact csInf_le_csInf (bddBelow_nonneg_set fun _ ht => ht.1)
    (setH_nonempty (hv.le.trans hvv) (hρ.le.trans hρρ) hβ hδ0 hn hm
      (Or.inr ⟨hv.trans_le hvv, hρ.trans_le hρρ⟩)) hsub

theorem sInf_set0_mono_const {D v v' ρbar ρbar' δ : ℝ} {n m : ℕ} (hv : 0 < v) (hvv : v ≤ v')
    (hρ : 0 < ρbar) (hρρ : ρbar ≤ ρbar') (hδ0 : 0 < δ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    sInf (set0 D v ρbar δ n m) ≤ sInf (set0 D v' ρbar' δ n m) := by
  have hsub : set0 D v' ρbar' δ n m ⊆ set0 D v ρbar δ n m := fun t ht =>
    ⟨ht.1, (psiH_mono_const hv hvv hρ hρρ le_rfl (sNM_pos hn hm) (cNM_pos (m := m) hn) ht.1).trans ht.2⟩
  exact csInf_le_csInf (bddBelow_nonneg_set fun _ ht => ht.1)
    (set0_nonempty (hv.le.trans hvv) (hρ.le.trans hρρ) hδ0 hn hm
      (Or.inr ⟨hv.trans_le hvv, hρ.trans_le hρρ⟩)) hsub

/-! ### `τ_{P'}` -/

theorem tauSplit_nonneg {D v ρbar α δ f : ℝ} {n m : ℕ} (hρ : 0 ≤ ρbar) : 0 ≤ tauSplit D v ρbar α δ f n m :=
  add_nonneg (rootH_nonneg _ _ _ _ _ _ _) (mul_nonneg hρ (rootR_nonneg _ _ _ _))

theorem tauPs_nonneg {D v ρbar α δ : ℝ} {n m : ℕ} (hρ : 0 ≤ ρbar) : 0 ≤ tauPs D v ρbar α δ n m := by
  unfold tauPs
  split_ifs
  · exact sInf_set0_nonneg _ _ _ _ _ _
  · exact le_min (tauSplit_nonneg hρ) (le_min (tauSplit_nonneg hρ) (le_min (tauSplit_nonneg hρ)
      (le_min (tauSplit_nonneg hρ) (tauSplit_nonneg hρ))))

theorem tauPs_pos_eq {D v ρbar α δ : ℝ} {n m : ℕ} (h0 : α ≠ 0) :
    tauPs D v ρbar α δ n m = min (tauSplit D v ρbar α δ (1 / 2) n m) (min (tauSplit D v ρbar α δ (3 / 5) n m)
      (min (tauSplit D v ρbar α δ (7 / 10) n m) (min (tauSplit D v ρbar α δ (4 / 5) n m)
        (tauSplit D v ρbar α δ (9 / 10) n m)))) := by
  simp [tauPs, h0]

theorem tauPs_zero_eq (D v ρbar δ : ℝ) (n m : ℕ) : tauPs D v ρbar 0 δ n m = sInf (set0 D v ρbar δ n m) := by
  simp [tauPs, set0]

/-- The five splits as a predicate. -/
def IsSplit (f : ℝ) : Prop := f = 1 / 2 ∨ f = 3 / 5 ∨ f = 7 / 10 ∨ f = 4 / 5 ∨ f = 9 / 10

theorem IsSplit.bounds {f : ℝ} (hf : IsSplit f) : 0 < f ∧ f < 1 := by
  rcases hf with h | h | h | h | h <;> subst h <;> norm_num

/-- The minimum over the five splits is attained, and is below every split. -/
theorem tauPs_pos_attained {D v ρbar α δ : ℝ} {n m : ℕ} (h0 : α ≠ 0) :
    ∃ f, IsSplit f ∧ tauPs D v ρbar α δ n m = tauSplit D v ρbar α δ f n m := by
  rw [tauPs_pos_eq h0]
  set g := fun f => tauSplit D v ρbar α δ f n m
  change ∃ f, IsSplit f ∧ min (g (1/2)) (min (g (3/5)) (min (g (7/10)) (min (g (4/5)) (g (9/10))))) = g f
  rcases min_choice (g (1/2)) (min (g (3/5)) (min (g (7/10)) (min (g (4/5)) (g (9/10))))) with h | h <;>
    rw [h]
  · exact ⟨1/2, Or.inl rfl, rfl⟩
  rcases min_choice (g (3/5)) (min (g (7/10)) (min (g (4/5)) (g (9/10)))) with h | h <;> rw [h]
  · exact ⟨3/5, Or.inr (Or.inl rfl), rfl⟩
  rcases min_choice (g (7/10)) (min (g (4/5)) (g (9/10))) with h | h <;> rw [h]
  · exact ⟨7/10, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  rcases min_choice (g (4/5)) (g (9/10)) with h | h <;> rw [h]
  · exact ⟨4/5, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  · exact ⟨9/10, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩

theorem tauPs_pos_le {D v ρbar α δ f : ℝ} {n m : ℕ} (h0 : α ≠ 0) (hf : IsSplit f) :
    tauPs D v ρbar α δ n m ≤ tauSplit D v ρbar α δ f n m := by
  rw [tauPs_pos_eq h0]
  rcases hf with h | h | h | h | h <;> subst h
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

theorem le_tauPs_pos {D v ρbar α δ c : ℝ} {n m : ℕ} (h0 : α ≠ 0)
    (h : ∀ f, IsSplit f → c ≤ tauSplit D v ρbar α δ f n m) : c ≤ tauPs D v ρbar α δ n m := by
  obtain ⟨f, hf, he⟩ := tauPs_pos_attained (D := D) (v := v) (ρbar := ρbar) (δ := δ) (n := n) (m := m) h0
  rw [he]; exact h f hf

theorem tauSplit_mono_alpha {D v ρbar α α' δ f : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar)
    (hα0 : 0 ≤ α) (hαα : α ≤ α') (hα'1 : α' < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hf : IsSplit f) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : tauSplit D v ρbar α δ f n m ≤ tauSplit D v ρbar α' δ f n m := by
  obtain ⟨hf0, hf1⟩ := hf.bounds
  have hβ := one_le_beta hα0 (hαα.trans_lt hα'1)
  have hββ := beta_mono hα'1 hαα
  unfold tauSplit
  have h1 := rootH_mono_beta (D := D) (v := v) (ρbar := ρbar) (δ1 := f * δ) (n := n) (m := m) hD hv hρ hβ hββ
    (by positivity) (by nlinarith) hn hm
  have h2 := rootR_mono_beta (δ2 := (1 - f) * δ) (n := n) (m := m) hβ hββ (by nlinarith)
  have := mul_le_mul_of_nonneg_left h2 hρ
  linarith

theorem sInf_set0_le_tauSplit {D v ρbar α δ f : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hf : IsSplit f) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    sInf (set0 D v ρbar δ n m) ≤ tauSplit D v ρbar α δ f n m := by
  obtain ⟨hf0, hf1⟩ := hf.bounds
  have hβ := one_le_beta hα0 hα1
  have hfδ : f * δ ≤ δ := by nlinarith
  unfold tauSplit
  have hR := mul_nonneg hρ (rootR_nonneg (1 / (1 - α)) ((1 - f) * δ) n m)
  by_cases hne : (setH D v ρbar (1 / (1 - α)) (f * δ) n m).Nonempty
  · have hsub : setH D v ρbar (1 / (1 - α)) (f * δ) n m ⊆ set0 D v ρbar δ n m := fun t ht => by
      refine ⟨ht.1, le_trans ?_ (ht.2.trans hfδ)⟩
      refine (psiH_mono_beta hv hρ le_rfl hβ (sNM_pos hn hm) (cNM_pos (m := m) hn) ht.1).trans ?_
      unfold psiH3
      have := psiH_nonneg D v ρbar (1 / (1 - α)) (1 / (n : ℝ)) (1 / (n : ℝ)) t
      have := psiH_nonneg D v ρbar (1 / (1 - α)) (1 / (m : ℝ)) (1 / (m : ℝ)) t
      linarith
    have := csInf_le_csInf (bddBelow_nonneg_set fun _ ht => ht.1) hne hsub
    rw [rootH_eq]; linarith
  · rw [setH_nonempty_iff hD hv hρ hβ (by positivity) (by nlinarith) hn hm] at hne
    push_neg at hne
    have hD0 : D = 0 := le_antisymm hne.1 hD
    have hj : v = 0 ∨ ρbar = 0 := by
      by_contra hj; push_neg at hj
      exact absurd (hne.2 (lt_of_le_of_ne hv (Ne.symm hj.1))) (not_le.2 (lt_of_le_of_ne hρ (Ne.symm hj.2)))
    subst hD0
    rw [set0_empty hρ hδ1 hn hm hj, Real.sInf_empty]
    linarith [rootH_nonneg 0 v ρbar (1 / (1 - α)) (f * δ) n m]

theorem tauPs_mono_alpha {D v ρbar δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) : MonotoneOn (fun α => tauPs D v ρbar α δ n m) (Ico 0 1) := by
  intro α hα α' hα' hαα
  simp only
  by_cases h0' : α' = 0
  · have : α = 0 := le_antisymm (h0' ▸ hαα) hα.1
    rw [this, h0']
  by_cases h0 : α = 0
  · subst h0
    rw [tauPs_zero_eq]
    exact le_tauPs_pos h0' fun f hf => sInf_set0_le_tauSplit hD hv hρ hα'.1 hα'.2 hδ0 hδ1 hf hn hm
  · exact le_tauPs_pos h0' fun f hf => (tauPs_pos_le h0 hf).trans
      (tauSplit_mono_alpha hD hv hρ hα.1 hαα hα'.2 hδ0 hδ1 hf hn hm)

theorem sharp_tau_monotone : Claims.sharp_tau_monotone := fun D v ρbar δ n m hD hv hρ hδ0 hδ1 hn hm =>
  ⟨tauPs_mono_alpha hD hv hρ hδ0 hδ1 hn hm, fun _ _ => tauPs_nonneg hρ⟩

theorem tauPs_mono_const {D v v' ρbar ρbar' α δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 < v) (hvv : v ≤ v')
    (hρ : 0 < ρbar) (hρρ : ρbar ≤ ρbar') (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : tauPs D v ρbar α δ n m ≤ tauPs D v' ρbar' α δ n m := by
  by_cases h0 : α = 0
  · subst h0
    rw [tauPs_zero_eq, tauPs_zero_eq]
    exact sInf_set0_mono_const hv hvv hρ hρρ hδ0 hn hm
  · refine le_tauPs_pos h0 fun f hf => (tauPs_pos_le h0 hf).trans ?_
    obtain ⟨hf0, hf1⟩ := hf.bounds
    have hβ := one_le_beta hα0 hα1
    unfold tauSplit
    have h1 := rootH_mono_const (δ1 := f * δ) (n := n) (m := m) hD hv hvv hρ hρρ hβ (by positivity) hn hm
    have h2 := mul_le_mul_of_nonneg_right hρρ (rootR_nonneg (1 / (1 - α)) ((1 - f) * δ) n m)
    linarith

theorem coupled_tau_mono : Claims.coupled_tau_mono :=
  fun D v v' ρbar ρbar' α δ n m hD hv hvv hρ hρρ hα0 hα1 hδ0 hδ1 hn hm =>
    tauPs_mono_const hD hv hvv hρ hρρ hα0 hα1 hδ0 hδ1 hn hm

/-! ### The grid -/

theorem foldr_max_nonneg (L : List ℝ) : 0 ≤ L.foldr max 0 := by
  induction L with
  | nil => simp
  | cons x L ih => exact le_max_of_le_right ih

theorem le_foldr_max {L : List ℝ} {x : ℝ} (hx : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at hx
  | cons y L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {L : List ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ L, x ≤ c) : L.foldr max 0 ≤ c := by
  induction L with
  | nil => simpa using hc
  | cons y L ih =>
    simp only [List.foldr_cons]
    exact max_le (h y (List.mem_cons_self ..)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem tauGrid_nonneg (D : ℝ) (v ρ : ℕ → ℝ) (J : ℕ) (α δ : ℝ) (n m : ℕ) : 0 ≤ tauGrid D v ρ J α δ n m :=
  foldr_max_nonneg _

theorem le_tauGrid {D : ℝ} {v ρ : ℕ → ℝ} {J j : ℕ} (hj : j < J) (α δ : ℝ) (n m : ℕ) :
    tauPs D (v j) (ρ j) α δ n m ≤ tauGrid D v ρ J α δ n m :=
  le_foldr_max (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

theorem tauGrid_le {D : ℝ} {v ρ : ℕ → ℝ} {J : ℕ} {α δ c : ℝ} {n m : ℕ} (hc : 0 ≤ c)
    (h : ∀ j < J, tauPs D (v j) (ρ j) α δ n m ≤ c) : tauGrid D v ρ J α δ n m ≤ c := by
  refine foldr_max_le hc fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact h j (List.mem_range.1 hj)

theorem tauGrid_monotone {D : ℝ} {J : ℕ} {v ρ : ℕ → ℝ} {δ : ℝ} {n m : ℕ} (hD : 0 ≤ D)
    (hvρ : ∀ j < J, 0 ≤ v j ∧ 0 ≤ ρ j) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    MonotoneOn (fun α => tauGrid D v ρ J α δ n m) (Ico 0 1) ∧ ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauGrid D v ρ J α δ n m := by
  refine ⟨fun α hα α' hα' hαα => ?_, fun α _ => tauGrid_nonneg _ _ _ _ _ _ _ _⟩
  refine tauGrid_le (tauGrid_nonneg _ _ _ _ _ _ _ _) fun j hj => ?_
  exact (tauPs_mono_alpha hD (hvρ j hj).1 (hvρ j hj).2 hδ0 hδ1 hn hm hα hα' hαα).trans (le_tauGrid hj _ _ _ _)

theorem uniform_grid_cover : Claims.uniform_grid_cover := by
  intro κ J hJ u hu
  have hJpos : (0 : ℝ) < J := Nat.cast_pos.2 (by omega)
  rcases (sq_nonneg κ).eq_or_lt with hk | hk
  · refine ⟨0, by omega, ?_, ?_⟩
    · simp [← hk, hu.1]
    · have : u = 0 := le_antisymm (hk ▸ hu.2) hu.1
      simp [← hk, this]
  set x := u * J / κ ^ 2 with hx
  have hx0 : 0 ≤ x := by have := hu.1; positivity
  have hxJ : x ≤ J := by rw [hx, div_le_iff₀ hk]; nlinarith [hu.2]
  set j := min ⌊x⌋₊ (J - 1) with hj
  have hjJ : j < J := lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hjx : (j : ℝ) ≤ x := (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hx0)
  have hxj : x ≤ (j : ℝ) + 1 := by
    rcases le_total ⌊x⌋₊ (J - 1) with h | h
    · rw [hj, min_eq_left h]; exact (Nat.lt_floor_add_one x).le
    · rw [hj, min_eq_right h, Nat.cast_sub (by omega)]; push_cast; linarith
  refine ⟨j, hjJ, ?_, ?_⟩
  · rw [div_le_iff₀ hJpos]
    have := mul_le_mul_of_nonneg_right hjx hk.le
    rw [hx, div_mul_cancel₀ _ hk.ne'] at this
    linarith
  · rw [le_div_iff₀ hJpos]
    have := mul_le_mul_of_nonneg_right hxj hk.le
    rw [hx, div_mul_cancel₀ _ hk.ne'] at this
    linarith

theorem tauCpl_bddAbove {D κ α δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    BddAbove (range fun u : Ico (0 : ℝ) (κ ^ 2) => tauPs D (√(κ ^ 2 - (u : ℝ))) (√(κ ^ 2 + (u : ℝ))) α δ n m) := by
  refine ⟨tauPs D (√(κ ^ 2)) (√(κ ^ 2 + κ ^ 2)) α δ n m, ?_⟩
  rintro _ ⟨⟨u, hu0, hu1⟩, rfl⟩
  exact tauPs_mono_const hD (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt (by linarith))
    (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt (by linarith)) hα0 hα1 hδ0 hδ1 hn hm

theorem le_tauCpl {D κ α δ u : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) (hu : u ∈ Ico (0 : ℝ) (κ ^ 2)) :
    tauPs D (√(κ ^ 2 - u)) (√(κ ^ 2 + u)) α δ n m ≤ tauCpl D κ α δ n m :=
  le_ciSup (f := fun u : Ico (0 : ℝ) (κ ^ 2) => tauPs D (√(κ ^ 2 - (u : ℝ))) (√(κ ^ 2 + (u : ℝ))) α δ n m)
    (tauCpl_bddAbove hD hα0 hα1 hδ0 hδ1 hn hm) ⟨u, hu⟩

theorem tauCpl_le {D κ α δ c : ℝ} {n m : ℕ} (hc : 0 ≤ c)
    (h : ∀ u ∈ Ico (0 : ℝ) (κ ^ 2), tauPs D (√(κ ^ 2 - u)) (√(κ ^ 2 + u)) α δ n m ≤ c) :
    tauCpl D κ α δ n m ≤ c := by
  unfold tauCpl
  rcases isEmpty_or_nonempty (Ico (0 : ℝ) (κ ^ 2)) with he | he
  · rw [Real.iSup_of_isEmpty]; exact hc
  · exact ciSup_le fun u => h u u.2

theorem tauCpl_nonneg (D κ α δ : ℝ) (n m : ℕ) : 0 ≤ tauCpl D κ α δ n m := by
  unfold tauCpl
  exact Real.iSup_nonneg fun u => tauPs_nonneg (Real.sqrt_nonneg _)

theorem tauCpl_monotone {D κ δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    MonotoneOn (fun α => tauCpl D κ α δ n m) (Ico 0 1) := by
  intro α hα α' hα' hαα
  refine tauCpl_le (tauCpl_nonneg _ _ _ _ _ _) fun u hu => ?_
  exact (tauPs_mono_alpha hD (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hδ0 hδ1 hn hm hα hα' hαα).trans
    (le_tauCpl hD hα'.1 hα'.2 hδ0 hδ1 hn hm hu)

theorem coupled_grid_bound : Claims.coupled_grid_bound := by
  intro D κ α δ J n m hD hJ hα0 hα1 hδ0 hδ1 hn hm
  have hpt : ∀ u ∈ Ico (0 : ℝ) (κ ^ 2), tauPs D (√(κ ^ 2 - u)) (√(κ ^ 2 + u)) α δ n m ≤
      tauGrid D (fun j => √(κ ^ 2 - (j : ℝ) * κ ^ 2 / J)) (fun j => √(κ ^ 2 + ((j : ℝ) + 1) * κ ^ 2 / J)) J α δ n m := by
    intro u hu
    obtain ⟨j, hj, hlo, hhi⟩ := uniform_grid_cover κ J hJ u ⟨hu.1, hu.2.le⟩
    refine le_trans ?_ (le_tauGrid (v := fun j => √(κ ^ 2 - (j : ℝ) * κ ^ 2 / J))
      (ρ := fun j => √(κ ^ 2 + ((j : ℝ) + 1) * κ ^ 2 / J)) hj α δ n m)
    exact tauPs_mono_const hD (Real.sqrt_pos.2 (by linarith [hu.2])) (Real.sqrt_le_sqrt (by linarith))
      (Real.sqrt_pos.2 (by linarith [hu.1, hu.2])) (Real.sqrt_le_sqrt (by linarith)) hα0 hα1 hδ0 hδ1 hn hm
  exact ⟨hpt, tauCpl_le (tauGrid_nonneg _ _ _ _ _ _ _ _) hpt⟩

end StatFormal.Wave30ts
