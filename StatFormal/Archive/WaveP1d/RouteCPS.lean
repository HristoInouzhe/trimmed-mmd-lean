import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.ICL.CPS
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Route: ICL `prop:cps-gradient`, logit derivative, extension to faces, fixed prompts (untrusted)

* `G` is homogeneous of degree `0` (`e_M(cu) = c^M e_M(u)`), so `G(softmax(η with η_ℓ = t)) = G(w with w_ℓ = e^t/Z)`,
  `Z = Σ_k e^{η_k}`: a one-coordinate update of `w = softmax η`; the chain rule with the certified `cps_gradient` and
  `cps_incl` gives `∂G/∂η_ℓ = w_ℓ e_{M−1}(w_{−ℓ})/e_M(w) (V_ℓ − G) = π_ℓ(V_ℓ − G)`.
* `π_ℓ`, `V_ℓ`, `G` are polynomials divided by `e_M(w) > 0`, resp. `e_{M−1}(w_{−ℓ}) > 0`, on `Δ^(M)` (certified
  positivity): continuous there.
* At `w = 1_P/M`, `∏_{j∈S} w_j = M^{−|S|} 1{S ⊆ P}`, so `e_k(w|_s) = M^{−k} C(|s ∩ P|, k)`; `G = L(P)`, `V_ℓ = L(P)` on `P`,
  and off `P` the ratio is `M · M^{−(M−1)}/M^{−M} = M²` and `V_ℓ` averages `L(ℓ ∪ P∖{k})` over `k ∈ P`; Euler gives
  `⟨w, g⟩ = 0`, and the gap is `−min_ℓ g_ℓ`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.WaveP1d

namespace RouteCPS

open StatFormal.ICL
open StatFormal.OTFD.Bands (softmax)

variable {n : ℕ}

lemma esym_smul (c : ℝ) (u : Fin n → ℝ) (s : Finset (Fin n)) (k : ℕ) :
    esym (c • u) s k = c ^ k * esym u s k := by
  unfold esym
  rw [mul_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [(mem_powersetCard.1 hS).2.symm, ← prod_const, ← prod_mul_distrib]
  rfl

lemma Grisk_smul {M : ℕ} (c : ℝ) (hc : c ≠ 0) (u : Fin n → ℝ) (L : Finset (Fin n) → ℝ) :
    Grisk (c • u) M L = Grisk u M L := by
  unfold Grisk cps
  rw [esym_smul]
  refine sum_congr rfl fun S hS => ?_
  have hcard := (mem_powersetCard.1 hS).2
  have : ∏ j ∈ S, (c • u) j = c ^ M * ∏ j ∈ S, u j := by
    rw [← hcard, ← prod_const, ← prod_mul_distrib]; rfl
  rw [this]
  have hcM : c ^ M ≠ 0 := pow_ne_zero _ hc
  by_cases he : esym u univ M = 0
  · simp [he]
  · field_simp

lemma softmax_pos (η : Fin n → ℝ) (j : Fin n) : 0 < softmax η j := by
  unfold softmax
  have : 0 < ∑ k, Real.exp (η k) := sum_pos (fun k _ => Real.exp_pos _) ⟨j, mem_univ _⟩
  positivity

lemma softmax_sum (η : Fin n → ℝ) (hn : 0 < n) : ∑ j, softmax η j = 1 := by
  unfold softmax
  have : 0 < ∑ k, Real.exp (η k) :=
    sum_pos (fun k _ => Real.exp_pos _) ⟨⟨0, hn⟩, mem_univ _⟩
  rw [← sum_div, div_self this.ne']

lemma softmax_inDeltaM (η : Fin n → ℝ) {M : ℕ} (hM : 1 ≤ M) (hMn : M ≤ n) : InDeltaM (softmax η) M := by
  refine ⟨fun j => (softmax_pos η j).le, softmax_sum η (by omega), ?_⟩
  have : (univ.filter fun j => softmax η j ≠ 0) = univ := by
    ext j; simp [(softmax_pos η j).ne']
  rw [this, card_univ, Fintype.card_fin]; exact hMn

theorem cps_logit_aux (n M : ℕ) (η : Fin n → ℝ) (L : Finset (Fin n) → ℝ) (hM : 1 ≤ M) (hMn : M ≤ n) :
    InDeltaM (softmax η) M ∧
    ∀ ℓ, HasDerivAt (fun t => Grisk (softmax (Function.update η ℓ t)) M L)
      (incl (softmax η) M ℓ * (Vrisk (softmax η) M L ℓ - Grisk (softmax η) M L)) (η ℓ) := by
  have hw := softmax_inDeltaM η hM hMn
  refine ⟨hw, fun ℓ => ?_⟩
  set w := softmax η with hwdef
  set Z := ∑ k, Real.exp (η k) with hZ
  have hZpos : 0 < Z := sum_pos (fun k _ => Real.exp_pos _) ⟨ℓ, mem_univ _⟩
  -- reduction to a one-coordinate update of `w`
  have hred : (fun t => Grisk (softmax (Function.update η ℓ t)) M L) =
      fun t => Grisk (Function.update w ℓ (Real.exp t / Z)) M L := by
    funext t
    set Zt := ∑ k, Real.exp (Function.update η ℓ t k)
    have hZt : 0 < Zt := sum_pos (fun k _ => Real.exp_pos _) ⟨ℓ, mem_univ _⟩
    have hvec : softmax (Function.update η ℓ t) = (Z / Zt) • Function.update w ℓ (Real.exp t / Z) := by
      funext j
      have e1 : softmax (Function.update η ℓ t) j = Real.exp (Function.update η ℓ t j) / Zt := rfl
      have e2 : ∀ k, w k = Real.exp (η k) / Z := fun k => rfl
      rw [e1, Pi.smul_apply, smul_eq_mul]
      by_cases hj : j = ℓ
      · subst hj; simp only [Function.update_self]; field_simp
      · simp only [Function.update_of_ne hj, e2]; field_simp
    rw [hvec, Grisk_smul _ (div_pos hZpos hZt).ne']
  rw [hred]
  have hgrad := ((cps_gradient n M w L hM hw).1 ℓ)
  have hexp : HasDerivAt (fun t => Real.exp t / Z) (Real.exp (η ℓ) / Z) (η ℓ) :=
    (Real.hasDerivAt_exp (η ℓ)).div_const Z
  have hwl : Real.exp (η ℓ) / Z = w ℓ := by simp [hwdef, softmax, hZ]
  rw [hwl] at hexp
  have hcomp := hgrad.comp (η ℓ) hexp
  have hincl := (cps_incl n M w hM hw).1 ℓ
  convert hcomp using 1
  · funext t; simp [Function.comp]
  · rw [hincl]; ring


lemma continuous_esym (s : Finset (Fin n)) (k : ℕ) : Continuous fun w : Fin n → ℝ => esym w s k := by
  unfold esym; fun_prop

lemma continuousOn_cps (s : Finset (Fin n)) (k : ℕ) (S : Finset (Fin n)) {D : Set (Fin n → ℝ)}
    (hD : ∀ w ∈ D, esym w s k ≠ 0) : ContinuousOn (fun w => cps w s k S) D := by
  unfold cps
  exact ContinuousOn.div (by fun_prop) (continuous_esym s k).continuousOn hD

theorem cps_logit_extension_aux (n M : ℕ) (L : Finset (Fin n) → ℝ) (ℓ : Fin n) (_hM : 1 ≤ M) :
    ContinuousOn (fun w => incl w M ℓ * (Vrisk w M L ℓ - Grisk w M L)) {w | InDeltaM w M} := by
  have h1 : ∀ w ∈ {w : Fin n → ℝ | InDeltaM w M}, esym w univ M ≠ 0 :=
    fun w hw => (esym_univ_pos hw).ne'
  have h2 : ∀ w ∈ {w : Fin n → ℝ | InDeltaM w M}, esym w (univ.erase ℓ) (M - 1) ≠ 0 :=
    fun w hw => (esym_erase_pos hw ℓ).ne'
  unfold incl Vrisk Grisk
  refine ContinuousOn.mul ?_ (ContinuousOn.sub ?_ ?_)
  · exact continuousOn_finsetSum _ fun S _ => continuousOn_cps _ _ S h1
  · exact continuousOn_finsetSum _ fun T _ => (continuousOn_cps _ _ T h2).mul continuousOn_const
  · exact continuousOn_finsetSum _ fun S _ => (continuousOn_cps _ _ S h1).mul continuousOn_const


/-! ### Fixed prompts -/

/-- Uniform weights on a prompt `P`. -/
abbrev unifP (P : Finset (Fin n)) (M : ℕ) : Fin n → ℝ := fun j => if j ∈ P then 1 / (M : ℝ) else 0

lemma prod_unifP (P : Finset (Fin n)) (M : ℕ) (S : Finset (Fin n)) :
    ∏ j ∈ S, unifP P M j = if S ⊆ P then (1 / (M : ℝ)) ^ S.card else 0 := by
  split_ifs with h
  · rw [← prod_const]; exact prod_congr rfl fun j hj => by simp [unifP, h hj]
  · obtain ⟨j, hjS, hjP⟩ := not_subset.1 h
    exact prod_eq_zero hjS (by simp [unifP, hjP])

lemma filter_subset_powersetCard (s P : Finset (Fin n)) (k : ℕ) :
    (s.powersetCard k).filter (fun S => S ⊆ P) = (s ∩ P).powersetCard k := by
  ext S
  simp only [mem_filter, mem_powersetCard, subset_inter_iff]
  tauto

lemma sum_unifP (P : Finset (Fin n)) (M : ℕ) (s : Finset (Fin n)) (k : ℕ) (f : Finset (Fin n) → ℝ) :
    ∑ S ∈ s.powersetCard k, (∏ j ∈ S, unifP P M j) * f S =
      (1 / (M : ℝ)) ^ k * ∑ S ∈ (s ∩ P).powersetCard k, f S := by
  simp_rw [prod_unifP]
  rw [mul_sum, ← filter_subset_powersetCard, sum_filter]
  refine sum_congr rfl fun S hS => ?_
  rw [(mem_powersetCard.1 hS).2]
  split_ifs <;> ring

lemma esym_unifP (P : Finset (Fin n)) (M : ℕ) (s : Finset (Fin n)) (k : ℕ) :
    esym (unifP P M) s k = (1 / (M : ℝ)) ^ k * ((s ∩ P).card.choose k : ℝ) := by
  have := sum_unifP P M s k (fun _ => 1)
  simp only [mul_one, sum_const, card_powersetCard, nsmul_eq_mul] at this
  unfold esym; rw [this]


lemma sum_powersetCard_pred (P : Finset (Fin n)) (M : ℕ) (hP : P.card = M) (hM : 1 ≤ M)
    (f : Finset (Fin n) → ℝ) :
    ∑ T ∈ P.powersetCard (M - 1), f T = ∑ k ∈ P, f (P.erase k) := by
  symm
  refine sum_bij (fun k _ => P.erase k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_powersetCard]
    exact ⟨erase_subset k P, by rw [card_erase_of_mem hk, hP]⟩
  · intro k hk k' hk' h
    by_contra hne
    have : k ∈ P.erase k' := mem_erase.2 ⟨hne, hk⟩
    rw [← h] at this
    exact (notMem_erase k P) this
  · intro T hT
    rw [mem_powersetCard] at hT
    have hc : (P \ T).card = 1 := by rw [card_sdiff_of_subset hT.1, hT.2, hP]; omega
    obtain ⟨k, hk⟩ := card_eq_one.1 hc
    have hkP : k ∈ P := (mem_sdiff.1 (hk ▸ mem_singleton_self k)).1
    refine ⟨k, hkP, ?_⟩
    ext j
    simp only [mem_erase]
    constructor
    · rintro ⟨hjk, hjP⟩
      by_contra hjT
      have : j ∈ P \ T := mem_sdiff.2 ⟨hjP, hjT⟩
      rw [hk, mem_singleton] at this
      exact hjk this
    · intro hjT
      refine ⟨?_, hT.1 hjT⟩
      rintro rfl
      have : j ∈ P \ T := hk ▸ mem_singleton_self j
      exact (mem_sdiff.1 this).2 hjT
  · intro k _; rfl


lemma sum_cps_unifP (P : Finset (Fin n)) {M : ℕ} (hM : 0 < M) (s : Finset (Fin n)) (k : ℕ)
    (f : Finset (Fin n) → ℝ) :
    ∑ S ∈ s.powersetCard k, cps (unifP P M) s k S * f S =
      (∑ S ∈ (s ∩ P).powersetCard k, f S) / ((s ∩ P).card.choose k : ℝ) := by
  have hr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold cps
  simp_rw [div_mul_eq_mul_div]
  rw [← sum_div, sum_unifP, esym_unifP]
  have : (1 / (M : ℝ)) ^ k ≠ 0 := by positivity
  by_cases hc : ((s ∩ P).card.choose k : ℝ) = 0
  · simp [hc]
  · field_simp

theorem cps_fixed_prompt_aux (n M : ℕ) (P : Finset (Fin n)) (L : Finset (Fin n) → ℝ) (hM : 1 ≤ M)
    (hP : P.card = M) :
    let w : Fin n → ℝ := fun j => if j ∈ P then 1 / (M : ℝ) else 0
    let g : Fin n → ℝ := fun ℓ =>
      esym w (univ.erase ℓ) (M - 1) / esym w univ M * (Vrisk w M L ℓ - Grisk w M L)
    InDeltaM w M ∧ Grisk w M L = L P ∧
    (∀ ℓ, incl w M ℓ * (Vrisk w M L ℓ - Grisk w M L) = 0) ∧
    (∀ ℓ ∈ P, g ℓ = 0) ∧
    (∀ ℓ ∉ P, esym w (univ.erase ℓ) (M - 1) / esym w univ M = (M : ℝ) ^ 2 ∧
       Vrisk w M L ℓ = (1 / (M : ℝ)) * ∑ k ∈ P, L (insert ℓ (P.erase k))) ∧
    IsGreatest (insert 0 ((fun ℓ => (M : ℝ) ^ 2 * (Grisk w M L - Vrisk w M L ℓ)) '' {ℓ | ℓ ∉ P}))
      ((∑ ℓ, w ℓ * g ℓ) - ⨅ ℓ, g ℓ) := by
  intro w g
  have hw : w = unifP P M := rfl
  have hM0 : 0 < M := hM
  have hr : (0 : ℝ) < M := by exact_mod_cast hM0
  -- membership in `Δ^(M)`
  have hD : InDeltaM w M := by
    refine ⟨fun j => by simp only [w]; split_ifs <;> positivity, ?_, ?_⟩
    · simp only [w, sum_ite_mem, univ_inter, sum_const, hP, nsmul_eq_mul]
      field_simp
    · have : (univ.filter fun j => w j ≠ 0) = P := by
        ext j; simp only [w, mem_filter, mem_univ, true_and]
        split_ifs with h <;> simp [h, hr.ne']
      rw [this, hP]
  have hPne : P.Nonempty := card_pos.1 (by omega)
  -- the risk
  have hG : Grisk w M L = L P := by
    unfold Grisk
    rw [hw, sum_cps_unifP P hM0, univ_inter, hP, Nat.choose_self, ← hP, powersetCard_self]
    simp
  -- `V_ℓ` on and off the prompt
  have hVin : ∀ ℓ ∈ P, Vrisk w M L ℓ = L P := by
    intro ℓ hℓ
    unfold Vrisk
    have hint : univ.erase ℓ ∩ P = P.erase ℓ := by
      ext j; simp only [mem_inter, mem_erase, mem_univ, and_true]
    have hcard : (P.erase ℓ).card = M - 1 := by rw [card_erase_of_mem hℓ, hP]
    rw [hw, sum_cps_unifP P hM0, hint, hcard, Nat.choose_self, ← hcard, powersetCard_self]
    simp [insert_erase hℓ]
  have hVout : ∀ ℓ ∉ P, Vrisk w M L ℓ = (1 / (M : ℝ)) * ∑ k ∈ P, L (insert ℓ (P.erase k)) := by
    intro ℓ hℓ
    unfold Vrisk
    have hint : univ.erase ℓ ∩ P = P := by
      ext j; simp only [mem_inter, mem_erase, mem_univ, and_true, and_iff_right_iff_imp]
      rintro hj rfl; exact hℓ hj
    rw [hw, sum_cps_unifP P hM0, hint, hP, Nat.choose_symm_of_eq_add (show M = (M - 1) + 1 by omega), Nat.choose_one_right,
      ← hP, sum_powersetCard_pred P _ rfl (by omega)]
    rw [hP]; ring
  -- the factor `e_{M−1}(w_{−ℓ})/e_M(w)`
  have heM : esym w univ M = (1 / (M : ℝ)) ^ M := by
    rw [hw, esym_unifP, univ_inter, hP, Nat.choose_self]; simp
  have hratio : ∀ ℓ ∉ P, esym w (univ.erase ℓ) (M - 1) / esym w univ M = (M : ℝ) ^ 2 := by
    intro ℓ hℓ
    have hint : univ.erase ℓ ∩ P = P := by
      ext j; simp only [mem_inter, mem_erase, mem_univ, and_true, and_iff_right_iff_imp]
      rintro hj rfl; exact hℓ hj
    rw [heM, hw, esym_unifP, hint, hP, Nat.choose_symm_of_eq_add (show M = (M - 1) + 1 by omega), Nat.choose_one_right]
    have hpow : (1 / (M : ℝ)) ^ M = (1 / (M : ℝ)) ^ (M - 1) * (1 / (M : ℝ)) := by
      rw [← pow_succ, Nat.sub_add_cancel hM]
    rw [hpow]
    field_simp
  have hgin : ∀ ℓ ∈ P, g ℓ = 0 := by
    intro ℓ hℓ; simp only [g, hVin ℓ hℓ, hG, sub_self, mul_zero]
  have hgout : ∀ ℓ ∉ P, g ℓ = (M : ℝ) ^ 2 * (Vrisk w M L ℓ - Grisk w M L) := by
    intro ℓ hℓ; simp only [g, hratio ℓ hℓ]
  -- Euler
  have heuler : ∑ ℓ, w ℓ * g ℓ = 0 := (cps_gradient n M w L hM hD).2
  refine ⟨hD, hG, ?_, hgin, fun ℓ hℓ => ⟨hratio ℓ hℓ, hVout ℓ hℓ⟩, ?_⟩
  · intro ℓ
    by_cases hℓ : ℓ ∈ P
    · rw [hVin ℓ hℓ, hG, sub_self, mul_zero]
    · rw [((cps_incl n M w hM hD).1 ℓ)]
      have : w ℓ = 0 := by simp [w, hℓ]
      rw [this]; ring
  · rw [heuler, zero_sub]
    have : Nonempty (Fin n) := ⟨hPne.choose⟩
    obtain ⟨ℓ₀, hℓ₀⟩ := exists_eq_ciInf_of_finite (f := g)
    rw [← hℓ₀]
    have hle : ∀ ℓ, g ℓ₀ ≤ g ℓ := fun ℓ => hℓ₀ ▸ ciInf_le (Set.finite_range g).bddBelow ℓ
    refine ⟨?_, ?_⟩
    · by_cases h : ℓ₀ ∈ P
      · rw [hgin ℓ₀ h, neg_zero]; exact Set.mem_insert _ _
      · refine Set.mem_insert_of_mem _ ⟨ℓ₀, h, ?_⟩
        simp only [hgout ℓ₀ h]; ring
    · rintro a (rfl | ⟨ℓ, hℓ, rfl⟩)
      · obtain ⟨k, hk⟩ := hPne
        have := hle k; rw [hgin k hk] at this; linarith
      · have := hle ℓ; rw [hgout ℓ hℓ] at this
        simp only; linarith

end RouteCPS

theorem cps_logit : Claims.cps_logit := fun n M η L hM hMn => RouteCPS.cps_logit_aux n M η L hM hMn

theorem cps_logit_extension : Claims.cps_logit_extension := fun n M L ℓ hM =>
  RouteCPS.cps_logit_extension_aux n M L ℓ hM

theorem cps_fixed_prompt : Claims.cps_fixed_prompt := fun n M P L hM hP =>
  RouteCPS.cps_fixed_prompt_aux n M P L hM hP

end StatFormal.WaveP1d
