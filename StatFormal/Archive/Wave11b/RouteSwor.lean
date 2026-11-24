import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.ICL.CPS
import StatFormal.Archive.ICL.Cond.Proofs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Route: ICL `prop:swor-score`, the value bound `C₀/n`

1. **Marginals of the i.i.d. index law** (`Fintype.prod_sum`): `Σ_j Π_m w_{j_m} g(j_k) = Σ_a w_a g(a)` and, for
   `k ≠ l`, `Pr(I_k = I_l) = Σ_a w_a²`.
2. **Collision bound.** On `D^c` two slots agree, so `1_{D^c} ≤ ½ Σ_{k ≠ l} 1{I_k = I_l}`; hence
   `p ≤ ½M(M−1)Σ w² = binom(M,2) Σ w² ≤ binom(M,2) max w`.
3. **CPS = conditioned i.i.d. law, up to order.** The injective tuples with image `S` are the `M!` bijections
   `Fin M ≃ S`, each with weight `Π_{i∈S} w_i`, and for a symmetric loss `L(x; z_j) = L(x; z_S)`. Hence
   `Σ_{j inj} Π w_{j_k} H(im j) = M! Σ_{|S|=M} Π_{i∈S} w_i H(S)`, `1 − p = M! e_M(w)`, `G(w) = E°L`,
   `π_l/M = E°[#{k : I_k = l}/M]`.
4. **Perturbation identity** and assembly: risk `≤ 4B_L p`; coverage `|log ρ° − log ρ| ≤ |ρ° − ρ|/K_min ≤
   4(K_max/K_min)p`; the `KL(w|u_n)` terms cancel; `p ≤ M(M−1)s₊/(2s₋n)`.
-/

noncomputable section
open Finset

namespace StatFormal.Wave11b

open StatFormal.ICL StatFormal.ICL.Cond

variable {n M : ℕ}

/-! ### Marginals of the i.i.d. index law -/

lemma iidLaw_nonneg {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j) (j : Fin M → Fin n) : 0 ≤ iidLaw w M j :=
  prod_nonneg fun k _ => hw (j k)

lemma iid_marginal (w : Fin n → ℝ) (hw1 : ∑ j, w j = 1) (k : Fin M) (g : Fin n → ℝ) :
    ∑ j : Fin M → Fin n, iidLaw w M j * g (j k) = ∑ a, w a * g a := by
  classical
  have h := Fintype.prod_sum (fun (m : Fin M) (a : Fin n) => if m = k then w a * g a else w a)
  have hl : ∏ m : Fin M, ∑ a, (if m = k then w a * g a else w a) = ∑ a, w a * g a := by
    rw [← Finset.prod_erase_mul _ _ (mem_univ k)]
    have h1 : ∏ m ∈ univ.erase k, ∑ a, (if m = k then w a * g a else w a) = 1 := by
      refine prod_eq_one fun m hm => ?_
      simp [ne_of_mem_erase hm, hw1]
    rw [h1, one_mul]; simp
  rw [hl] at h
  rw [h]
  refine sum_congr rfl fun j _ => ?_
  unfold iidLaw
  have h2 : ∏ m ∈ univ.erase k, (if m = k then w (j m) * g (j m) else w (j m)) =
      ∏ m ∈ univ.erase k, w (j m) := prod_congr rfl fun m hm => by simp [ne_of_mem_erase hm]
  rw [← Finset.prod_erase_mul _ _ (mem_univ k), ← Finset.prod_erase_mul _ _ (mem_univ k), h2]
  simp only [ite_true]
  ring

lemma prod_two {β : Type*} [CommMonoid β] (f : Fin M → β) {k l : Fin M} (hkl : k ≠ l) :
    ∏ m, f m = f k * f l * ∏ m ∈ (univ.erase k).erase l, f m := by
  rw [← mul_prod_erase univ f (mem_univ k),
    ← mul_prod_erase _ f (mem_erase.2 ⟨hkl.symm, mem_univ l⟩), mul_assoc]

lemma iid_pair_fixed (w : Fin n → ℝ) (hw1 : ∑ j, w j = 1) {k l : Fin M} (hkl : k ≠ l) (a : Fin n) :
    ∑ j : Fin M → Fin n, iidLaw w M j * ((if j k = a then 1 else 0) * (if j l = a then 1 else 0)) =
      w a ^ 2 := by
  classical
  let h : Fin M → Fin n → ℝ := fun m b =>
    if m = k ∨ m = l then (if b = a then w b else 0) else w b
  have hprod := Fintype.prod_sum h
  have hL : ∏ m, ∑ b, h m b = w a ^ 2 := by
    rw [prod_two _ hkl]
    have hk : ∑ b, h k b = w a := by simp [h]
    have hl : ∑ b, h l b = w a := by simp [h]
    have hr : ∏ m ∈ (univ.erase k).erase l, ∑ b, h m b = 1 := by
      refine prod_eq_one fun m hm => ?_
      have hmk : m ≠ k := ne_of_mem_erase (mem_of_mem_erase hm)
      have hml : m ≠ l := ne_of_mem_erase hm
      simp [h, hmk, hml, hw1]
    rw [hk, hl, hr]; ring
  rw [← hL, hprod]
  refine sum_congr rfl fun j _ => ?_
  unfold iidLaw
  rw [prod_two _ hkl, prod_two (fun m => h m (j m)) hkl]
  have hr : ∏ m ∈ (univ.erase k).erase l, h m (j m) = ∏ m ∈ (univ.erase k).erase l, w (j m) := by
    refine prod_congr rfl fun m hm => ?_
    have hmk : m ≠ k := ne_of_mem_erase (mem_of_mem_erase hm)
    have hml : m ≠ l := ne_of_mem_erase hm
    simp [h, hmk, hml]
  rw [hr]
  simp only [h, true_or, or_true, ite_true]
  split_ifs <;> ring

lemma iid_pair (w : Fin n → ℝ) (hw1 : ∑ j, w j = 1) {k l : Fin M} (hkl : k ≠ l) :
    ∑ j : Fin M → Fin n, iidLaw w M j * (if j k = j l then 1 else 0) = ∑ a, w a ^ 2 := by
  classical
  have e : ∀ j : Fin M → Fin n, (if j k = j l then (1 : ℝ) else 0) =
      ∑ a, (if j k = a then 1 else 0) * (if j l = a then 1 else 0) := by
    intro j
    rw [Finset.sum_eq_single (j k)]
    · simp [eq_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp_rw [e, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun a _ => iid_pair_fixed w hw1 hkl a

/-! ### The collision bound -/

lemma two_le_offDiag (j : Fin M → Fin n) (hj : ¬ Function.Injective j) :
    (2 : ℝ) ≤ ∑ q ∈ (univ : Finset (Fin M)).offDiag, (if j q.1 = j q.2 then 1 else 0) := by
  classical
  obtain ⟨k, l, hkl, hne⟩ : ∃ k l, j k = j l ∧ k ≠ l := by
    simp only [Function.Injective, not_forall] at hj
    obtain ⟨k, l, h1, h2⟩ := hj
    exact ⟨k, l, h1, h2⟩
  have hpair : (k, l) ≠ (l, k) := fun h => hne (Prod.ext_iff.1 h).1
  have hsub : ({(k, l), (l, k)} : Finset (Fin M × Fin M)) ⊆ univ.offDiag := by
    intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl
    · simp [mem_offDiag, hne]
    · simp [mem_offDiag, Ne.symm hne]
  calc (2 : ℝ) = ∑ q ∈ {(k, l), (l, k)}, (if j q.1 = j q.2 then (1 : ℝ) else 0) := by
        rw [sum_pair hpair]; simp [hkl]; norm_num
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by split_ifs <;> norm_num)

lemma collision_le (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) :
    collision w M ≤ (M.choose 2 : ℝ) * ∑ j, w j ^ 2 := by
  classical
  set Sf : (Fin M → Fin n) → ℝ := fun j =>
    ∑ q ∈ (univ : Finset (Fin M)).offDiag, (if j q.1 = j q.2 then 1 else 0) with hSf
  have hSf0 : ∀ j, 0 ≤ Sf j := fun j => sum_nonneg fun _ _ => by split_ifs <;> norm_num
  calc collision w M
      ≤ ∑ j ∈ univ.filter (fun j : Fin M → Fin n => ¬ Function.Injective j),
          iidLaw w M j * ((1 / 2) * Sf j) := by
        refine sum_le_sum fun j hj => ?_
        have := two_le_offDiag j (mem_filter.1 hj).2
        exact le_mul_of_one_le_right (iidLaw_nonneg hw j) (by simp only [hSf]; linarith)
    _ ≤ ∑ j, iidLaw w M j * ((1 / 2) * Sf j) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun j _ _ => mul_nonneg (iidLaw_nonneg hw j) (by have := hSf0 j; positivity))
    _ = (1 / 2) * ∑ q ∈ (univ : Finset (Fin M)).offDiag,
          ∑ j, iidLaw w M j * (if j q.1 = j q.2 then 1 else 0) := by
        simp only [hSf, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun q _ => sum_congr rfl fun j _ => by ring
    _ = (1 / 2) * ∑ q ∈ (univ : Finset (Fin M)).offDiag, ∑ a, w a ^ 2 := by
        congr 1
        exact sum_congr rfl fun q hq => iid_pair w hw1 (mem_offDiag.1 hq).2.2
    _ = (M.choose 2 : ℝ) * ∑ j, w j ^ 2 := by
        rw [sum_const, offDiag_card, card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_sub (Nat.le_mul_self M), Nat.cast_choose_two]
        push_cast
        ring

theorem swor_collision : Claims.swor_collision := by
  intro n M w hw hw1
  exact collision_le w hw hw1

lemma wScore_facts {Z Θ : Type*} {z : Fin n → Z} {s : Θ → Z → ℝ} {sm sp : ℝ} {θ : Θ} (hn : 0 < n)
    (hsm : 0 < sm) (hs : ∀ θ x, sm ≤ s θ x ∧ s θ x ≤ sp) :
    (∀ j, 0 < wScore s z θ j) ∧ ∑ j, wScore s z θ j = 1 ∧
      ∀ j, wScore s z θ j ≤ sp / (sm * n) := by
  have hT : (n : ℝ) * sm ≤ ∑ l, s θ (z l) := by
    calc (n : ℝ) * sm = ∑ _l : Fin n, sm := by simp
      _ ≤ _ := sum_le_sum fun l _ => (hs θ (z l)).1
  have hTpos : 0 < ∑ l, s θ (z l) := lt_of_lt_of_le (by positivity) hT
  refine ⟨fun j => div_pos (lt_of_lt_of_le hsm (hs θ (z j)).1) hTpos, ?_, fun j => ?_⟩
  · unfold wScore; rw [← sum_div, div_self hTpos.ne']
  · unfold wScore
    rw [div_le_div_iff₀ hTpos (by positivity)]
    calc s θ (z j) * (sm * n) ≤ sp * (sm * n) :=
          mul_le_mul_of_nonneg_right (hs θ (z j)).2 (by positivity)
      _ ≤ sp * ∑ l, s θ (z l) := by
          have hsp : 0 ≤ sp := hsm.le.trans ((hs θ (z j)).1.trans (hs θ (z j)).2)
          rw [mul_comm sm]; exact mul_le_mul_of_nonneg_left hT hsp

lemma collision_score {Z Θ : Type*} {z : Fin n → Z} {s : Θ → Z → ℝ} {sm sp : ℝ} {θ : Θ}
    (hn : 0 < n) (hsm : 0 < sm) (hs : ∀ θ x, sm ≤ s θ x ∧ s θ x ≤ sp) :
    collision (wScore s z θ) M ≤ M * ((M : ℝ) - 1) * sp / (2 * sm * n) := by
  obtain ⟨hpos, h1, hle⟩ := wScore_facts (z := z) (θ := θ) hn hsm hs
  refine (collision_le _ (fun j => (hpos j).le) h1).trans ?_
  have hsq : ∑ j, wScore s z θ j ^ 2 ≤ sp / (sm * n) := by
    calc ∑ j, wScore s z θ j ^ 2 ≤ ∑ j, wScore s z θ j * (sp / (sm * n)) :=
          sum_le_sum fun j _ => by rw [sq]; exact mul_le_mul_of_nonneg_left (hle j) (hpos j).le
      _ = sp / (sm * n) := by rw [← sum_mul, h1, one_mul]
  have hc : (0 : ℝ) ≤ M.choose 2 := by positivity
  calc (M.choose 2 : ℝ) * ∑ j, wScore s z θ j ^ 2 ≤ (M.choose 2 : ℝ) * (sp / (sm * n)) :=
        mul_le_mul_of_nonneg_left hsq hc
    _ = M * ((M : ℝ) - 1) * sp / (2 * sm * n) := by
        rw [Nat.cast_choose_two]; field_simp

theorem swor_collision_score : Claims.swor_collision_score := by
  intro Z Θ n M z s sm sp θ hn hsm hs
  have h := collision_score (M := M) (z := z) (θ := θ) hn hsm hs
  refine ⟨h, fun hN => h.trans ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity)]
  have : M * ((M : ℝ) - 1) * sp ≤ n * sm := by rwa [div_le_iff₀ hsm] at hN
  nlinarith

/-! ### The perturbation identity -/

lemma iidExp_split (w : Fin n → ℝ) (f : (Fin M → Fin n) → ℝ) :
    iidExp w M f = (∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
      iidLaw w M j * f j) + collisionPart w M f := by
  unfold iidExp collisionPart
  rw [sum_filter_add_sum_filter_not]

lemma one_sub_collision (w : Fin n → ℝ) (hw1 : ∑ j, w j = 1) :
    1 - collision w M = ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
      iidLaw w M j := by
  have h := iidLaw_sum w M hw1
  rw [← sum_filter_add_sum_filter_not univ (fun j : Fin M → Fin n => Function.Injective j)] at h
  unfold collision
  linarith

lemma perturb (w : Fin n → ℝ) (f : (Fin M → Fin n) → ℝ) (F : ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (hp : collision w M < 1) (hf : ∀ j, |f j| ≤ F) :
    swoExp w M f - iidExp w M f =
        (collision w M * iidExp w M f - collisionPart w M f) / (1 - collision w M) ∧
      |swoExp w M f - iidExp w M f| ≤ 2 * F * collision w M / (1 - collision w M) ∧
      (collision w M ≤ 1 / 2 → |swoExp w M f - iidExp w M f| ≤ 4 * F * collision w M) := by
  set p := collision w M with hpdef
  have hp1 : 0 < 1 - p := by linarith
  have hp0 : 0 ≤ p := sum_nonneg fun j _ => iidLaw_nonneg hw j
  set I := ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j), iidLaw w M j * f j
  set N := collisionPart w M f
  have hE : iidExp w M f = I + N := iidExp_split w f
  have hid : swoExp w M f - iidExp w M f = (p * iidExp w M f - N) / (1 - p) := by
    have : swoExp w M f = I / (1 - p) := rfl
    rw [this, hE]
    field_simp
    ring
  have hN : |N| ≤ F * p := by
    calc |N| ≤ ∑ j ∈ univ.filter (fun j : Fin M → Fin n => ¬ Function.Injective j),
          |iidLaw w M j * f j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ univ.filter (fun j : Fin M → Fin n => ¬ Function.Injective j), iidLaw w M j * F :=
          sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_nonneg (iidLaw_nonneg hw j)]
            exact mul_le_mul_of_nonneg_left (hf j) (iidLaw_nonneg hw j)
      _ = F * p := by rw [← sum_mul, mul_comm]; rfl
  have hEb : |iidExp w M f| ≤ F := by
    calc |iidExp w M f| ≤ ∑ j, |iidLaw w M j * f j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, iidLaw w M j * F := sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_nonneg (iidLaw_nonneg hw j)]
            exact mul_le_mul_of_nonneg_left (hf j) (iidLaw_nonneg hw j)
      _ = F := by rw [← sum_mul, iidLaw_sum w M hw1, one_mul]
  have hnum : |p * iidExp w M f - N| ≤ 2 * F * p := by
    calc |p * iidExp w M f - N| ≤ |p * iidExp w M f| + |N| := abs_sub _ _
      _ ≤ p * F + F * p := by
          rw [abs_mul, abs_of_nonneg hp0]
          exact add_le_add (mul_le_mul_of_nonneg_left hEb hp0) hN
      _ = 2 * F * p := by ring
  have hFp : 0 ≤ F * p := (abs_nonneg _).trans hN
  have hb2 : |swoExp w M f - iidExp w M f| ≤ 2 * F * p / (1 - p) := by
    rw [hid, abs_div, abs_of_pos hp1]
    exact div_le_div_of_nonneg_right hnum hp1.le
  refine ⟨hid, hb2, fun hhalf => hb2.trans ?_⟩
  rw [div_le_iff₀ hp1]
  nlinarith

theorem swor_perturb : Claims.swor_perturb := by
  intro n M w f F hw hw1 hp hf
  exact perturb w f F hw hw1 hp hf

/-! ### The conditional Poisson law is the conditioned i.i.d. law -/

lemma fiber_card (S : Finset (Fin n)) (hS : S.card = M) :
    ((univ.filter fun j : Fin M → Fin n => Function.Injective j).filter
      (fun j => univ.image j = S)).card = M.factorial := by
  classical
  rw [filter_filter, ← Fintype.card_subtype]
  let e : {j : Fin M → Fin n // Function.Injective j ∧ univ.image j = S} ≃ (Fin M ≃ S) :=
    { toFun := fun j => Equiv.ofBijective
        (fun k => ⟨j.1 k, by have := mem_image_of_mem j.1 (mem_univ k); rwa [j.2.2] at this⟩)
        ⟨fun a b hab => j.2.1 (congrArg Subtype.val hab), fun y => by
          have hy : (y : Fin n) ∈ univ.image j.1 := by rw [j.2.2]; exact y.2
          obtain ⟨k, -, hk⟩ := mem_image.1 hy
          exact ⟨k, Subtype.ext hk⟩⟩
      invFun := fun e => ⟨fun k => (e k : Fin n), fun a b hab => e.injective (Subtype.ext hab), by
          ext y
          simp only [mem_image, mem_univ, true_and]
          constructor
          · rintro ⟨k, rfl⟩; exact (e k).2
          · intro hy
            obtain ⟨k, hk⟩ := e.surjective ⟨y, hy⟩
            exact ⟨k, by rw [hk]⟩⟩
      left_inv := fun j => by ext k; rfl
      right_inv := fun e => by ext k; rfl }
  rw [Fintype.card_congr e, Fintype.card_equiv ((S.orderIsoOfFin hS).toEquiv), Fintype.card_fin]

lemma iidLaw_eq_prod_image (w : Fin n → ℝ) {j : Fin M → Fin n} (hj : Function.Injective j) :
    iidLaw w M j = ∏ i ∈ univ.image j, w i := by
  classical
  unfold iidLaw
  rw [prod_image (fun a _ b _ h => hj h)]

lemma sum_inj_image (w : Fin n → ℝ) (H : Finset (Fin n) → ℝ) :
    ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
        iidLaw w M j * H (univ.image j) =
      M.factorial * ∑ S ∈ (univ : Finset (Fin n)).powersetCard M, (∏ i ∈ S, w i) * H S := by
  classical
  have hmaps : ∀ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
      univ.image j ∈ (univ : Finset (Fin n)).powersetCard M := by
    intro j hj
    rw [mem_powersetCard]
    exact ⟨subset_univ _, by
      rw [card_image_of_injective _ (mem_filter.1 hj).2, card_univ, Fintype.card_fin]⟩
  have h1 : ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
        iidLaw w M j * H (univ.image j) =
      ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
        (fun S => (∏ i ∈ S, w i) * H S) (univ.image j) :=
    sum_congr rfl fun j hj => by rw [iidLaw_eq_prod_image w (mem_filter.1 hj).2]
  rw [h1, ← sum_fiberwise_of_maps_to' (f := fun S => (∏ i ∈ S, w i) * H S) hmaps, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [sum_const, nsmul_eq_mul, fiber_card S (mem_powersetCard.1 hS).2]

lemma loss_eq_lossSub {Z : Type*} (L : Z → (Fin M → Z) → ℝ)
    (hL : ∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t)
    (x : Z) (z : Fin n → Z) {j : Fin M → Fin n} (hj : Function.Injective j) :
    L x (z ∘ j) = lossSub L x z (univ.image j) := by
  classical
  have hc : (univ.image j).card = M := by
    rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  unfold lossSub
  rw [dif_pos hc]
  let σf : Fin M → Fin M := fun k =>
    ((univ.image j).orderIsoOfFin hc).symm ⟨j k, mem_image_of_mem _ (mem_univ k)⟩
  have hσf : ∀ k, (univ.image j).orderEmbOfFin hc (σf k) = j k := by
    intro k
    rw [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have hσinj : Function.Injective σf := by
    intro a b hab
    have := congrArg ((univ.image j).orderEmbOfFin hc) hab
    rw [hσf, hσf] at this
    exact hj this
  let σ : Equiv.Perm (Fin M) := Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hσinj)
  have hcomp : (fun k => z ((univ.image j).orderEmbOfFin hc k)) ∘ σ = z ∘ j := by
    funext k
    simp only [Function.comp_apply, σ, Equiv.ofBijective_apply, hσf]
  rw [← hcomp, hL]

lemma card_filter_inj {j : Fin M → Fin n} (hj : Function.Injective j) (l : Fin n) :
    ((univ.filter fun k => j k = l).card : ℝ) = if l ∈ univ.image j then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨k₀, -, hk₀⟩ := mem_image.1 h
    have : univ.filter (fun k => j k = l) = {k₀} := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun hk => hj (hk.trans hk₀.symm), fun hk => hk ▸ hk₀⟩
    rw [this, card_singleton]; norm_num
  · have : univ.filter (fun k => j k = l) = ∅ := by
      ext k
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hk => h (mem_image.2 ⟨k, mem_univ _, hk⟩)
    rw [this, card_empty]; norm_num

lemma one_sub_collision_eq (w : Fin n → ℝ) (hw1 : ∑ j, w j = 1) :
    1 - collision w M = M.factorial * esym w univ M := by
  rw [one_sub_collision w hw1]
  have := sum_inj_image (M := M) w (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  rfl

theorem swor_cps : Claims.swor_cps := by
  intro Z n M w L x z l hΔ hL
  classical
  have hw1 : ∑ j, w j = 1 := hΔ.2.1
  have hE := (StatFormal.ICL.cps_wellPosed n M w hΔ).1
  have h1p := one_sub_collision_eq (M := M) w hw1
  have hfac : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  have h1pos : 0 < 1 - collision w M := by rw [h1p]; positivity
  refine ⟨by linarith, ?_, fun hM => ?_⟩
  · unfold swoExp
    rw [h1p]
    have e1 : ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
          iidLaw w M j * L x (z ∘ j) =
        ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
          iidLaw w M j * lossSub L x z (univ.image j) :=
      sum_congr rfl fun j hj => by rw [loss_eq_lossSub L hL x z (mem_filter.1 hj).2]
    rw [e1, sum_inj_image, mul_div_mul_left _ _ hfac.ne', sum_div]
    unfold Grisk cps
    exact sum_congr rfl fun S _ => by ring
  · unfold swoExp
    rw [h1p]
    have e1 : ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
          iidLaw w M j * (((univ.filter fun k => j k = l).card : ℝ) / M) =
        ∑ j ∈ univ.filter (fun j : Fin M → Fin n => Function.Injective j),
          iidLaw w M j * ((fun S : Finset (Fin n) => (if l ∈ S then (1 : ℝ) else 0) / M)
            (univ.image j)) :=
      sum_congr rfl fun j hj => by rw [card_filter_inj (mem_filter.1 hj).2]
    rw [e1, sum_inj_image w (fun S : Finset (Fin n) => (if l ∈ S then (1 : ℝ) else 0) / M),
      mul_div_mul_left _ _ hfac.ne', sum_div]
    unfold incl cps
    rw [sum_filter, sum_div]
    refine sum_congr rfl fun S _ => ?_
    split_ifs <;> ring

/-! ### Assembly of the value bound -/

lemma swoExp_lin {ι : Type*} (w : Fin n → ℝ) (s : Finset ι) (a : ι → ℝ)
    (g : ι → (Fin M → Fin n) → ℝ) :
    swoExp w M (fun j => ∑ l ∈ s, g l j * a l) = ∑ l ∈ s, swoExp w M (g l) * a l := by
  unfold swoExp
  simp_rw [mul_sum]
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun l _ => ?_
  rw [div_mul_eq_mul_div, sum_mul]
  congr 1
  exact sum_congr rfl fun j _ => by ring

lemma iidExp_lin {ι : Type*} (w : Fin n → ℝ) (s : Finset ι) (a : ι → ℝ)
    (g : ι → (Fin M → Fin n) → ℝ) :
    iidExp w M (fun j => ∑ l ∈ s, g l j * a l) = ∑ l ∈ s, iidExp w M (g l) * a l := by
  unfold iidExp
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun j _ => by ring

lemma swoExp_ge (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hp : collision w M < 1)
    (f : (Fin M → Fin n) → ℝ) (A : ℝ) (hf : ∀ j, A ≤ f j) : A ≤ swoExp w M f := by
  unfold swoExp
  have h1p : 0 < 1 - collision w M := by linarith
  rw [le_div_iff₀ h1p, one_sub_collision w hw1, mul_sum]
  exact sum_le_sum fun j _ => by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hf j) (iidLaw_nonneg hw j)

lemma iidExp_ge (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (f : (Fin M → Fin n) → ℝ) (A : ℝ) (hf : ∀ j, A ≤ f j) : A ≤ iidExp w M f := by
  unfold iidExp
  calc A = ∑ j, iidLaw w M j * A := by rw [← sum_mul, iidLaw_sum w M hw1, one_mul]
    _ ≤ _ := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf j) (iidLaw_nonneg hw j)

lemma cnt_sum (j : Fin M → Fin n) :
    ∑ l, ((univ.filter fun k => j k = l).card : ℝ) = M := by
  classical
  have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin M))) (t := (univ : Finset (Fin n)))
    (f := j) (fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_fin] at this
  exact_mod_cast this.symm

lemma iidExp_cnt (w : Fin n → ℝ) (hw1 : ∑ j, w j = 1) (hM : 1 ≤ M) (l : Fin n) :
    iidExp w M (fun j => ((univ.filter fun k => j k = l).card : ℝ) / M) = w l := by
  classical
  unfold iidExp
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have e : ∀ j : Fin M → Fin n, iidLaw w M j * (((univ.filter fun k => j k = l).card : ℝ) / M) =
      (1 / (M : ℝ)) * ∑ k, iidLaw w M j * (if j k = l then 1 else 0) := by
    intro j
    rw [card_filter, ← mul_sum]
    push_cast
    ring
  simp_rw [e]
  rw [← mul_sum, sum_comm]
  have h2 : ∀ k : Fin M, ∑ j : Fin M → Fin n, iidLaw w M j * (if j k = l then (1 : ℝ) else 0) =
      w l := by
    intro k
    rw [iid_marginal w hw1 k (fun a => if a = l then (1 : ℝ) else 0)]
    simp
  simp_rw [h2]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma log_sub_le {a b K : ℝ} (hK : 0 < K) (ha : K ≤ a) (hb : K ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / K := by
  have ha0 : 0 < a := hK.trans_le ha
  have hb0 : 0 < b := hK.trans_le hb
  have h1 : Real.log a - Real.log b ≤ (a - b) / b := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    rw [sub_div, div_self hb0.ne']; exact this
  have h2 : Real.log b - Real.log a ≤ (b - a) / a := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [sub_div, div_self ha0.ne']; exact this
  rw [abs_le]
  constructor
  · have : (b - a) / a ≤ |a - b| / K := by
      rw [div_le_div_iff₀ ha0 hK]
      have := le_abs_self (b - a); rw [abs_sub_comm] at this
      nlinarith [abs_nonneg (a - b)]
    linarith
  · have : (a - b) / b ≤ |a - b| / K := by
      rw [div_le_div_iff₀ hb0 hK]
      have := le_abs_self (a - b)
      nlinarith [abs_nonneg (a - b)]
    linarith

theorem swor_value : Claims.swor_value := by
  intro Z Θ n M m z zt s L K sm sp BL Kmin Kmax lcov Λ lKL hM hMn hm hsm hs hL hsym hKmin hK
    hlcov hΛ hN θ
  classical
  have hn : 0 < n := by omega
  set w := wScore s z θ with hwdef
  obtain ⟨hwpos, hw1, -⟩ := wScore_facts (z := z) (θ := θ) hn hsm hs
  have hw : ∀ j, 0 ≤ w j := fun j => (hwpos j).le
  have hΔ : InDeltaM w M := ⟨hw, hw1, by
    rw [filter_true_of_mem (fun j _ => (hwpos j).ne'), card_univ, Fintype.card_fin]; exact hMn⟩
  have hp1 : collision w M < 1 := (swor_cps Z n M w L (zt ⟨0, hm⟩) z ⟨0, hn⟩ hΔ hsym).1
  have hpbar := collision_score (M := M) (z := z) (θ := θ) hn hsm hs
  have hhalf := (swor_collision_score Z Θ n M z s sm sp θ hn hsm hs).2 hN
  set p := collision w M with hpdef
  have hp0 : 0 ≤ p := sum_nonneg fun j _ => iidLaw_nonneg hw j
  have z0 : Z := z ⟨0, hn⟩
  have hBL : 0 ≤ BL := (hL z0 fun _ => z0).1.trans (hL z0 fun _ => z0).2
  have hKK : Kmin ≤ Kmax := (hK z0 z0).1.trans (hK z0 z0).2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  -- the risk terms
  have hrisk : ∀ i, |Grisk w M (lossSub L (zt i) z) -
      ∑ j, iidLaw w M j * L (zt i) (z ∘ j)| ≤ 4 * BL * p := by
    intro i
    rw [(swor_cps Z n M w L (zt i) z ⟨0, hn⟩ hΔ hsym).2.1]
    refine (perturb w (fun j => L (zt i) (z ∘ j)) BL hw hw1 hp1 (fun j => ?_)).2.2 hhalf
    rw [abs_of_nonneg (hL _ _).1]; exact (hL _ _).2
  -- the coverage terms
  set c : Fin n → (Fin M → Fin n) → ℝ := fun l j =>
    ((univ.filter fun k => j k = l).card : ℝ) / M with hc
  set f : Fin m → (Fin M → Fin n) → ℝ := fun i j => ∑ l, c l j * K (zt i) (z l) with hf
  have hc0 : ∀ l j, 0 ≤ c l j := fun l j => by simp only [hc]; positivity
  have hc1 : ∀ j, ∑ l, c l j = 1 := fun j => by
    simp only [hc]; rw [← sum_div, cnt_sum j, div_self hM'.ne']
  have hfb : ∀ i j, Kmin ≤ f i j ∧ f i j ≤ Kmax := by
    intro i j
    constructor
    · calc Kmin = ∑ l, c l j * Kmin := by rw [← sum_mul, hc1, one_mul]
        _ ≤ f i j := sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (hK _ _).1 (hc0 l j)
    · calc f i j ≤ ∑ l, c l j * Kmax := sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (hK _ _).2 (hc0 l j)
        _ = Kmax := by rw [← sum_mul, hc1, one_mul]
  have hswo : ∀ i, ∑ l, incl w M l / M * K (zt i) (z l) = swoExp w M (f i) := by
    intro i
    rw [hf, swoExp_lin]
    refine sum_congr rfl fun l _ => ?_
    rw [(swor_cps Z n M w L (zt i) z l hΔ hsym).2.2 hM]
  have hiid : ∀ i, ∑ l, w l * K (zt i) (z l) = iidExp w M (f i) := by
    intro i
    rw [hf, iidExp_lin]
    refine sum_congr rfl fun l _ => ?_
    rw [iidExp_cnt w hw1 hM l]
  have hcov : ∀ i, |Real.log (∑ l, incl w M l / M * K (zt i) (z l)) -
      Real.log (∑ l, w l * K (zt i) (z l))| ≤ 4 * (Kmax / Kmin) * p := by
    intro i
    rw [hswo, hiid]
    have hlo1 := swoExp_ge w hw hw1 hp1 (f i) Kmin fun j => (hfb i j).1
    have hlo2 := iidExp_ge w hw hw1 (f i) Kmin fun j => (hfb i j).1
    refine (log_sub_le hKmin hlo1 hlo2).trans ?_
    have hd := (perturb w (f i) Kmax hw hw1 hp1 (fun j => by
      rw [abs_of_nonneg (hKmin.le.trans (hfb i j).1)]; exact (hfb i j).2)).2.2 hhalf
    calc |swoExp w M (f i) - iidExp w M (f i)| / Kmin ≤ 4 * Kmax * p / Kmin :=
          div_le_div_of_nonneg_right hd hKmin.le
      _ = 4 * (Kmax / Kmin) * p := by ring
  -- assembly
  have hdecomp : jSwor L K z zt lcov lKL w - jIid L K z zt lcov lKL w =
      (1 / (m : ℝ)) * ∑ i, (Grisk w M (lossSub L (zt i) z) - ∑ j, iidLaw w M j * L (zt i) (z ∘ j)) +
        lcov * (-(1 / (m : ℝ)) * ∑ i, (Real.log (∑ l, incl w M l / M * K (zt i) (z l)) -
          Real.log (∑ l, w l * K (zt i) (z l)))) := by
    unfold jSwor jIid
    rw [sum_sub_distrib, sum_sub_distrib]
    ring
  rw [hdecomp]
  have hA : |(1 / (m : ℝ)) * ∑ i, (Grisk w M (lossSub L (zt i) z) -
      ∑ j, iidLaw w M j * L (zt i) (z ∘ j))| ≤ 4 * BL * p := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    calc 1 / (m : ℝ) * |∑ i, (Grisk w M (lossSub L (zt i) z) -
          ∑ j, iidLaw w M j * L (zt i) (z ∘ j))| ≤ 1 / (m : ℝ) * ∑ _i : Fin m, 4 * BL * p :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hrisk i))
            (by positivity)
      _ = 4 * BL * p := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hB : |lcov * (-(1 / (m : ℝ)) * ∑ i, (Real.log (∑ l, incl w M l / M * K (zt i) (z l)) -
      Real.log (∑ l, w l * K (zt i) (z l))))| ≤ Λ * (4 * (Kmax / Kmin) * p) := by
    rw [abs_mul, abs_of_nonneg hlcov, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    have hs' : |∑ i, (Real.log (∑ l, incl w M l / M * K (zt i) (z l)) -
        Real.log (∑ l, w l * K (zt i) (z l)))| ≤ m * (4 * (Kmax / Kmin) * p) := by
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => hcov i).trans ?_)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hq : 0 ≤ 4 * (Kmax / Kmin) * p := by
      have : 0 ≤ Kmax / Kmin := div_nonneg (hKmin.le.trans hKK) hKmin.le
      positivity
    calc lcov * (1 / (m : ℝ) * |∑ i, (Real.log (∑ l, incl w M l / M * K (zt i) (z l)) -
          Real.log (∑ l, w l * K (zt i) (z l)))|) ≤ lcov * (1 / (m : ℝ) * (m * (4 * (Kmax / Kmin) * p))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs' (by positivity)) hlcov
      _ = lcov * (4 * (Kmax / Kmin) * p) := by field_simp
      _ ≤ Λ * (4 * (Kmax / Kmin) * p) := mul_le_mul_of_nonneg_right hΛ hq
  have hR : 0 ≤ BL + Λ * (Kmax / Kmin) := by
    have : 0 ≤ Kmax / Kmin := div_nonneg (hKmin.le.trans hKK) hKmin.le
    have : 0 ≤ Λ := hlcov.trans hΛ
    positivity
  calc _ ≤ 4 * BL * p + Λ * (4 * (Kmax / Kmin) * p) := (abs_add_le _ _).trans (add_le_add hA hB)
    _ = 4 * p * (BL + Λ * (Kmax / Kmin)) := by ring
    _ ≤ 4 * (M * ((M : ℝ) - 1) * sp / (2 * sm * n)) * (BL + Λ * (Kmax / Kmin)) := by
        gcongr
    _ = swC0 M sm sp BL Kmin Kmax Λ / n := by
        unfold swC0
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        field_simp
        ring

end StatFormal.Wave11b
