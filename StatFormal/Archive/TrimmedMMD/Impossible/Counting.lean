import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Impossibility theorem — counting extensions

Untrusted proof library for `Claims.impossible`: the number of `σ : Fin K → Fin L` with
prescribed values on the image of an injective `β : Fin m → Fin K` is `L ^ (K - m)`.
-/

namespace StatFormal.TrimmedMMD.Impossible

open Finset

theorem card_extensions {K L m : ℕ} (β : Fin m → Fin K) (hβ : Function.Injective β)
    (lam : Fin m → Fin L) :
    (univ.filter (fun σ : Fin K → Fin L => ∀ i, σ (β i) = lam i)).card = L ^ (K - m) := by
  classical
  have step1 : (univ.filter (fun σ : Fin K → Fin L => ∀ i, σ (β i) = lam i)).card
      = ∑ σ : Fin K → Fin L, ∏ j, (if (∀ i, β i = j → σ j = lam i) then 1 else 0 : ℕ) := by
    rw [card_filter]
    refine sum_congr rfl fun σ _ => ?_
    simp only [Fintype.prod_boole]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (fun j i hij => hij ▸ h1 i) h2
    · exact absurd (fun i => h2 (β i) i rfl) h1
    · rfl
  have step2 : ∀ j : Fin K, ∑ l : Fin L, (if (∀ i, β i = j → l = lam i) then 1 else 0 : ℕ)
      = if j ∈ univ.image β then 1 else L := by
    intro j
    split_ifs with hj
    · obtain ⟨i₀, -, rfl⟩ := mem_image.1 hj
      have : ∀ l : Fin L, (∀ i, β i = β i₀ → l = lam i) ↔ l = lam i₀ :=
        fun l => ⟨fun H => H i₀ rfl, fun H i hi => by rw [hβ hi]; exact H⟩
      simp only [this, sum_ite_eq', mem_univ, ite_true]
    · have : ∀ l : Fin L, (∀ i, β i = j → l = lam i) :=
        fun l i hi => absurd (mem_image.2 ⟨i, mem_univ _, hi⟩) hj
      rw [sum_congr rfl fun l _ => ite_eq_left_of_eq_true _ _ (eq_true (this l))]
      simp
  rw [step1, ← Fintype.prod_sum
    (fun j l => (if (∀ i, β i = j → l = lam i) then 1 else 0 : ℕ)),
    Fintype.prod_congr _ _ step2, prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  have h2 : (univ.filter fun j => j ∉ univ.image β) = (univ.image β)ᶜ := by ext; simp
  rw [h2, card_compl, card_image_of_injective _ hβ, Fintype.card_fin, card_univ,
    Fintype.card_fin]

end StatFormal.TrimmedMMD.Impossible
