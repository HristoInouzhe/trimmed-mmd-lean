import StatFormal.Archive.OTFD.WaveL2.Statements
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Sign
import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity

/-!
# Route (wave L2): optimal assignments are cyclically monotone (untrusted)

If the identity is an optimal assignment for a cost matrix `C` (`Σ_a C a a ≤ Σ_a C a (π a)` for every `π ∈ S_N`),
then for every finite family of indices `i : Fin n → Fin N` (repetitions allowed) and every `ρ ∈ S_n`,
`Σ_k C (i k) (i k) ≤ Σ_k C (i k) (i (ρ k))`. Proof by strong induction on `#supp ρ`:
* `i` injective on `supp ρ`: conjugate `ρ` by `i` into a permutation of `Fin N`;
* `ρ` not a cycle: split off a cycle factor (disjoint supports, additivity);
* `ρ` a cycle and `i a = i b` for `a ≠ b` in its support: `swap a b * ρ` has the same sum, and either a smaller
  support or the same support and the opposite sign, so it is not a cycle.
The point form: the support `{((z_a, β_a), u_{σ a})}` of the plan of an optimal assignment `σ` is
`c`-cyclically monotone (Tau Ceti `IsCyclicallyMonotone`) for `c((x, β), y) = ‖x − y‖²/2`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset
open scoped ENNReal

namespace StatFormal.OTFD.WaveL2

open Equiv Equiv.Perm

section Index

variable {N : ℕ} (C : Fin N → Fin N → ℝ)

/-- The excess `D a b = C a b − C a a`. -/
def excess (a b : Fin N) : ℝ := C a b - C a a

theorem exists_perm_conj {n : ℕ} (i : Fin n → Fin N) (ρ : Perm (Fin n))
    (hinj : Set.InjOn i (ρ.support : Set (Fin n))) :
    ∃ π : Perm (Fin N), (∀ k ∈ ρ.support, π (i k) = i (ρ k)) ∧
      ∀ a, a ∉ i '' (ρ.support : Set (Fin n)) → π a = a := by
  classical
  set s : Set (Fin n) := (ρ.support : Set (Fin n))
  have hs : ∀ x, ρ x ∈ s ↔ x ∈ s := fun x => by simp [s, apply_mem_support]
  set ρs : Perm s := ρ.subtypePerm hs
  set e : s ≃ i '' s := Equiv.Set.imageOfInjOn i s hinj
  refine ⟨ofSubtype ((e.symm.trans ρs).trans e), fun k hk => ?_, fun a ha => ofSubtype_apply_of_not_mem _ ha⟩
  have hk' : k ∈ s := hk
  have him : i k ∈ i '' s := Set.mem_image_of_mem i hk'
  rw [ofSubtype_apply_of_mem _ him]
  have he : e.symm ⟨i k, him⟩ = ⟨k, hk'⟩ := by
    rw [Equiv.symm_apply_eq]; rfl
  simp only [Equiv.trans_apply, he]
  rfl

/-- The sum of excesses along `ρ` is nonnegative when `i` is injective on the support of `ρ`. -/
theorem excess_nonneg_of_injOn (hopt : ∀ π : Perm (Fin N), ∑ a, C a a ≤ ∑ a, C a (π a)) {n : ℕ}
    (i : Fin n → Fin N) (ρ : Perm (Fin n)) (hinj : Set.InjOn i (ρ.support : Set (Fin n))) :
    0 ≤ ∑ k, excess C (i k) (i (ρ k)) := by
  classical
  obtain ⟨π, h1, h2⟩ := exists_perm_conj i ρ hinj
  have hπ : 0 ≤ ∑ a, excess C a (π a) := by
    have := hopt π
    simp only [excess, Finset.sum_sub_distrib]
    linarith
  have hz : ∀ k ∉ ρ.support, excess C (i k) (i (ρ k)) = 0 := fun k hk => by
    rw [notMem_support.1 hk]; simp [excess]
  rw [← Finset.sum_subset (Finset.subset_univ ρ.support) (fun k _ hk => hz k hk)]
  have hz' : ∀ a ∉ ρ.support.image i, excess C a (π a) = 0 := fun a ha => by
    rw [h2 a (by simpa using ha)]; simp [excess]
  rw [← Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hz' a ha)] at hπ
  rw [Finset.sum_image (fun x hx y hy hxy => hinj hx hy hxy)] at hπ
  calc (0 : ℝ) ≤ ∑ k ∈ ρ.support, excess C (i k) (π (i k)) := hπ
    _ = ∑ k ∈ ρ.support, excess C (i k) (i (ρ k)) := Finset.sum_congr rfl fun k hk => by rw [h1 k hk]

theorem excess_mul_of_disjoint {n : ℕ} (i : Fin n → Fin N) {σ τ : Perm (Fin n)} (h : Disjoint σ τ) :
    ∑ k, excess C (i k) (i ((σ * τ) k)) = ∑ k, excess C (i k) (i (σ k)) + ∑ k, excess C (i k) (i (τ k)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Perm.mul_apply]
  rcases h k with hσ | hτ
  · by_cases hτk : τ k = k
    · rw [hτk, hσ]; simp [excess]
    · have hτ2 : τ (τ k) ≠ τ k := fun h' => hτk (τ.injective h')
      have : σ (τ k) = τ k := (h (τ k)).resolve_right hτ2
      rw [this, hσ]; simp [excess]
  · rw [hτ]; simp [excess]

theorem excess_swap_mul {n : ℕ} (i : Fin n → Fin N) (ρ : Perm (Fin n)) {a b : Fin n} (hab : i a = i b) :
    ∑ k, excess C (i k) (i ((swap a b * ρ) k)) = ∑ k, excess C (i k) (i (ρ k)) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Perm.mul_apply]
  have : i (swap a b (ρ k)) = i (ρ k) := by
    rcases eq_or_ne (ρ k) a with h | h
    · rw [h, swap_apply_left, hab]
    rcases eq_or_ne (ρ k) b with h' | h'
    · rw [h', swap_apply_right]; exact hab
    · rw [swap_apply_of_ne_of_ne h h']
  rw [this]

/-- **Optimal assignments are cyclically monotone** (index form). -/
theorem excess_nonneg (hopt : ∀ π : Perm (Fin N), ∑ a, C a a ≤ ∑ a, C a (π a)) :
    ∀ (m n : ℕ) (i : Fin n → Fin N) (ρ : Perm (Fin n)), #ρ.support ≤ m →
      0 ≤ ∑ k, excess C (i k) (i (ρ k)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro n i ρ hρ
    have : ρ = 1 := card_support_eq_zero.1 (Nat.le_zero.1 hρ)
    subst this; simp [excess]
  | succ m ih =>
    intro n i ρ hρ
    -- the splitting step for a non-cycle with support of size `≤ m + 1`
    have split : ∀ τ : Perm (Fin n), #τ.support ≤ m + 1 → ¬ IsCycle τ → τ ≠ 1 →
        0 ≤ ∑ k, excess C (i k) (i (τ k)) := by
      intro τ hτ hncyc hne
      obtain ⟨x, hx⟩ : ∃ x, τ x ≠ x := by
        by_contra hcon; push Not at hcon; exact hne (Perm.ext hcon)
      set c := τ.cycleOf x
      have hmem : c ∈ τ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.2 (mem_support.2 hx)
      have hdis : Disjoint (τ * c⁻¹) c := disjoint_mul_inv_of_mem_cycleFactorsFinset hmem
      have hcyc : IsCycle c := isCycle_cycleOf τ hx
      have hdecomp : τ = (τ * c⁻¹) * c := by group
      have hcard := hdis.card_support_mul
      rw [← hdecomp] at hcard
      have hc0 : 0 < #c.support := Finset.card_pos.2 hcyc.nonempty_support
      have hr0 : 0 < #(τ * c⁻¹).support := by
        refine Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 fun h0 => hncyc ?_)
        have : τ * c⁻¹ = 1 := support_eq_empty_iff.1 h0
        rw [hdecomp, this, one_mul]; exact hcyc
      rw [hdecomp, excess_mul_of_disjoint C i hdis]
      exact add_nonneg (ih n i _ (by omega)) (ih n i _ (by omega))
    by_cases hinj : Set.InjOn i (ρ.support : Set (Fin n))
    · exact excess_nonneg_of_injOn C hopt i ρ hinj
    by_cases hcyc : IsCycle ρ
    swap
    · by_cases h1 : ρ = 1
      · subst h1; simp [excess]
      · exact split ρ hρ hcyc h1
    -- `ρ` is a cycle and `i` is not injective on its support
    simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨a, ha, b, hb, hab, hne⟩ := hinj
    set ρ' := swap a b * ρ
    rw [← excess_swap_mul C i ρ hab]
    have hsub : ρ'.support ⊆ ρ.support := by
      intro y hy
      have := support_mul_le (swap a b) ρ hy
      rcases Finset.mem_union.1 this with h | h
      · rw [support_swap hne] at h
        rcases Finset.mem_insert.1 h with rfl | h
        · exact ha
        · rw [Finset.mem_singleton.1 h]; exact hb
      · exact h
    rcases (Finset.card_le_card hsub).lt_or_eq with hlt | heq
    · exact ih n i ρ' (by omega)
    · have hne1 : ρ' ≠ 1 := by
        intro h1
        have : #ρ'.support = 0 := by rw [h1]; simp
        have hpos : 0 < #ρ.support := Finset.card_pos.2 hcyc.nonempty_support
        omega
      have hncyc : ¬ IsCycle ρ' := by
        intro hc'
        have hs1 := hcyc.sign
        have hs2 := hc'.sign
        have hs3 : sign ρ' = -sign ρ := by
          rw [Perm.sign_mul, Perm.sign_swap hne, neg_one_mul]
        rw [heq, ← hs1] at hs2
        rw [hs2] at hs3
        exact units_ne_neg_self _ hs3
      exact split ρ' (by omega) hncyc hne1

theorem sum_le_sum_perm_of_opt (hopt : ∀ π : Perm (Fin N), ∑ a, C a a ≤ ∑ a, C a (π a)) {n : ℕ}
    (i : Fin n → Fin N) (ρ : Perm (Fin n)) :
    ∑ k, C (i k) (i k) ≤ ∑ k, C (i k) (i (ρ k)) := by
  have := excess_nonneg C hopt _ n i ρ le_rfl
  simp only [excess, Finset.sum_sub_distrib] at this
  linarith

end Index

end StatFormal.OTFD.WaveL2
