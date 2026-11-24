import StatFormal.Lib.Concentration.Rademacher

/-!
# Sign averages over an arbitrary finite index set; coordinatewise contraction

Library component (concentration). Untrusted library code. Generalises `Rademacher.lean` (index `Fin n`) to an arbitrary
finite index type `ι`, which is what two-sample (or, more generally, non-identically distributed) symmetrisation needs:
the coordinates of a joint sample `X_1, …, X_n, Y_1, …, Y_m` are indexed by `Fin n ⊕ Fin m`.

## Conventions

* A sign vector is `σ : ι → Bool` with sign `rsign`; `signE F = 2^{-|ι|} · ∑_σ F σ` is exactly `E_σ F(σ)` for i.i.d.
  uniform signs (`signE_eq_radE`: for `ι = Fin n` it is `radE`).
* Classes are indexed by an arbitrary nonempty type `T`; every result assumes a uniform bound, so suprema are finite.

## Main results

* `signE_iSup_contraction` (**coordinatewise contraction principle**, signed form, constant 1; Shalev-Shwartz and
  Ben-David 2014, Lemma 26.9; Mohri et al. 2018, Lemma 5.7): for an arbitrary bounded set of vectors `a t ∈ ℝ^ι` and
  **coordinate-specific** 1-Lipschitz maps `φ i`, `E_σ sup_t ∑ σᵢ φᵢ(a t i) ≤ E_σ sup_t ∑ σᵢ a t i`;
* `signE_iSup_contraction_lip`: the version with `Lᵢ`-Lipschitz maps, compared with `∑ σᵢ Lᵢ a t i`;
* `signE_rsign_mul` (`E σᵢσⱼ = δᵢⱼ`), `sq_signE_le` (Jensen), `signE_norm_sum_le` (`E‖∑σᵢvᵢ‖ ≤ √∑‖vᵢ‖²`);
* `signE_comp_inl`, `signE_comp_inr`: marginals of `signE` over `ι ⊕ ι'`;
* `signE_negSigns`: invariance under `σ ↦ −σ`.
-/

noncomputable section
open Finset Real

namespace StatFormal.Concentration

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expectation over a uniform sign vector `σ ∈ {±1}^ι`. -/
def signE (F : (ι → Bool) → ℝ) : ℝ := ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ σ, F σ

theorem signE_eq_radE {n : ℕ} (F : (Fin n → Bool) → ℝ) : signE F = radE F := by
  simp [signE, radE, Fintype.card_fin]

theorem signE_mono {F G : (ι → Bool) → ℝ} (h : ∀ σ, F σ ≤ G σ) : signE F ≤ signE G := by
  unfold signE
  gcongr with σ
  exact h σ

theorem signE_add (F G : (ι → Bool) → ℝ) :
    signE (fun σ => F σ + G σ) = signE F + signE G := by
  simp [signE, sum_add_distrib, mul_add]

theorem signE_const_mul (c : ℝ) (F : (ι → Bool) → ℝ) :
    signE (fun σ => c * F σ) = c * signE F := by
  simp only [signE, ← mul_sum]; ring

theorem signE_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → Bool) → ℝ) :
    signE (fun σ => ∑ k ∈ s, F k σ) = ∑ k ∈ s, signE (F k) := by
  simp only [signE, mul_sum]
  rw [Finset.sum_comm]

theorem card_signsι : (Fintype.card (ι → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card ι := by
  rw [Fintype.card_fun, Fintype.card_bool]; push_cast; ring

theorem signE_const (c : ℝ) : signE (fun _ : ι → Bool => c) = c := by
  simp only [signE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signsι]
  field_simp

theorem signE_nonneg {F : (ι → Bool) → ℝ} (h : ∀ σ, 0 ≤ F σ) : 0 ≤ signE F := by
  unfold signE; exact mul_nonneg (by positivity) (sum_nonneg fun σ _ => h σ)

theorem abs_signE_le {F : (ι → Bool) → ℝ} {C : ℝ} (h : ∀ σ, |F σ| ≤ C) : |signE F| ≤ C := by
  unfold signE
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ Fintype.card ι)]
  calc ((2 : ℝ) ^ Fintype.card ι)⁻¹ * |∑ σ, F σ|
      ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ _σ : ι → Bool, C := by
        gcongr; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun σ _ => h σ)
    _ = C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signsι]; field_simp

/-- Flip the sign at coordinate `i`. -/
def flipι (i : ι) (σ : ι → Bool) : ι → Bool := fun j => if j = i then !σ j else σ j

omit [Fintype ι] in
theorem flipι_flipι (i : ι) (σ : ι → Bool) : flipι i (flipι i σ) = σ := by
  funext j; by_cases h : j = i <;> simp [flipι, h]

theorem sum_flipι (i : ι) (F : (ι → Bool) → ℝ) : ∑ σ, F (flipι i σ) = ∑ σ, F σ :=
  Equiv.sum_comp (Function.Involutive.toPerm _ (flipι_flipι i)) F

/-- Flip all signs. -/
def negSignsι (σ : ι → Bool) : ι → Bool := fun j => !σ j

theorem signE_negSigns (F : (ι → Bool) → ℝ) : signE (fun σ => F (negSignsι σ)) = signE F := by
  have h : Function.Involutive (negSignsι (ι := ι)) := fun σ => by funext j; simp [negSignsι]
  simp only [signE]
  exact congrArg _ (Equiv.sum_comp (Function.Involutive.toPerm _ h) F)

/-! ### Coordinatewise contraction -/

/-- One step of the contraction principle: replace the identity at coordinate `i` by a 1-Lipschitz `φ`. -/
theorem signE_iSup_update_le {T : Type*} [Nonempty T] (a : T → ι → ℝ) {B : ℝ}
    (ha : ∀ t j, |a t j| ≤ B) (ψ : ι → ℝ → ℝ) (hψ : ∀ j x y, |ψ j x - ψ j y| ≤ |x - y|)
    (i : ι) (hψi : ψ i = id) (φ : ℝ → ℝ) (hφ : ∀ x y, |φ x - φ y| ≤ |x - y|) :
    signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j)) ≤
      signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * ψ j (a t j)) := by
  set u : (ι → Bool) → T → ℝ :=
    fun σ t => ∑ j ∈ univ.erase i, rsign (σ j) * ψ j (a t j) with hu
  have hsplitG : ∀ σ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j) =
      u σ t + rsign (σ i) * φ (a t i) := by
    intro σ t
    rw [← Finset.add_sum_erase _ _ (mem_univ i), Function.update_self, add_comm]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  have hsplitF : ∀ σ t, ∑ j, rsign (σ j) * ψ j (a t j) = u σ t + rsign (σ i) * a t i := by
    intro σ t
    rw [← Finset.add_sum_erase _ _ (mem_univ i), hψi, add_comm]
    rfl
  have hu_flip : ∀ σ t, u (flipι i σ) t = u σ t := by
    intro σ t
    refine sum_congr rfl fun j hj => ?_
    simp [flipι, ne_of_mem_erase hj]
  have hflip_i : ∀ σ, rsign (flipι i σ i) = -rsign (σ i) := by
    intro σ; simp [flipι, rsign_not]
  set C := ∑ j, (|ψ j 0| + B) with hC
  have hψb : ∀ j y, |ψ j y| ≤ |ψ j 0| + |y| := by
    intro j y
    have := hψ j y 0
    rw [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (ψ j y) (ψ j 0)
    linarith
  have hCu : ∀ σ t, |u σ t| ≤ C := by
    intro σ t
    calc |u σ t| ≤ ∑ j ∈ univ.erase i, |rsign (σ j) * ψ j (a t j)| := abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ univ.erase i, |ψ j (a t j)| := by simp [abs_mul, abs_rsign]
      _ ≤ ∑ j ∈ univ.erase i, (|ψ j 0| + B) :=
          sum_le_sum fun j _ => (hψb j _).trans (by linarith [ha t j])
      _ ≤ C := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun j _ _ => by
          have := (abs_nonneg _).trans (ha t j); positivity
  have hbdd : ∀ σ (c : ℝ), |c| ≤ 1 → BddAbove (Set.range fun t => u σ t + c * a t i) := by
    intro σ c hc
    refine bddAbove_of_abs_le (C := C + B) fun t => ?_
    refine (abs_add_le _ _).trans ?_
    have h1 := hCu σ t
    have h2 : |c * a t i| ≤ B := by
      rw [abs_mul]
      calc |c| * |a t i| ≤ 1 * B := mul_le_mul hc (ha t i) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    linarith
  have hpair : ∀ σ, (⨆ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j)) +
      (⨆ t, ∑ j, rsign (flipι i σ j) * Function.update ψ i φ j (a t j)) ≤
      (⨆ t, ∑ j, rsign (σ j) * ψ j (a t j)) +
        ⨆ t, ∑ j, rsign (flipι i σ j) * ψ j (a t j) := by
    intro σ
    simp_rw [hsplitG, hsplitF, hu_flip, hflip_i]
    have key := iSup_add_iSup_sub_le (u σ) (fun t => φ (a t i)) (fun t => a t i)
      (fun s t => hφ _ _)
    rcases Bool.eq_false_or_eq_true (σ i) with h | h
    · rw [h, rsign_true]
      have h1 := hbdd σ 1 (by simp)
      have h2 := hbdd σ (-1) (by simp)
      simp only [one_mul, neg_mul, ← sub_eq_add_neg] at h1 h2 ⊢
      exact key h1 h2
    · rw [h, rsign_false]
      have h1 := hbdd σ 1 (by simp)
      have h2 := hbdd σ (-1) (by simp)
      simp only [one_mul, neg_mul, neg_neg, ← sub_eq_add_neg] at h1 h2 ⊢
      linarith [key h1 h2]
  unfold signE
  have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have hG := sum_flipι i (fun σ => ⨆ t, ∑ j, rsign (σ j) * Function.update ψ i φ j (a t j))
  have hF := sum_flipι i (fun σ => ⨆ t, ∑ j, rsign (σ j) * ψ j (a t j))
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ univ) => hpair σ
  rw [sum_add_distrib, sum_add_distrib] at hsum
  linarith

/-- Mixed family: `φ j` on `S`, identity off `S`. -/
def mixφι (φ : ι → ℝ → ℝ) (S : Finset ι) : ι → ℝ → ℝ :=
  fun j => if j ∈ S then φ j else id

/-- **Coordinatewise contraction principle** (signed form, constant 1): for an arbitrary bounded set
`{a t : t ∈ T} ⊆ ℝ^ι` and 1-Lipschitz maps `φ i` that may differ from coordinate to coordinate,
`E_σ sup_t ∑ σᵢ φᵢ(a t i) ≤ E_σ sup_t ∑ σᵢ a t i`. -/
theorem signE_iSup_contraction {T : Type*} [Nonempty T] (a : T → ι → ℝ) {B : ℝ}
    (ha : ∀ t j, |a t j| ≤ B) (φ : ι → ℝ → ℝ) (hφ : ∀ j x y, |φ j x - φ j y| ≤ |x - y|) :
    signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * φ j (a t j)) ≤
      signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * a t j) := by
  have hS : ∀ S : Finset ι,
      signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * mixφι φ S j (a t j)) ≤
        signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * a t j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [mixφι]
    | insert i S hi ih =>
      have hupd : mixφι φ (insert i S) = Function.update (mixφι φ S) i (φ i) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [mixφι]
        · simp [mixφι, hj]
      rw [hupd]
      refine le_trans (signE_iSup_update_le a ha _ ?_ i (by simp [mixφι, hi]) (φ i) (hφ i)) ih
      intro j x y
      simp only [mixφι]
      split_ifs
      · exact hφ j x y
      · exact le_rfl
  simpa [mixφι] using hS univ

/-- Coordinatewise contraction with Lipschitz constants: if `φ i` is `L i`-Lipschitz (`L i ≥ 0`), then
`E_σ sup_t ∑ σᵢ φᵢ(a t i) ≤ E_σ sup_t ∑ σᵢ Lᵢ a t i`. -/
theorem signE_iSup_contraction_lip {T : Type*} [Nonempty T] (a : T → ι → ℝ) {B : ℝ}
    (ha : ∀ t j, |a t j| ≤ B) (φ : ι → ℝ → ℝ) (L : ι → ℝ) (hL : ∀ j, 0 ≤ L j)
    (hφ : ∀ j x y, |φ j x - φ j y| ≤ L j * |x - y|) :
    signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * φ j (a t j)) ≤
      signE (fun σ => ⨆ t, ∑ j, rsign (σ j) * (L j * a t j)) := by
  -- on coordinates with `L j > 0`, `φ j = ψ j ∘ (L j ·)` with `ψ j` 1-Lipschitz; with `L j = 0`, `φ j` is constant
  set ψ : ι → ℝ → ℝ := fun j u => if L j = 0 then φ j 0 else φ j (u / L j) with hψdef
  have hψ : ∀ j x y, |ψ j x - ψ j y| ≤ |x - y| := by
    intro j x y
    by_cases h : L j = 0
    · simp [hψdef, h]
    · simp only [hψdef, h, ite_false]
      have hpos : 0 < L j := lt_of_le_of_ne (hL j) (Ne.symm h)
      calc |φ j (x / L j) - φ j (y / L j)| ≤ L j * |x / L j - y / L j| := hφ j _ _
        _ = |x - y| := by
          rw [← sub_div, abs_div, abs_of_pos hpos]; field_simp
  have heq : ∀ t j, φ j (a t j) = ψ j (L j * a t j) := by
    intro t j
    by_cases h : L j = 0
    · simp only [hψdef, h, ite_true]
      have := hφ j (a t j) 0
      rw [h, zero_mul, abs_nonpos_iff, sub_eq_zero] at this
      exact this
    · simp only [hψdef, h, ite_false]
      congr 1; field_simp
  simp_rw [heq]
  exact signE_iSup_contraction (fun t j => L j * a t j) (B := ∑ j, L j * B)
    (fun t j => by
      rw [abs_mul, abs_of_nonneg (hL j)]
      calc L j * |a t j| ≤ L j * B := mul_le_mul_of_nonneg_left (ha t j) (hL j)
        _ ≤ ∑ k, L k * B := single_le_sum (f := fun k => L k * B) (fun k _ => by
            have := (abs_nonneg _).trans (ha t k); exact mul_nonneg (hL k) this) (mem_univ j)) ψ hψ

/-! ### Second moments -/

theorem signE_rsign_mul (i j : ι) :
    signE (fun σ => rsign (σ i) * rsign (σ j)) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij; simp only [rsign_mul_self, signE_const]
  · have h := sum_flipι i (fun σ : ι → Bool => rsign (σ i) * rsign (σ j))
    have hj : ∀ σ, flipι i σ j = σ j := fun σ => by simp [flipι, Ne.symm hij]
    have hi : ∀ σ, rsign (flipι i σ i) = -rsign (σ i) := fun σ => by simp [flipι, rsign_not]
    simp only [hj, hi, neg_mul, sum_neg_distrib] at h
    unfold signE
    have : ∑ σ : ι → Bool, rsign (σ i) * rsign (σ j) = 0 := by linarith
    rw [this, mul_zero]

/-- Jensen for the sign average. -/
theorem sq_signE_le (F : (ι → Bool) → ℝ) : signE F ^ 2 ≤ signE (fun σ => F σ ^ 2) := by
  unfold signE
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (ι → Bool))) (f := F)
  rw [Finset.card_univ, card_signsι] at h
  have h2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
  rw [mul_pow]
  calc ((2 : ℝ) ^ Fintype.card ι)⁻¹ ^ 2 * (∑ σ, F σ) ^ 2
      ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ ^ 2 * ((2 : ℝ) ^ Fintype.card ι * ∑ σ, F σ ^ 2) := by gcongr
    _ = ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ σ, F σ ^ 2 := by field_simp

/-- `E_σ ‖∑ σᵢ vᵢ‖ ≤ √(∑ ‖vᵢ‖²)` in a real inner-product space. -/
theorem signE_norm_sum_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : ι → H) :
    signE (fun σ => ‖∑ i, rsign (σ i) • v i‖) ≤ √(∑ i, ‖v i‖ ^ 2) := by
  have hsq : signE (fun σ => ‖∑ i, rsign (σ i) • v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
    have hpt : ∀ σ : ι → Bool, ‖∑ i, rsign (σ i) • v i‖ ^ 2 =
        ∑ i, ∑ j, inner ℝ (v i) (v j) * (rsign (σ i) * rsign (σ j)) := by
      intro σ
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      refine sum_congr rfl fun i _ => ?_
      rw [inner_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right]; ring
    simp_rw [hpt]
    rw [signE_sum]
    simp_rw [signE_sum, signE_const_mul, signE_rsign_mul]
    simp
  have hJ := sq_signE_le (fun σ => ‖∑ i, rsign (σ i) • v i‖)
  rw [hsq] at hJ
  exact (le_abs_self _).trans (Real.abs_le_sqrt hJ)

/-! ### Marginals over a sum of index types -/

section Marginal

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι']

theorem signE_comp_inl (F : (ι → Bool) → ℝ) :
    signE (ι := ι ⊕ ι') (fun σ => F (fun i => σ (Sum.inl i))) = signE F := by
  unfold signE
  rw [← (Equiv.sumArrowEquivProdArrow ι ι' Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signsι, Fintype.card_sum, pow_add]
  rw [← Finset.mul_sum]
  field_simp

theorem signE_comp_inr (F : (ι' → Bool) → ℝ) :
    signE (ι := ι ⊕ ι') (fun σ => F (fun j => σ (Sum.inr j))) = signE F := by
  unfold signE
  rw [← (Equiv.sumArrowEquivProdArrow ι ι' Bool).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signsι, Fintype.card_sum, pow_add]
  rw [← Finset.mul_sum]
  field_simp

end Marginal

end StatFormal.Concentration
