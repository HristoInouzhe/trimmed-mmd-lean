import StatFormal.Wave30tm.RouteCells

set_option linter.style.longLine false

/-!
# Wave 30tm — the mixture dominates the uniform product off collisions (untrusted proof file)

Index the `n + m` observations by `ι = Fin n ⊕ Fin m` (the `X`'s, then the `Y`'s). Coordinate `i` has law
`Qσ K 2 (sig σ i)`: `P_σ` for an `X`, `Q_σ` for a `Y`. With `w = 2^{-K}`, the mixture `∑_σ w • ∏_i Qσ K 2 (sig σ i)`
dominates `P_u^ι` restricted to `goodSetι K ι` (all points in `[0,1)`, in pairwise distinct blocks): there the mixture
density is exactly `1` (`2^{-K} · 2^{n+m} · 2^{K-n-m}`, the count of `card_extensions_fintype`). And
`P_u^ι (goodSetι K ι)ᶜ ≤ (n + m)² / K`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatFormal.Wave30tm

open StatFormal.TrimmedMMD.Impossible

variable {K : ℕ}

/-- No two of the coordinates fall into the same block `[b/K, (b+1)/K)`, and all lie in `[0,1)`. -/
def goodSetι (K : ℕ) (ι : Type*) : Set (ι → ℝ) :=
  {y | (∀ i, y i ∈ Ico (0 : ℝ) 1) ∧ Function.Injective (fun i => ⌊(K : ℝ) * y i⌋₊)}

theorem measurableSet_goodSetι (K : ℕ) (ι : Type*) [Fintype ι] :
    MeasurableSet (goodSetι K ι) := by
  have hΦ : Measurable (fun y : ι → ℝ => fun i => ⌊(K : ℝ) * y i⌋₊) :=
    measurable_pi_iff.2 fun i =>
      Nat.measurable_floor.comp ((measurable_pi_apply i).const_mul _)
  have : goodSetι K ι = (univ.pi fun _ => Ico (0 : ℝ) 1) ∩
      (fun y : ι → ℝ => fun i => ⌊(K : ℝ) * y i⌋₊) ⁻¹' {f | Function.Injective f} := by
    ext y; simp [goodSetι]
  rw [this]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).inter
    (hΦ (Set.to_countable _).measurableSet)

/-- The cell choice of coordinate `i`: `σ` for an `X`, the other cells `flipσ σ` for a `Y`. -/
def sig {n m : ℕ} (σ : Fin K → Fin 2) : Fin n ⊕ Fin m → Fin K → Fin 2 :=
  Sum.elim (fun _ => σ) (fun _ => flipσ σ)

/-- Pointwise: on `goodSetι`, the mixture density equals `1`. -/
theorem one_le_mixture_density2 {n m : ℕ} (hK : 0 < K) {y : Fin n ⊕ Fin m → ℝ}
    (hy : y ∈ goodSetι K (Fin n ⊕ Fin m)) :
    1 ≤ ∑ σ : Fin K → Fin 2, ((((2 : ℕ) : ℝ≥0∞)) ^ K)⁻¹ *
      (((2 : ℕ) : ℝ≥0∞) ^ Fintype.card (Fin n ⊕ Fin m) *
        (univ.pi fun i => cellSet K 2 (sig σ i)).indicator 1 y) := by
  classical
  set β : Fin n ⊕ Fin m → Fin K := fun i =>
    ⟨⌊((K : ℝ) * ((2 : ℕ) : ℝ)) * y i⌋₊ / 2, floor_div_lt hK two_pos (hy.1 i)⟩ with hβdef
  set lam : Fin n ⊕ Fin m → Fin 2 := fun i =>
    ⟨⌊((K : ℝ) * ((2 : ℕ) : ℝ)) * y i⌋₊ % 2, Nat.mod_lt _ two_pos⟩ with hlamdef
  set lam' : Fin n ⊕ Fin m → Fin 2 := fun i => Sum.elim (fun _ => lam i) (fun _ => (lam i).rev) i
    with hlam'def
  have hβ : Function.Injective β := by
    intro i i' h
    have h' := congrArg Fin.val h
    simp only [β, floor_mul_div two_pos] at h'
    exact hy.2 h'
  have hNK : Fintype.card (Fin n ⊕ Fin m) ≤ K := by
    simpa using Fintype.card_le_of_injective β hβ
  have hind : ∀ σ : Fin K → Fin 2, (univ.pi fun i => cellSet K 2 (sig σ i)).indicator
      (1 : (Fin n ⊕ Fin m → ℝ) → ℝ≥0∞) y = if (∀ i, σ (β i) = lam' i) then 1 else 0 := by
    intro σ
    simp only [Set.indicator_apply, Set.mem_univ_pi, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    refine forall_congr' fun i => ?_
    rw [mem_cellSet_iff' hK two_pos _ (hy.1 i)]
    rcases i with j | j
    · rfl
    · simp only [sig, flipσ, Sum.elim_inr, lam', Fin.rev_eq_iff]
      rfl
  simp only [hind, ← Finset.mul_sum, Finset.sum_boole, card_extensions_fintype β hβ lam']
  refine le_of_eq ?_
  rw [Nat.cast_pow, ← pow_add, Nat.add_sub_cancel' hNK,
    ENNReal.inv_mul_cancel (pow_ne_zero _ (by norm_num))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top 2))]

/-- **Domination**: `P_u^ι |_{goodSetι} ≤ ∑_σ 2^{-K} • ∏_i Qσ K 2 (sig σ i)`. -/
theorem restrict_goodSetι_le_mixture {n m : ℕ} (hK : 0 < K) :
    (Measure.pi fun _ : Fin n ⊕ Fin m => volume.restrict (Icc (0 : ℝ) 1)).restrict
        (goodSetι K (Fin n ⊕ Fin m)) ≤
      ∑ σ : Fin K → Fin 2, ((((2 : ℕ) : ℝ≥0∞)) ^ K)⁻¹ •
        Measure.pi (fun i : Fin n ⊕ Fin m => Qσ K 2 (sig σ i)) := by
  rw [Measure.le_iff]
  intro B hB
  rw [Measure.restrict_apply hB, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hE := measurableSet_goodSetι K (Fin n ⊕ Fin m)
  calc (Measure.pi fun _ : Fin n ⊕ Fin m => volume.restrict (Icc (0 : ℝ) 1))
          (B ∩ goodSetι K (Fin n ⊕ Fin m))
      ≤ Measure.pi (fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ))
          (B ∩ goodSetι K (Fin n ⊕ Fin m)) := by
        rw [← Measure.restrict_pi_pi]
        exact Measure.le_iff'.1 Measure.restrict_le_self _
    _ = ∫⁻ y in B, (goodSetι K (Fin n ⊕ Fin m)).indicator 1 y
          ∂(Measure.pi fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ)) := by
        rw [lintegral_indicator_one hE, Measure.restrict_apply hE, inter_comm]
    _ ≤ ∫⁻ y in B, ∑ σ : Fin K → Fin 2, ((((2 : ℕ) : ℝ≥0∞)) ^ K)⁻¹ *
          (((2 : ℕ) : ℝ≥0∞) ^ Fintype.card (Fin n ⊕ Fin m) *
            (univ.pi fun i => cellSet K 2 (sig σ i)).indicator 1 y)
          ∂(Measure.pi fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ)) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ goodSetι K (Fin n ⊕ Fin m)
        · rw [Set.indicator_of_mem hy, Pi.one_apply]
          exact one_le_mixture_density2 hK hy
        · rw [Set.indicator_of_notMem hy]; exact zero_le
    _ = ∑ σ : Fin K → Fin 2, ((((2 : ℕ) : ℝ≥0∞)) ^ K)⁻¹ *
          Measure.pi (fun i : Fin n ⊕ Fin m => Qσ K 2 (sig σ i)) B := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun σ _ => ?_
          have hA : MeasurableSet (univ.pi fun i : Fin n ⊕ Fin m => cellSet K 2 (sig σ i)) :=
            MeasurableSet.univ_pi fun _ => measurableSet_cellSet _
          rw [lintegral_const_mul _ (((measurable_one).indicator hA).const_mul _),
            lintegral_const_mul _ ((measurable_one).indicator hA), lintegral_indicator_one hA,
            Measure.restrict_apply hA, inter_comm, pi_Qσ_apply_coord hK two_pos _ hB]
        · intro σ _
          exact (((measurable_one).indicator
            (MeasurableSet.univ_pi fun _ => measurableSet_cellSet _)).const_mul _).const_mul _

/-- **Collision bound**: `P_u^ι (goodSetι K ι)ᶜ ≤ |ι|²/K`. -/
theorem pi_goodSetι_compl_le {ι : Type*} [Fintype ι] (hK : 0 < K) :
    (Measure.pi fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) (goodSetι K ι)ᶜ ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Fintype.card ι / K) := by
  classical
  set P := Measure.pi fun _ : ι => volume.restrict (Icc (0 : ℝ) 1) with hPdef
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  set T : (ι × ι) × Fin K → Set (ι → ℝ) := fun p =>
    {y | p.1.1 ≠ p.1.2 ∧ y p.1.1 ∈ block K p.2 ∧ y p.1.2 ∈ block K p.2} with hT
  have hsub : (goodSetι K ι)ᶜ ⊆ (univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ ∪ ⋃ p, T p := by
    intro y hy
    by_cases h0 : ∀ i, y i ∈ Ico (0 : ℝ) 1
    · right
      have hni : ¬ Function.Injective (fun i => ⌊(K : ℝ) * y i⌋₊) := fun h => hy ⟨h0, h⟩
      simp only [Function.Injective, not_forall] at hni
      obtain ⟨i, i', hii', hne⟩ := hni
      have hb : ⌊(K : ℝ) * y i⌋₊ < K := by
        rw [Nat.floor_lt (mul_nonneg hKR.le (h0 i).1)]
        nlinarith [(h0 i).2]
      refine mem_iUnion.2 ⟨((i, i'), ⟨⌊(K : ℝ) * y i⌋₊, hb⟩), hne, ?_, ?_⟩
      · exact (mem_Ico_div_iff hKR (h0 i).1 _).2 rfl
      · exact (mem_Ico_div_iff hKR (h0 i').1 _).2 hii'.symm
    · left
      simpa [Set.mem_univ_pi] using h0
  have h1 : P (univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ = 0 := by
    rw [hPdef, P₀_eq_Ico, ← Measure.restrict_pi_pi,
      Measure.restrict_apply (MeasurableSet.univ_pi fun _ => measurableSet_Ico).compl,
      compl_inter_self, measure_empty]
  have hJ : ∀ b : Fin K, volume.restrict (Icc (0 : ℝ) 1) (block K b) ≤ ENNReal.ofReal (1 / K) :=
    fun b => (Measure.le_iff'.1 Measure.restrict_le_self _).trans_eq (volume_Ico_div _)
  have h2 : ∀ p, P (T p) ≤ ENNReal.ofReal (1 / K) * ENNReal.ofReal (1 / K) := by
    rintro ⟨⟨i, i'⟩, b⟩
    by_cases hii : i = i'
    · have : T ((i, i'), b) = ∅ := by
        ext y; simp [hT, hii]
      rw [this, measure_empty]; exact zero_le
    set s : ι → Set ℝ := fun k => if k = i ∨ k = i' then block K b else univ with hs
    have hTs : T ((i, i'), b) ⊆ univ.pi s := by
      rintro y ⟨-, hyi, hyi'⟩
      rw [Set.mem_univ_pi]
      intro k
      simp only [hs]
      split_ifs with hk
      · rcases hk with rfl | rfl
        · exact hyi
        · exact hyi'
      · exact mem_univ _
    refine (measure_mono hTs).trans ?_
    rw [hPdef, Measure.pi_pi]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hii, Finset.mem_univ i'⟩)]
    have hrest : ∏ k ∈ (Finset.univ.erase i).erase i', volume.restrict (Icc (0 : ℝ) 1) (s k)
        ≤ 1 := by
      refine Finset.prod_le_one fun k _ => ?_
      exact prob_le_one
    have hsi : s i = block K b := by simp [hs]
    have hsi' : s i' = block K b := by simp [hs]
    rw [hsi, hsi']
    calc volume.restrict (Icc (0 : ℝ) 1) (block K b) *
          (volume.restrict (Icc (0 : ℝ) 1) (block K b) *
            ∏ k ∈ (Finset.univ.erase i).erase i', volume.restrict (Icc (0 : ℝ) 1) (s k))
        ≤ ENNReal.ofReal (1 / K) * (ENNReal.ofReal (1 / K) * 1) := by
          gcongr
          · exact hJ b
          · exact hJ b
      _ = _ := by rw [mul_one]
  calc P (goodSetι K ι)ᶜ ≤ P ((univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ ∪ ⋃ p, T p) := measure_mono hsub
    _ ≤ P (univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ + P (⋃ p, T p) := measure_union_le _ _
    _ ≤ 0 + ∑ p, P (T p) := by rw [h1]; gcongr; exact measure_iUnion_fintype_le _ _
    _ ≤ 0 + ∑ _p : (ι × ι) × Fin K, ENNReal.ofReal (1 / K) * ENNReal.ofReal (1 / K) := by
        gcongr with p; exact h2 p
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * Fintype.card ι / K) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_fin]
        rw [nsmul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        field_simp

end StatFormal.Wave30tm
