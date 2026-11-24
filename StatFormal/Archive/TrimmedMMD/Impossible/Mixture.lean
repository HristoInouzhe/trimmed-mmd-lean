import StatFormal.Archive.TrimmedMMD.Impossible.Cells
import StatFormal.Archive.TrimmedMMD.Impossible.Counting

/-!
# Impossibility theorem — the mixture dominates `P₀^m` off collisions

Untrusted proof library for `Claims.impossible`.

With `w = L^{-K}`, the mixture `∑_σ w • (Qσ K L σ)^m` dominates `P₀^m` restricted to the event
`goodSet K m` (all points in `[0,1)`, in pairwise distinct blocks `⌊K y⌋₊`), and
`P₀^m (goodSet K m)ᶜ ≤ m²/K`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatFormal.TrimmedMMD.Impossible

variable {K L m : ℕ}

/-- No two of the `m` points fall into the same block `[b/K, (b+1)/K)`. -/
def goodSet (K m : ℕ) : Set (Fin m → ℝ) :=
  {y | (∀ i, y i ∈ Ico (0 : ℝ) 1) ∧ Function.Injective (fun i => ⌊(K : ℝ) * y i⌋₊)}

theorem measurableSet_goodSet (K m : ℕ) : MeasurableSet (goodSet K m) := by
  have hΦ : Measurable (fun y : Fin m → ℝ => fun i => ⌊(K : ℝ) * y i⌋₊) :=
    measurable_pi_iff.2 fun i =>
      Nat.measurable_floor.comp ((measurable_pi_apply i).const_mul _)
  have : goodSet K m = (univ.pi fun _ => Ico (0 : ℝ) 1) ∩
      (fun y : Fin m → ℝ => fun i => ⌊(K : ℝ) * y i⌋₊) ⁻¹' {f | Function.Injective f} := by
    ext y; simp [goodSet]
  rw [this]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).inter
    (hΦ (Set.to_countable _).measurableSet)

theorem P₀_eq_Ico : volume.restrict (Icc (0 : ℝ) 1) = volume.restrict (Ico (0 : ℝ) 1) :=
  (Measure.restrict_congr_set Ico_ae_eq_Icc).symm

/-- `(Qσ)^m (B) = L^m · λ^m (B ∩ (cellSet)^m)`. -/
theorem pi_Qσ_apply (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) {B : Set (Fin m → ℝ)}
    (hB : MeasurableSet B) :
    Measure.pi (fun _ : Fin m => Qσ K L σ) B =
      (L : ℝ≥0∞) ^ m * Measure.pi (fun _ : Fin m => (volume : Measure ℝ))
        (B ∩ univ.pi fun _ => cellSet K L σ) := by
  have := isProbabilityMeasure_Qσ hK hL σ
  have h : Measure.pi (fun _ : Fin m => Qσ K L σ) = (L : ℝ≥0∞) ^ m •
      (Measure.pi fun _ : Fin m => (volume : Measure ℝ)).restrict
        (univ.pi fun _ => cellSet K L σ) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
      ← Set.pi_inter_distrib, Measure.pi_pi, smul_eq_mul]
    simp only [Qσ, Measure.smul_apply, Measure.restrict_apply (hs _), smul_eq_mul,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h, Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]

theorem floor_mul_div (hL : 0 < L) (y : ℝ) :
    ⌊((K : ℝ) * L) * y⌋₊ / L = ⌊(K : ℝ) * y⌋₊ := by
  rw [← Nat.floor_div_natCast]
  congr 1
  have : (L : ℝ) ≠ 0 := by positivity
  field_simp

/-- Pointwise: on `goodSet`, the mixture density equals `1`. -/
theorem one_le_mixture_density (hK : 0 < K) (hL : 0 < L) {y : Fin m → ℝ} (hy : y ∈ goodSet K m) :
    1 ≤ ∑ σ : Fin K → Fin L, ((L : ℝ≥0∞) ^ K)⁻¹ *
      ((L : ℝ≥0∞) ^ m * (univ.pi fun _ => cellSet K L σ).indicator 1 y) := by
  classical
  set β : Fin m → Fin K := fun i => ⟨⌊((K : ℝ) * L) * y i⌋₊ / L, floor_div_lt hK hL (hy.1 i)⟩
  set lam : Fin m → Fin L := fun i => ⟨⌊((K : ℝ) * L) * y i⌋₊ % L, Nat.mod_lt _ hL⟩
  have hβ : Function.Injective β := by
    intro i i' h
    have h' := congrArg Fin.val h
    simp only [β, floor_mul_div hL] at h'
    exact hy.2 h'
  have hmK : m ≤ K := by
    simpa using Fintype.card_le_of_injective β hβ
  have hind : ∀ σ : Fin K → Fin L, (univ.pi fun _ => cellSet K L σ).indicator
      (1 : (Fin m → ℝ) → ℝ≥0∞) y = if (∀ i, σ (β i) = lam i) then 1 else 0 := by
    intro σ
    simp only [Set.indicator_apply, Set.mem_univ_pi, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    exact forall_congr' fun i => mem_cellSet_iff' hK hL σ (hy.1 i)
  simp only [hind, ← Finset.mul_sum, Finset.sum_boole, card_extensions β hβ lam]
  refine le_of_eq ?_
  rw [Nat.cast_pow, ← pow_add, Nat.add_sub_cancel' hmK,
    ENNReal.inv_mul_cancel (pow_ne_zero _ (by exact_mod_cast hL.ne'))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top L))]

/-- **Domination**: `P₀^m |_{goodSet} ≤ ∑_σ L^{-K} • (Qσ)^m`. -/
theorem restrict_goodSet_le_mixture (hK : 0 < K) (hL : 0 < L) :
    (Measure.pi fun _ : Fin m => volume.restrict (Icc (0 : ℝ) 1)).restrict (goodSet K m) ≤
      ∑ σ : Fin K → Fin L, ((L : ℝ≥0∞) ^ K)⁻¹ • Measure.pi (fun _ : Fin m => Qσ K L σ) := by
  rw [Measure.le_iff]
  intro B hB
  rw [Measure.restrict_apply hB, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hE := measurableSet_goodSet K m
  calc (Measure.pi fun _ : Fin m => volume.restrict (Icc (0 : ℝ) 1)) (B ∩ goodSet K m)
      ≤ Measure.pi (fun _ : Fin m => (volume : Measure ℝ)) (B ∩ goodSet K m) := by
        rw [← Measure.restrict_pi_pi]
        exact Measure.le_iff'.1 Measure.restrict_le_self _
    _ = ∫⁻ y in B, (goodSet K m).indicator 1 y
          ∂(Measure.pi fun _ : Fin m => (volume : Measure ℝ)) := by
        rw [lintegral_indicator_one hE, Measure.restrict_apply hE, inter_comm]
    _ ≤ ∫⁻ y in B, ∑ σ : Fin K → Fin L, ((L : ℝ≥0∞) ^ K)⁻¹ *
          ((L : ℝ≥0∞) ^ m * (univ.pi fun _ => cellSet K L σ).indicator 1 y)
          ∂(Measure.pi fun _ : Fin m => (volume : Measure ℝ)) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ goodSet K m
        · rw [Set.indicator_of_mem hy, Pi.one_apply]
          exact one_le_mixture_density hK hL hy
        · rw [Set.indicator_of_notMem hy]; exact zero_le
    _ = ∑ σ : Fin K → Fin L, ((L : ℝ≥0∞) ^ K)⁻¹ * Measure.pi (fun _ : Fin m => Qσ K L σ) B := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun σ _ => ?_
          have hA : MeasurableSet (univ.pi fun _ : Fin m => cellSet K L σ) :=
            MeasurableSet.univ_pi fun _ => measurableSet_cellSet σ
          rw [lintegral_const_mul _ (((measurable_one).indicator hA).const_mul _),
            lintegral_const_mul _ ((measurable_one).indicator hA), lintegral_indicator_one hA,
            Measure.restrict_apply hA, inter_comm, pi_Qσ_apply hK hL σ hB]
        · intro σ _
          exact (((measurable_one).indicator
            (MeasurableSet.univ_pi fun _ => measurableSet_cellSet σ)).const_mul _).const_mul _

/-- The `j`-th block. -/
def block (K : ℕ) (b : Fin K) : Set ℝ := Ico (((b : ℕ) : ℝ) / K) ((((b : ℕ) : ℝ) + 1) / K)

/-- **Collision bound**: `P₀^m (goodSet K m)ᶜ ≤ m²/K`. -/
theorem pi_goodSet_compl_le (hK : 0 < K) :
    (Measure.pi fun _ : Fin m => volume.restrict (Icc (0 : ℝ) 1)) (goodSet K m)ᶜ ≤
      ENNReal.ofReal ((m : ℝ) * m / K) := by
  classical
  set P := Measure.pi fun _ : Fin m => volume.restrict (Icc (0 : ℝ) 1) with hPdef
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  set T : (Fin m × Fin m) × Fin K → Set (Fin m → ℝ) := fun p =>
    {y | p.1.1 ≠ p.1.2 ∧ y p.1.1 ∈ block K p.2 ∧ y p.1.2 ∈ block K p.2} with hT
  have hsub : (goodSet K m)ᶜ ⊆ (univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ ∪ ⋃ p, T p := by
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
    set s : Fin m → Set ℝ := fun k => if k = i ∨ k = i' then block K b else univ with hs
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
  calc P (goodSet K m)ᶜ ≤ P ((univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ ∪ ⋃ p, T p) := measure_mono hsub
    _ ≤ P (univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ + P (⋃ p, T p) := measure_union_le _ _
    _ ≤ 0 + ∑ p, P (T p) := by rw [h1]; gcongr; exact measure_iUnion_fintype_le _ _
    _ ≤ 0 + ∑ _p : (Fin m × Fin m) × Fin K, ENNReal.ofReal (1 / K) * ENNReal.ofReal (1 / K) := by
        gcongr with p; exact h2 p
    _ = ENNReal.ofReal ((m : ℝ) * m / K) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod]
        simp only [Fintype.card_fin]
        rw [nsmul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        field_simp

end StatFormal.TrimmedMMD.Impossible
