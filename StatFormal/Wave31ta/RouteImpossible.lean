import StatFormal.Wave31ta.Statements
import StatFormal.Archive.TrimmedMMD.Impossible.Proofs

/-!
# Route (untrusted): `thm:impossible (v2 short)`, coverage over `𝒫₂` only

Construction: `[0,1)` is cut into `K` blocks of two half-cells (`Cells.lean` with `L = 2`). For `σ : Fin K → Fin 2`,
`P_σ = Qσ K 2 σ` is uniform on the half-cells `σ b` and `Q_σ = Qσ K 2 (rev ∘ σ)` on the complementary ones: both have
density `2` on `[0,1]` (`Density2`) and `TV(P_σ, Q_σ) = 1`. The uniform mixture over `σ` of `P_σ^{⊗n} ⊗ Q_σ^{⊗m}`
dominates `P₀^{⊗n} ⊗ P₀^{⊗m}` on the event that the `n + m` points lie in pairwise distinct blocks (exact count of the
compatible `σ`), whose complement has `P₀`-mass `≤ (n+m)²/K` (both shown on `Fin n ⊕ Fin m → ℝ` and transported by
`MeasurableEquiv.sumPiEquivProdPi`). Hence `Pr_{P₀,P₀}(Û ≥ 1) ≥ 1 − δ − (n+m)²/K`; let `K → ∞`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave31ta.RImp

open StatFormal.TrimmedMMD.Impossible

/-! ### The good event on a finite index set -/

/-- All coordinates in `[0,1)`, in pairwise distinct blocks `⌊K w_k⌋₊`. -/
def goodι (K : ℕ) (ι : Type*) : Set (ι → ℝ) :=
  {w | (∀ k, w k ∈ Ico (0 : ℝ) 1) ∧ Function.Injective (fun k => ⌊(K : ℝ) * w k⌋₊)}

theorem measurableSet_goodι (K : ℕ) (ι : Type*) [Fintype ι] : MeasurableSet (goodι K ι) := by
  have hΦ : Measurable (fun w : ι → ℝ => fun k => ⌊(K : ℝ) * w k⌋₊) :=
    measurable_pi_iff.2 fun k =>
      Nat.measurable_floor.comp ((measurable_pi_apply k).const_mul _)
  have : goodι K ι = (univ.pi fun _ => Ico (0 : ℝ) 1) ∩
      (fun w : ι → ℝ => fun k => ⌊(K : ℝ) * w k⌋₊) ⁻¹' {f | Function.Injective f} := by
    ext w; simp [goodι]
  rw [this]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).inter
    (hΦ (Set.to_countable _).measurableSet)

/-- **Collision bound** on a finite index set: `P₀^ι (goodι K ι)ᶜ ≤ |ι|²/K`. -/
theorem pi_goodι_compl_le {ι : Type*} [Fintype ι] {K : ℕ} (hK : 0 < K) :
    (Measure.pi fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) (goodι K ι)ᶜ ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Fintype.card ι / K) := by
  classical
  set P := Measure.pi fun _ : ι => volume.restrict (Icc (0 : ℝ) 1) with hPdef
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  set T : (ι × ι) × Fin K → Set (ι → ℝ) := fun p =>
    {y | p.1.1 ≠ p.1.2 ∧ y p.1.1 ∈ block K p.2 ∧ y p.1.2 ∈ block K p.2} with hT
  have hsub : (goodι K ι)ᶜ ⊆ (univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ ∪ ⋃ p, T p := by
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
  calc P (goodι K ι)ᶜ ≤ P ((univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ ∪ ⋃ p, T p) := measure_mono hsub
    _ ≤ P (univ.pi fun _ => Ico (0 : ℝ) 1)ᶜ + P (⋃ p, T p) := measure_union_le _ _
    _ ≤ 0 + ∑ p, P (T p) := by rw [h1]; gcongr; exact measure_iUnion_fintype_le _ _
    _ ≤ 0 + ∑ _p : (ι × ι) × Fin K, ENNReal.ofReal (1 / K) * ENNReal.ofReal (1 / K) := by
        gcongr with p; exact h2 p
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * Fintype.card ι / K) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod]
        simp only [Fintype.card_fin]
        rw [nsmul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        field_simp

/-! ### Products of cell laws -/

/-- `∏_k Qσ K L (c k)` applied to `B` is `L^{|ι|} λ^ι(B ∩ ∏_k cellSet (c k))`. -/
theorem pi_cells_apply {ι : Type*} [Fintype ι] {K L : ℕ} (hK : 0 < K) (hL : 0 < L)
    (c : ι → Fin K → Fin L) {B : Set (ι → ℝ)} (hB : MeasurableSet B) :
    Measure.pi (fun k => Qσ K L (c k)) B =
      (L : ℝ≥0∞) ^ Fintype.card ι * Measure.pi (fun _ : ι => (volume : Measure ℝ))
        (B ∩ univ.pi fun k => cellSet K L (c k)) := by
  have : ∀ k, IsProbabilityMeasure (Qσ K L (c k)) := fun k => isProbabilityMeasure_Qσ hK hL (c k)
  have h : Measure.pi (fun k => Qσ K L (c k)) = (L : ℝ≥0∞) ^ Fintype.card ι •
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).restrict (univ.pi fun k => cellSet K L (c k)) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
      ← Set.pi_inter_distrib, Measure.pi_pi, smul_eq_mul]
    simp only [Qσ, Measure.smul_apply, Measure.restrict_apply (hs _), smul_eq_mul,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [h, Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]

/-- Counting extensions over any finite index type. -/
theorem card_extensions_fintype {ι : Type*} [Fintype ι] {K L : ℕ} (β : ι → Fin K)
    (hβ : Function.Injective β) (lam : ι → Fin L) :
    (Finset.univ.filter (fun σ : Fin K → Fin L => ∀ i, σ (β i) = lam i)).card =
      L ^ (K - Fintype.card ι) := by
  classical
  set e := Fintype.equivFin ι
  have hβ' : Function.Injective (β ∘ e.symm) := hβ.comp e.symm.injective
  have h := card_extensions (β ∘ e.symm) hβ' (lam ∘ e.symm)
  rw [← h]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
  exact ⟨fun H i => H _, fun H k => by simpa using H (e k)⟩

/-- The cell choices: `σ` on the first sample, `rev ∘ σ` (the complementary half-cells) on the second. -/
def cfam {n m K : ℕ} (σ : Fin K → Fin 2) : Fin n ⊕ Fin m → Fin K → Fin 2 :=
  fun k => Sum.elim (fun _ => σ) (fun _ => Fin.rev ∘ σ) k

/-- Pointwise: on `goodι`, the mixture density is `1`. -/
theorem one_le_mixture2 {n m K : ℕ} (hK : 0 < K) {w : Fin n ⊕ Fin m → ℝ}
    (hw : w ∈ goodι K (Fin n ⊕ Fin m)) :
    1 ≤ ∑ σ : Fin K → Fin 2, ((2 : ℝ≥0∞) ^ K)⁻¹ *
      ((2 : ℝ≥0∞) ^ (n + m) *
        (univ.pi fun k => cellSet K 2 (cfam (n := n) (m := m) σ k)).indicator 1 w) := by
  classical
  have h2 : (0 : ℕ) < 2 := two_pos
  set β : Fin n ⊕ Fin m → Fin K := fun k => ⟨⌊((K : ℝ) * (2 : ℕ)) * w k⌋₊ / 2, floor_div_lt hK h2 (hw.1 k)⟩
  set lam : Fin n ⊕ Fin m → Fin 2 := fun k => ⟨⌊((K : ℝ) * (2 : ℕ)) * w k⌋₊ % 2, Nat.mod_lt _ h2⟩
  set lam' : Fin n ⊕ Fin m → Fin 2 := fun k => Sum.elim (fun _ => lam k) (fun _ => Fin.rev (lam k)) k
  have hβ : Function.Injective β := by
    intro i i' h
    have h' := congrArg Fin.val h
    simp only [β, floor_mul_div h2] at h'
    exact hw.2 h'
  have hmK : n + m ≤ K := by
    simpa using Fintype.card_le_of_injective β hβ
  have hind : ∀ σ : Fin K → Fin 2, (univ.pi fun k => cellSet K 2 (cfam (n := n) (m := m) σ k)).indicator
      (1 : (Fin n ⊕ Fin m → ℝ) → ℝ≥0∞) w = if (∀ k, σ (β k) = lam' k) then 1 else 0 := by
    intro σ
    simp only [Set.indicator_apply, Set.mem_univ_pi, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    refine forall_congr' fun k => ?_
    rw [mem_cellSet_iff' hK h2 (cfam σ k) (hw.1 k)]
    rcases k with i | j
    · rfl
    · change Fin.rev (σ (β (Sum.inr j))) = lam (Sum.inr j) ↔ σ (β (Sum.inr j)) = Fin.rev (lam (Sum.inr j))
      constructor
      · intro h; rw [← h, Fin.rev_rev]
      · intro h; rw [h, Fin.rev_rev]
  simp only [hind, ← Finset.mul_sum, Finset.sum_boole, card_extensions_fintype β hβ lam']
  refine le_of_eq ?_
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    ← pow_add, Nat.add_sub_cancel' hmK,
    ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

/-- **Domination** on `Fin n ⊕ Fin m → ℝ`. -/
theorem restrict_good_le_mixture2 {n m K : ℕ} (hK : 0 < K) :
    (Measure.pi fun _ : Fin n ⊕ Fin m => volume.restrict (Icc (0 : ℝ) 1)).restrict (goodι K (Fin n ⊕ Fin m)) ≤
      ∑ σ : Fin K → Fin 2, ((2 : ℝ≥0∞) ^ K)⁻¹ •
        Measure.pi (fun k => Qσ K 2 (cfam (n := n) (m := m) σ k)) := by
  rw [Measure.le_iff]
  intro B hB
  rw [Measure.restrict_apply hB, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hE := measurableSet_goodι K (Fin n ⊕ Fin m)
  calc (Measure.pi fun _ : Fin n ⊕ Fin m => volume.restrict (Icc (0 : ℝ) 1)) (B ∩ goodι K (Fin n ⊕ Fin m))
      ≤ Measure.pi (fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ)) (B ∩ goodι K (Fin n ⊕ Fin m)) := by
        rw [← Measure.restrict_pi_pi]
        exact Measure.le_iff'.1 Measure.restrict_le_self _
    _ = ∫⁻ y in B, (goodι K (Fin n ⊕ Fin m)).indicator 1 y
          ∂(Measure.pi fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ)) := by
        rw [lintegral_indicator_one hE, Measure.restrict_apply hE, inter_comm]
    _ ≤ ∫⁻ y in B, ∑ σ : Fin K → Fin 2, ((2 : ℝ≥0∞) ^ K)⁻¹ *
          ((2 : ℝ≥0∞) ^ (n + m) *
            (univ.pi fun k => cellSet K 2 (cfam (n := n) (m := m) σ k)).indicator 1 y)
          ∂(Measure.pi fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ)) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ goodι K (Fin n ⊕ Fin m)
        · rw [Set.indicator_of_mem hy, Pi.one_apply]
          exact one_le_mixture2 hK hy
        · rw [Set.indicator_of_notMem hy]; exact zero_le
    _ = ∑ σ : Fin K → Fin 2, ((2 : ℝ≥0∞) ^ K)⁻¹ *
          Measure.pi (fun k => Qσ K 2 (cfam (n := n) (m := m) σ k)) B := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun σ _ => ?_
          have hA : MeasurableSet (univ.pi fun k => cellSet K 2 (cfam (n := n) (m := m) σ k)) :=
            MeasurableSet.univ_pi fun _ => measurableSet_cellSet _
          rw [lintegral_const_mul _ (((measurable_one).indicator hA).const_mul _),
            lintegral_const_mul _ ((measurable_one).indicator hA), lintegral_indicator_one hA,
            Measure.restrict_apply hA, inter_comm, pi_cells_apply hK two_pos _ hB,
            Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
          norm_num
        · intro σ _
          exact (((measurable_one).indicator
            (MeasurableSet.univ_pi fun _ => measurableSet_cellSet _)).const_mul _).const_mul _

/-! ### The two cell laws are in `𝒫₂`, at total variation one -/

theorem density2_Qσ {K : ℕ} (hK : 0 < K) (σ : Fin K → Fin 2) : Density2 (Qσ K 2 σ) := by
  refine ⟨isProbabilityMeasure_Qσ hK two_pos σ, ?_⟩
  rw [Measure.le_iff]
  intro s hs
  rw [Qσ, Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hs,
    Measure.restrict_apply hs, smul_eq_mul, smul_eq_mul]
  have : ((2 : ℕ) : ℝ≥0∞) = 2 := by norm_num
  rw [this]
  gcongr
  exact (cellSet_subset σ).trans Ico_subset_Icc_self

theorem cellSet_disjoint_rev {K : ℕ} (hK : 0 < K) (σ : Fin K → Fin 2) :
    Disjoint (cellSet K 2 σ) (cellSet K 2 (Fin.rev ∘ σ)) := by
  rw [Set.disjoint_left]
  intro y h1 h2
  have hy := cellSet_subset σ h1
  rw [mem_cellSet_iff' hK two_pos σ hy] at h1
  rw [mem_cellSet_iff' hK two_pos _ hy, Function.comp_apply, h1] at h2
  revert h2
  generalize (⟨⌊((K : ℝ) * (2 : ℕ)) * y⌋₊ % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = a
  fin_cases a <;> decide

theorem one_le_tvDist_rev {K : ℕ} (hK : 0 < K) (σ : Fin K → Fin 2) :
    1 ≤ StatFormal.Distances.tvDist (Qσ K 2 σ) (Qσ K 2 (Fin.rev ∘ σ)) := by
  have := isProbabilityMeasure_Qσ hK two_pos σ
  have := isProbabilityMeasure_Qσ hK two_pos (Fin.rev ∘ σ)
  have h := StatFormal.Distances.abs_measureReal_sub_le_tvDist
    (μ := Qσ K 2 σ) (ν := Qσ K 2 (Fin.rev ∘ σ)) (measurableSet_cellSet σ)
  have h1 : (Qσ K 2 σ).real (cellSet K 2 σ) = 1 := by
    rw [measureReal_def, Qσ_apply_cellSet hK two_pos, ENNReal.toReal_one]
  have h0 : (Qσ K 2 (Fin.rev ∘ σ)).real (cellSet K 2 σ) = 0 := by
    rw [measureReal_def, Qσ, Measure.smul_apply, Measure.restrict_apply (measurableSet_cellSet σ),
      (cellSet_disjoint_rev hK σ).inter_eq, measure_empty, smul_zero, ENNReal.toReal_zero]
  rw [h1, h0, sub_zero, abs_one] at h
  exact h

/-! ### The key bound -/

theorem key_bound2 {n m : ℕ} {δ : ℝ} {Ξ : Type} [MeasurableSpace Ξ] {R : Measure Ξ}
    [IsProbabilityMeasure R] {U : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ} (hδ : 0 ≤ δ)
    (hU : Measurable U)
    (H : ∀ P Q : Measure ℝ, Density2 P → Density2 Q →
      1 - δ ≤ (dataLaw n m P Q R).real {z | StatFormal.Distances.tvDist P Q ≤ U z})
    {K : ℕ} (hK : 0 < K) :
    1 - δ - ((n + m : ℕ) : ℝ) * (n + m : ℕ) / K ≤ (dataLaw n m (volume.restrict (Icc (0 : ℝ) 1))
      (volume.restrict (Icc (0 : ℝ) 1)) R).real {z | 1 ≤ U z} := by
  set P₀ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hP₀
  set A := {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | 1 ≤ U z} with hAdef
  have hA : MeasurableSet A := measurableSet_le measurable_const hU
  set w : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ K)⁻¹ with hw
  -- each pair `(P_σ, Q_σ)` is covered, so `Pr(Aᶜ) ≤ δ`
  have hσ : ∀ σ : Fin K → Fin 2,
      dataLaw n m (Qσ K 2 σ) (Qσ K 2 (Fin.rev ∘ σ)) R Aᶜ ≤ ENNReal.ofReal δ := by
    intro σ
    have := isProbabilityMeasure_Qσ hK two_pos σ
    have := isProbabilityMeasure_Qσ hK two_pos (Fin.rev ∘ σ)
    have := isProbabilityMeasure_dataLaw n m (Qσ K 2 σ) (Qσ K 2 (Fin.rev ∘ σ)) R
    have h := H _ _ (density2_Qσ hK σ) (density2_Qσ hK (Fin.rev ∘ σ))
    have hsub : {z | StatFormal.Distances.tvDist (Qσ K 2 σ) (Qσ K 2 (Fin.rev ∘ σ)) ≤ U z} ⊆ A :=
      fun z hz => (one_le_tvDist_rev hK σ).trans hz
    have h' := h.trans (measureReal_mono hsub)
    have hc := measureReal_add_measureReal_compl
      (μ := dataLaw n m (Qσ K 2 σ) (Qσ K 2 (Fin.rev ∘ σ)) R) hA
    rw [probReal_univ] at hc
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- disintegrate along the pair of samples
  set F : (Fin n → ℝ) × (Fin m → ℝ) → ℝ≥0∞ := fun z => R (Prod.mk z ⁻¹' Aᶜ) with hF
  have hFm : Measurable F := measurable_measure_prodMk_left hA.compl
  have hD : ∀ P Q : Measure ℝ, IsProbabilityMeasure P → IsProbabilityMeasure Q →
      dataLaw n m P Q R Aᶜ = ∫⁻ z, F z ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
    intro P Q _ _
    exact Measure.prod_apply hA.compl
  have hF1 : ∀ z, F z ≤ 1 := fun z => prob_le_one
  -- the transport `Fin n ⊕ Fin m → ℝ ≃ᵐ (Fin n → ℝ) × (Fin m → ℝ)`
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ) with he
  have mp0 : MeasurePreserving e (Measure.pi fun _ : Fin n ⊕ Fin m => P₀)
      ((Measure.pi fun _ : Fin n => P₀).prod (Measure.pi fun _ : Fin m => P₀)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => P₀)
  have mpσ : ∀ σ : Fin K → Fin 2, MeasurePreserving e
      (Measure.pi fun k => Qσ K 2 (cfam (n := n) (m := m) σ k))
      ((Measure.pi fun _ : Fin n => Qσ K 2 σ).prod (Measure.pi fun _ : Fin m => Qσ K 2 (Fin.rev ∘ σ))) := by
    intro σ
    have : ∀ k, IsProbabilityMeasure (Qσ K 2 (cfam (n := n) (m := m) σ k)) :=
      fun k => isProbabilityMeasure_Qσ hK two_pos _
    exact measurePreserving_sumPiEquivProdPi (fun k => Qσ K 2 (cfam (n := n) (m := m) σ k))
  set G : Set ((Fin n → ℝ) × (Fin m → ℝ)) := e.symm ⁻¹' goodι K (Fin n ⊕ Fin m) with hG
  have hGm : MeasurableSet G := e.symm.measurable (measurableSet_goodι K _)
  have hpre : ∀ S : Set ((Fin n → ℝ) × (Fin m → ℝ)), e ⁻¹' (S ∩ G) = e ⁻¹' S ∩ goodι K (Fin n ⊕ Fin m) := by
    intro S; ext v; simp [hG]
  set ν₀ := (Measure.pi fun _ : Fin n => P₀).prod (Measure.pi fun _ : Fin m => P₀) with hν₀
  set μσ : (Fin K → Fin 2) → Measure ((Fin n → ℝ) × (Fin m → ℝ)) := fun σ =>
    (Measure.pi fun _ : Fin n => Qσ K 2 σ).prod (Measure.pi fun _ : Fin m => Qσ K 2 (Fin.rev ∘ σ)) with hμσ
  -- domination on the product space
  have hdom : ν₀.restrict G ≤ ∑ σ : Fin K → Fin 2, w • μσ σ := by
    rw [Measure.le_iff]
    intro B hB
    rw [Measure.restrict_apply hB, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [← mp0.measure_preimage (hB.inter hGm).nullMeasurableSet, hpre,
      ← Measure.restrict_apply (e.measurable hB)]
    refine (Measure.le_iff'.1 (restrict_good_le_mixture2 (n := n) (m := m) hK) _).trans_eq ?_
    rw [Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, (mpσ σ).measure_preimage hB.nullMeasurableSet]
  have hGc : ν₀ Gᶜ ≤ ENNReal.ofReal (((n + m : ℕ) : ℝ) * (n + m : ℕ) / K) := by
    rw [← mp0.measure_preimage hGm.compl.nullMeasurableSet]
    have : e ⁻¹' Gᶜ = (goodι K (Fin n ⊕ Fin m))ᶜ := by ext v; simp [hG]
    rw [this]
    have h := pi_goodι_compl_le (ι := Fin n ⊕ Fin m) hK
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
    exact h
  have hmain : dataLaw n m P₀ P₀ R Aᶜ ≤
      ENNReal.ofReal δ + ENNReal.ofReal (((n + m : ℕ) : ℝ) * (n + m : ℕ) / K) := by
    rw [hD P₀ P₀ inferInstance inferInstance, ← lintegral_add_compl F hGm]
    gcongr
    · calc ∫⁻ z in G, F z ∂ν₀
          ≤ ∫⁻ z, F z ∂(∑ σ : Fin K → Fin 2, w • μσ σ) := lintegral_mono' hdom le_rfl
        _ = ∑ σ : Fin K → Fin 2, w * dataLaw n m (Qσ K 2 σ) (Qσ K 2 (Fin.rev ∘ σ)) R Aᶜ := by
            rw [lintegral_finsetSum_measure]
            refine Finset.sum_congr rfl fun σ _ => ?_
            have := isProbabilityMeasure_Qσ hK two_pos σ
            have := isProbabilityMeasure_Qσ hK two_pos (Fin.rev ∘ σ)
            rw [lintegral_smul_measure, smul_eq_mul, hD _ _ inferInstance inferInstance]
        _ ≤ ∑ _σ : Fin K → Fin 2, w * ENNReal.ofReal δ := by
            gcongr with σ; exact hσ σ
        _ = ENNReal.ofReal δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hw, Nat.cast_pow,
              Nat.cast_ofNat,
              ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
                (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]
    · calc ∫⁻ z in Gᶜ, F z ∂ν₀ ≤ ∫⁻ _z in Gᶜ, (1 : ℝ≥0∞) ∂ν₀ := lintegral_mono fun z => hF1 z
        _ = ν₀ Gᶜ := by rw [lintegral_one, Measure.restrict_apply_univ]
        _ ≤ _ := hGc
  have := isProbabilityMeasure_dataLaw n m P₀ P₀ R
  rw [← ENNReal.ofReal_add hδ (by positivity)] at hmain
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hmain
  have hc := measureReal_add_measureReal_compl (μ := dataLaw n m P₀ P₀ R) hA
  rw [probReal_univ] at hc
  simp only [measureReal_def] at hc ⊢
  linarith

end StatFormal.Wave31ta.RImp

namespace StatFormal.Wave31ta

open StatFormal.TrimmedMMD.Impossible

theorem impossible_two : Claims.impossible_two := by
  intro n m δ Ξ _ R _ U _ _ hδ _ hU H
  have ht : Tendsto (fun K : ℕ => 1 - δ - ((n + m : ℕ) : ℝ) * (n + m : ℕ) / K) atTop (𝓝 (1 - δ - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at ht
  refine le_of_tendsto ht (eventually_atTop.2 ⟨1, fun K hK => ?_⟩)
  exact RImp.key_bound2 hδ.le hU H (by omega)

end StatFormal.Wave31ta
