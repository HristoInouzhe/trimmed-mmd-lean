import StatFormal.Archive.TrimmedMMD.Impossible.Statements
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Impossibility theorem — the cell construction

Untrusted proof library for `Claims.impossible`.

`[0,1)` is cut into `K` blocks of `L` cells each (cell `n = b * L + l` is
`[n/(KL), (n+1)/(KL))`). For `σ : Fin K → Fin L`, `cellSet K L σ` is the union of the cells
`b * L + σ b` (one cell per block), and `Qσ K L σ` is the uniform law on it (density `L`).
Then `Qσ` has a bounded density on `[0,1]` and `TV(P₀, Qσ) ≥ 1 - 1/L`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatFormal.TrimmedMMD.Impossible

/-- `y ∈ [n/a, (n+1)/a)` iff `⌊a y⌋₊ = n`, for `y ≥ 0`. -/
theorem mem_Ico_div_iff {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (n : ℕ) :
    y ∈ Ico ((n : ℝ) / a) ((n + 1) / a) ↔ ⌊a * y⌋₊ = n := by
  rw [Nat.floor_eq_iff (mul_nonneg ha.le hy), mem_Ico, div_le_iff₀ ha, lt_div_iff₀ ha]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith [mul_comm a y]

theorem volume_Ico_div {a : ℝ} (n : ℕ) :
    volume (Ico ((n : ℝ) / a) ((n + 1) / a)) = ENNReal.ofReal (1 / a) := by
  rw [Real.volume_Ico]; congr 1; ring

/-- The index of the chosen cell in block `b`. -/
def cellOf (L : ℕ) {K : ℕ} (σ : Fin K → Fin L) (b : Fin K) : ℕ := (b : ℕ) * L + σ b

/-- The union of the chosen cells. -/
def cellSet (K L : ℕ) (σ : Fin K → Fin L) : Set ℝ :=
  ⋃ b : Fin K, Ico ((cellOf L σ b : ℝ) / ((K : ℝ) * L)) (((cellOf L σ b : ℝ) + 1) / ((K : ℝ) * L))

/-- The uniform law on `cellSet K L σ`. -/
def Qσ (K L : ℕ) (σ : Fin K → Fin L) : Measure ℝ :=
  (L : ℝ≥0∞) • volume.restrict (cellSet K L σ)

variable {K L : ℕ}

theorem cellOf_div (hL : 0 < L) (σ : Fin K → Fin L) (b : Fin K) : cellOf L σ b / L = b := by
  unfold cellOf
  rw [add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt (σ b).isLt, zero_add]

theorem cellOf_mod (σ : Fin K → Fin L) (b : Fin K) : cellOf L σ b % L = σ b := by
  unfold cellOf
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (σ b).isLt]

theorem cellOf_injective (hL : 0 < L) (σ : Fin K → Fin L) : Function.Injective (cellOf L σ) := by
  intro b b' h
  have := congrArg (· / L) h
  simp only [cellOf_div hL] at this
  exact Fin.ext this

theorem cellOf_succ_le (σ : Fin K → Fin L) (b : Fin K) : cellOf L σ b + 1 ≤ K * L := by
  unfold cellOf
  have h1 := b.isLt
  have h2 := (σ b).isLt
  nlinarith

theorem mem_cellSet_iff (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) {y : ℝ} (hy : 0 ≤ y) :
    y ∈ cellSet K L σ ↔ ∃ b : Fin K, ⌊((K : ℝ) * L) * y⌋₊ = cellOf L σ b := by
  have ha : (0 : ℝ) < (K : ℝ) * L := by positivity
  simp only [cellSet, mem_iUnion, mem_Ico_div_iff ha hy]

theorem floor_lt_of_lt_one (hK : 0 < K) (hL : 0 < L) {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    ⌊((K : ℝ) * L) * y⌋₊ < K * L := by
  have ha : (0 : ℝ) < (K : ℝ) * L := by positivity
  rw [Nat.floor_lt (mul_nonneg ha.le hy.1)]
  push_cast
  nlinarith [hy.2]

theorem floor_div_lt (hK : 0 < K) (hL : 0 < L) {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    ⌊((K : ℝ) * L) * y⌋₊ / L < K :=
  (Nat.div_lt_iff_lt_mul hL).2 (floor_lt_of_lt_one hK hL hy)

theorem mem_cellSet_iff' (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) {y : ℝ}
    (hy : y ∈ Ico (0 : ℝ) 1) :
    y ∈ cellSet K L σ ↔ σ ⟨⌊((K : ℝ) * L) * y⌋₊ / L, floor_div_lt hK hL hy⟩ =
      ⟨⌊((K : ℝ) * L) * y⌋₊ % L, Nat.mod_lt _ hL⟩ := by
  rw [mem_cellSet_iff hK hL σ hy.1]
  set n := ⌊((K : ℝ) * L) * y⌋₊ with hn
  constructor
  · rintro ⟨b, hb⟩
    rw [← hn] at hb
    have hb' : (⟨n / L, floor_div_lt hK hL hy⟩ : Fin K) = b := by
      apply Fin.ext; simp only [hb, cellOf_div hL]
    rw [hb']
    apply Fin.ext
    change (σ b : ℕ) = n % L
    rw [hb, cellOf_mod]
  · intro h
    refine ⟨⟨n / L, floor_div_lt hK hL hy⟩, ?_⟩
    have h' := congrArg Fin.val h
    simp only at h'
    unfold cellOf
    rw [h']
    exact (Nat.div_add_mod' n L).symm

theorem measurableSet_cellSet (σ : Fin K → Fin L) : MeasurableSet (cellSet K L σ) :=
  MeasurableSet.iUnion fun _ => measurableSet_Ico

theorem cellSet_subset (σ : Fin K → Fin L) : cellSet K L σ ⊆ Ico (0 : ℝ) 1 := by
  intro y hy
  simp only [cellSet, mem_iUnion, mem_Ico] at hy
  obtain ⟨b, h1, h2⟩ := hy
  rcases Nat.eq_zero_or_pos K with hK | hK
  · exact absurd b.isLt (by omega)
  rcases Nat.eq_zero_or_pos L with hL | hL
  · exact absurd (σ b).isLt (by omega)
  have ha : (0 : ℝ) < (K : ℝ) * L := by positivity
  have hle : ((cellOf L σ b : ℝ) + 1) ≤ (K : ℝ) * L := by exact_mod_cast cellOf_succ_le σ b
  refine ⟨le_trans (by positivity) h1, lt_of_lt_of_le h2 ?_⟩
  rw [div_le_one ha]; exact hle

theorem volume_cellSet (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) :
    volume (cellSet K L σ) = ENNReal.ofReal (1 / L) := by
  have ha : (0 : ℝ) < (K : ℝ) * L := by positivity
  unfold cellSet
  rw [measure_iUnion]
  · simp only [volume_Ico_div, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  · intro b b' hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro y h1 h2
    have hy : 0 ≤ y := le_trans (by positivity) h1.1
    rw [mem_Ico_div_iff ha hy] at h1 h2
    exact hne (cellOf_injective hL σ (h1.symm.trans h2))
  · exact fun _ => measurableSet_Ico

theorem nat_mul_ofReal_inv (hL : 0 < L) : (L : ℝ≥0∞) * ENNReal.ofReal (1 / L) = 1 := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [mul_one_div_cancel (by positivity), ENNReal.ofReal_one]

theorem Qσ_apply_cellSet (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) :
    Qσ K L σ (cellSet K L σ) = 1 := by
  rw [Qσ, Measure.smul_apply, Measure.restrict_apply (measurableSet_cellSet σ), inter_self,
    volume_cellSet hK hL, smul_eq_mul, nat_mul_ofReal_inv hL]

theorem Qσ_univ (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) : Qσ K L σ univ = 1 := by
  rw [Qσ, Measure.smul_apply, Measure.restrict_apply_univ, volume_cellSet hK hL, smul_eq_mul,
    nat_mul_ofReal_inv hL]

theorem isProbabilityMeasure_Qσ (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) :
    IsProbabilityMeasure (Qσ K L σ) :=
  ⟨Qσ_univ hK hL σ⟩

instance isProbabilityMeasure_P₀ : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩

theorem bddDensity01_P₀ : BddDensity01 (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨inferInstance, 1, by simp⟩

theorem bddDensity01_Qσ (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) :
    BddDensity01 (Qσ K L σ) := by
  refine ⟨isProbabilityMeasure_Qσ hK hL σ, (L : ℝ≥0), ?_⟩
  rw [Measure.le_iff]
  intro s hs
  rw [Qσ, Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hs,
    Measure.restrict_apply hs, ENNReal.coe_natCast, smul_eq_mul, smul_eq_mul]
  gcongr
  exact (cellSet_subset σ).trans Ico_subset_Icc_self

theorem tvDist_Qσ (hK : 0 < K) (hL : 0 < L) (σ : Fin K → Fin L) :
    1 - 1 / (L : ℝ) ≤ StatFormal.Distances.tvDist (volume.restrict (Icc (0 : ℝ) 1)) (Qσ K L σ) := by
  have := isProbabilityMeasure_Qσ hK hL σ
  have h := StatFormal.Distances.abs_measureReal_sub_le_tvDist
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (ν := Qσ K L σ) (measurableSet_cellSet σ)
  have h1 : (volume.restrict (Icc (0 : ℝ) 1)).real (cellSet K L σ) = 1 / L := by
    rw [measureReal_def, Measure.restrict_apply (measurableSet_cellSet σ),
      inter_eq_left.2 ((cellSet_subset σ).trans Ico_subset_Icc_self), volume_cellSet hK hL,
      ENNReal.toReal_ofReal (by positivity)]
  have h2 : (Qσ K L σ).real (cellSet K L σ) = 1 := by
    rw [measureReal_def, Qσ_apply_cellSet hK hL, ENNReal.toReal_one]
  rw [h1, h2] at h
  linarith [neg_le_abs (1 / (L : ℝ) - 1)]

end StatFormal.TrimmedMMD.Impossible
