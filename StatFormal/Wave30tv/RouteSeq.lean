import StatFormal.Wave30tv.RouteCoord

/-!
# Wave 30tv route: the sequential betting certificate (untrusted)

Fold-wise data `ω = (x, y) ∈ 𝒳^n × 𝒳^m` under `P^{⊗n} ⊗ Q^{⊗m}`, rules already evaluated at a fixed `u`.

* `predSet t`: the coordinates known before pair `t` — all batches before `bat t` and the blocks of the earlier pairs
  (everything for `t ≥ N`); `seqFiltration t = σ(coordinates in predSet t)`. It increases because `bat` is monotone.
* `core_level`: for every event `s` of batch 0, `P(reject ∩ s) ≤ δ P(s)`. The wealth started at `1_s` is a nonnegative
  supermartingale (`Lib/Betting/Predictable.lean`): `Λ_k` is a function of `predSet k`, `Z_k` of `predSet (k+1)`, and
  given `predSet k` the block coordinates of pair `k` are fresh, so `E[V Z_k] = E[V (E_P g − E_Q g)] ≤ α E V`
  (freezing, `integral_mul_coord`, and `lem:ramp` (iii)); Ville's inequality at the level `1/δ`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tv

open StatFormal.Wave30tq StatFormal.Betting

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}

/-- The batch of coordinate `j`. -/
def label (lx : Fin n → ℕ) (ly : Fin m → ℕ) (j : Fin n ⊕ Fin m) : ℕ := Sum.elim lx ly j

/-- The coordinates of the batches before `b`. -/
def before (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) : Set (Fin n ⊕ Fin m) := {j | label lx ly j < b}

/-- The coordinates known before pair `t`. -/
def predSet (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n))
    (B : Fin N → Finset (Fin m)) (t : ℕ) : Set (Fin n ⊕ Fin m) :=
  if h : t < N then before lx ly (bat ⟨t, h⟩) ∪ {j | ∃ l : Fin N, (l : ℕ) < t ∧ j ∈ blockSet A B l}
  else Set.univ

variable {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
  {B : Fin N → Finset (Fin m)}

lemma predSet_mono (hmono : Monotone bat) : Monotone (predSet lx ly bat A B) := by
  intro t t' htt'
  unfold predSet
  split_ifs with h1 h2 h2
  · refine Set.union_subset_union (fun j hj => ?_) (fun j ⟨l, hl, hj⟩ => ⟨l, lt_of_lt_of_le hl htt', hj⟩)
    exact lt_of_lt_of_le hj (hmono (Fin.mk_le_mk.2 htt'))
  · exact Set.subset_univ _
  · omega
  · exact le_rfl

lemma before_subset_predSet (k : Fin N) : before lx ly (bat k) ⊆ predSet lx ly bat A B k := by
  unfold predSet
  rw [dif_pos k.isLt]
  exact Set.subset_union_left

lemma before_subset_predSet_succ (hmono : Monotone bat) (k : Fin N) :
    before lx ly (bat k) ⊆ predSet lx ly bat A B (k + 1) :=
  (before_subset_predSet k).trans (predSet_mono hmono (Nat.le_succ _))

lemma blockSet_subset_predSet_succ (k : Fin N) : blockSet A B k ⊆ predSet lx ly bat A B (k + 1) := by
  unfold predSet
  split_ifs with h
  · exact fun j hj => Or.inr ⟨k, Nat.lt_succ_self _, hj⟩
  · exact Set.subset_univ _

lemma before_one_subset_predSet_zero (hpair : IsBatchPairing lx ly bat A B) :
    before lx ly 1 ⊆ predSet lx ly bat A B 0 := by
  unfold predSet
  split_ifs with h
  · exact fun j hj => Or.inl (lt_of_lt_of_le hj (hpair.2.2.1 _))
  · exact Set.subset_univ _

lemma notMem_predSet_of_mem_blockSet (hpair : IsBatchPairing lx ly bat A B) (k : Fin N)
    {j : Fin n ⊕ Fin m} (hj : j ∈ blockSet A B k) : j ∉ predSet lx ly bat A B k := by
  unfold predSet
  rw [dif_pos k.isLt]
  rintro (hb | ⟨l, hl, hjl⟩)
  · have hlab : label lx ly j = bat k := by
      rcases hj with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · exact hpair.2.2.2.1 k i (by exact_mod_cast hi)
      · exact hpair.2.2.2.2 k i (by exact_mod_cast hi)
    have : label lx ly j < bat k := hb
    omega
  · have hkl : l ≠ k := fun h => by rw [h] at hl; exact lt_irrefl _ hl
    exact Set.disjoint_left.1 (blockSet_disjoint hpair.1 hkl) hjl hj

/-- The filtration of the sequential certificate. -/
def seqFiltration (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n))
    (B : Fin N → Finset (Fin m)) (hmono : Monotone bat) :
    Filtration ℕ (inferInstance : MeasurableSpace ((Fin n → 𝒳) × (Fin m → 𝒳))) where
  seq t := coordSigma (predSet lx ly bat A B t)
  mono' _ _ h := coordSigma_mono (predSet_mono hmono h)
  le' _ := coordSigma_le _

omit [MeasurableSpace 𝒳] in
lemma pairZ_congr {g : 𝒳 → ℝ} (k : Fin N) {x x' : Fin n → 𝒳} {y y' : Fin m → 𝒳}
    (hx : ∀ i ∈ A k, x i = x' i) (hy : ∀ j ∈ B k, y j = y' j) :
    pairZ g A B x y k = pairZ g A B x' y' k := by
  have h1 : ∑ i ∈ A k, g (x i) = ∑ i ∈ A k, g (x' i) := Finset.sum_congr rfl fun i hi => by rw [hx i hi]
  have h2 : ∑ j ∈ B k, g (y j) = ∑ j ∈ B k, g (y' j) := Finset.sum_congr rfl fun j hj => by rw [hy j hj]
  simp only [pairZ, blockMean]
  rw [h1, h2]

lemma integrable_of_abs_le {μ : Measure ((Fin n → 𝒳) × (Fin m → 𝒳))} [IsFiniteMeasure μ]
    {f : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ} (hf : Measurable f) (K : ℝ) (hK : ∀ ω, |f ω| ≤ K) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable K (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hK ω)

/-- The mean of `V · Z_k` given the past: for `V`, `G` functions of the coordinates in `C` and blocks outside `C`,
`E[V Z_k] = E[V (E_P G − E_Q G)]`. -/
lemma integral_mul_pairZ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {C : Set (Fin n ⊕ Fin m)} (k : Fin N) (hA : (A k).Nonempty) (hB : (B k).Nonempty)
    (hAC : ∀ i ∈ A k, Sum.inl i ∉ C) (hBC : ∀ j ∈ B k, Sum.inr j ∉ C)
    {V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ} (hVm : Measurable V) (hVd : DepOn C V) {K : ℝ}
    (hVb : ∀ ω, |V ω| ≤ K)
    {G : (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ}
    (hGm : Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => G p.1 p.2)
    (hGd : DepOn C G) (hG01 : ∀ ω t, G ω t ∈ Icc (0 : ℝ) 1) :
    ∫ ω, V ω * pairZ (G ω) A B ω.1 ω.2 k ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) =
      ∫ ω, V ω * ((∫ t, G ω t ∂P) - ∫ t, G ω t ∂Q)
        ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hVb (nonempty_of_isProbabilityMeasure μ).some)
  have hGb : ∀ ω t, |G ω t| ≤ 1 := fun ω t => by
    rw [abs_le]; constructor <;> linarith [(hG01 ω t).1, (hG01 ω t).2]
  have hGx : ∀ i : Fin n, Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => G ω (ω.1 i) := fun i =>
    hGm.comp (measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst))
  have hGy : ∀ j : Fin m, Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => G ω (ω.2 j) := fun j =>
    hGm.comp (measurable_id.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hIP : Measurable fun ω => ∫ t, G ω t ∂P :=
    (hGm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hIQ : Measurable fun ω => ∫ t, G ω t ∂Q :=
    (hGm.stronglyMeasurable.integral_prod_right' (ν := Q)).measurable
  have hIb : ∀ (ν : Measure 𝒳) [IsProbabilityMeasure ν] ω, |∫ t, G ω t ∂ν| ≤ 1 := fun ν _ ω => by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (C := 1)
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hGb ω t)
    simpa [Real.norm_eq_abs] using h
  have hix : ∀ i ∈ A k, ∫ ω, V ω * G ω (ω.1 i) ∂μ = ∫ ω, V ω * ∫ t, G ω t ∂P ∂μ := fun i hi =>
    integral_mul_coord P Q (j := Sum.inl i) (hAC i hi) hVm hVd hVb hGm hGd hGb
  have hiy : ∀ j ∈ B k, ∫ ω, V ω * G ω (ω.2 j) ∂μ = ∫ ω, V ω * ∫ t, G ω t ∂Q ∂μ := fun j hj =>
    integral_mul_coord P Q (j := Sum.inr j) (hBC j hj) hVm hVd hVb hGm hGd hGb
  have hintx : ∀ i : Fin n, Integrable (fun ω => V ω * G ω (ω.1 i)) μ := fun i =>
    integrable_of_abs_le (hVm.mul (hGx i)) (K * 1) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hVb ω) (hGb _ _) (abs_nonneg _) hK0
  have hinty : ∀ j : Fin m, Integrable (fun ω => V ω * G ω (ω.2 j)) μ := fun j =>
    integrable_of_abs_le (hVm.mul (hGy j)) (K * 1) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hVb ω) (hGb _ _) (abs_nonneg _) hK0
  have hintP : Integrable (fun ω => V ω * ∫ t, G ω t ∂P) μ :=
    integrable_of_abs_le (hVm.mul hIP) (K * 1) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hVb ω) (hIb P ω) (abs_nonneg _) hK0
  have hintQ : Integrable (fun ω => V ω * ∫ t, G ω t ∂Q) μ :=
    integrable_of_abs_le (hVm.mul hIQ) (K * 1) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hVb ω) (hIb Q ω) (abs_nonneg _) hK0
  have hcA : ((A k).card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have hcB : ((B k).card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hpt : ∀ ω : (Fin n → 𝒳) × (Fin m → 𝒳), V ω * pairZ (G ω) A B ω.1 ω.2 k =
      (∑ i ∈ A k, V ω * G ω (ω.1 i)) / ((A k).card : ℝ) - (∑ j ∈ B k, V ω * G ω (ω.2 j)) / ((B k).card : ℝ) := by
    intro ω
    unfold pairZ blockMean
    rw [mul_sub, ← Finset.mul_sum, ← Finset.mul_sum, mul_div_assoc, mul_div_assoc]
  simp_rw [hpt]
  rw [integral_sub ((integrable_finsetSum _ fun i _ => hintx i).div_const _)
      ((integrable_finsetSum _ fun j _ => hinty j).div_const _), integral_div, integral_div,
    integral_finsetSum _ fun i _ => hintx i, integral_finsetSum _ fun j _ => hinty j,
    Finset.sum_congr rfl hix, Finset.sum_congr rfl hiy]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hcA, mul_div_cancel_left₀ _ hcB]
  simp_rw [mul_sub]
  rw [integral_sub hintP hintQ]

/-- **The core of `thm:betting` (v2 seq)**: for every event `s` of batch 0, `P(reject ∩ s) ≤ δ P(s)`. -/
theorem core_level (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α δ c : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hc1 : c ≤ 1)
    (G : ℕ → (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ)
    (hGm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => G (bat k) p.1 p.2)
    (hG01 : ∀ k : Fin N, ∀ ω z, G (bat k) ω z ∈ Icc (0 : ℝ) 1)
    (hGd : ∀ k : Fin N, DepOn (before lx ly (bat k)) (G (bat k)))
    (Lam : (k : ℕ) → (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin k → ℝ) → ℝ)
    (hLm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => Lam k p.1 p.2)
    (hLb : ∀ k : Fin N, ∀ ω z, 0 ≤ Lam k ω z ∧ Lam k ω z ≤ c / (1 + α))
    (hLd : ∀ k : Fin N, DepOn (before lx ly (bat k)) (Lam k))
    (hTV : StatFormal.Distances.tvDist P Q ≤ α)
    {s : Set ((Fin n → 𝒳) × (Fin m → 𝒳))} (hs : MeasurableSet s)
    (hsd : DepOn (before lx ly 1) (fun ω => ω ∈ s)) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real
        ({ω | betReject (fun k => Lam k ω) α δ (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k)} ∩ s) ≤
      δ * ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real s := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  have hmono : Monotone bat := hpair.2.1
  set 𝒢 := seqFiltration (𝒳 := 𝒳) lx ly bat A B hmono with h𝒢
  set Z : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => pairZ (G (bat k) ω) A B ω.1 ω.2 k with hZ
  set Y : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => Z k ω - α with hYdef
  set Λ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => Lam k ω (past (fun i => Z i ω) k) with hΛdef
  set W0 : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := s.indicator fun _ => 1 with hW0def
  have h1α : 0 < 1 + α := by linarith
  -- measurability and dependence of the pair statistics
  have hZm : ∀ k, Measurable (Z k) := fun k => by
    simp only [hZ]
    unfold pairZ blockMean
    refine Measurable.sub (Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _)
      (Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _)
    · exact (hGm k).comp (measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst))
    · exact (hGm k).comp (measurable_id.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hZd : ∀ k : Fin N, DepOn (predSet lx ly bat A B (k + 1)) (Z k) := fun k ω ω' h => by
    simp only [hZ]
    rw [hGd k ω ω' fun j hj => h j (before_subset_predSet_succ hmono k hj)]
    exact pairZ_congr k
      (fun i hi => h (Sum.inl i) (blockSet_subset_predSet_succ k (Or.inl ⟨i, by exact_mod_cast hi, rfl⟩)))
      (fun j hj => h (Sum.inr j) (blockSet_subset_predSet_succ k (Or.inr ⟨j, by exact_mod_cast hj, rfl⟩)))
  have hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k) := fun k =>
    measurable_coordSigma_of_depOn ((hZm k).sub_const α) fun ω ω' h => by
      simp only [hYdef]; rw [hZd k ω ω' h]
  have hΛm : ∀ k, Measurable (Λ k) := fun k =>
    (hLm k).comp (measurable_id.prodMk (Measurable.of_eval fun i => hZm _))
  have hΛd : ∀ k : Fin N, DepOn (predSet lx ly bat A B k) (Λ k) := fun k ω ω' h => by
    simp only [hΛdef]
    rw [hLd k ω ω' fun j hj => h j (before_subset_predSet k hj)]
    congr 1
    funext i
    simp only [past]
    refine hZd _ ω ω' fun j hj => h j (predSet_mono hmono ?_ hj)
    have := i.isLt
    simp only [Fin.val_castLE]
    omega
  have hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k) := fun k => measurable_coordSigma_of_depOn (hΛm k) (hΛd k)
  have hW0 : Measurable[𝒢 0] W0 := by
    refine measurable_coordSigma_of_depOn (measurable_const.indicator hs) fun ω ω' h => ?_
    have := hsd ω ω' fun j hj => h j (before_one_subset_predSet_zero hpair hj)
    simp only [hW0def, Set.indicator]
    by_cases hω : ω ∈ s
    · have hω' : ω' ∈ s := cast this hω
      simp [hω, hω']
    · have hω' : ω' ∉ s := fun h' => hω (cast this.symm h')
      simp [hω, hω']
  have hW0b : ∀ ω, 0 ≤ W0 ω ∧ W0 ω ≤ 1 := fun ω => by
    simp only [hW0def, Set.indicator]
    split_ifs <;> norm_num
  have hZb : ∀ k ω, Z k ω ∈ Icc (-1 : ℝ) 1 := fun k ω => pairZ_mem (hG01 k ω) hpair.1 k ω.1 ω.2
  have hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ c / (1 + α) := fun k ω => hLb k ω _
  have hYb : ∀ k ω, |Y k ω| ≤ 1 + α := fun k ω => by
    have := hZb k ω
    rw [abs_le]; constructor <;> simp only [hYdef] <;> linarith [this.1, this.2]
  have hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω := fun k ω => by
    have hYlo : -(1 + α) ≤ Y k ω := by
      have := hZb k ω; simp only [hYdef]; linarith [this.1]
    have hl := hΛb k ω
    have hcap : Λ k ω * (1 + α) ≤ c := by
      have := mul_le_mul_of_nonneg_right hl.2 h1α.le
      rwa [div_mul_cancel₀ c h1α.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left hYlo hl.1]
  -- the conditional mean of `Y_k` given the past is `≤ 0`
  have hmean : ∀ k : Fin N, ∀ V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ, Measurable[𝒢 k] V → (∀ ω, 0 ≤ V ω) →
      (∃ C, ∀ ω, V ω ≤ C) → ∫ ω, V ω * Y k ω ∂μ ≤ 0 := by
    intro k V hV hV0 ⟨K, hK⟩
    have hVd : DepOn (predSet lx ly bat A B k) V := depOn_of_measurable hV
    have hVm : Measurable V := hV.mono (𝒢.le k) le_rfl
    have hVb : ∀ ω, |V ω| ≤ K := fun ω => by rw [abs_of_nonneg (hV0 ω)]; exact hK ω
    have hK0 : 0 ≤ K := (hV0 (nonempty_of_isProbabilityMeasure μ).some).trans (hK _)
    have hGdk : DepOn (predSet lx ly bat A B k) (G (bat k)) := (hGd k).mono (before_subset_predSet k)
    have hEq := integral_mul_pairZ P Q (C := predSet lx ly bat A B k) k (hpair.1.1 k) (hpair.1.2.1 k)
      (fun i hi => notMem_predSet_of_mem_blockSet hpair k (Or.inl ⟨i, by exact_mod_cast hi, rfl⟩))
      (fun j hj => notMem_predSet_of_mem_blockSet hpair k (Or.inr ⟨j, by exact_mod_cast hj, rfl⟩))
      hVm hVd hVb (hGm k) hGdk (hG01 k)
    have hintZ : Integrable (fun ω => V ω * Z k ω) μ :=
      integrable_of_abs_le (hVm.mul (hZm k)) (K * 1) fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hVb ω) (abs_le.2 ⟨(hZb k ω).1, (hZb k ω).2⟩) (abs_nonneg _) hK0
    have hintV : Integrable V μ := integrable_of_abs_le hVm K hVb
    have hsplit : (fun ω => V ω * Y k ω) = fun ω => V ω * Z k ω - α * V ω := by
      funext ω; simp only [hYdef]; ring
    rw [hsplit, integral_sub hintZ (hintV.const_mul α), integral_const_mul]
    have hIP : Measurable fun ω => ∫ t, G (bat k) ω t ∂P :=
      ((hGm k).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
    have hIQ : Measurable fun ω => ∫ t, G (bat k) ω t ∂Q :=
      ((hGm k).stronglyMeasurable.integral_prod_right' (ν := Q)).measurable
    have hle : ∫ ω, V ω * Z k ω ∂μ ≤ ∫ ω, α * V ω ∂μ := by
      simp only [hZ]
      rw [hEq]
      have hIb : ∀ (ν : Measure 𝒳) [IsProbabilityMeasure ν] ω, |∫ t, G (bat k) ω t ∂ν| ≤ 1 := fun ν _ ω => by
        have hGb : ∀ t, ‖G (bat k) ω t‖ ≤ 1 := fun t => by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hG01 k ω t).1, (hG01 k ω t).2]
        have h := norm_integral_le_of_norm_le_const (μ := ν) (C := 1) (ae_of_all _ hGb)
        simpa [Real.norm_eq_abs] using h
      have hintD : Integrable (fun ω => V ω * ((∫ t, G (bat k) ω t ∂P) - ∫ t, G (bat k) ω t ∂Q)) μ :=
        integrable_of_abs_le (hVm.mul (hIP.sub hIQ)) (K * 2) fun ω => by
          rw [abs_mul]
          refine mul_le_mul (hVb ω) ((abs_sub _ _).trans ?_) (abs_nonneg _) hK0
          linarith [hIb P ω, hIb Q ω]
      refine integral_mono hintD (hintV.const_mul α) fun ω => ?_
      · have hgm : Measurable (G (bat k) ω) := (hGm k).comp (measurable_const.prodMk measurable_id)
        have hΔ := delta_le_tv P Q hgm (hG01 k ω)
        simp only
        rw [mul_comm α]
        exact mul_le_mul_of_nonneg_left (hΔ.trans hTV) (hV0 ω)
    rw [integral_const_mul] at hle
    linarith
  -- Ville's inequality at `1/δ` for the wealth started at `1_s`
  have hV := betting_ville_pred 𝒢 W0 Λ Y hW0 hW0b hY hΛ hΛb hYb hfac hmean (a := 1 / δ) (by positivity)
  have hint0 : ∫ ω, W0 ω ∂μ = μ.real s := by
    simp only [hW0def]
    rw [integral_indicator_const _ hs, smul_eq_mul, mul_one]
  have hset : {ω | ∃ t ≤ N, 1 / δ ≤ W0 ω * wealthP Λ Y t ω} =
      {ω | betReject (fun k => Lam k ω) α δ (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k)} ∩ s := by
    ext ω
    by_cases hω : ω ∈ s
    · simp only [hW0def, Set.indicator_of_mem hω, one_mul, Set.mem_ofPred_eq, Set.mem_inter_iff, hω, and_true]
      rfl
    · simp only [hW0def, Set.indicator_of_notMem hω, zero_mul, Set.mem_ofPred_eq, Set.mem_inter_iff, hω,
        and_false, iff_false]
      push Not
      intro t _
      positivity
  rw [hset, hint0] at hV
  have hδ' : 0 < 1 / δ := by positivity
  rw [one_div, inv_mul_le_iff₀ hδ] at hV
  exact hV

end StatFormal.Wave30tv
