import StatFormal.Lib.Bootstrap.CltProb

/-!
# Coverage of the percentile bootstrap lower limit of the split statistic (library)

* `fOrd k R = min_{|S| = k} max_{i ∈ S} R i`, the `k`-th smallest value of `R : ι → ℝ` on a finite type;
  `fOrd_le_iff`: `fOrd k R ≤ x ↔ k ≤ #{i : R i ≤ x}` (`1 ≤ k ≤ |ι|`);
* `percLo`: the percentile lower limit, the `⌈δN⌉`-th smallest of the `N = n^n m^m` bootstrap replicates `T̂*`;
* `perc_coverage`: `liminf P(percLo ≤ T₀) ≥ 1 − δ` — on `{√n(T₀ − T̂) ≥ σ(θ − z)}` (probability `→ Φ(z − θ)` by the
  CLT) and `{K_n(σ(θ − z)) ≥ δ + g}` (probability `→ 1` by the bootstrap CLT in probability, `g > 0` since the
  Gaussian charges every interval), at least `⌈δN⌉` replicates are `≤ T₀`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatFormal.Foundations.Bootstrap

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT

/-! ### Order statistics on a finite type -/

section FOrd
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `k`-th smallest value of `R`: `min_{|S| = k} max_{i ∈ S} R i`. -/
def fOrd (k : ℕ) (R : ι → ℝ) : ℝ := ⨅ S : {S : Finset ι // S.card = k}, ⨆ i : S.1, R i

lemma fOrd_spec {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (R : ι → ℝ) :
    k ≤ (univ.filter fun j => R j ≤ fOrd k R).card ∧ (univ.filter fun j => R j < fOrd k R).card < k := by
  have hne : Nonempty {S : Finset ι // S.card = k} := by
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset ι)) (by simpa using hkn)
    exact ⟨⟨S, hS⟩⟩
  have hSne : ∀ S : {S : Finset ι // S.card = k}, Nonempty S.1 := fun S => by
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [S.2]; omega)
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨S0, hS0⟩ := exists_eq_ciInf_of_finite (f := fun S : {S : Finset ι // S.card = k} => ⨆ i : S.1, R i)
  have hmax : ∀ S : {S : Finset ι // S.card = k}, ∃ i : S.1, R i = ⨆ i : S.1, R i := fun S => by
    haveI := hSne S
    exact exists_eq_ciSup_of_finite
  have hc : fOrd k R = ⨆ i : S0.1, R i := hS0.symm
  refine ⟨?_, ?_⟩
  · have hsub : S0.1 ⊆ univ.filter fun j => R j ≤ fOrd k R := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and]
      rw [hc]
      haveI := hSne S0
      exact le_ciSup (f := fun i : S0.1 => R i) (Finite.bddAbove_range _) ⟨j, hj⟩
    calc k = S0.1.card := S0.2.symm
      _ ≤ _ := card_le_card hsub
  · by_contra hlt
    push_neg at hlt
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hlt
    obtain ⟨t, ht⟩ := hmax ⟨T, hTc⟩
    have h1 : fOrd k R ≤ ⨆ i : T, R i :=
      ciInf_le (f := fun S : {S : Finset ι // S.card = k} => ⨆ i : S.1, R i) (Finite.bddBelow_range _) ⟨T, hTc⟩
    have h2 : R t < fOrd k R := by
      have := hT t.2
      simpa using this
    have : (⨆ i : T, R i) = R t := ht.symm
    linarith

lemma fOrd_le_iff {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (R : ι → ℝ) (x : ℝ) :
    fOrd k R ≤ x ↔ k ≤ (univ.filter fun j => R j ≤ x).card := by
  obtain ⟨s1, s2⟩ := fOrd_spec hk1 hkn R
  constructor
  · intro h
    exact s1.trans (card_le_card fun j hj => by
      simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact hj.trans h)
  · intro h
    by_contra hc
    push_neg at hc
    have : (univ.filter fun j => R j ≤ x).card ≤ (univ.filter fun j => R j < fOrd k R).card :=
      card_le_card fun j hj => by
        simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact hj.trans_lt hc
    omega

lemma measurable_fOrd {Ω : Type*} [MeasurableSpace Ω] (k : ℕ) {R : ι → Ω → ℝ} (hR : ∀ i, Measurable (R i)) :
    Measurable fun ω => fOrd k (fun i => R i ω) := by
  unfold fOrd
  exact Measurable.iInf fun S => Measurable.iSup fun i => hR i

end FOrd

/-! ### The percentile lower limit -/

/-- The percentile lower limit `T̂*_{(⌈δN⌉)}`, `N = n^n m^m`. -/
def percLo (n m : ℕ) (α δ : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ :=
  fOrd ⌈δ * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m))⌉₊
    (fun p : (Fin n → Fin n) × (Fin m → Fin m) => tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2))

lemma card_boot_ge {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (n : ℝ) ≤ Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) := by
  have hc : (Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) : ℝ) = (n : ℝ) ^ n * (m : ℝ) ^ m := by
    simp [Fintype.card_prod]
  rw [hc]
  have h1 : (n : ℝ) ≤ (n : ℝ) ^ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ n := pow_le_pow_right₀ this hn
  have h2 : (1 : ℝ) ≤ (m : ℝ) ^ m := one_le_pow₀ (by exact_mod_cast hm)
  nlinarith

/-- Gaussian scaling: `N(0, s²)(−∞, s y] = Φ(y)`. -/
lemma gaussian_scale {s : ℝ} (hs : 0 < s) (y : ℝ) :
    (gaussianReal 0 (s ^ 2).toNNReal).real (Set.Iic (s * y)) = (gaussianReal 0 1).real (Set.Iic y) := by
  have hν : gaussianReal 0 (s ^ 2).toNNReal = (gaussianReal 0 1).map (s * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.coe_toNNReal _ (sq_nonneg s)]
  rw [hν, map_measureReal_apply (measurable_const_mul s) measurableSet_Iic]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor
  · intro hx; nlinarith
  · intro hx; nlinarith

/-- `Φ(Ioi z) = Φ(−∞, −z)`. -/
lemma gaussian_Ioi_eq (z : ℝ) : (gaussianReal 0 1).real (Set.Ioi z) = (gaussianReal 0 1).real (Set.Iio (-z)) := by
  have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  rw [neg_zero] at h
  conv_lhs => rw [← h]
  rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
  constructor <;> intro hx <;> linarith

/-- The standard Gaussian charges `[a, b]`, `a < b`. -/
lemma gaussian_Icc_pos {a b : ℝ} (hab : a < b) : 0 < (gaussianReal 0 1).real (Set.Icc a b) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hac := gaussianReal_absolutelyContinuous' (0 : ℝ) hv
  have hvol : volume (Set.Icc a b) ≠ 0 := by
    rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hne : gaussianReal 0 1 (Set.Icc a b) ≠ 0 := fun h0 => hvol (hac h0)
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

/-- Left continuity of `Φ`: `Φ(z − θ) > Φ(z) − η` for some `θ > 0`. -/
lemma exists_gaussian_left {η : ℝ} (hη : 0 < η) (z : ℝ) :
    ∃ θ > 0, (gaussianReal 0 1).real (Set.Iic z) - η < (gaussianReal 0 1).real (Set.Iic (z - θ)) := by
  set G := gaussianReal 0 1
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have : NullSingletonClass G := nullSingletonClass_gaussianReal hv
  have hmono : Monotone fun j : ℕ => Set.Iic (z - 1 / ((j : ℝ) + 1)) := fun i j hij => Set.Iic_subset_Iic.2 (by
    have : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    linarith)
  have hU : (⋃ j : ℕ, Set.Iic (z - 1 / ((j : ℝ) + 1))) = Set.Iio z := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_Iio]
    constructor
    · rintro ⟨j, hj⟩; have : 0 < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨j, by linarith⟩
  have ht := tendsto_measure_iUnion_atTop (μ := G) hmono
  rw [hU] at ht
  have hIio : G (Set.Iio z) = G (Set.Iic z) := by
    rw [← Set.Iio_union_right, measure_union (by simp) (measurableSet_singleton _), measure_singleton, add_zero]
  rw [hIio] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top G _)).comp ht
  obtain ⟨j, hj⟩ := (ht'.eventually (lt_mem_nhds (show G.real (Set.Iic z) - η < (G (Set.Iic z)).toReal by
    rw [← measureReal_def]; linarith))).exists
  exact ⟨1 / ((j : ℝ) + 1), by positivity, by simpa [Function.comp, measureReal_def] using hj⟩

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X Y : ℕ → Ω → 𝒳}

/-- The counting step: if the bootstrap cdf of the root at `xp` exceeds `δ + g`, `1/n < g`, and
`√n (T̂ − T₀) ≤ −xp`, then at least `⌈δN⌉` replicates are `≤ T₀`. -/
lemma perc_le_of_root {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {α δ g xp T₀ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg : 0 < g) (hNn : 1 / (n : ℝ) < g) (vx : Fin n → ℝ) (vy : Fin m → ℝ)
    (hK : δ + g ≤ bAvg (fun p => if bootRoot n m α vx vy p ≤ xp then (1 : ℝ) else 0))
    (hW : √(n : ℝ) * ((tLo n α vx - tUp m α vy) - T₀) ≤ -xp) :
    percLo n m α δ vx vy ≤ T₀ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have : Nonempty ((Fin n → Fin n) × (Fin m → Fin m)) := ⟨(fun i => i, fun j => j)⟩
  have hNpos : (0 : ℝ) < Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) := by exact_mod_cast Fintype.card_pos
  have hNn' := card_boot_ge hn hm
  have hroot : ∀ p : (Fin n → Fin n) × (Fin m → Fin m), bootRoot n m α vx vy p ≤ xp →
      tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2) ≤ T₀ := by
    intro p hp
    unfold bootRoot at hp
    have key : √(n : ℝ) * ((tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2)) - T₀) =
        √(n : ℝ) * ((tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2)) - (tLo n α vx - tUp m α vy)) +
          √(n : ℝ) * ((tLo n α vx - tUp m α vy) - T₀) := by ring
    have h0 : √(n : ℝ) * ((tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2)) - T₀) ≤ 0 := by linarith
    by_contra hc
    push_neg at hc
    have := mul_pos hsn (sub_pos.2 hc)
    linarith
  have hcount : bAvg (fun p => if bootRoot n m α vx vy p ≤ xp then (1 : ℝ) else 0) *
      Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) ≤
      (univ.filter fun p : (Fin n → Fin n) × (Fin m → Fin m) =>
        tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2) ≤ T₀).card := by
    have hKN : bAvg (fun p => if bootRoot n m α vx vy p ≤ xp then (1 : ℝ) else 0) *
        Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) =
        ∑ p, if bootRoot n m α vx vy p ≤ xp then (1 : ℝ) else 0 := by
      unfold bAvg; field_simp
    rw [hKN, ← natCast_card_filter]
    exact_mod_cast card_le_card fun p hp => by
      simp only [mem_filter, mem_univ, true_and] at hp ⊢; exact hroot p hp
  have hk1 : 1 ≤ ⌈δ * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m))⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hkN : ⌈δ * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m))⌉₊ ≤ Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) :=
    Nat.ceil_le.2 (by nlinarith)
  unfold percLo
  rw [fOrd_le_iff hk1 hkN]
  have hceil : (⌈δ * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m))⌉₊ : ℝ) <
      δ * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1N : 1 < g * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) := by
    have e : (1 : ℝ) = 1 / n * n := by field_simp
    calc (1 : ℝ) = 1 / n * n := e
      _ < g * n := mul_lt_mul_of_pos_right hNn hn'
      _ ≤ g * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) := mul_le_mul_of_nonneg_left hNn' hg.le
  have a1 := mul_le_mul_of_nonneg_right hK hNpos.le
  have : (⌈δ * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m))⌉₊ : ℝ) ≤
      (univ.filter fun p : (Fin n → Fin n) × (Fin m → Fin m) => tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2) ≤ T₀).card := by
    have e2 : (δ + g) * (Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) : ℝ) =
        δ * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) + g * Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) := by
      ring
    linarith
  exact_mod_cast this

/-- **Coverage of the percentile lower limit**, from the CLT for `T̂` and the bootstrap CLT in probability:
`liminf P(percLo ≤ T₀) ≥ 1 − δ`. -/
theorem perc_coverage_of {h : 𝒳 → ℝ} {α σ2 T₀ : ℝ} {m : ℕ → ℕ} (hmtop : Tendsto m atTop atTop) (hσ : 0 < σ2)
    (hclt : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (statT X Y h m α n ω - T₀)) atTop id (fun _ => μ)
      (gaussianReal 0 σ2.toNNReal))
    (hboot : ∀ t, TIP0 μ (fun n ω => bAvg (fun p => if bootRoot n (m n) α (smp X h n ω) (smp Y h (m n) ω) p ≤ t
      then (1 : ℝ) else 0) - (gaussianReal 0 σ2.toNNReal).real (Set.Iic t)))
    {δ z : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hz : (gaussianReal 0 1).real (Set.Ioi z) = δ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
      percLo n (m n) α δ (smp X h n ω) (smp Y h (m n) ω) ≤ T₀} := by
  intro η hη
  set s := √σ2 with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hσ
  have hs2 : s ^ 2 = σ2 := Real.sq_sqrt hσ.le
  set G := gaussianReal 0 1
  -- `Φ(z) = 1 − δ`
  have hΦz : G.real (Set.Iic z) = 1 - δ := by
    rw [← hz, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; ring
  -- choose `θ`
  obtain ⟨θ, hθ, hθz⟩ := exists_gaussian_left (by linarith : 0 < η / 2) z
  -- the gap at `x₊ = s(θ − z)`
  set xp := s * (θ - z)
  have hΦxp : (gaussianReal 0 σ2.toNNReal).real (Set.Iic xp) = G.real (Set.Iic (θ - z)) := by
    rw [← hs2]; exact gaussian_scale hs _
  have hδΦ : δ = G.real (Set.Iio (-z)) := by rw [← hz]; exact gaussian_Ioi_eq z
  have hgap : δ < G.real (Set.Iic (θ - z)) := by
    have hsplit : Set.Iic (θ - z) = Set.Iio (-z) ∪ Set.Icc (-z) (θ - z) := by
      ext x; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_Icc]
      constructor
      · intro hx; by_cases h : x < -z
        · exact Or.inl h
        · exact Or.inr ⟨not_lt.1 h, hx⟩
      · rintro (hx | ⟨-, hx⟩) <;> linarith
    rw [hsplit, measureReal_union (Set.disjoint_left.2 fun x hx1 hx2 => by
        simp only [Set.mem_Iio] at hx1; simp only [Set.mem_Icc] at hx2; linarith [hx2.1]) measurableSet_Icc, hδΦ]
    linarith [gaussian_Icc_pos (show -z < θ - z by linarith)]
  set g := (G.real (Set.Iic (θ - z)) - δ) / 2 with hg_def
  have hg : 0 < g := by rw [hg_def]; linarith
  -- bootstrap CLT at `x₊`
  have hboot := hboot xp g hg
  -- CLT at `s(z − θ)`
  have hv : (s ^ 2).toNNReal = σ2.toNNReal := by rw [hs2]
  rw [← hv] at hclt
  have hcov := coverage_lim hs hclt (S := fun _ _ => s) (tip0_zero.congr (Eventually.of_forall fun n ω => by ring))
    (fun _ => measurable_const) (z - θ)
  -- eventually bounds
  have hE : ∀ᶠ n : ℕ in atTop, G.real (Set.Iic (z - θ)) - η / 4 < μ.real {ω |
      √(n : ℝ) * (statT X Y h m α n ω - T₀) - (z - θ) * s ≤ 0} :=
    hcov.eventually (lt_mem_nhds (by linarith))
  have hBad : ∀ᶠ n : ℕ in atTop, μ {ω | g ≤ |bAvg (fun p => if bootRoot n (m n) α (smp X h n ω) (smp Y h (m n) ω) p ≤ xp
      then (1 : ℝ) else 0) - (gaussianReal 0 σ2.toNNReal).real (Set.Iic xp)|} ≤ ENNReal.ofReal (η / 4) :=
    (ENNReal.tendsto_nhds_zero.1 hboot) _ (ENNReal.ofReal_pos.2 (by linarith))
  have hNg : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < g := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).eventually (gt_mem_nhds hg)
    exact this
  filter_upwards [hE, hBad, hNg, eventually_gt_atTop 0, hmtop.eventually_gt_atTop 0] with n hEn hBn hNn hn hmn
  have hsub : {ω | √(n : ℝ) * (statT X Y h m α n ω - T₀) - (z - θ) * s ≤ 0} ⊆
      {ω | percLo n (m n) α δ (smp X h n ω) (smp Y h (m n) ω) ≤ T₀} ∪
      {ω | g ≤ |bAvg (fun p => if bootRoot n (m n) α (smp X h n ω) (smp Y h (m n) ω) p ≤ xp
        then (1 : ℝ) else 0) - (gaussianReal 0 σ2.toNNReal).real (Set.Iic xp)|} := by
    intro ω hω
    by_cases hb : g ≤ |bAvg (fun p => if bootRoot n (m n) α (smp X h n ω) (smp Y h (m n) ω) p ≤ xp
        then (1 : ℝ) else 0) - (gaussianReal 0 σ2.toNNReal).real (Set.Iic xp)|
    · exact Or.inr hb
    left
    rw [not_le] at hb
    have hK := (abs_lt.1 hb).1
    rw [hΦxp] at hK
    refine perc_le_of_root hn hmn hδ0 hδ1 hg hNn _ _ (by linarith [hg_def]) ?_
    have hω' : √(n : ℝ) * (statT X Y h m α n ω - T₀) - (z - θ) * s ≤ 0 := hω
    have e : statT X Y h m α n ω = tLo n α (smp X h n ω) - tUp (m n) α (smp Y h (m n) ω) := rfl
    rw [e] at hω'
    have : xp = s * (θ - z) := rfl
    linarith
  have hmeas := (measureReal_mono (μ := μ) hsub (measure_ne_top μ _)).trans (measureReal_union_le (μ := μ) _ _)
  have hBd : μ.real {ω | g ≤ |bAvg (fun p => if bootRoot n (m n) α (smp X h n ω) (smp Y h (m n) ω) p ≤ xp
        then (1 : ℝ) else 0) - (gaussianReal 0 σ2.toNNReal).real (Set.Iic xp)|} ≤ η / 4 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hBn
  have hzθ : G.real (Set.Iic (z - θ)) > 1 - δ - η / 2 := by rw [← hΦz]; linarith
  linarith

/-- **Coverage of the percentile lower limit**: `liminf P(percLo ≤ T₀) ≥ 1 − δ`. -/
theorem perc_coverage (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {m : ℕ → ℕ} (hκ : 0 < κ)
    (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q')
    (hσ : 0 < sigma2 P Q h α q q' κ) {δ z : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hz : (gaussianReal 0 1).real (Set.Ioi z) = δ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
      percLo n (m n) α δ (smp X h n ω) (smp Y h (m n) ω) ≤ popLo P h α q - popUp Q h α q'} :=
  perc_coverage_of (tendsto_atTop_of_ratio hκ hmr) hσ (clt_split hX hY hXY hm hB hα0 hα1 hκ hmr hP hQ)
    (fun t => tip0_bootCdf hX hY hm hB hα0 hα1 hκ hmr hP hQ hσ t) hδ0 hδ1 hz

end StatFormal.Foundations.Bootstrap
