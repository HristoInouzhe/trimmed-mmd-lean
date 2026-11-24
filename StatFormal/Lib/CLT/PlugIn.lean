import StatFormal.Lib.CLT.AsympLinear

/-!
# Two-sample plug-in statistics (library)

Statistics of the form `P_m F_n = m^{−1} Σ_{i<m} F_n(Z_{1:n}; Z̃_i)` with `F_n` a bounded function of the pool and
of one validation point.

* `cond_cheb`: conditional Chebyshev for independent samples,
  `E[(P_m − P₀) G(Z_{1:n}, ·)]² ≤ m^{−1} E ∫ G(Z_{1:n}, y)² dP₀(y)`;
* `isAL_twoSample`: if `F_n → F₀` in `L²(P ⊗ P₀)` and the pool part `∫ F_n dP₀` is asymptotically linear with
  influence function `α`, then `P_m F_n` is `IsAL` with influence functions `(α, F₀ − P₀F₀)`;
* `vstat_sq_le`: `E(V_n f − θ)² ≤ C/n` (Hoeffding);
* `isAL_vstat2`: the two-sample V-statistic `m^{−1} Σ_i n^{−M} Σ_j k(Z̃_i; Z_{j_1}, …, Z_{j_M})` of degree
  `(1, M)` with a bounded measurable kernel (the Hoeffding decomposition of `eq:e-linear`, risk term);
* `isAL_ratio2`: `m^{−1} Σ_i P_n b(Z̃_i, ·)/P_n a(Z̃_i, ·)` with `a ≥ a₀ > 0` (the coverage term: second-order
  Taylor expansion of `v/u` and the conditional variance bound).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset Function
open scoped ENNReal NNReal Real

namespace StatFormal.Foundations.CLT

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {P : Measure Ω} [IsProbabilityMeasure P]
  {P0 : Measure Z} [IsProbabilityMeasure P0] {X Y : ℕ → Ω → Z} {m : ℕ → ℕ} {κ : ℝ}

lemma measurable_integral_right {α : Type*} [MeasurableSpace α] {G : α → Z → ℝ}
    (hG : Measurable (uncurry G)) : Measurable (fun x => ∫ y, G x y ∂P0) :=
  (hG.stronglyMeasurable.integral_prod_right' (ν := P0)).measurable

lemma integral_sub_mean_sq_le {g : Z → ℝ} (hg : Measurable g) {B : ℝ} (hb : ∀ z, |g z| ≤ B) :
    ∫ z, (g z - ∫ y, g y ∂P0) ^ 2 ∂P0 ≤ ∫ z, g z ^ 2 ∂P0 := by
  set c := ∫ y, g y ∂P0
  have hi : Integrable g P0 := integrable_of_abs_le hg hb
  have hi2 : Integrable (fun z => g z ^ 2) P0 := integrable_of_abs_le (hg.pow_const 2) (C := B ^ 2) fun z => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb z) 2
  have e : (fun z => (g z - c) ^ 2) = fun z => g z ^ 2 - 2 * c * g z + c ^ 2 := by funext z; ring
  rw [e, integral_add (f := fun z => g z ^ 2 - 2 * c * g z) (g := fun _ => c ^ 2) (hi2.sub (hi.const_mul _))
    (integrable_const _), integral_sub (f := fun z => g z ^ 2) (g := fun z => 2 * c * g z) hi2 (hi.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  nlinarith [sq_nonneg c]

lemma abs_sq_le_of_abs_le {x B : ℝ} (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-! ### Conditional Chebyshev -/

/-- `E[(m^{−1} Σ_{i<m} (G(Z_{1:n}, Z̃_i) − ∫ G(Z_{1:n}, ·) dP₀))²] ≤ m^{−1} E ∫ G(Z_{1:n}, y)² dP₀(y)`. -/
lemma cond_cheb (hS : TwoSampleIID P P0 X Y m κ) {n k : ℕ} (hk : 1 ≤ k) {G : (Fin n → Z) → Z → ℝ}
    (hG : Measurable (uncurry G)) {B : ℝ} (hGb : ∀ x y, |G x y| ≤ B) :
    ∫ ω, ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (G (fun j => X j ω) (Y i ω) - ∫ y, G (fun j => X j ω) y ∂P0)) ^ 2 ∂P ≤
      (k : ℝ)⁻¹ * ∫ ω, ∫ y, G (fun j => X j ω) y ^ 2 ∂P0 ∂P := by
  set Xn : Ω → (Fin n → Z) := fun ω j => X j ω with hXn
  set Yp : Ω → (ℕ → Z) := fun ω i => Y i ω with hYp
  have hXnm : Measurable Xn := measurable_pi_iff.2 fun j => hS.hXm j
  have hYpm : Measurable Yp := measurable_pi_iff.2 fun i => hS.hYm i
  have hind : IndepFun Xn Yp P := hS.hXY.comp (φ := fun x : ℕ → Z => fun j : Fin n => x j) (ψ := id)
    (measurable_pi_iff.2 fun j => measurable_pi_apply _) measurable_id
  set gb : (Fin n → Z) → ℝ := fun x => ∫ y, G x y ∂P0 with hgb
  have hgbm : Measurable gb := measurable_integral_right hG
  have hgbb : ∀ x, |gb x| ≤ B := fun x => abs_integral_le_of_abs_le (hGb x)
  set H : (Fin n → Z) × (ℕ → Z) → ℝ := fun p =>
    ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (G p.1 (p.2 i) - gb p.1)) ^ 2 with hH
  have hGi : ∀ i, Measurable (fun p : (Fin n → Z) × (ℕ → Z) => G p.1 (p.2 i)) := fun i =>
    hG.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hHm : Measurable H := by
    refine (Measurable.const_mul ?_ _).pow_const 2
    exact Finset.measurable_sum _ fun i _ => (hGi i).sub (hgbm.comp measurable_fst)
  have hHb : ∀ p, |H p| ≤ (2 * B) ^ 2 := by
    intro p
    rw [hH, abs_of_nonneg (sq_nonneg _)]
    refine abs_sq_le_of_abs_le ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [abs_mul, abs_of_pos (inv_pos.2 hk0)]
    calc (k : ℝ)⁻¹ * |∑ i ∈ Finset.range k, (G p.1 (p.2 i) - gb p.1)| ≤ (k : ℝ)⁻¹ * ∑ _i ∈ Finset.range k, 2 * B := by
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_))
            (by positivity)
          exact (abs_sub _ _).trans (by linarith [hGb p.1 (p.2 i), hgbb p.1])
      _ = 2 * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have hmap : P.map (fun ω => (Xn ω, Yp ω)) = (P.map Xn).prod (P.map Yp) :=
    (indepFun_iff_map_prod_eq_prod_map_map hXnm.aemeasurable hYpm.aemeasurable).1 hind
  have hlaw : ∀ i, P.map (Yp · i) = P0 := fun i => hS.hYl i
  -- the inner integral over the validation sample
  have hinner : ∀ x, ∫ yp, H (x, yp) ∂(P.map Yp) ≤ (k : ℝ)⁻¹ * ∫ y, G x y ^ 2 ∂P0 := by
    intro x
    have hGx : Measurable (G x) := hG.comp (measurable_const.prodMk measurable_id)
    rw [integral_map (f := fun yp => H (x, yp)) hYpm.aemeasurable
      (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
    simp only [hH]
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hφb : ∀ y, |G x y - gb x| ≤ 2 * B := fun y => (abs_sub _ _).trans (by linarith [hGb x y, hgbb x])
    have hφ0 : ∫ y, (G x y - gb x) ∂P0 = 0 := by
      rw [integral_sub (integrable_of_abs_le hGx (hGb x)) (integrable_const _), integral_const, probReal_univ,
        one_smul, sub_self]
    rw [integral_sq_sum_comp hS.hYm hS.hYi hS.hYl (φ := fun y => G x y - gb x) (hGx.sub_const _) hφb hφ0,
      Finset.card_range]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have := integral_sub_mean_sq_le (P0 := P0) hGx (hGb x)
    calc ((k : ℝ)⁻¹) ^ 2 * (k * ∫ y, (G x y - gb x) ^ 2 ∂P0) = (k : ℝ)⁻¹ * ∫ y, (G x y - gb x) ^ 2 ∂P0 := by
          field_simp
      _ ≤ (k : ℝ)⁻¹ * ∫ y, G x y ^ 2 ∂P0 := mul_le_mul_of_nonneg_left this (by positivity)
  have hG2m : Measurable (fun x => ∫ y, G x y ^ 2 ∂P0) :=
    measurable_integral_right (G := fun x y => G x y ^ 2) (hG.pow_const 2)
  have hG2b : ∀ x, |∫ y, G x y ^ 2 ∂P0| ≤ B ^ 2 := fun x =>
    abs_integral_le_of_abs_le fun y => by rw [abs_of_nonneg (sq_nonneg _)]; exact abs_sq_le_of_abs_le (hGb x y)
  calc ∫ ω, ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (G (fun j => X j ω) (Y i ω) - ∫ y, G (fun j => X j ω) y ∂P0)) ^ 2 ∂P
      = ∫ ω, H (Xn ω, Yp ω) ∂P := rfl
    _ = ∫ p, H p ∂((P.map Xn).prod (P.map Yp)) := by
        rw [← hmap, integral_map (hXnm.prodMk hYpm).aemeasurable hHm.aestronglyMeasurable]
    _ = ∫ x, ∫ yp, H (x, yp) ∂(P.map Yp) ∂(P.map Xn) := integral_prod _ (integrable_of_abs_le hHm hHb)
    _ ≤ ∫ x, (k : ℝ)⁻¹ * ∫ y, G x y ^ 2 ∂P0 ∂(P.map Xn) := by
        have : IsProbabilityMeasure (P.map Xn) := (Measure.isProbabilityMeasure_map_iff hXnm.aemeasurable).2 inferInstance
        have : IsProbabilityMeasure (P.map Yp) := (Measure.isProbabilityMeasure_map_iff hYpm.aemeasurable).2 inferInstance
        refine integral_mono (integrable_of_abs_le (measurable_integral_right (P0 := P.map Yp)
          (G := fun x yp => H (x, yp)) hHm) (C := (2 * B) ^ 2) fun x => abs_integral_le_of_abs_le fun yp => hHb _)
          ((integrable_of_abs_le hG2m hG2b).const_mul _) hinner
    _ = (k : ℝ)⁻¹ * ∫ ω, ∫ y, G (fun j => X j ω) y ^ 2 ∂P0 ∂P := by
        rw [integral_const_mul, integral_map hXnm.aemeasurable hG2m.aestronglyMeasurable]

/-! ### The two-sample plug-in theorem -/

lemma tendsto_ratio_inv (hS : TwoSampleIID P P0 X Y m κ) :
    Tendsto (fun n : ℕ => (n : ℝ) / m n) atTop (𝓝 κ⁻¹) := by
  have := hS.hm.inv₀ hS.hκ.ne'
  simpa only [inv_div] using this

/-- The two-sample plug-in theorem. -/
theorem isAL_twoSample (hS : TwoSampleIID P P0 X Y m κ) {F : ∀ n : ℕ, (Fin n → Z) → Z → ℝ}
    (hFm : ∀ n, Measurable (uncurry (F n))) {B : ℝ} (hB0 : 0 ≤ B) (hFb : ∀ n x y, |F n x y| ≤ B) {F0 : Z → ℝ}
    (hF0m : Measurable F0) (hF0b : ∀ y, |F0 y| ≤ B)
    (hL2 : Tendsto (fun n => ∫ ω, ∫ y, (F n (fun i => X i ω) y - F0 y) ^ 2 ∂P0 ∂P) atTop (𝓝 0))
    {α : Z → ℝ} (hα : IsInfl P0 α)
    (hpool : TIP0 P (fun n ω => √(n : ℝ) * (∫ y, F n (fun i => X i ω) y ∂P0 - ∫ y, F0 y ∂P0) -
      (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, α (X i ω))) :
    IsAL P P0 X Y m (fun n ω => (m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n), F n (fun i => X i ω) (Y i ω))
      (∫ y, F0 y ∂P0) := by
  set θ := ∫ y, F0 y ∂P0 with hθ
  refine ⟨α, fun y => F0 y - θ, hα, isInfl_center hF0m hF0b, ?_⟩
  set G : ∀ n : ℕ, (Fin n → Z) → Z → ℝ := fun n x y => F n x y - F0 y with hGdef
  have hGm : ∀ n, Measurable (uncurry (G n)) := fun n => (hFm n).sub (hF0m.comp measurable_snd)
  have hGb : ∀ n x y, |G n x y| ≤ 2 * B := fun n x y => (abs_sub _ _).trans (by linarith [hFb n x y, hF0b y])
  set D : ℕ → Ω → ℝ := fun n ω => √(n : ℝ) * ((m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n),
    (G n (fun j => X j ω) (Y i ω) - ∫ y, G n (fun j => X j ω) y ∂P0)) with hD
  have hmpos := (tendsto_atTop_of_ratio hS.hκ hS.hm).eventually_gt_atTop 0
  have hXnm : ∀ n, Measurable (fun ω (j : Fin n) => X j ω) := fun n => measurable_pi_iff.2 fun j => hS.hXm j
  have hDt : TIP0 P D := by
    refine tip0_of_integral_sq ?_ ?_
    · refine Eventually.of_forall fun n => integrable_of_abs_le ?_ (C := (√(n : ℝ) * (2 * (2 * B))) ^ 2) fun ω => ?_
      · refine ((Measurable.const_mul (Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _) _).pow_const 2)
        exact ((hGm n).comp ((hXnm n).prodMk (hS.hYm i))).sub
          ((measurable_integral_right (hGm n)).comp (hXnm n))
      · rw [abs_of_nonneg (sq_nonneg _)]
        refine abs_sq_le_of_abs_le ?_
        rw [hD, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [abs_mul]
        rcases Nat.eq_zero_or_pos (m n) with h0 | hpos
        · simp only [h0, Finset.range_zero, Finset.sum_empty, abs_zero, mul_zero]; positivity
        · have hk : (0 : ℝ) < m n := by exact_mod_cast hpos
          rw [abs_of_pos (inv_pos.2 hk)]
          calc (m n : ℝ)⁻¹ * |∑ i ∈ Finset.range (m n), (G n (fun j => X j ω) (Y i ω) -
                ∫ y, G n (fun j => X j ω) y ∂P0)| ≤ (m n : ℝ)⁻¹ * ∑ _i ∈ Finset.range (m n), 2 * (2 * B) := by
                refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                  (Finset.sum_le_sum fun i _ => (abs_sub _ _).trans ?_)) (by positivity)
                linarith [hGb n (fun j => X j ω) (Y i ω), abs_integral_le_of_abs_le (μ := P0) (hGb n (fun j => X j ω))]
            _ = 2 * (2 * B) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    · -- E D² ≤ (n/m) E ∫ G² → 0
      have hlim : Tendsto (fun n : ℕ => (n : ℝ) / m n * ∫ ω, ∫ y, G n (fun j => X j ω) y ^ 2 ∂P0 ∂P) atTop (𝓝 0) := by
        have := (tendsto_ratio_inv hS).mul hL2
        simpa [hGdef] using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun n => integral_nonneg fun ω => sq_nonneg _) ?_
      filter_upwards [hmpos] with n hn
      have hc := cond_cheb hS (n := n) (k := m n) hn (hGm n) (hGb n)
      have hDeq : (fun ω => D n ω ^ 2) = fun ω => (n : ℝ) * ((m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n),
          (G n (fun j => X j ω) (Y i ω) - ∫ y, G n (fun j => X j ω) y ∂P0)) ^ 2 := by
        funext ω; rw [hD]; dsimp only; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [hDeq, integral_const_mul]
      calc (n : ℝ) * ∫ ω, ((m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n),
            (G n (fun j => X j ω) (Y i ω) - ∫ y, G n (fun j => X j ω) y ∂P0)) ^ 2 ∂P
          ≤ (n : ℝ) * ((m n : ℝ)⁻¹ * ∫ ω, ∫ y, G n (fun j => X j ω) y ^ 2 ∂P0 ∂P) :=
            mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
        _ = (n : ℝ) / m n * ∫ ω, ∫ y, G n (fun j => X j ω) y ^ 2 ∂P0 ∂P := by ring
  refine (hpool.add hDt).congr ?_
  filter_upwards [hmpos] with n hn ω
  have hk : (0 : ℝ) < m n := by exact_mod_cast hn
  have hint : ∫ y, G n (fun j => X j ω) y ∂P0 = ∫ y, F n (fun i => X i ω) y ∂P0 - θ := by
    rw [hGdef]; dsimp only
    rw [integral_sub (f := fun y => F n (fun j => X j ω) y) (g := F0)
      (integrable_of_abs_le ((hFm n).comp (measurable_const.prodMk measurable_id))
      (hFb n (fun j => X j ω))) (integrable_of_abs_le hF0m hF0b)]
  rw [hD]; dsimp only
  rw [hint]
  unfold linStat
  simp only [hGdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-! ### Hoeffding: the V-statistic second moment -/

variable {M : ℕ}

lemma abs_vstat_le (hM : 1 ≤ M) {n : ℕ} {f : (Fin M → Z) → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ u, |f u| ≤ B)
    (z : Fin n → Z) : |vstat f z| ≤ B := by
  unfold vstat
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : (0 : ℝ) ^ M = 0 := zero_pow (by omega)
    simp [this, hB0]
  · have hn : (0 : ℝ) < (n : ℝ) ^ M := by positivity
    rw [abs_mul, abs_of_pos (inv_pos.2 hn)]
    calc ((n : ℝ) ^ M)⁻¹ * |∑ j : Fin M → Fin n, f (z ∘ j)| ≤ ((n : ℝ) ^ M)⁻¹ * ∑ _j : Fin M → Fin n, B :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hB _)) (by positivity)
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; field_simp

lemma measurable_vstat {n : ℕ} {f : (Fin M → Z) → ℝ} (hf : Measurable f) :
    Measurable (fun z : Fin n → Z => vstat f z) :=
  (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)).const_mul _

/-- `∫ f_r dP₀ = θ`. -/
lemma integral_hProj_P0 {f : (Fin M → Z) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ u, |f u| ≤ B) (r : Fin M) :
    ∫ c, hProj P0 f r c ∂P0 = hMean P0 f := by
  rw [← integral_hProj (P0 := P0) hf hB r]
  exact integral_eq_of_measurePreserving (measurePreserving_eval (fun _ : Fin M => P0) r)
    (measurable_hProj hf r)

/-- The influence function `α_f = Σ_r (f_r − θ)` of a V-statistic. -/
def vInfl (P0 : Measure Z) (f : (Fin M → Z) → ℝ) (c : Z) : ℝ := ∑ r, (hProj P0 f r c - hMean P0 f)

lemma isInfl_vInfl {f : (Fin M → Z) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ u, |f u| ≤ B) :
    IsInfl P0 (vInfl P0 f) ∧ ∀ c, |vInfl P0 f c| ≤ M * (2 * B) := by
  have hb : ∀ c, |vInfl P0 f c| ≤ M * (2 * B) := by
    intro c
    unfold vInfl
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r, |hProj P0 f r c - hMean P0 f| ≤ ∑ _r : Fin M, 2 * B :=
          Finset.sum_le_sum fun r _ => (abs_sub _ _).trans (by
            linarith [abs_hProj_le (P0 := P0) hB r c, abs_hMean_le (P0 := P0) hB])
      _ = M * (2 * B) := by simp
  refine ⟨⟨Finset.measurable_sum _ fun r _ => (measurable_hProj hf r).sub_const _, ⟨_, hb⟩, ?_⟩, hb⟩
  unfold vInfl
  rw [integral_finset_sum (f := fun r z => hProj P0 f r z - hMean P0 f) _ fun r _ =>
    (integrable_of_abs_le (measurable_hProj hf r) (abs_hProj_le hB r)).sub (integrable_const _)]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [integral_sub (integrable_of_abs_le (measurable_hProj hf r) (abs_hProj_le hB r)) (integrable_const _),
    integral_hProj_P0 hf hB r, integral_const, probReal_univ, one_smul, sub_self]

/-- The Hoeffding residual in `range` form. -/
lemma vstat_resid_sq_le (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    (hM : 1 ≤ M) {n : ℕ} (hn : 1 ≤ n) {f : (Fin M → Z) → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u, |f u| ≤ B) :
    ∫ ω, (vstat f (fun i : Fin n => X i ω) - hMean P0 f -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, vInfl P0 f (X i ω)) ^ 2 ∂P ≤
      4 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 / (n : ℝ) ^ 2 := by
  have h := vstat_hoeffding_sq_le hXm hXi hXl hM hn hf hB0 hB
  have e : ∀ ω, ∑ i ∈ Finset.range n, vInfl P0 f (X i ω) =
      ∑ a : Fin n, ∑ r, (hProj P0 f r (X a ω) - hMean P0 f) := fun ω =>
    (Fin.sum_univ_eq_sum_range (fun i => vInfl P0 f (X i ω)) n).symm
  simp_rw [e]
  exact h

/-- `E(V_n f − θ)² ≤ C_V B² / n`. -/
lemma vstat_sq_le (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    (hM : 1 ≤ M) {n : ℕ} (hn : 1 ≤ n) {f : (Fin M → Z) → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u, |f u| ≤ B) :
    ∫ ω, (vstat f (fun i : Fin n => X i ω) - hMean P0 f) ^ 2 ∂P ≤
      (8 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 + 2 * (M * (2 * B)) ^ 2) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hI, hIb⟩ := isInfl_vInfl (P0 := P0) hf hB
  set R : Ω → ℝ := fun ω => vstat f (fun i : Fin n => X i ω) - hMean P0 f -
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, vInfl P0 f (X i ω) with hR
  set L : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, vInfl P0 f (X i ω) with hL
  have hRb := vstat_resid_sq_le hXm hXi hXl hM hn hf hB0 hB
  have hLm : Measurable L := (Finset.measurable_sum _ fun i _ => hI.1.comp (hXm i)).const_mul _
  have hRm : Measurable R := (((measurable_vstat hf).comp (measurable_pi_iff.2 fun i => hXm i)).sub_const _).sub hLm
  have hLb : ∀ ω, |L ω| ≤ M * (2 * B) := by
    intro ω
    rw [hL, abs_mul, abs_of_pos (inv_pos.2 hn0)]
    calc (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, vInfl P0 f (X i ω)| ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, M * (2 * B) :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hIb _))
            (by positivity)
      _ = M * (2 * B) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have hVb : ∀ ω, |vstat f (fun i : Fin n => X i ω) - hMean P0 f| ≤ 2 * B := fun ω =>
    (abs_sub _ _).trans (by linarith [abs_vstat_le hM hB0 hB (fun i : Fin n => X i ω), abs_hMean_le (P0 := P0) hB])
  have hRbd : ∀ ω, |R ω| ≤ 2 * B + M * (2 * B) := fun ω => (abs_sub _ _).trans (by linarith [hVb ω, hLb ω])
  have hL2 : ∫ ω, L ω ^ 2 ∂P ≤ (M * (2 * B)) ^ 2 / n := by
    simp_rw [hL, mul_pow]
    rw [integral_const_mul, integral_sq_sum_comp hXm hXi hXl hI.1 hIb hI.2.2, Finset.card_range]
    have : ∫ z, vInfl P0 f z ^ 2 ∂P0 ≤ (M * (2 * B)) ^ 2 := by
      calc ∫ z, vInfl P0 f z ^ 2 ∂P0 ≤ ∫ _z, (M * (2 * B)) ^ 2 ∂P0 :=
            integral_mono (integrable_of_abs_le (hI.1.pow_const 2) (C := (M * (2 * B)) ^ 2) fun z => by
              rw [abs_of_nonneg (sq_nonneg _)]; exact abs_sq_le_of_abs_le (hIb z)) (integrable_const _)
              fun z => abs_sq_le_of_abs_le (hIb z)
        _ = _ := by rw [integral_const, probReal_univ, one_smul]
    calc ((n : ℝ)⁻¹) ^ 2 * (n * ∫ z, vInfl P0 f z ^ 2 ∂P0) = (∫ z, vInfl P0 f z ^ 2 ∂P0) / n := by
          field_simp
      _ ≤ (M * (2 * B)) ^ 2 / n := div_le_div_of_nonneg_right this hn0.le
      _ = (M : ℝ) ^ 2 * (2 ^ 2 * B ^ 2) / n := by ring
  have hsplit : ∀ ω, (vstat f (fun i : Fin n => X i ω) - hMean P0 f) ^ 2 ≤ 2 * R ω ^ 2 + 2 * L ω ^ 2 := by
    intro ω
    have : vstat f (fun i : Fin n => X i ω) - hMean P0 f = R ω + L ω := by rw [hR, hL]; ring
    rw [this]; nlinarith [sq_nonneg (R ω - L ω)]
  have hR2i : Integrable (fun ω => R ω ^ 2) P := integrable_of_abs_le (hRm.pow_const 2)
    (C := (2 * B + M * (2 * B)) ^ 2) fun ω => by rw [abs_of_nonneg (sq_nonneg _)]; exact abs_sq_le_of_abs_le (hRbd ω)
  have hL2i : Integrable (fun ω => L ω ^ 2) P := integrable_of_abs_le (hLm.pow_const 2)
    (C := (M * (2 * B)) ^ 2) fun ω => by rw [abs_of_nonneg (sq_nonneg _)]; exact abs_sq_le_of_abs_le (hLb ω)
  calc ∫ ω, (vstat f (fun i : Fin n => X i ω) - hMean P0 f) ^ 2 ∂P ≤ ∫ ω, (2 * R ω ^ 2 + 2 * L ω ^ 2) ∂P :=
        integral_mono (integrable_of_abs_le ((((measurable_vstat hf).comp (measurable_pi_iff.2 fun i => hXm i)).sub_const
          _).pow_const 2) (C := (2 * B) ^ 2) fun ω => by
            rw [abs_of_nonneg (sq_nonneg _)]; exact abs_sq_le_of_abs_le (hVb ω))
          ((hR2i.const_mul 2).add (hL2i.const_mul 2)) hsplit
    _ = 2 * ∫ ω, R ω ^ 2 ∂P + 2 * ∫ ω, L ω ^ 2 ∂P := by
        rw [integral_add (hR2i.const_mul 2) (hL2i.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 2 * (4 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 / (n : ℝ) ^ 2) + 2 * ((M * (2 * B)) ^ 2 / n) := by
        gcongr
    _ ≤ 2 * (4 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 / n) + 2 * ((M * (2 * B)) ^ 2 / n) := by
        gcongr
        · exact le_self_pow₀ (by exact_mod_cast hn) (by norm_num)
    _ = (8 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 + 2 * (M * (2 * B)) ^ 2) / n := by ring

/-! ### The two-sample V-statistic -/

lemma integral_vstat_left {n : ℕ} {k : Z → (Fin M → Z) → ℝ} (hk : Measurable (uncurry k)) {B : ℝ}
    (hkb : ∀ y t, |k y t| ≤ B) (x : Fin n → Z) :
    ∫ y, vstat (k y) x ∂P0 = vstat (fun t => ∫ y, k y t ∂P0) x := by
  unfold vstat
  rw [integral_const_mul, integral_finset_sum (f := fun j y => k y (x ∘ j)) _ fun j _ => integrable_of_abs_le
    (hk.comp (measurable_id.prodMk measurable_const)) (fun y => hkb y _)]

/-- The two-sample V-statistic of degree `(1, M)` is asymptotically linear. -/
theorem isAL_vstat2 (hS : TwoSampleIID P P0 X Y m κ) (hM : 1 ≤ M) {k : Z → (Fin M → Z) → ℝ}
    (hk : Measurable (uncurry k)) {B : ℝ} (hB0 : 0 ≤ B) (hkb : ∀ y t, |k y t| ≤ B) :
    IsAL P P0 X Y m (fun n ω => (m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n), vstat (k (Y i ω)) (fun j : Fin n => X j ω))
      (∫ y, hMean P0 (k y) ∂P0) := by
  set kb : (Fin M → Z) → ℝ := fun t => ∫ y, k y t ∂P0 with hkbdef
  have hkbm : Measurable kb := (hk.stronglyMeasurable.integral_prod_left' (μ := P0)).measurable
  have hkbb : ∀ t, |kb t| ≤ B := fun t => abs_integral_le_of_abs_le fun y => hkb y t
  have hθ : ∫ y, hMean P0 (k y) ∂P0 = hMean P0 kb := by
    unfold hMean
    exact integral_integral_swap (integrable_of_abs_le hk (C := B) fun p => hkb p.1 p.2)
  have hFm : ∀ n, Measurable (uncurry fun (x : Fin n → Z) (y : Z) => vstat (k y) x) := by
    intro n
    unfold vstat
    exact (Finset.measurable_sum _ fun j _ => hk.comp (measurable_snd.prodMk
      ((measurable_pi_iff.2 fun l => measurable_pi_apply _).comp measurable_fst))).const_mul _
  have hF0m : Measurable fun y => hMean P0 (k y) :=
    (hk.stronglyMeasurable.integral_prod_right' (ν := Measure.pi fun _ : Fin M => P0)).measurable
  have hXnm : ∀ n, Measurable (fun ω (j : Fin n) => X j ω) := fun n => measurable_pi_iff.2 fun j => hS.hXm j
  set CV : ℝ := 8 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 + 2 * (M * (2 * B)) ^ 2 with hCV
  refine isAL_twoSample hS (F := fun n x y => vstat (k y) x) hFm hB0 (fun n x y => abs_vstat_le hM hB0 (hkb y) x)
    hF0m (fun y => abs_hMean_le (hkb y)) ?_ (isInfl_vInfl (P0 := P0) hkbm hkbb).1 ?_
  · -- `L²` convergence
    have hlim : Tendsto (fun n : ℕ => CV / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat CV
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => integral_nonneg fun ω => integral_nonneg fun y => sq_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hjm : Measurable (uncurry fun (ω : Ω) (y : Z) => (vstat (k y) (fun i : Fin n => X i ω) - hMean P0 (k y)) ^ 2) :=
      (((hFm n).comp (((hXnm n).comp measurable_fst).prodMk measurable_snd)).sub
        (hF0m.comp measurable_snd)).pow_const 2
    rw [integral_integral_swap (integrable_of_abs_le hjm (C := (2 * B) ^ 2) fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact abs_sq_le_of_abs_le ((abs_sub _ _).trans (by
        linarith [abs_vstat_le hM hB0 (hkb p.2) (fun i : Fin n => X i p.1), abs_hMean_le (P0 := P0) (hkb p.2)])))]
    calc ∫ y, ∫ ω, (vstat (k y) (fun i : Fin n => X i ω) - hMean P0 (k y)) ^ 2 ∂P ∂P0 ≤ ∫ _y, CV / n ∂P0 :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => integral_nonneg fun ω => sq_nonneg _)
            (integrable_const _) (Eventually.of_forall fun y =>
              vstat_sq_le hS.hXm hS.hXi hS.hXl hM hn (hk.comp (measurable_const.prodMk measurable_id)) hB0 (hkb y))
      _ = CV / n := by rw [integral_const, probReal_univ, one_smul]
  · -- the pool part
    refine tip0_of_integral_sq (Eventually.of_forall fun n => ?_) ?_
    · refine integrable_of_abs_le ?_ (C := (√(n : ℝ) * (2 * B) + (√(n : ℝ))⁻¹ * (n * (M * (2 * B)))) ^ 2) fun ω => ?_
      · refine (((Measurable.const_mul ?_ _).sub (Measurable.const_mul ?_ _))).pow_const 2
        · exact (measurable_integral_right (G := fun (x : Fin n → Z) y => vstat (k y) x) (hFm n) |>.comp
            (hXnm n)).sub_const _
        · exact Finset.measurable_sum _ fun i _ => (isInfl_vInfl (P0 := P0) hkbm hkbb).1.1.comp (hS.hXm i)
      · rw [abs_of_nonneg (sq_nonneg _)]
        refine abs_sq_le_of_abs_le ((abs_sub _ _).trans (add_le_add ?_ ?_))
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (Real.sqrt_nonneg _)
          have h1 := abs_integral_le_of_abs_le (μ := P0) fun y => abs_vstat_le hM hB0 (hkb y) (fun i : Fin n => X i ω)
          have h2 := abs_integral_le_of_abs_le (μ := P0) fun y => abs_hMean_le (P0 := P0) (hkb y)
          linarith
        · rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by positivity)
          calc ∑ i ∈ Finset.range n, |vInfl P0 kb (X i ω)| ≤ ∑ _i ∈ Finset.range n, M * (2 * B) :=
                Finset.sum_le_sum fun i _ => (isInfl_vInfl (P0 := P0) hkbm hkbb).2 _
            _ = n * (M * (2 * B)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · set CR : ℝ := 4 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 with hCR
      have hlim : Tendsto (fun n : ℕ => CR / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat CR
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun n => integral_nonneg fun ω => sq_nonneg _) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hr := vstat_resid_sq_le hS.hXm hS.hXi hS.hXl hM hn hkbm hB0 hkbb
      have hpt : ∀ ω, (√(n : ℝ) * (∫ y, vstat (k y) (fun i : Fin n => X i ω) ∂P0 - ∫ y, hMean P0 (k y) ∂P0) -
          (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, vInfl P0 kb (X i ω)) ^ 2 =
          n * (vstat kb (fun i : Fin n => X i ω) - hMean P0 kb -
            (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, vInfl P0 kb (X i ω)) ^ 2 := by
        intro ω
        rw [integral_vstat_left hk hkb, hθ]
        have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
        have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 hn0
        set t := √(n : ℝ)
        rw [← hs]
        field_simp
        ring
      simp_rw [hpt]
      rw [integral_const_mul]
      calc (n : ℝ) * ∫ ω, (vstat kb (fun i : Fin n => X i ω) - hMean P0 kb -
            (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, vInfl P0 kb (X i ω)) ^ 2 ∂P ≤ n * (CR / (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hr hn0.le
        _ = CR / n := by field_simp

/-! ### Ratios of pool averages (the coverage term) -/

/-- The pool average `P_n f = n^{−1} Σ_{l<n} f(z_l)`. -/
def pAvg {n : ℕ} (x : Fin n → Z) (f : Z → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ l, f (x l)

lemma ratio_diff_abs {u v u0 v0 a0 B : ℝ} (ha0 : 0 < a0) (hu : a0 ≤ u) (hu0 : a0 ≤ u0) (hv0 : |v0| ≤ B) :
    |v / u - v0 / u0| ≤ |v - v0| / a0 + B * |u - u0| / a0 ^ 2 := by
  have hu' : 0 < u := ha0.trans_le hu
  have hu0' : 0 < u0 := ha0.trans_le hu0
  have e : v / u - v0 / u0 = (v - v0) / u + v0 * (u0 - u) / (u * u0) := by field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hu']; exact div_le_div_of_nonneg_left (abs_nonneg _) ha0 hu
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hu' hu0'), abs_sub_comm]
    have h1 : a0 ^ 2 ≤ u * u0 := by nlinarith
    calc |v0| * |u - u0| / (u * u0) ≤ B * |u - u0| / (u * u0) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv0 (abs_nonneg _)) (by positivity)
      _ ≤ B * |u - u0| / a0 ^ 2 :=
          div_le_div_of_nonneg_left (mul_nonneg ((abs_nonneg _).trans hv0) (abs_nonneg _)) (by positivity) h1

lemma ratio_rem_abs {u v u0 v0 a0 B : ℝ} (ha0 : 0 < a0) (hu : a0 ≤ u) (hu0 : a0 ≤ u0) (hv0 : |v0| ≤ B) :
    |v / u - v0 / u0 - ((v - v0) / u0 - v0 * (u - u0) / u0 ^ 2)| ≤
      B * (u - u0) ^ 2 / a0 ^ 3 + ((u - u0) ^ 2 + (v - v0) ^ 2) / (2 * a0 ^ 2) := by
  have hu' : 0 < u := ha0.trans_le hu
  have hu0' : 0 < u0 := ha0.trans_le hu0
  have e : v / u - v0 / u0 - ((v - v0) / u0 - v0 * (u - u0) / u0 ^ 2) =
      v0 * (u - u0) ^ 2 / (u * u0 ^ 2) - (u - u0) * (v - v0) / (u * u0) := by field_simp; ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (u - u0)), abs_of_pos (by positivity : 0 < u * u0 ^ 2)]
    have h1 : a0 ^ 3 ≤ u * u0 ^ 2 := by
      have : a0 ^ 2 ≤ u0 ^ 2 := pow_le_pow_left₀ ha0.le hu0 2
      calc a0 ^ 3 = a0 * a0 ^ 2 := by ring
        _ ≤ u * u0 ^ 2 := mul_le_mul hu this (by positivity) hu'.le
    calc |v0| * (u - u0) ^ 2 / (u * u0 ^ 2) ≤ B * (u - u0) ^ 2 / (u * u0 ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv0 (sq_nonneg _)) (by positivity)
      _ ≤ B * (u - u0) ^ 2 / a0 ^ 3 :=
          div_le_div_of_nonneg_left (mul_nonneg ((abs_nonneg _).trans hv0) (sq_nonneg _)) (by positivity) h1
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hu' hu0')]
    have h1 : a0 ^ 2 ≤ u * u0 := by nlinarith
    have h2 : |u - u0| * |v - v0| ≤ ((u - u0) ^ 2 + (v - v0) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u - u0| - |v - v0|), sq_abs (u - u0), sq_abs (v - v0)]
    calc |u - u0| * |v - v0| / (u * u0) ≤ |u - u0| * |v - v0| / a0 ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h1
      _ ≤ ((u - u0) ^ 2 + (v - v0) ^ 2) / 2 / a0 ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
      _ = ((u - u0) ^ 2 + (v - v0) ^ 2) / (2 * a0 ^ 2) := by rw [div_div]

lemma pAvg_sub_sq_le (hS : TwoSampleIID P P0 X Y m κ) {n : ℕ} (hn : 1 ≤ n) {g : Z → ℝ} (hg : Measurable g) {B : ℝ}
    (hb : ∀ z, |g z| ≤ B) :
    ∫ ω, (pAvg (fun i : Fin n => X i ω) g - ∫ z, g z ∂P0) ^ 2 ∂P ≤ (2 * B) ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hφb : ∀ z, |g z - ∫ z, g z ∂P0| ≤ 2 * B := fun z =>
    (abs_sub _ _).trans (by linarith [hb z, abs_integral_le_of_abs_le (μ := P0) hb])
  have hφ0 : ∫ z, (g z - ∫ z, g z ∂P0) ∂P0 = 0 := by
    rw [integral_sub (integrable_of_abs_le hg hb) (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_self]
  have e : ∀ ω, pAvg (fun i : Fin n => X i ω) g - ∫ z, g z ∂P0 =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (g (X i ω) - ∫ z, g z ∂P0) := by
    intro ω
    unfold pAvg
    rw [Fin.sum_univ_eq_sum_range (fun i => g (X i ω)) n, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp
  simp_rw [e, mul_pow]
  rw [integral_const_mul, integral_sq_sum_comp hS.hXm hS.hXi hS.hXl (hg.sub_const _) hφb hφ0, Finset.card_range]
  have : ∫ z, (g z - ∫ z, g z ∂P0) ^ 2 ∂P0 ≤ (2 * B) ^ 2 := by
    calc ∫ z, (g z - ∫ z, g z ∂P0) ^ 2 ∂P0 ≤ ∫ _z, (2 * B) ^ 2 ∂P0 :=
          integral_mono (integrable_of_abs_le ((hg.sub_const _).pow_const 2) (C := (2 * B) ^ 2) fun z => by
            rw [abs_of_nonneg (sq_nonneg _)]; exact abs_sq_le_of_abs_le (hφb z)) (integrable_const _)
            fun z => abs_sq_le_of_abs_le (hφb z)
      _ = (2 * B) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  calc ((n : ℝ)⁻¹) ^ 2 * (n * ∫ z, (g z - ∫ z, g z ∂P0) ^ 2 ∂P0) = (∫ z, (g z - ∫ z, g z ∂P0) ^ 2 ∂P0) / n := by
        field_simp
    _ ≤ (2 * B) ^ 2 / n := div_le_div_of_nonneg_right this hn0.le
    _ = 2 ^ 2 * B ^ 2 / n := by ring

lemma measurable_pAvg {n : ℕ} {g : Z → Z → ℝ} (hg : Measurable (uncurry g)) :
    Measurable (uncurry fun (x : Fin n → Z) (y : Z) => pAvg x (g y)) := by
  unfold pAvg
  exact (Finset.measurable_sum _ fun l _ => hg.comp (measurable_snd.prodMk
    ((measurable_pi_apply l).comp measurable_fst))).const_mul _

omit [MeasurableSpace Z] in
lemma pAvg_ge {n : ℕ} (hn : 1 ≤ n) {g : Z → ℝ} {a0 : ℝ} (hg : ∀ z, a0 ≤ g z) (x : Fin n → Z) :
    a0 ≤ pAvg x g := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pAvg
  calc a0 = (n : ℝ)⁻¹ * ∑ _l : Fin n, a0 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hg _) (by positivity)

omit [MeasurableSpace Z] in
lemma abs_pAvg_le {n : ℕ} {g : Z → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hg : ∀ z, |g z| ≤ B) (x : Fin n → Z) :
    |pAvg x g| ≤ B := by
  unfold pAvg
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [hB0]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    rw [abs_mul, abs_of_pos (inv_pos.2 hn0)]
    calc (n : ℝ)⁻¹ * |∑ l, g (x l)| ≤ (n : ℝ)⁻¹ * ∑ _l : Fin n, B :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => hg _))
            (by positivity)
      _ = B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

/-- The coverage-type statistic `m^{−1} Σ_i P_n b(Z̃_i, ·) / P_n a(Z̃_i, ·)` is asymptotically linear. -/
theorem isAL_ratio2 (hS : TwoSampleIID P P0 X Y m κ) {a b : Z → Z → ℝ} (ha : Measurable (uncurry a))
    (hb : Measurable (uncurry b)) {a0 B : ℝ} (ha0 : 0 < a0) (hab : ∀ y x, a0 ≤ a y x ∧ a y x ≤ B)
    (hbb : ∀ y x, |b y x| ≤ B) :
    IsAL P P0 X Y m (fun n ω => (m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n),
        pAvg (fun j : Fin n => X j ω) (b (Y i ω)) / pAvg (fun j : Fin n => X j ω) (a (Y i ω)))
      (∫ y, (∫ x, b y x ∂P0) / (∫ x, a y x ∂P0) ∂P0) := by
  have hB0 : 0 ≤ B := by
    obtain ⟨ω⟩ : Nonempty Ω := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := measure_univ (μ := P)
      rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
      exact zero_ne_one this
    exact ha0.le.trans ((hab (X 0 ω) (X 0 ω)).1.trans (hab _ _).2)
  set u0 : Z → ℝ := fun y => ∫ x, a y x ∂P0 with hu0def
  set v0 : Z → ℝ := fun y => ∫ x, b y x ∂P0 with hv0def
  have hay : ∀ y, Measurable (a y) := fun y => ha.comp (measurable_const.prodMk measurable_id)
  have hby : ∀ y, Measurable (b y) := fun y => hb.comp (measurable_const.prodMk measurable_id)
  have hayb : ∀ y x, |a y x| ≤ B := fun y x => abs_le.2 ⟨by linarith [(hab y x).1], (hab y x).2⟩
  have hu0 : ∀ y, a0 ≤ u0 y := by
    intro y
    calc a0 = ∫ _x, a0 ∂P0 := by rw [integral_const, probReal_univ, one_smul]
      _ ≤ u0 y := integral_mono (integrable_const _) (integrable_of_abs_le (hay y) (hayb y)) fun x => (hab y x).1
  have hu0p : ∀ y, 0 < u0 y := fun y => ha0.trans_le (hu0 y)
  have hv0 : ∀ y, |v0 y| ≤ B := fun y => abs_integral_le_of_abs_le (hbb y)
  have hu0m : Measurable u0 := measurable_integral_right ha
  have hv0m : Measurable v0 := measurable_integral_right hb
  set F : ∀ n : ℕ, (Fin n → Z) → Z → ℝ := fun n x y => pAvg x (b y) / pAvg x (a y) with hFdef
  set F0 : Z → ℝ := fun y => v0 y / u0 y with hF0def
  have hFm : ∀ n, Measurable (uncurry (F n)) := fun n => (measurable_pAvg hb).div (measurable_pAvg ha)
  have hFb : ∀ n x y, |F n x y| ≤ B / a0 := by
    intro n x y
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [hFdef, pAvg]; positivity
    · have hu := pAvg_ge hpos (fun z => (hab y z).1) x
      rw [hFdef]; dsimp only
      rw [abs_div, abs_of_pos (ha0.trans_le hu)]
      exact div_le_div₀ hB0 (abs_pAvg_le hB0 (hbb y) x) ha0 hu
  have hF0b : ∀ y, |F0 y| ≤ B / a0 := by
    intro y
    rw [hF0def]; dsimp only
    rw [abs_div, abs_of_pos (hu0p y)]
    exact div_le_div₀ hB0 (hv0 y) ha0 (hu0 y)
  -- the influence function
  set h : Z → Z → ℝ := fun y x => b y x / u0 y - v0 y * a y x / u0 y ^ 2 with hhdef
  have hhm : Measurable (uncurry h) :=
    (hb.div (hu0m.comp measurable_fst)).sub (((hv0m.comp measurable_fst).mul ha).div
      ((hu0m.comp measurable_fst).pow_const 2))
  set Ch : ℝ := B / a0 + B * B / a0 ^ 2 with hCh
  have hhb : ∀ y x, |h y x| ≤ Ch := by
    intro y x
    rw [hhdef]; dsimp only
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (hu0p y)]; exact div_le_div₀ hB0 (hbb y x) ha0 (hu0 y)
    · rw [abs_div, abs_mul, abs_of_pos (pow_pos (hu0p y) 2)]
      exact div_le_div₀ (by positivity) (mul_le_mul (hv0 y) (hayb y x) (abs_nonneg _) hB0) (by positivity)
        (pow_le_pow_left₀ ha0.le (hu0 y) 2)
  set α : Z → ℝ := fun x => ∫ y, h y x ∂P0 with hαdef
  have hαm : Measurable α := (hhm.stronglyMeasurable.integral_prod_left' (μ := P0)).measurable
  have hαb : ∀ x, |α x| ≤ Ch := fun x => abs_integral_le_of_abs_le fun y => hhb y x
  have hhy0 : ∀ y, ∫ x, h y x ∂P0 = 0 := by
    intro y
    rw [hhdef]; dsimp only
    rw [integral_sub (f := fun x => b y x / u0 y) (g := fun x => v0 y * a y x / u0 y ^ 2)
      ((integrable_of_abs_le (hby y) (hbb y)).div_const _)
      (((integrable_of_abs_le (hay y) (hayb y)).const_mul _).div_const _), integral_div, integral_div,
      integral_const_mul]
    have := hu0p y
    field_simp
    ring
  have hα0 : ∫ x, α x ∂P0 = 0 := by
    rw [hαdef]; dsimp only
    rw [integral_integral_swap (f := fun x y => h y x) (integrable_of_abs_le (hhm.comp measurable_swap) (C := Ch)
      fun p => hhb p.2 p.1)]
    simp only [hhy0, integral_zero]
  have hαI : IsInfl P0 α := ⟨hαm, ⟨Ch, hαb⟩, hα0⟩
  have hXnm : ∀ n, Measurable (fun ω (j : Fin n) => X j ω) := fun n => measurable_pi_iff.2 fun j => hS.hXm j
  -- pointwise deterministic bounds
  have hdiff : ∀ n, 1 ≤ n → ∀ x y, (F n x y - F0 y) ^ 2 ≤
      2 / a0 ^ 2 * (pAvg x (b y) - v0 y) ^ 2 + 2 * B ^ 2 / a0 ^ 4 * (pAvg x (a y) - u0 y) ^ 2 := by
    intro n hn x y
    have h1 := ratio_diff_abs (v := pAvg x (b y)) ha0 (pAvg_ge hn (fun z => (hab y z).1) x) (hu0 y) (hv0 y)
    have h2 : (F n x y - F0 y) ^ 2 ≤ (|pAvg x (b y) - v0 y| / a0 + B * |pAvg x (a y) - u0 y| / a0 ^ 2) ^ 2 :=
      abs_sq_le_of_abs_le h1
    refine h2.trans ?_
    set p1 := |pAvg x (b y) - v0 y| / a0
    set q1 := B * |pAvg x (a y) - u0 y| / a0 ^ 2
    have e1 : p1 ^ 2 = (pAvg x (b y) - v0 y) ^ 2 / a0 ^ 2 := by rw [div_pow, sq_abs]
    have e2 : q1 ^ 2 = B ^ 2 * (pAvg x (a y) - u0 y) ^ 2 / a0 ^ 4 := by
      rw [div_pow, mul_pow, sq_abs]; ring
    calc (p1 + q1) ^ 2 ≤ 2 * p1 ^ 2 + 2 * q1 ^ 2 := by nlinarith [sq_nonneg (p1 - q1)]
      _ = _ := by rw [e1, e2]; ring
  set Dfun : ∀ n : ℕ, (Fin n → Z) → Z → ℝ := fun n x y => F n x y - F0 y - pAvg x (h y) with hDdef
  have hpAh : ∀ {n : ℕ} (x : Fin n → Z) y, pAvg x (h y) = pAvg x (b y) / u0 y - v0 y * pAvg x (a y) / u0 y ^ 2 := by
    intro n x y
    unfold pAvg
    rw [hhdef]; dsimp only
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum]
    ring
  have hrem : ∀ n, 1 ≤ n → ∀ x y, |Dfun n x y| ≤ (B / a0 ^ 3 + 1 / (2 * a0 ^ 2)) * (pAvg x (a y) - u0 y) ^ 2 +
      1 / (2 * a0 ^ 2) * (pAvg x (b y) - v0 y) ^ 2 := by
    intro n hn x y
    have h1 := ratio_rem_abs (v := pAvg x (b y)) ha0 (pAvg_ge hn (fun z => (hab y z).1) x) (hu0 y) (hv0 y)
    have e : Dfun n x y = pAvg x (b y) / pAvg x (a y) - v0 y / u0 y - ((pAvg x (b y) - v0 y) / u0 y -
        v0 y * (pAvg x (a y) - u0 y) / u0 y ^ 2) := by
      rw [hDdef]; dsimp only; rw [hpAh, hFdef, hF0def]
      have := (hu0p y).ne'
      show pAvg x (b y) / pAvg x (a y) - v0 y / u0 y - (pAvg x (b y) / u0 y - v0 y * pAvg x (a y) / u0 y ^ 2) = _
      set A := pAvg x (b y) / pAvg x (a y)
      field_simp
      ring
    rw [e]
    refine h1.trans (le_of_eq ?_)
    ring
  have hDm : ∀ n, Measurable (uncurry (Dfun n)) := by
    intro n
    refine ((hFm n).sub ((hv0m.div hu0m).comp measurable_snd)).sub (measurable_pAvg hhm)
  have hDb : ∀ n x y, |Dfun n x y| ≤ 2 * (B / a0) + Ch := by
    intro n x y
    rw [hDdef]; dsimp only
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (by linarith [hFb n x y, hF0b y]))
      (abs_pAvg_le (by positivity) (fun z => hhb y z) x))
  have hpAhint : ∀ {n : ℕ} (x : Fin n → Z), ∫ y, pAvg x (h y) ∂P0 = pAvg x α := by
    intro n x
    unfold pAvg
    rw [integral_const_mul, integral_finset_sum (f := fun l y => h y (x l)) _ fun l _ =>
      integrable_of_abs_le (hhm.comp (measurable_id.prodMk measurable_const)) fun y => hhb y _]
  -- the variance of pool averages, uniformly in the validation point
  have hΔ : ∀ n, 1 ≤ n → ∀ (g : Z → Z → ℝ), Measurable (uncurry g) → (∀ y x, |g y x| ≤ B) → ∀ y,
      ∫ ω, (pAvg (fun i : Fin n => X i ω) (g y) - ∫ x, g y x ∂P0) ^ 2 ∂P ≤ (2 * B) ^ 2 / n :=
    fun n hn g hg hgb y => pAvg_sub_sq_le hS hn (hg.comp (measurable_const.prodMk measurable_id)) (hgb y)
  have hΔi : ∀ n (g : Z → Z → ℝ), Measurable (uncurry g) → (∀ y x, |g y x| ≤ B) → ∀ y,
      Integrable (fun ω => (pAvg (fun i : Fin n => X i ω) (g y) - ∫ x, g y x ∂P0) ^ 2) P := by
    intro n g hg hgb y
    refine integrable_of_abs_le ((((measurable_pAvg hg).comp ((hXnm n).prodMk measurable_const)).sub_const _).pow_const 2)
      (C := (2 * B) ^ 2) fun ω => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact abs_sq_le_of_abs_le ((abs_sub _ _).trans (by
      linarith [abs_pAvg_le hB0 (hgb y) (fun i : Fin n => X i ω), abs_integral_le_of_abs_le (μ := P0) (hgb y)]))
  have hIa : ∀ n y, Integrable (fun ω => (pAvg (fun i : Fin n => X i ω) (a y) - u0 y) ^ 2) P :=
    fun n y => hΔi n a ha hayb y
  have hIb : ∀ n y, Integrable (fun ω => (pAvg (fun i : Fin n => X i ω) (b y) - v0 y) ^ 2) P :=
    fun n y => hΔi n b hb hbb y
  have hEa : ∀ n, 1 ≤ n → ∀ y, ∫ ω, (pAvg (fun i : Fin n => X i ω) (a y) - u0 y) ^ 2 ∂P ≤ (2 * B) ^ 2 / n :=
    fun n hn y => hΔ n hn a ha hayb y
  have hEb : ∀ n, 1 ≤ n → ∀ y, ∫ ω, (pAvg (fun i : Fin n => X i ω) (b y) - v0 y) ^ 2 ∂P ≤ (2 * B) ^ 2 / n :=
    fun n hn y => hΔ n hn b hb hbb y
  have hF0m : Measurable F0 := hv0m.div hu0m
  have hBa : 0 ≤ B / a0 := by positivity
  suffices key : IsAL P P0 X Y m (fun n ω => (m n : ℝ)⁻¹ * ∑ i ∈ Finset.range (m n),
      F n (fun j : Fin n => X j ω) (Y i ω)) (∫ y, F0 y ∂P0) by
    rw [hFdef, hF0def] at key; exact key
  clear_value u0 v0 F F0 h α Dfun
  refine isAL_twoSample hS (F := F) hFm hBa hFb hF0m hF0b ?_ hαI ?_
  · set C1 : ℝ := (2 / a0 ^ 2 + 2 * B ^ 2 / a0 ^ 4) * (2 * B) ^ 2 with hC1
    have hlim : Tendsto (fun n : ℕ => C1 / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat C1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => integral_nonneg fun ω => integral_nonneg fun y => sq_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hjm : Measurable (uncurry fun (ω : Ω) (y : Z) => (F n (fun i : Fin n => X i ω) y - F0 y) ^ 2) :=
      (((hFm n).comp (((hXnm n).comp measurable_fst).prodMk measurable_snd)).sub
        (hF0m.comp measurable_snd)).pow_const 2
    rw [integral_integral_swap (integrable_of_abs_le hjm (C := (2 * (B / a0)) ^ 2) fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact abs_sq_le_of_abs_le ((abs_sub _ _).trans (by linarith [hFb n (fun i : Fin n => X i p.1) p.2, hF0b p.2])))]
    calc ∫ y, ∫ ω, (F n (fun i : Fin n => X i ω) y - F0 y) ^ 2 ∂P ∂P0 ≤ ∫ _y, C1 / n ∂P0 := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => integral_nonneg fun ω => sq_nonneg _)
            (integrable_const _) (Eventually.of_forall fun y => ?_)
          calc ∫ ω, (F n (fun i : Fin n => X i ω) y - F0 y) ^ 2 ∂P
              ≤ ∫ ω, (2 / a0 ^ 2 * (pAvg (fun i : Fin n => X i ω) (b y) - v0 y) ^ 2 +
                  2 * B ^ 2 / a0 ^ 4 * (pAvg (fun i : Fin n => X i ω) (a y) - u0 y) ^ 2) ∂P := by
                refine integral_mono (integrable_of_abs_le (hjm.comp (measurable_id.prodMk measurable_const))
                  (C := (2 * (B / a0)) ^ 2) fun ω => ?_) (((hIb n y).const_mul (2 / a0 ^ 2)).add
                  ((hIa n y).const_mul (2 * B ^ 2 / a0 ^ 4))) fun ω => hdiff n hn _ y
                rw [abs_of_nonneg (sq_nonneg _)]
                exact abs_sq_le_of_abs_le ((abs_sub _ _).trans (by
                  linarith [hFb n (fun i : Fin n => X i ω) y, hF0b y]))
            _ = 2 / a0 ^ 2 * ∫ ω, (pAvg (fun i : Fin n => X i ω) (b y) - v0 y) ^ 2 ∂P +
                  2 * B ^ 2 / a0 ^ 4 * ∫ ω, (pAvg (fun i : Fin n => X i ω) (a y) - u0 y) ^ 2 ∂P := by
                rw [integral_add ((hIb n y).const_mul (2 / a0 ^ 2)) ((hIa n y).const_mul (2 * B ^ 2 / a0 ^ 4)),
                  integral_const_mul, integral_const_mul]
            _ ≤ 2 / a0 ^ 2 * ((2 * B) ^ 2 / n) + 2 * B ^ 2 / a0 ^ 4 * ((2 * B) ^ 2 / n) := by
                gcongr
                · exact hEb n hn y
                · exact hEa n hn y
            _ = C1 / n := by rw [hC1]; ring
      _ = C1 / n := by rw [integral_const, probReal_univ, one_smul]
  · set C2 : ℝ := ((B / a0 ^ 3 + 1 / (2 * a0 ^ 2)) + 1 / (2 * a0 ^ 2)) * (2 * B) ^ 2 with hC2
    have hres : TIP0 P (fun n ω => √(n : ℝ) * ∫ y, Dfun n (fun i : Fin n => X i ω) y ∂P0) := by
      refine tip0_of_integral_abs (Eventually.of_forall fun n => ?_) ?_
      · exact integrable_of_abs_le (((measurable_integral_right (hDm n)).comp (hXnm n)).const_mul _)
          (C := √(n : ℝ) * (2 * (B / a0) + Ch)) fun ω => by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
            exact mul_le_mul_of_nonneg_left (abs_integral_le_of_abs_le fun y => hDb n _ y) (Real.sqrt_nonneg _)
      · have hlim : Tendsto (fun n : ℕ => C2 / √(n : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
          (Eventually.of_forall fun n => integral_nonneg fun ω => abs_nonneg _) ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have hjm : Measurable (uncurry fun (ω : Ω) (y : Z) => |Dfun n (fun i : Fin n => X i ω) y|) :=
          continuous_abs.measurable.comp ((hDm n).comp (((hXnm n).comp measurable_fst).prodMk measurable_snd))
        calc ∫ ω, |√(n : ℝ) * ∫ y, Dfun n (fun i : Fin n => X i ω) y ∂P0| ∂P
            ≤ ∫ ω, √(n : ℝ) * ∫ y, |Dfun n (fun i : Fin n => X i ω) y| ∂P0 ∂P := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
                ((integrable_of_abs_le ((measurable_integral_right hjm)) (C := 2 * (B / a0) + Ch) fun ω =>
                  abs_integral_le_of_abs_le fun y => by rw [abs_abs]; exact hDb n _ y).const_mul _)
                (Eventually.of_forall fun ω => ?_)
              dsimp only
              rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
              exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (Real.sqrt_nonneg _)
          _ = √(n : ℝ) * ∫ y, ∫ ω, |Dfun n (fun i : Fin n => X i ω) y| ∂P ∂P0 := by
              rw [integral_const_mul, integral_integral_swap (integrable_of_abs_le hjm (C := 2 * (B / a0) + Ch)
                fun p => by
                  show |(|Dfun n (fun i : Fin n => X i p.1) p.2|)| ≤ _
                  rw [abs_abs]; exact hDb n _ p.2)]
          _ ≤ √(n : ℝ) * ∫ _y, C2 / n ∂P0 := by
              refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
                (Eventually.of_forall fun y => integral_nonneg fun ω => abs_nonneg _) (integrable_const _)
                (Eventually.of_forall fun y => ?_)) (Real.sqrt_nonneg _)
              calc ∫ ω, |Dfun n (fun i : Fin n => X i ω) y| ∂P
                  ≤ ∫ ω, ((B / a0 ^ 3 + 1 / (2 * a0 ^ 2)) * (pAvg (fun i : Fin n => X i ω) (a y) - u0 y) ^ 2 +
                      1 / (2 * a0 ^ 2) * (pAvg (fun i : Fin n => X i ω) (b y) - v0 y) ^ 2) ∂P :=
                    integral_mono (integrable_of_abs_le (hjm.comp (measurable_id.prodMk measurable_const))
                      (C := 2 * (B / a0) + Ch) fun ω => by rw [abs_abs]; exact hDb n _ y)
                      (((hIa n y).const_mul (B / a0 ^ 3 + 1 / (2 * a0 ^ 2))).add
                        ((hIb n y).const_mul (1 / (2 * a0 ^ 2))))
                      fun ω => hrem n hn _ y
                _ = (B / a0 ^ 3 + 1 / (2 * a0 ^ 2)) * ∫ ω, (pAvg (fun i : Fin n => X i ω) (a y) - u0 y) ^ 2 ∂P +
                      1 / (2 * a0 ^ 2) * ∫ ω, (pAvg (fun i : Fin n => X i ω) (b y) - v0 y) ^ 2 ∂P := by
                    rw [integral_add ((hIa n y).const_mul (B / a0 ^ 3 + 1 / (2 * a0 ^ 2)))
                      ((hIb n y).const_mul (1 / (2 * a0 ^ 2))), integral_const_mul, integral_const_mul]
                _ ≤ (B / a0 ^ 3 + 1 / (2 * a0 ^ 2)) * ((2 * B) ^ 2 / n) + 1 / (2 * a0 ^ 2) * ((2 * B) ^ 2 / n) := by
                    gcongr
                    · exact hEa n hn y
                    · exact hEb n hn y
                _ = C2 / n := by rw [hC2]; ring
          _ = C2 / √(n : ℝ) := by
              rw [integral_const, probReal_univ, one_smul]
              have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
              have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 hn0
              set t := √(n : ℝ)
              rw [← hs]; field_simp
    refine hres.congr (eventually_atTop.2 ⟨1, fun n hn ω => ?_⟩)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hFi : Integrable (fun y => F n (fun i : Fin n => X i ω) y) P0 :=
      integrable_of_abs_le ((hFm n).comp (measurable_const.prodMk measurable_id)) (hFb n _)
    have hF0i : Integrable F0 P0 := integrable_of_abs_le hF0m hF0b
    have hhi : Integrable (fun y => pAvg (fun i : Fin n => X i ω) (h y)) P0 :=
      integrable_of_abs_le ((measurable_pAvg hhm).comp (measurable_const.prodMk measurable_id))
        (fun y => abs_pAvg_le (by positivity) (fun z => hhb y z) _)
    have hDint : ∫ y, Dfun n (fun i : Fin n => X i ω) y ∂P0 =
        ∫ y, F n (fun i : Fin n => X i ω) y ∂P0 - ∫ y, F0 y ∂P0 - pAvg (fun i : Fin n => X i ω) α := by
      rw [hDdef]; dsimp only
      rw [integral_sub (f := fun y => F n (fun i : Fin n => X i ω) y - F0 y)
        (g := fun y => pAvg (fun i : Fin n => X i ω) (h y)) (hFi.sub hF0i) hhi,
        integral_sub (f := fun y => F n (fun i : Fin n => X i ω) y) (g := F0) hFi hF0i, hpAhint]
    have hsum : (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, α (X i ω) = √(n : ℝ) * pAvg (fun i : Fin n => X i ω) α := by
      unfold pAvg
      rw [← Fin.sum_univ_eq_sum_range (fun i => α (X i ω)) n]
      have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
      have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 hn0
      set t := √(n : ℝ)
      rw [← hs]; field_simp
    rw [hDint, hsum]
    ring

end StatFormal.Foundations.CLT
