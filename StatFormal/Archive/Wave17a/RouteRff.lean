import StatFormal.Archive.Wave17a.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs

/-!
# Route: TM `thm:rffjoint` (untrusted)

* Deterministic step (`lem:qpstability` in region form): an element of the empirical region is
  `Σ_i w_i φ(x_i)` with `w_i = g(x_i)/n ≥ 0`, `Σ w_i = 1`; the same trimming function `g` gives the matching
  element for the feature map. For a signed weight vector `c` with `Σ|c| = 2`,
  `|‖Σ c ψ‖² − ‖Σ c φ‖²| ≤ Σ_{kl}|c_k||c_l| ε = 4ε`, so `|D̂^{(r)2} − D̂²| ≤ 4ε`.
* `|a − b| ≤ √|a² − b²|` and `|a − b| = |a² − b²|/(a + b)` for `a, b ≥ 0`.
* Sampling: the certified `thm:concentration` at level `δ/3` on each sample and `|D̂ − D| ≤ d_H + d_H`.
* Probability: the event is a product `A_P × A_Q × E_f`, of mass `≥ (1 − δ/3)³ ≥ 1 − δ`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.Wave17a

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

section Det
variable {𝒳 : Type*} [MeasurableSpace 𝒳]

lemma integral_empirical {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {n : ℕ}
    (x : Fin n → 𝒳) {f : 𝒳 → E} (hf : StronglyMeasurable f) :
    ∫ z, f z ∂(empirical x) = ∑ i, (1 / (n : ℝ)) • f (x i) := by
  unfold empirical
  have hint : ∀ i ∈ Finset.univ, Integrable f (ENNReal.ofReal (1 / n) • Measure.dirac (x i)) :=
    fun i _ => (integrable_dirac' hf enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finset_sum_measure hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac' f _ hf, ENNReal.toReal_ofReal (by positivity)]

/-- `‖Σ_k c_k F(r_k)‖² = Σ_k Σ_l c_k c_l ⟨F r_k, F r_l⟩`. -/
lemma norm_sq_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ι → ℝ)
    (F : ι → E) : ‖∑ k, c k • F k‖ ^ 2 = ∑ k, ∑ l, c k * c l * ⟪F k, F l⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]; ring

lemma norm_sq_close {ι H H' : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] (φ : 𝒳 → H) (ψ : 𝒳 → H') {ε : ℝ}
    (hk : ∀ x y : 𝒳, |⟪ψ x, ψ y⟫ - ⟪φ x, φ y⟫| ≤ ε) (c : ι → ℝ) (r : ι → 𝒳) :
    |‖∑ k, c k • ψ (r k)‖ ^ 2 - ‖∑ k, c k • φ (r k)‖ ^ 2| ≤ ε * (∑ k, |c k|) ^ 2 := by
  rw [norm_sq_sum, norm_sq_sum, ← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [← mul_sub, abs_mul, abs_mul, mul_comm ε]
  exact mul_le_mul_of_nonneg_left (hk _ _) (by positivity)

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']

/-- The weights of an empirical trimming. -/
lemma region_empirical_repr {n : ℕ} (x : Fin n → 𝒳) {F : 𝒳 → H} (hF : StronglyMeasurable F) {α : ℝ}
    {g : 𝒳 → ℝ} (hg : Measurable g) :
    ∫ z, g z • F z ∂(empirical x) = ∑ i, ((1 / (n : ℝ)) * g (x i)) • F (x i) := by
  have := integral_empirical x (f := fun z => g z • F z) (hg.stronglyMeasurable.smul hF)
  rw [this]
  simp_rw [smul_smul]

lemma sq_le_of_forall {S : Set ℝ} (hne : S.Nonempty) (hnn : ∀ s ∈ S, 0 ≤ s) {c : ℝ}
    (h : ∀ s ∈ S, c ≤ s ^ 2) : c ≤ sInf S ^ 2 := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (sq_nonneg _)
  · have : Real.sqrt c ≤ sInf S := le_csInf hne fun s hs => by
      rw [← Real.sqrt_sq (hnn s hs)]; exact Real.sqrt_le_sqrt (h s hs)
    calc c = Real.sqrt c ^ 2 := (Real.sq_sqrt hc.le).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2

lemma setDist_nonneg' {E : Type*} [NormedAddCommGroup E] (A B : Set E) : 0 ≤ setDist A B :=
  Real.sInf_nonneg (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

/-- One direction: `D̂_F² ≤ D̂_G² + 4ε` with the roles of the two feature maps arbitrary. -/
lemma Demp_sq_le {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (x : Fin n → 𝒳) (y : Fin m → 𝒳) {α ε : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) {F : 𝒳 → H} {G : 𝒳 → H'} (hF : StronglyMeasurable F)
    (hG : StronglyMeasurable G) (hk : ∀ x y : 𝒳, |⟪G x, G y⟫ - ⟪F x, F y⟫| ≤ ε) :
    Demp F x y α ^ 2 ≤ Demp G x y α ^ 2 + 4 * ε := by
  have := isProbabilityMeasure_empirical hn x
  have := isProbabilityMeasure_empirical hm y
  have hne : {r | ∃ a ∈ region G α (empirical x), ∃ b ∈ region G α (empirical y), r = ‖a - b‖}.Nonempty := by
    obtain ⟨a, ha⟩ := region_nonempty (φ := G) (empirical x) hα0 hα1
    obtain ⟨b, hb⟩ := region_nonempty (φ := G) (empirical y) hα0 hα1
    exact ⟨_, a, ha, b, hb, rfl⟩
  have key := sq_le_of_forall hne (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)
    (c := Demp F x y α ^ 2 - 4 * ε) ?_
  · unfold Demp setDist at *; linarith
  rintro _ ⟨a, ⟨g, hg, hgb, hg1, rfl⟩, b, ⟨g', hg', hgb', hg1', rfl⟩, rfl⟩
  -- the matching elements for `F`
  have haF : ∫ z, g z • F z ∂(empirical x) ∈ region F α (empirical x) := ⟨g, hg, hgb, hg1, rfl⟩
  have hbF : ∫ z, g' z • F z ∂(empirical y) ∈ region F α (empirical y) := ⟨g', hg', hgb', hg1', rfl⟩
  have hle : Demp F x y α ≤ ‖∫ z, g z • F z ∂(empirical x) - ∫ z, g' z • F z ∂(empirical y)‖ :=
    setDist_le_norm haF hbF
  set w : Fin n → ℝ := fun i => (1 / (n : ℝ)) * g (x i)
  set v : Fin m → ℝ := fun j => (1 / (m : ℝ)) * g' (y j)
  have hw0 : ∀ i, 0 ≤ w i := fun i => mul_nonneg (by positivity) (hgb _).1
  have hv0 : ∀ j, 0 ≤ v j := fun j => mul_nonneg (by positivity) (hgb' _).1
  have hw1 : ∑ i, w i = 1 := by
    have := integral_empirical x hg.stronglyMeasurable
    rw [hg1] at this; rw [this]; simp [w, smul_eq_mul]
  have hv1 : ∑ j, v j = 1 := by
    have := integral_empirical y hg'.stronglyMeasurable
    rw [hg1'] at this; rw [this]; simp [v, smul_eq_mul]
  -- signed weights on `Fin n ⊕ Fin m`
  set c : Fin n ⊕ Fin m → ℝ := Sum.elim w (fun j => -v j)
  set r : Fin n ⊕ Fin m → 𝒳 := Sum.elim x y
  have hrepr : ∀ K : 𝒳 → H, StronglyMeasurable K →
      ∫ z, g z • K z ∂(empirical x) - ∫ z, g' z • K z ∂(empirical y) = ∑ k, c k • K (r k) := by
    intro K hK
    rw [region_empirical_repr (α := α) x hK hg, region_empirical_repr (α := α) y hK hg',
      Fintype.sum_sum_type]
    simp only [c, r, Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg, w, v]
  have hrepr' : ∀ K : 𝒳 → H', StronglyMeasurable K →
      ∫ z, g z • K z ∂(empirical x) - ∫ z, g' z • K z ∂(empirical y) = ∑ k, c k • K (r k) := by
    intro K hK
    rw [region_empirical_repr (α := α) x hK hg, region_empirical_repr (α := α) y hK hg',
      Fintype.sum_sum_type]
    simp only [c, r, Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg, w, v]
  have hc : ∑ k, |c k| = 2 := by
    rw [Fintype.sum_sum_type]
    simp only [c, Sum.elim_inl, Sum.elim_inr, abs_neg]
    rw [Finset.sum_congr rfl fun i _ => abs_of_nonneg (hw0 i), Finset.sum_congr rfl fun j _ => abs_of_nonneg (hv0 j),
      hw1, hv1]; norm_num
  have hclose := norm_sq_close F G hk c r
  rw [hc, ← hrepr F hF, ← hrepr' G hG] at hclose
  have h1 : Demp F x y α ^ 2 ≤ ‖∫ z, g z • F z ∂(empirical x) - ∫ z, g' z • F z ∂(empirical y)‖ ^ 2 :=
    pow_le_pow_left₀ (setDist_nonneg' _ _) hle 2
  have h2 := (abs_le.1 hclose).1
  nlinarith

lemma abs_sub_le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |a - b| ≤ Real.sqrt |a ^ 2 - b ^ 2| := by
  rw [Real.le_sqrt (abs_nonneg _) (abs_nonneg _), sq_abs]
  have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [this, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  rcases le_total a b with h | h
  · rw [sq, abs_of_nonpos (by linarith)]; nlinarith
  · rw [sq, abs_of_nonneg (by linarith)]; nlinarith

end Det

theorem rffjoint : Claims.rffjoint := by
  intro 𝒳 H H' Ω _ _ _ _ _ _ _ _ _ P Q _ _ ν _ φ z κ α δ ε n m hφ hκ hκ0 hz hα0 hα1 hδ0 hδ1 hn hm hε
    ⟨Ef, hEfm, hEfp, hEf⟩
  have hδ3 : 0 < δ / 3 := by positivity
  have hδ31 : δ / 3 < 1 := by linarith
  obtain ⟨AP, hAPm, hAPp, hAP⟩ := concentration 𝒳 H P φ κ α (δ / 3) n hφ hκ hα0 hα1 hn hδ3 hδ31
  obtain ⟨AQ, hAQm, hAQp, hAQ⟩ := concentration 𝒳 H Q φ κ α (δ / 3) m hφ hκ hα0 hα1 hm hδ3 hδ31
  refine ⟨AP ×ˢ (AQ ×ˢ Ef), hAPm.prod (hAQm.prod hEfm), ?_, ?_⟩
  · rw [Measure.prod_prod, Measure.prod_prod]
    have h1 : ENNReal.ofReal (1 - δ / 3) ≤ (Measure.pi fun _ : Fin n => P) AP := by
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]; exact hAPp
    have h2 : ENNReal.ofReal (1 - δ / 3) ≤ (Measure.pi fun _ : Fin m => Q) AQ := by
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]; exact hAQp
    calc ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal ((1 - δ / 3) * ((1 - δ / 3) * (1 - δ / 3))) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (δ / 3), mul_nonneg (sq_nonneg (δ / 3)) (by linarith : (0:ℝ) ≤ 3 - δ / 3)]
      _ = ENNReal.ofReal (1 - δ / 3) * (ENNReal.ofReal (1 - δ / 3) * ENNReal.ofReal (1 - δ / 3)) := by
          rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul (by linarith)]
      _ ≤ _ := mul_le_mul' h1 (mul_le_mul' h2 hEfp)
  · rintro ⟨xs, ys, ω⟩ ⟨hx, hy, hω⟩
    simp only
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
    have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.1 hm
    have hk : ∀ x y : 𝒳, |⟪z ω x, z ω y⟫ - ⟪φ x, φ y⟫| ≤ ε := hEf ω hω
    have hk' : ∀ x y : 𝒳, |⟪φ x, φ y⟫ - ⟪z ω x, z ω y⟫| ≤ ε := fun x y => by rw [abs_sub_comm]; exact hk x y
    have hA := Demp_sq_le hn0 hm0 xs ys hα0 hα1 (hz ω) hφ hk'
    have hB := Demp_sq_le hn0 hm0 xs ys hα0 hα1 hφ (hz ω) hk
    have hsq : |Demp (z ω) xs ys α ^ 2 - Demp φ xs ys α ^ 2| ≤ 4 * ε := abs_le.2 ⟨by linarith, by linarith⟩
    have ha := setDist_nonneg' (region (z ω) α (empirical xs)) (region (z ω) α (empirical ys))
    have hb := setDist_nonneg' (region φ α (empirical xs)) (region φ α (empirical ys))
    change 0 ≤ Demp (z ω) xs ys α at ha
    change 0 ≤ Demp φ xs ys α at hb
    refine ⟨?_, fun hpos => ?_⟩
    · have hfeat : |Demp (z ω) xs ys α - Demp φ xs ys α| ≤ 2 * Real.sqrt ε := by
        refine (abs_sub_le_sqrt ha hb).trans ?_
        calc Real.sqrt |Demp (z ω) xs ys α ^ 2 - Demp φ xs ys α ^ 2| ≤ Real.sqrt (4 * ε) := Real.sqrt_le_sqrt hsq
          _ = 2 * Real.sqrt ε := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hsamp := abs_Demp_sub_Dpop_le (P := P) (Q := Q) hκ hα0 hα1 hn0 hm0 xs ys
      have h1 := hAP hx
      have h2 := hAQ hy
      simp only [mem_setOf_eq] at h1 h2
      calc |Demp (z ω) xs ys α - Dpop φ P Q α|
          ≤ |Demp (z ω) xs ys α - Demp φ xs ys α| + |Demp φ xs ys α - Dpop φ P Q α| := abs_sub_le _ _ _
        _ ≤ _ := by linarith
    · rw [le_div_iff₀ hpos]
      have : (Demp (z ω) xs ys α - Demp φ xs ys α) * (Demp (z ω) xs ys α + Demp φ xs ys α) =
          Demp (z ω) xs ys α ^ 2 - Demp φ xs ys α ^ 2 := by ring
      calc |Demp (z ω) xs ys α - Demp φ xs ys α| * (Demp (z ω) xs ys α + Demp φ xs ys α)
          = |Demp (z ω) xs ys α ^ 2 - Demp φ xs ys α ^ 2| := by
            rw [← this, abs_mul, abs_of_pos hpos]
        _ ≤ 4 * ε := hsq

end StatFormal.Wave17a
