import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.TrimmedMMD.Projection.Proofs
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs

/-!
# Route — trimmed MMD `prop:witnessstab`

1. (Bridge) With measurable singletons, `𝒞_{α,k}(P_n)` is exactly the image of the capped simplex
   (ties are handled by averaging the weights over tied atoms), so the QP witness `d̂` is the
   minimum-norm element of `𝒞(P_n) − 𝒞(Q_m)`.
2. On the two concentration events at level `δ/2` (product event of probability `≥ 1 − δ`),
   `lem:minkhaus` gives `d_H(𝒞(P_n) − 𝒞(Q_m), 𝒞(P) − 𝒞(Q)) ≤ η`.
3. `lem:projstab` applied to the closures (closed, convex, same Hausdorff distance, same minimum-norm
   elements) gives the three bounds; Cauchy–Schwarz gives the sup-norm bound.
-/

noncomputable section
open MeasureTheory Set Metric Finset
open scoped Pointwise
open Classical

namespace StatFormal.Wave4b

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.BangBang
  StatFormal.TrimmedMMD.Projection

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Step 1: the empirical region is the capped-simplex image -/

lemma integral_empirical_vec [CompleteSpace H] {n : ℕ} (x : Fin n → 𝒳) {f : 𝒳 → H} (hf : StronglyMeasurable f)
    {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂(empirical x) = ∑ i, (n : ℝ)⁻¹ • f (x i) := by
  unfold empirical
  rw [integral_finsetSum_measure fun i _ =>
    (Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun y => hC y)).smul_measure
      ENNReal.ofReal_ne_top]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hf]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp [one_div]

/-- Number of indices tied with `i`. -/
def tieCount {n : ℕ} (x : Fin n → 𝒳) (i : Fin n) : ℕ := (Finset.univ.filter fun j => x j = x i).card

lemma tieCount_pos {n : ℕ} (x : Fin n → 𝒳) (i : Fin n) : 0 < tieCount x i :=
  Finset.card_pos.2 ⟨i, by simp⟩

/-- Averaging over ties: `Σ_k (Σ_i [x_i = x_k] w_i / c_i) • f(x_k) = Σ_i w_i • f(x_i)`. -/
lemma sum_tie {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (x : Fin n → 𝒳) (w : Fin n → ℝ)
    (f : 𝒳 → V) :
    ∑ k, (∑ i, if x i = x k then w i / tieCount x i else 0) • f (x k) = ∑ i, w i • f (x i) := by
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∀ k, (if x i = x k then w i / tieCount x i else 0) • f (x k) =
      if x k = x i then (w i / tieCount x i) • f (x i) else 0 := by
    intro k
    by_cases h : x i = x k
    · rw [if_pos h, if_pos h.symm, h]
    · rw [if_neg h, if_neg (Ne.symm h), zero_smul]
  simp_rw [h1]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, ← tieCount,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have := (tieCount_pos x i).ne'
  field_simp

lemma empirical_region_eq [CompleteSpace H] [MeasurableSingletonClass 𝒳] {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝒳)
    {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    region φ α (empirical x) = (fun w => ∑ i, w i • φ (x i)) '' capped n α := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < 1 - α := by linarith
  have hcap : cap n α = (n : ℝ)⁻¹ * (1 / (1 - α)) := by
    unfold cap; field_simp
  ext z
  constructor
  · rintro ⟨g, hg, hgb, hgi, rfl⟩
    have hgabs : ∀ y, |g y| ≤ 1 / (1 - α) := fun y => by
      rw [abs_of_nonneg (hgb y).1]; exact (hgb y).2
    rw [integral_empirical x hg.stronglyMeasurable hgabs] at hgi
    refine ⟨fun i => (n : ℝ)⁻¹ * g (x i), ⟨fun i => ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact mul_nonneg (by positivity) (hgb _).1
    · rw [hcap]; exact mul_le_mul_of_nonneg_left (hgb _).2 (by positivity)
    · rw [← Finset.mul_sum]; exact hgi
    · have hb : ∀ y, ‖g y • φ y‖ ≤ 1 / (1 - α) * κ := fun y => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hgabs y) (hκ y) (norm_nonneg _) (by positivity)
      rw [integral_empirical_vec x (f := fun y => g y • φ y) (hg.stronglyMeasurable.smul hφ) hb]
      simp_rw [smul_smul]
  · rintro ⟨w, ⟨hw, hws⟩, rfl⟩
    set g : 𝒳 → ℝ := fun y => (n : ℝ) * ∑ i, if x i = y then w i / tieCount x i else 0 with hgdef
    have hgm : Measurable g := by
      refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
      exact Measurable.ite (measurableSet_singleton (x i) |>.congr (by ext; simp [eq_comm]))
        measurable_const measurable_const
    have hgb : ∀ y, 0 ≤ g y ∧ g y ≤ 1 / (1 - α) := by
      intro y
      set S := Finset.univ.filter fun i => x i = y
      have hsum : (∑ i, if x i = y then w i / tieCount x i else 0) =
          (∑ i ∈ S, w i) / S.card := by
        rw [← Finset.sum_filter, Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : x i = y := (Finset.mem_filter.1 hi).2
        have hc' : tieCount x i = S.card := by
          unfold tieCount; congr 1; ext j; simp [S, hi']
        rw [hc']
      have hS : (∑ i ∈ S, w i) ≤ S.card * cap n α := by
        have := Finset.sum_le_card_nsmul S w (cap n α) fun i _ => (hw i).2
        simpa [nsmul_eq_mul] using this
      have hS0 : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg fun i _ => (hw i).1
      simp only [hgdef, hsum]
      constructor
      · positivity
      · rcases Nat.eq_zero_or_pos S.card with h0 | hpos
        · rw [h0, Nat.cast_zero, div_zero, mul_zero]; positivity
        · have hpos' : (0 : ℝ) < S.card := by exact_mod_cast hpos
          rw [mul_div_assoc', div_le_iff₀ hpos']
          calc (n : ℝ) * ∑ i ∈ S, w i ≤ n * (S.card * cap n α) :=
                mul_le_mul_of_nonneg_left hS hn0.le
            _ = 1 / (1 - α) * S.card := by rw [hcap]; field_simp
    have hgabs : ∀ y, |g y| ≤ 1 / (1 - α) := fun y => by
      rw [abs_of_nonneg (hgb y).1]; exact (hgb y).2
    have hx : ∀ k, (n : ℝ)⁻¹ * g (x k) =
        ∑ i, if x i = x k then w i / tieCount x i else 0 := by
      intro k; simp only [hgdef]; field_simp
    refine ⟨g, hgm, hgb, ?_, ?_⟩
    · rw [integral_empirical x hgm.stronglyMeasurable hgabs, Finset.mul_sum]
      simp_rw [hx]
      have := sum_tie x w (fun _ => (1 : ℝ))
      simp only [smul_eq_mul, mul_one] at this
      rw [this, hws]
    · have hb : ∀ y, ‖g y • φ y‖ ≤ 1 / (1 - α) * κ := fun y => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hgabs y) (hκ y) (norm_nonneg _) (by positivity)
      rw [integral_empirical_vec x (f := fun y => g y • φ y) (hgm.stronglyMeasurable.smul hφ) hb]
      simp_rw [smul_smul, hx]
      exact (sum_tie x w φ).symm

/-! ### Step 3 helpers -/

lemma isMinNorm_closure {C : Set H} {p : H} (hp : IsMinNorm C p) : IsMinNorm (closure C) p :=
  ⟨subset_closure hp.1, fun q hq =>
    closure_minimal (s := C) (t := {q | ‖p‖ ≤ ‖q‖}) hp.2
      (isClosed_le continuous_const continuous_norm) hq⟩

lemma witness_isMinNorm [CompleteSpace H] [MeasurableSingletonClass 𝒳] {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {p : (Fin n → ℝ) × (Fin m → ℝ)} (hp : p ∈ capped n α ×ˢ capped m β)
    (hmin : IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m β) p) :
    IsMinNorm (region φ α (empirical x) - region φ β (empirical y)) (witness φ x y p) := by
  rw [empirical_region_eq hn x hφ hκ hα0 hα1, empirical_region_eq hm y hφ hκ hβ0 hβ1]
  refine ⟨⟨_, ⟨p.1, hp.1, rfl⟩, _, ⟨p.2, hp.2, rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨_, ⟨w, hw, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
  have := isMinOn_iff.1 hmin (w, v) ⟨hw, hv⟩
  unfold qp at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem witnessstab : Claims.witnessstab := by
  intro 𝒳 H _ _ _ _ _ _ P Q _ _ φ κ α β δ n m hφ hκ hα0 hα1 hβ0 hβ1 hn hm hδ0 hδ1
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ21 : δ / 2 < 1 := by linarith
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x₀)
  obtain ⟨AP, hAPm, hAPp, hAP⟩ :=
    StatFormal.TrimmedMMD.Concentration.concentration 𝒳 H P φ κ α (δ / 2) n hφ hκ hα0 hα1 hn
      hδ2 hδ21
  obtain ⟨AQ, hAQm, hAQp, hAQ⟩ :=
    StatFormal.TrimmedMMD.Concentration.concentration 𝒳 H Q φ κ β (δ / 2) m hφ hκ hβ0 hβ1 hm
      hδ2 hδ21
  have hP : ENNReal.ofReal (1 - δ / 2) ≤
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) (Prod.fst ⁻¹' AP) := by
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one,
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hAPp
  have hQ : ENNReal.ofReal (1 - δ / 2) ≤
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) (Prod.snd ⁻¹' AQ) := by
    rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul,
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hAQp
  refine ⟨Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, (measurable_fst hAPm).inter (measurable_snd hAQm),
    StatFormal.TrimmedMMD.prob_inter_ge hδ0 hδ1 (measurable_snd hAQm) hP hQ, ?_⟩
  rintro z ⟨hz1, hz2⟩ p dstar hp hmin hdstar
  have h1 := hAP hz1
  have h2 := hAQ hz2
  simp only [mem_setOf_eq] at h1 h2
  set η := etaNM κ α β δ n m with hηdef
  have hη0 : 0 ≤ η := add_nonneg (StatFormal.TrimmedMMD.rn_nonneg hκ0 hα1 _ _)
    (StatFormal.TrimmedMMD.rn_nonneg hκ0 hβ1 _ _)
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hn) z.1
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hm) z.2
  -- the four regions
  set An := region φ α (empirical z.1)
  set Bm := region φ β (empirical z.2)
  set AP' := region φ α P
  set BQ := region φ β Q
  have neAn : An.Nonempty := region_nonempty _ hα0 hα1
  have neBm : Bm.Nonempty := region_nonempty _ hβ0 hβ1
  have neAP : AP'.Nonempty := region_nonempty _ hα0 hα1
  have neBQ : BQ.Nonempty := region_nonempty _ hβ0 hβ1
  have bAn : Bornology.IsBounded An := StatFormal.TrimmedMMD.Unconditional.region_isBounded _ hκ
  have bBm : Bornology.IsBounded Bm := StatFormal.TrimmedMMD.Unconditional.region_isBounded _ hκ
  have bAP : Bornology.IsBounded AP' := StatFormal.TrimmedMMD.Unconditional.region_isBounded _ hκ
  have bBQ : Bornology.IsBounded BQ := StatFormal.TrimmedMMD.Unconditional.region_isBounded _ hκ
  have hmk := (StatFormal.TrimmedMMD.Projection.lem_minkhaus H AP' An BQ Bm neAP neAn neBQ neBm
    bAP bAn bBQ bBm).2.2
  have hH : hausdorffDist (AP' - BQ) (An - Bm) ≤ η := by
    rw [hausdorffDist_comm (s := AP'), hausdorffDist_comm (s := BQ)] at hmk
    calc _ ≤ _ := hmk
      _ ≤ _ := add_le_add h1 h2
  have hne1 : (AP' - BQ).Nonempty := neAP.sub neBQ
  have hne2 : (An - Bm).Nonempty := neAn.sub neBm
  have hb1 : Bornology.IsBounded (AP' - BQ) := bAP.sub bBQ
  have hb2 : Bornology.IsBounded (An - Bm) := bAn.sub bBm
  have hE : hausdorffEDist (closure (AP' - BQ)) (closure (An - Bm)) ≤ ENNReal.ofReal η := by
    rw [hausdorffEDist_closure]
    rw [hausdorffDist, ← ENNReal.ofReal_le_ofReal_iff hη0,
      ENNReal.ofReal_toReal (hausdorffEDist_ne_top_of_nonempty_of_bounded hne1 hne2 hb1 hb2)] at hH
    exact hH
  have cv1 : Convex ℝ (AP' - BQ) := (region_convex _ hφ hκ).sub (region_convex _ hφ hκ)
  have cv2 : Convex ℝ (An - Bm) := (region_convex _ hφ hκ).sub (region_convex _ hφ hκ)
  have hdh := witness_isMinNorm hn hm z.1 z.2 hφ hκ hα0 hα1 hβ0 hβ1 hp hmin
  obtain ⟨r1, -, r2, r4⟩ := StatFormal.TrimmedMMD.Projection.lem_projstab H
    (closure (AP' - BQ)) (closure (An - Bm)) dstar (witness φ z.1 z.2 p) η hne1.closure
    hne2.closure cv1.closure cv2.closure isClosed_closure isClosed_closure hη0 hE
    (isMinNorm_closure hdstar) (isMinNorm_closure hdh)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_sub_comm]; exact r1
  · rw [norm_sub_rev]; exact r2
  · refine r4.trans ?_
    gcongr
    exact min_le_left _ _
  · intro x
    rw [← inner_sub_left]
    calc |inner ℝ (witness φ z.1 z.2 p - dstar) (φ x)| ≤
          ‖witness φ z.1 z.2 p - dstar‖ * ‖φ x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖witness φ z.1 z.2 p - dstar‖ * κ := mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg _)
      _ = κ * ‖witness φ z.1 z.2 p - dstar‖ := mul_comm _ _

end StatFormal.Wave4b
