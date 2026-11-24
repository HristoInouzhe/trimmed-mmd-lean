import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.Wave4b.RouteWitness
import StatFormal.Archive.Wave8a.RouteGeorep

/-!
# Route — trimmed MMD `prop:witnessstab` without measurable singletons, and the rate `eq:witnessrate`

1. The certified Wave 8a `georep_empirical` (`𝒞_α(P_n)` is the capped-simplex image in ANY measurable space) replaces
   the measurable-singleton bridge of the Wave 4b route; the rest of the Wave 4b proof is unchanged.
2. Every element of `𝒞_α(P)` has norm `≤ κ` (`‖∫ g φ‖ ≤ κ ∫ g = κ`), so `D ≤ 2κ`.
3. `η_{n,m} ≤ C (n∧m)^{-1/2}` coordinatewise; then `√(2ηD) + 2η ≤ (√(4κC) + 2C)(n∧m)^{-1/4}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric
open scoped Pointwise

namespace StatFormal.Wave30az

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.BangBang
  StatFormal.TrimmedMMD.Projection
open StatFormal.Wave4b (witness etaNM isMinNorm_closure)

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma witness_isMinNorm_gen [CompleteSpace H] {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) {φ : 𝒳 → H} (hφ : StronglyMeasurable φ)
    {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {p : (Fin n → ℝ) × (Fin m → ℝ)} (hp : p ∈ capped n α ×ˢ capped m β)
    (hmin : IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m β) p) :
    IsMinNorm (region φ α (empirical x) - region φ β (empirical y)) (witness φ x y p) := by
  rw [StatFormal.Wave8a.georep_empirical 𝒳 H φ α n x hφ hα0 hα1 (by omega),
    StatFormal.Wave8a.georep_empirical 𝒳 H φ β m y hφ hβ0 hβ1 (by omega)]
  refine ⟨⟨_, ⟨p.1, hp.1, rfl⟩, _, ⟨p.2, hp.2, rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨_, ⟨w, hw, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
  have := isMinOn_iff.1 hmin (w, v) ⟨hw, hv⟩
  unfold qp at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem witnessstab_gen : Claims.witnessstab_gen := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α β δ n m hφ hκ hα0 hα1 hβ0 hβ1 hn hm hδ0 hδ1
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
  have hdh := witness_isMinNorm_gen hn hm z.1 z.2 hφ hα0 hα1 hβ0 hβ1 hp hmin
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

/-- Every element of `𝒞_α(P)` has norm at most `κ`. -/
lemma norm_le_of_mem_region [CompleteSpace H] {P : Measure 𝒳} [IsProbabilityMeasure P] {φ : 𝒳 → H}
    (hφ : StronglyMeasurable φ) {κ α : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) {z : H}
    (hz : z ∈ region φ α P) : ‖z‖ ≤ κ := by
  obtain ⟨g, hg, hgb, hgi, rfl⟩ := hz
  have hgint : Integrable g P :=
    Integrable.of_bound hg.aestronglyMeasurable (1 / (1 - α)) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgb x).1]; exact (hgb x).2)
  have hle : ∀ᵐ x ∂P, ‖g x • φ x‖ ≤ g x * κ := Filter.Eventually.of_forall fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
    exact mul_le_mul_of_nonneg_left (hκ x) (hgb x).1
  calc ‖∫ x, g x • φ x ∂P‖ ≤ ∫ x, g x * κ ∂P := norm_integral_le_of_norm_le (hgint.mul_const κ) hle
    _ = κ := by rw [integral_mul_const, hgi, one_mul]

/-- `4/√n + √(A/n) ≤ (4 + √A)/√N` for `n ≥ N ≥ 1`, `A ≥ 0`. -/
lemma rn_core {n N : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n) {A : ℝ} (hA : 0 ≤ A) :
    4 / Real.sqrt n + Real.sqrt (A / n) ≤ (4 + Real.sqrt A) / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hN hNn)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hle : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hNn)
  rw [Real.sqrt_div hA, ← add_div]
  exact div_le_div_of_nonneg_left (by positivity) hsN hle

theorem witnessstab_rate : Claims.witnessstab_rate := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α β hφ hκ hα0 hα1 hβ0 hβ1
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x₀)
  have hD : ∀ d ∈ region φ α P - region φ β Q, ‖d‖ ≤ 2 * κ := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ κ + κ := add_le_add (norm_le_of_mem_region hφ hκ hα1 ha) (norm_le_of_mem_region hφ hκ hβ1 hb)
      _ = 2 * κ := by ring
  refine ⟨hD, fun δ hδ0 hδ1 => ?_⟩
  set A : ℝ := 2 * Real.log (2 / (δ / 2)) with hAdef
  have hA : 0 ≤ A := by
    have : 1 ≤ 2 / (δ / 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    have := Real.log_nonneg this
    positivity
  set C : ℝ := κ / (1 - α) * (4 + Real.sqrt A) + κ / (1 - β) * (4 + Real.sqrt A) with hCdef
  have hC0 : 0 ≤ C := by
    have h1 : 0 < 1 - α := by linarith
    have h2 : 0 < 1 - β := by linarith
    positivity
  have hpow : ∀ N : ℕ, 1 ≤ N → ((N : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt N := by
    intro N hN
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [Real.rpow_neg hN0, Real.sqrt_eq_rpow, one_div]
    norm_num
  have hη : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      etaNM κ α β δ n m ≤ C * ((min n m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro n m hn hm
    have hN : 1 ≤ min n m := le_min hn hm
    rw [hpow _ hN]
    unfold etaNM StatFormal.TrimmedMMD.rn
    have h1 := rn_core hN (min_le_left n m) hA
    have h2 := rn_core hN (min_le_right n m) hA
    have ha : 0 ≤ κ / (1 - α) := div_nonneg hκ0 (by linarith)
    have hb : 0 ≤ κ / (1 - β) := div_nonneg hκ0 (by linarith)
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hb
    rw [hCdef]
    calc _ ≤ κ / (1 - α) * ((4 + Real.sqrt A) / Real.sqrt (min n m : ℕ)) +
          κ / (1 - β) * ((4 + Real.sqrt A) / Real.sqrt (min n m : ℕ)) := add_le_add e1 e2
      _ = _ := by ring
  refine ⟨⟨C, hη⟩, Real.sqrt (4 * κ * C) + 2 * C, fun n m hn hm => ?_⟩
  obtain ⟨E, hEm, hEp, hE⟩ := witnessstab_gen 𝒳 H P Q φ κ α β δ n m hφ hκ hα0 hα1 hβ0 hβ1 hn hm hδ0 hδ1
  refine ⟨E, hEm, hEp, fun z hz p dstar hp hmin hdstar => ?_⟩
  obtain ⟨-, b2, b3, -⟩ := hE hz p dstar hp hmin hdstar
  have hN : 1 ≤ min n m := le_min hn hm
  set N : ℝ := ((min n m : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; exact_mod_cast hN
  set η := etaNM κ α β δ n m
  have hη0 : 0 ≤ η := add_nonneg (StatFormal.TrimmedMMD.rn_nonneg hκ0 hα1 _ _)
    (StatFormal.TrimmedMMD.rn_nonneg hκ0 hβ1 _ _)
  have hηle := hη n m hn hm
  have hq : N ^ (-(1 / 2 : ℝ)) = (N ^ (-(1 / 4 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hq0 : 0 ≤ N ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hq1 : N ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hDs : ‖dstar‖ ≤ 2 * κ := hD dstar hdstar.1
  have hs : Real.sqrt (2 * η * ‖dstar‖) ≤ Real.sqrt (4 * κ * C) * N ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.sqrt_sq hq0, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [← hq]
    have := mul_le_mul hηle hDs (norm_nonneg _) (by positivity)
    nlinarith
  have h2η : 2 * η ≤ 2 * C * N ^ (-(1 / 4 : ℝ)) := by
    have : N ^ (-(1 / 2 : ℝ)) ≤ N ^ (-(1 / 4 : ℝ)) := by
      rw [hq]; nlinarith
    nlinarith
  calc ‖witness φ z.1 z.2 p - dstar‖ ≤ _ := b2
    _ ≤ Real.sqrt (2 * η * ‖dstar‖) + 2 * η := b3
    _ ≤ Real.sqrt (4 * κ * C) * N ^ (-(1 / 4 : ℝ)) + 2 * C * N ^ (-(1 / 4 : ℝ)) := add_le_add hs h2η
    _ = (Real.sqrt (4 * κ * C) + 2 * C) * N ^ (-(1 / 4 : ℝ)) := by ring

end StatFormal.Wave30az
