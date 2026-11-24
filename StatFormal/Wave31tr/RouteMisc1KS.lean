import StatFormal.Wave31tr.Statements
import StatFormal.Lib.KernelFacts.OneSidedKS
import StatFormal.Wave30tn.RouteSplitFS

/-!
# Wave 31tr, chunk M1: `tv_one_sided_ks`, `ks_lower_confidence` (T28)

(a) `(x₀, ∞)` is a Hahn set of `P − Q` under the sign hypotheses (`KernelFacts.tvDist_eq_of_hahn_set`), so `TV = P(R) − Q(R)`, and
the one-sided Kolmogorov distance attains it at `x₀`. (b) the one-sided DKW–Massart bounds (`KernelFacts.dkw_upper_real`,
`dkw_lower_real`) at `t_k = √(log(2/δ)/(2k))`, each of probability `≤ δ/2`, the KS stability `iSup_tail_sub_le_add`, a union bound
and a measurable hull (`exists_measurable_compl_of_le`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteMisc1

open StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.TrimmedMMD.Concentration

theorem tv_one_sided_ks_route : Claims.tv_one_sided_ks := by
  intro P Q _ _ p q x₀ hp hq hP hQ h1 h2
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ x₀ := by
    rw [ae_iff]; simp
  have hA1 : ∀ A, MeasurableSet A → A ⊆ Ioi x₀ → Q A ≤ P A := by
    intro A hA hAR
    rw [hP, hQ]
    refine KernelFacts.withDensity_le_withDensity_on volume ?_ hA hAR
    filter_upwards [h1] with x hx hxR using ENNReal.ofReal_le_ofReal (hx hxR)
  have hA2 : ∀ A, MeasurableSet A → A ⊆ (Ioi x₀)ᶜ → P A ≤ Q A := by
    intro A hA hAR
    rw [hP, hQ]
    refine KernelFacts.withDensity_le_withDensity_on volume ?_ hA hAR
    filter_upwards [h2, hne] with x hx hx0 hxR
    exact ENNReal.ofReal_le_ofReal (hx (lt_of_le_of_ne (not_lt.1 hxR) hx0))
  have htv := KernelFacts.tvDist_eq_of_hahn_set P Q measurableSet_Ioi hA1 hA2
  have hcdf : StatFormal.Distances.tvDist P Q = Q.real (Iic x₀) - P.real (Iic x₀) := by
    rw [htv, KernelFacts.tail_sub_eq_cdf_sub]
  have hle : ∀ x, P.real (Ioi x) - Q.real (Ioi x) ≤ StatFormal.Distances.tvDist P Q := fun x =>
    (le_abs_self _).trans (StatFormal.Distances.abs_measureReal_sub_le_tvDist measurableSet_Ioi)
  refine ⟨htv, hcdf, ?_, ?_⟩
  · refine (KernelFacts.ciSup_eq_of_le_of_eq (fun x => ?_) x₀ hcdf.symm).symm
    rw [← KernelFacts.tail_sub_eq_cdf_sub]; exact hle x
  · exact (KernelFacts.ciSup_eq_of_le_of_eq (F := fun x : ℝ => P.real (Ioi x) - Q.real (Ioi x)) hle x₀ htv.symm).symm

/-- `2 exp(−2k t_k²) = δ`, i.e. `exp(−2k t_k²) = δ/2`, for `t_k = ksRadius δ k`. -/
lemma exp_ksRadius {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Real.exp (-2 * k * ksRadius δ k ^ 2) = δ / 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  unfold ksRadius
  rw [Real.sq_sqrt (by positivity)]
  have : -2 * (k : ℝ) * (Real.log (2 / δ) / (2 * k)) = Real.log (δ / 2) := by
    rw [show δ / 2 = (2 / δ)⁻¹ by field_simp, Real.log_inv]; field_simp
  rw [this, Real.exp_log (by positivity)]

lemma ksRadius_nonneg (δ : ℝ) (k : ℕ) : 0 ≤ ksRadius δ k := Real.sqrt_nonneg _

lemma ksRadius_le_min {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) (δ : ℝ) :
    ksRadius δ k ≤ √(Real.log (2 / δ) / 2) / √((min k j : ℕ) : ℝ) := by
  unfold ksRadius
  have hmin : (0 : ℝ) < ((min k j : ℕ) : ℝ) := by exact_mod_cast (show 0 < min k j by omega)
  have hle : ((min k j : ℕ) : ℝ) ≤ k := by exact_mod_cast min_le_left k j
  rcases le_or_gt (Real.log (2 / δ) / 2) 0 with hL | hL
  · rw [Real.sqrt_eq_zero'.2 (by
      rw [show Real.log (2 / δ) / (2 * k) = (Real.log (2 / δ) / 2) / k by ring]
      exact div_nonpos_of_nonpos_of_nonneg hL (Nat.cast_nonneg _))]
    positivity
  rw [show Real.log (2 / δ) / (2 * k) = (Real.log (2 / δ) / 2) / k by ring, Real.sqrt_div hL.le]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.sqrt_pos.2 hmin) (Real.sqrt_le_sqrt hle)

/-- The four one-sided deviation events, each of probability at most `δ/2`. -/
lemma dev_bounds (R : Measure ℝ) [IsProbabilityMeasure R] {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin k => R) {y | ∃ u : ℝ, ksRadius δ k < R.real (Iic u) - (empirical y).real (Iic u)} ≤
      ENNReal.ofReal (δ / 2) ∧
    (Measure.pi fun _ : Fin k => R) {y | ∃ u : ℝ, ksRadius δ k < (empirical y).real (Iic u) - R.real (Iic u)} ≤
      ENNReal.ofReal (δ / 2) := by
  have e1 : ∀ (y : Fin k → ℝ) u, (empirical y).real (Iic u) = ((Finset.univ.filter fun i => y i ≤ u).card : ℝ) / k :=
    fun y u => Wave30tn.empirical_real_Iic hk y u
  simp_rw [e1]
  rw [← exp_ksRadius hk hδ0 hδ1]
  exact ⟨KernelFacts.dkw_lower_real R hk (ksRadius_nonneg δ k), KernelFacts.dkw_upper_real R hk (ksRadius_nonneg δ k)⟩

lemma sampleLaw_fst (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) (N : Set (Fin n → ℝ)) :
    sampleLaw P Q n m (N ×ˢ univ) = (Measure.pi fun _ : Fin n => P) N := by
  unfold sampleLaw; rw [Measure.prod_prod, measure_univ, mul_one]

lemma sampleLaw_snd (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) (N : Set (Fin m → ℝ)) :
    sampleLaw P Q n m (univ ×ˢ N) = (Measure.pi fun _ : Fin m => Q) N := by
  unfold sampleLaw; rw [Measure.prod_prod, measure_univ, one_mul]

theorem ks_lower_confidence_route : Claims.ks_lower_confidence := by
  intro P Q _ _ n m δ hn hm hδ0 hδ1
  haveI : IsProbabilityMeasure (sampleLaw P Q n m) := by unfold sampleLaw; infer_instance
  set tn := ksRadius δ n
  set tm := ksRadius δ m
  set NXlo := {y : Fin n → ℝ | ∃ u : ℝ, tn < P.real (Iic u) - (empirical y).real (Iic u)}
  set NXup := {y : Fin n → ℝ | ∃ u : ℝ, tn < (empirical y).real (Iic u) - P.real (Iic u)}
  set NYlo := {y : Fin m → ℝ | ∃ u : ℝ, tm < Q.real (Iic u) - (empirical y).real (Iic u)}
  set NYup := {y : Fin m → ℝ | ∃ u : ℝ, tm < (empirical y).real (Iic u) - Q.real (Iic u)}
  obtain ⟨bXlo, bXup⟩ := dev_bounds P hn hδ0 hδ1
  obtain ⟨bYlo, bYup⟩ := dev_bounds Q hm hδ0 hδ1
  have half : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  -- the event of the lower bound
  set N1 := NXlo ×ˢ (univ : Set (Fin m → ℝ)) ∪ (univ : Set (Fin n → ℝ)) ×ˢ NYup
  have hN1 : sampleLaw P Q n m N1 ≤ ENNReal.ofReal δ := by
    refine (measure_union_le _ _).trans ?_
    rw [sampleLaw_fst, sampleLaw_snd, ← half]
    exact add_le_add bXlo bYup
  obtain ⟨E1, hE1m, hE1p, hE1N⟩ := KernelFacts.exists_measurable_compl_of_le _ hδ0.le hN1
  have lower : ∀ ω ∈ E1, ksPlus (empirical ω.1) (empirical ω.2) id - tn - tm ≤ ksPlus P Q id := by
    intro ω hω
    haveI := Wave30tn.isProbabilityMeasure_empirical' ω.1 hn
    haveI := Wave30tn.isProbabilityMeasure_empirical' ω.2 hm
    have hω' := hE1N hω
    simp only [N1, mem_compl_iff, mem_union, mem_prod, mem_univ, and_true, true_and, not_or] at hω'
    have hX : ∀ u, P.real (Iic u) - (empirical ω.1).real (Iic u) ≤ tn := fun u => by
      by_contra h; exact hω'.1 ⟨u, not_le.1 h⟩
    have hY : ∀ u, (empirical ω.2).real (Iic u) - Q.real (Iic u) ≤ tm := fun u => by
      by_contra h; exact hω'.2 ⟨u, not_le.1 h⟩
    have := KernelFacts.iSup_tail_sub_le_add P Q (empirical ω.1) (empirical ω.2) hX hY
    show (⨆ x : ℝ, ((empirical ω.1).real (Ioi x) - (empirical ω.2).real (Ioi x))) - tn - tm ≤
      ⨆ x : ℝ, (P.real (Ioi x) - Q.real (Ioi x))
    linarith
  have ksle : ksPlus P Q id ≤ StatFormal.Distances.tvDist P Q := KernelFacts.iSup_tail_sub_le_tvDist P Q
  -- the two-sided event
  set N2 := N1 ∪ (NXup ×ˢ (univ : Set (Fin m → ℝ)) ∪ (univ : Set (Fin n → ℝ)) ×ˢ NYlo)
  have hN2 : sampleLaw P Q n m N2 ≤ ENNReal.ofReal (2 * δ) := by
    have h2 : sampleLaw P Q n m (NXup ×ˢ (univ : Set (Fin m → ℝ)) ∪ (univ : Set (Fin n → ℝ)) ×ˢ NYlo) ≤
        ENNReal.ofReal δ := by
      refine (measure_union_le _ _).trans ?_
      rw [sampleLaw_fst, sampleLaw_snd, ← half]; exact add_le_add bXup bYlo
    refine (measure_union_le _ _).trans ((add_le_add hN1 h2).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add hδ0.le hδ0.le]; ring_nf
  obtain ⟨E2, hE2m, hE2p, hE2N⟩ := KernelFacts.exists_measurable_compl_of_le _ (by positivity) hN2
  refine ⟨⟨E1, hE1m, hE1p, lower⟩, ksle, ⟨E1, hE1m, hE1p, fun ω hω => (lower ω hω).trans ksle⟩,
    ⟨E2, hE2m, hE2p, fun ω hω => ?_⟩, ?_⟩
  · have hω1 : ω ∈ E1 ∨ True := Or.inr trivial
    have hωN := hE2N hω
    have hω1' : ω ∈ N1ᶜ := fun h => hωN (Or.inl h)
    haveI := Wave30tn.isProbabilityMeasure_empirical' ω.1 hn
    haveI := Wave30tn.isProbabilityMeasure_empirical' ω.2 hm
    have hω2 : ω ∉ NXup ×ˢ (univ : Set (Fin m → ℝ)) ∪ (univ : Set (Fin n → ℝ)) ×ˢ NYlo := fun h => hωN (Or.inr h)
    simp only [N1, mem_compl_iff, mem_union, mem_prod, mem_univ, and_true, true_and, not_or] at hω1' hω2
    have hX : ∀ u, P.real (Iic u) - (empirical ω.1).real (Iic u) ≤ tn := fun u => by
      by_contra h; exact hω1'.1 ⟨u, not_le.1 h⟩
    have hY : ∀ u, (empirical ω.2).real (Iic u) - Q.real (Iic u) ≤ tm := fun u => by
      by_contra h; exact hω1'.2 ⟨u, not_le.1 h⟩
    have hX' : ∀ u, (empirical ω.1).real (Iic u) - P.real (Iic u) ≤ tn := fun u => by
      by_contra h; exact hω2.1 ⟨u, not_le.1 h⟩
    have hY' : ∀ u, Q.real (Iic u) - (empirical ω.2).real (Iic u) ≤ tm := fun u => by
      by_contra h; exact hω2.2 ⟨u, not_le.1 h⟩
    have a1 := KernelFacts.iSup_tail_sub_le_add P Q (empirical ω.1) (empirical ω.2) hX hY
    have a2 := KernelFacts.iSup_tail_sub_le_add (empirical ω.1) (empirical ω.2) P Q hX' hY'
    show (⨆ x : ℝ, ((empirical ω.1).real (Ioi x) - (empirical ω.2).real (Ioi x))) - tn - tm ≤
        (⨆ x : ℝ, (P.real (Ioi x) - Q.real (Ioi x))) ∧
      (⨆ x : ℝ, (P.real (Ioi x) - Q.real (Ioi x))) ≤
        (⨆ x : ℝ, ((empirical ω.1).real (Ioi x) - (empirical ω.2).real (Ioi x))) - tn - tm + 2 * (tn + tm)
    constructor <;> linarith
  · have h1 := ksRadius_le_min hn hm δ
    have h2 := ksRadius_le_min hm hn δ
    rw [min_comm m n] at h2
    have : 2 * (tn + tm) ≤ 2 * (√(Real.log (2 / δ) / 2) / √((min n m : ℕ) : ℝ) +
        √(Real.log (2 / δ) / 2) / √((min n m : ℕ) : ℝ)) := by linarith
    refine this.trans (le_of_eq ?_)
    ring

end StatFormal.Wave31tr.RouteMisc1
