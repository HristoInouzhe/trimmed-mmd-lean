import StatFormal.Archive.Wave29i.Statements
import StatFormal.Lib.TrimmedMean.Population
import StatFormal.Lib.TrimmedMean.Normal
import StatFormal.Lib.TrimmedMean.Density
import StatFormal.Archive.Wave22c.RouteSplit

/-!
# Route — TM `thm:split`: population identification, asymptotic normality, coverage, level (untrusted)

* `split_pop_trimmed`: `Foundations/TrimmedMean/Population` (weak duality `∫ g h ≥ c − β⁻¹ ∫ (c − h)_+`, attained by
  `β⁻¹ 1{h < q} + t 1{h = q}`).
* `split_ass_unique`: `Foundations/TrimmedMean/Density`.
* `split_asymp_normal`: `Foundations/TrimmedMean/{Empirical,Asymp,Normal}` (LP duality for the capped simplex, the
  deterministic asymptotic-linearity inequality, Chebyshev, `clt_two_sample`, Slutsky).
* `split_coverage`: plug-in consistency (`tip0_seHat`), Slutsky + portmanteau (`coverage_lim`).
* `split_level_boot`, `split_level_discharged`, `split_check`: coverage fed into the frozen certified
  `Wave22c.split_level`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave29i

open StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT
open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

theorem split_pop_trimmed : Claims.split_pop_trimmed := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α q q' f hφ hκ hα0 hα1 h1 h2 h3 h4
  exact ⟨iInf_coe_of_isLeast (isLeast_region P hφ hκ hα0 hα1 f h1 h2),
    iSup_coe_of_isGreatest (isGreatest_region Q hφ hκ hα0 hα1 f h3 h4),
    sepVal_eq P Q hφ hκ hα0 hα1 f h1 h2 h3 h4⟩

theorem split_ass_unique : Claims.split_ass_unique := by
  intro 𝒳 _ P _ h B p q hm hB hA
  exact ⟨AssDens.uq hm hA, fun hp => AssDens.var_pos hm hB hA hp⟩

section Core

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ' α q q' κ : ℝ} {f : H}
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : ℕ → Ω → 𝒳} {m : ℕ → ℕ}

lemma sep_eq_of_uq (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ') (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hP : UQ P (fun x => ⟪f, φ x⟫) (1 - α) q) (hQ : UQ Q (fun x => ⟪f, φ x⟫) α q') :
    sepVal f (region φ α P) (region φ α Q) =
      ((popLo P (fun x => ⟪f, φ x⟫) α q - popUp Q (fun x => ⟪f, φ x⟫) α q' : ℝ) : EReal) :=
  sepVal_eq P Q hφ hκ hα0 hα1 f hP.1 hP.2.1 hQ.1 hQ.2.1

/-- Coverage for any standard error with `√n ŝe_n → σ` in probability. -/
lemma cov_core (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ') (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hP : UQ P (fun x => ⟪f, φ x⟫) (1 - α) q) (hQ : UQ Q (fun x => ⟪f, φ x⟫) α q')
    (hX : IIDSample μ P X) (hY : IIDSample μ Q Y) (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ)
    (hκ0 : 0 < κ) (hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ))
    (hσ : 0 < sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ) {se : ℕ → Ω → ℝ} (hsem : ∀ n, Measurable (se n))
    (hcons : TIP0 μ (fun n ω => √(n : ℝ) * se n ω - √(sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ))) (z : ℝ) :
    Tendsto (fun n => μ.real {ω | ((splitStat φ f X Y m α n ω - z * se n ω : ℝ) : EReal) ≤
      sepVal f (region φ α P) (region φ α Q)}) atTop (𝓝 ((gaussianReal 0 1).real (Iic z))) := by
  have hm := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have clt := clt_split hX hY hXY hm hB hα0 hα1 hκ0 hmr hP hQ
  set s2 := sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ
  have hσ' : 0 < √s2 := Real.sqrt_pos.2 hσ
  have hv : (√s2 ^ 2).toNNReal = s2.toNNReal := by rw [Real.sq_sqrt hσ.le]
  rw [← hv] at clt
  have key := coverage_lim hσ' clt hcons (fun n => (hsem n).const_mul _) z
  have hsep := sep_eq_of_uq hφ hκ hα0 hα1 hP hQ
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  congr 1
  ext ω
  simp only [mem_setOf_eq]
  rw [hsep, EReal.coe_le_coe_iff]
  change √(n : ℝ) * (statT X Y (fun x => ⟪f, φ x⟫) m α n ω - _) - z * (√(n : ℝ) * se n ω) ≤ 0 ↔
    statT X Y (fun x => ⟪f, φ x⟫) m α n ω - z * se n ω ≤ _
  set T := statT X Y (fun x => ⟪f, φ x⟫) m α n ω
  rw [show √(n : ℝ) * (T - (popLo P (fun x => ⟪f, φ x⟫) α q - popUp Q (fun x => ⟪f, φ x⟫) α q')) -
      z * (√(n : ℝ) * se n ω) = √(n : ℝ) * ((T - z * se n ω) -
        (popLo P (fun x => ⟪f, φ x⟫) α q - popUp Q (fun x => ⟪f, φ x⟫) α q')) by ring]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have := mul_pos hs (sub_pos.2 hc)
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith)

/-- Coverage ⇒ the frozen level statement's conclusions, through the certified `Wave22c.split_level`. -/
lemma level_of_cov (hlevel : StatFormal.Wave22c.Claims.split_level) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ') (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hP : UQ P (fun x => ⟪f, φ x⟫) (1 - α) q) (hQ : UQ Q (fun x => ⟪f, φ x⟫) α q')
    {Tlo : ℕ → Ω → ℝ} (hTm : ∀ n, Measurable (Tlo n)) {δ z : ℝ} (hz : (gaussianReal 0 1).real (Ioi z) = δ)
    (hcov : Tendsto (fun n => μ.real {ω | ((Tlo n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)}) atTop
      (𝓝 ((gaussianReal 0 1).real (Iic z)))) :
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω | ((Tlo n ω : ℝ) : EReal) ≤
        sepVal f (region φ α P) (region φ α Q)}) ∧
    (StatFormal.Distances.tvDist P Q ≤ α →
        ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, μ {ω | 0 < Tlo n ω} ≤ ENNReal.ofReal (δ + η)) ∧
    (∀ n, ∀ ω, ((Tlo n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q) → 0 < Tlo n ω →
        α < StatFormal.Distances.tvDist P Q) := by
  have hΦ : (gaussianReal 0 1).real (Iic z) = 1 - δ := by
    rw [← hz, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; ring
  rw [hΦ] at hcov
  have h1 : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω | ((Tlo n ω : ℝ) : EReal) ≤
      sepVal f (region φ α P) (region φ α Q)} := fun η hη =>
    (hcov.eventually (Ioi_mem_nhds (show 1 - δ - η < 1 - δ by linarith))).mono fun n hn => le_of_lt hn
  have hsep := sep_eq_of_uq hφ hκ hα0 hα1 hP hQ
  have hEm : ∀ n, MeasurableSet {ω | ((Tlo n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)} := fun n => by
    simp only [hsep, EReal.coe_le_coe_iff]
    exact measurableSet_le (hTm n) measurable_const
  obtain ⟨a, b⟩ := hlevel 𝒳 H P Q φ κ' α δ f Ω (fun _ => μ) Tlo
    (fun n => {ω | ((Tlo n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)}) hφ hκ hα0 hα1
    (fun _ => inferInstance) hEm (fun n ω hω => hω) h1
  exact ⟨h1, a, fun n ω hω hpos => b n ω hω hpos⟩

lemma tip0_of_ratio {se : ℕ → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (h : TendstoInMeasure μ (fun n ω => se n ω / (σ / √(n : ℝ))) atTop (fun _ => 1)) :
    TIP0 μ (fun n ω => √(n : ℝ) * se n ω - σ) := by
  have h0 : TIP0 μ (fun n ω => se n ω / (σ / √(n : ℝ)) - 1) := by
    intro ε hε
    have := (tendstoInMeasure_iff_norm.1 h) ε hε
    simpa only [Real.norm_eq_abs] using this
  refine (h0.const_mul σ).congr ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp

end Core

theorem split_asymp_normal : Claims.split_asymp_normal := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ f Ω _ μ _ X Y m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr
  refine ⟨_, sep_eq_of_uq hφ hκ hα0 hα1 hP hQ, ?_⟩
  exact clt_split ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ hXY (measurable_inner_comp hφ f) (abs_inner_le hκ f) hα0 hα1
    hκ0 hmr hP hQ

theorem split_coverage : Claims.split_coverage := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ f Ω _ μ _ X Y m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr
    hσ z
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  exact cov_core hφ hκ hα0 hα1 hP hQ hX hY hXY hκ0 hmr hσ (fun n => measurable_seHat hX hY hm α m n)
    (tip0_seHat hX hY hm (abs_inner_le hκ f) hα0 hα1 hκ0 hmr hP hQ hσ) z

lemma sigma2_pos {𝒳 : Type} [MeasurableSpace 𝒳] {P Q : Measure 𝒳} [IsProbabilityMeasure P]
    {h : 𝒳 → ℝ} (hm : Measurable h) {B α q q' κ : ℝ} (hB : ∀ x, |h x| ≤ B) (hα0 : 0 < α) (hα1 : α < 1)
    (hκ : 0 < κ) (hA : AssDens P h (1 - α) q) : 0 < sigma2 P Q h α q q' κ := by
  have hv := AssDens.var_pos hm hB hA (by linarith)
  have hβ : 0 < 1 - α := by linarith
  unfold sigma2
  exact div_pos (add_pos_of_pos_of_nonneg hv (div_nonneg (variance_nonneg _ _) hκ.le)) (by positivity)

/-- Route check (not a target): the frozen conditional `Wave22c.split_level` plus the coverage claim. -/
theorem split_check : StatFormal.Wave22c.Claims.split_level → Claims.split_coverage →
    Claims.split_level_discharged := by
  intro hlevel hcov
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ δ z f Ω _ μ _ X Y m hφ hκ hα0 hα1 hAP hAQ hXm hYm hXi hYi hXY hXl hYl
    hκ0 hmr hz
  have hm := measurable_inner_comp hφ f
  have hP : UQ P (fun x => ⟪f, φ x⟫) (1 - α) q := AssDens.uq hm hAP
  have hQ : UQ Q (fun x => ⟪f, φ x⟫) α q' := AssDens.uq hm hAQ
  have hσ := sigma2_pos (Q := Q) (q' := q') hm (abs_inner_le hκ f) hα0 hα1 hκ0 hAP
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hc := hcov 𝒳 H P Q φ κ' α q q' κ f Ω μ X Y m hφ hκ hα0.le hα1 hP hQ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr hσ z
  exact level_of_cov hlevel hφ hκ hα0.le hα1 hP hQ
    (fun n => (measurable_statT hX hY hm hα0.le hα1 m n).sub
      ((measurable_seHat hX hY hm α m n).const_mul z)) hz hc

theorem split_level_discharged : Claims.split_level_discharged :=
  split_check StatFormal.Wave22c.split_level split_coverage

theorem split_level_boot : Claims.split_level_boot := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ δ z f Ω _ μ _ X Y m se hφ hκ hα0 hα1 hAP hAQ hXm hYm hXi hYi hXY hXl
    hYl hκ0 hmr hsem hrat hz
  have hm := measurable_inner_comp hφ f
  have hP : UQ P (fun x => ⟪f, φ x⟫) (1 - α) q := AssDens.uq hm hAP
  have hQ : UQ Q (fun x => ⟪f, φ x⟫) α q' := AssDens.uq hm hAQ
  have hσ := sigma2_pos (Q := Q) (q' := q') hm (abs_inner_le hκ f) hα0 hα1 hκ0 hAP
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hcons := tip0_of_ratio (Real.sqrt_pos.2 hσ) hrat
  have hc := cov_core hφ hκ hα0.le hα1 hP hQ hX hY hXY hκ0 hmr hσ hsem hcons z
  exact level_of_cov StatFormal.Wave22c.split_level hφ hκ hα0.le hα1 hP hQ
    (fun n => (measurable_statT hX hY hm hα0.le hα1 m n).sub ((hsem n).const_mul z)) hz hc

end StatFormal.Wave29i

namespace StatFormal.Wave29i

open MeasureTheory Set

/-- Non-vacuity of `ass:split` as encoded (`splitAss`): the uniform law on `[0, 1]`, `h = id`, level and quantile
`1/2`, density `ρ ≡ 1` on `(0, 1)`. -/
lemma splitAss_uniform : splitAss (volume.restrict (Set.Icc (0:ℝ) 1)) id (1/2) (1/2) := by
  have hhalf' : volume.restrict (Set.Icc (0:ℝ) 1) (Set.Iio (1/2)) = ENNReal.ofReal (1/2) := by
    rw [Measure.restrict_apply measurableSet_Iio]
    have : Set.Iio (1/2 : ℝ) ∩ Set.Icc 0 1 = Set.Ico 0 (1/2) := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Ico]; norm_num
  refine ⟨?_, ?_, 1/2, by norm_num, fun _ => 1, measurable_const, fun _ _ => one_pos, ?_⟩
  · change (volume.restrict (Set.Icc (0:ℝ) 1) (Set.Iio (1/2))).toReal ≤ 1/2
    rw [hhalf']; norm_num
  · change 1/2 ≤ (volume.restrict (Set.Icc (0:ℝ) 1) (Set.Iic (1/2))).toReal
    have : volume.restrict (Set.Icc (0:ℝ) 1) (Set.Iic (1/2)) = ENNReal.ofReal (1/2) := by
      rw [Measure.restrict_apply measurableSet_Iic]
      have : Set.Iic (1/2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1/2) := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
      rw [this, Real.volume_Icc]; norm_num
    rw [this]; norm_num
  · intro a b ha hb
    change volume.restrict (Set.Icc (0:ℝ) 1) (Set.Ioc a b) = _
    rw [Measure.restrict_apply measurableSet_Ioc, setLIntegral_const, ENNReal.ofReal_one, one_mul]
    congr 1
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by linarith [h.1], by linarith [h.2]⟩

end StatFormal.Wave29i
