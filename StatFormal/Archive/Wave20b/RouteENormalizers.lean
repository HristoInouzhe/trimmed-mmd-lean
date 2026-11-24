import StatFormal.Archive.Wave20b.Statements
import TauCeti.InformationTheory.KullbackLeibler.ChangeOfReference
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Route — ICL `lem:e-normalizers` (untrusted)

* Compact-parametric Glivenko–Cantelli principle (`uniform_slln`): for `F` continuous on `Θ × 𝒵` (both compact),
  the strong law (`strong_law_ae`) at the points of a countable dense subset of `Θ`, uniform continuity
  (Heine–Cantor) and a finite subcover upgrade pointwise to uniform a.s. convergence.
* For a density `φ ∈ [m, M]`, `m > 0`, `∫ φ dν = 1`: `KL(φ ν ‖ ν) = ∫ φ log φ dν < ∞` (`llr_withDensity_exp`);
  with `φ = s_θ / c` this is `P(s log s)/P s − log P s`, both for `P₀` and for `P_n` (`μ_{θ,n} = P_n.withDensity`).
* `(a, c) ↦ a/c − log c` is uniformly continuous on `c ≥ s_−`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave20b

section SLLN
variable {Θ 𝒵 Ω : Type} [MetricSpace Θ] [CompactSpace Θ] [MetricSpace 𝒵] [CompactSpace 𝒵]
  [MeasurableSpace 𝒵] [BorelSpace 𝒵] [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
  {P0 : Measure 𝒵} [IsProbabilityMeasure P0] {Zs : ℕ → Ω → 𝒵}

lemma bound_of_continuous_compact {X : Type} [TopologicalSpace X] [CompactSpace X] {f : X → ℝ}
    (hf : Continuous f) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x (mem_univ x)⟩

/-- Pointwise strong law along the nested samples. -/
lemma slln_point (hZ : ∀ j, Measurable (Zs j)) (hind : iIndepFun Zs Pr) (hlaw : ∀ j, Pr.map (Zs j) = P0)
    {f : 𝒵 → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => empAvg Zs n f ω) atTop (𝓝 (∫ z, f z ∂P0)) := by
  obtain ⟨C, hC⟩ := bound_of_continuous_compact hf
  have hfm : Measurable f := hf.measurable
  set X : ℕ → Ω → ℝ := fun j ω => f (Zs j ω)
  have hint : Integrable (X 0) Pr := Integrable.of_bound (hfm.comp (hZ 0)).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)
  have hindep : Pairwise fun i j => IndepFun (X i) (X j) Pr := fun i j hij =>
    (hind.indepFun hij).comp hfm hfm
  have hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr := fun i =>
    (IdentDistrib.mk (hZ i).aemeasurable (hZ 0).aemeasurable (by rw [hlaw i, hlaw 0])).comp hfm
  have hmean : Pr[X 0] = ∫ z, f z ∂P0 := by
    simp only [X]
    rw [← hlaw 0, integral_map (hZ 0).aemeasurable hfm.aestronglyMeasurable]
  filter_upwards [strong_law_ae X hint hindep hident] with ω hω
  rw [hmean] at hω
  have h1 := (tendsto_add_atTop_iff_nat 1).mpr hω
  refine h1.congr fun n => ?_
  simp only [X, empAvg, smul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- **Compact-parametric Glivenko–Cantelli.** -/
theorem uniform_slln (hZ : ∀ j, Measurable (Zs j)) (hind : iIndepFun Zs Pr) (hlaw : ∀ j, Pr.map (Zs j) = P0)
    {F : Θ → 𝒵 → ℝ} (hF : Continuous (Function.uncurry F)) :
    ∀ᵐ ω ∂Pr, TendstoUniformly (fun n θ => empAvg Zs n (F θ) ω) (fun θ => ∫ z, F θ z ∂P0) atTop := by
  have hFθ : ∀ θ, Continuous (F θ) := fun θ => hF.comp (continuous_const.prodMk continuous_id)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Θ
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ω ∂Pr, ∀ d : D, Tendsto (fun n => empAvg Zs n (F d) ω) atTop (𝓝 (∫ z, F d z ∂P0)) :=
    ae_all_iff.mpr fun d => slln_point hZ hind hlaw (hFθ d)
  have huc := CompactSpace.uniformContinuous_of_continuous hF
  rw [Metric.uniformContinuous_iff] at huc
  filter_upwards [hall] with ω hω
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδF⟩ := huc (ε / 3) (by positivity)
  have hclose : ∀ θ θ' : Θ, dist θ θ' < δ → ∀ z, |F θ z - F θ' z| ≤ ε / 3 := by
    intro θ θ' h z
    have := hδF (a := (θ, z)) (b := (θ', z)) (by simpa [Prod.dist_eq] using h)
    exact (by simpa [Real.dist_eq] using this.le)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun d : D => Metric.ball (d : Θ) δ)
    (fun _ => Metric.isOpen_ball) (fun θ _ => by
      obtain ⟨d, hdD, hd⟩ := hDd.exists_dist_lt θ hδ
      exact mem_iUnion.mpr ⟨⟨d, hdD⟩, by rw [Metric.mem_ball]; exact hd⟩)
  have hev : ∀ᶠ n in atTop, ∀ d ∈ t, |empAvg Zs n (F d) ω - ∫ z, F d z ∂P0| < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro d _
    have := (hω d)
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N, hN⟩ := this (ε / 3) (by positivity)
    exact eventually_atTop.mpr ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  filter_upwards [hev] with n hn θ
  obtain ⟨d, hdt, hd⟩ := mem_iUnion₂.mp (ht (mem_univ θ))
  rw [Metric.mem_ball] at hd
  have h1 : |empAvg Zs n (F θ) ω - empAvg Zs n (F d) ω| ≤ ε / 3 := by
    unfold empAvg
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
    calc ((n : ℝ) + 1)⁻¹ * |∑ j ∈ Finset.range (n + 1), (F θ (Zs j ω) - F d (Zs j ω))|
        ≤ ((n : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), ε / 3 :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hclose θ d hd _)) (by positivity)
      _ = ε / 3 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
  have h2 : |∫ z, F θ z ∂P0 - ∫ z, F d z ∂P0| ≤ ε / 3 := by
    obtain ⟨C1, hC1⟩ := bound_of_continuous_compact (hFθ θ)
    obtain ⟨C2, hC2⟩ := bound_of_continuous_compact (hFθ d)
    rw [← integral_sub (Integrable.of_bound (hFθ θ).aestronglyMeasurable C1 (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hC1 z))
      (Integrable.of_bound (hFθ d).aestronglyMeasurable C2 (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hC2 z))]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ z, |F θ z - F d z| ∂P0 ≤ ∫ _z, ε / 3 ∂P0 :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun z => hclose θ d hd z)
      _ = ε / 3 := by rw [integral_const, probReal_univ, one_smul]
  have h3 := hn d hdt
  rw [Real.dist_eq, abs_sub_comm]
  calc |empAvg Zs n (F θ) ω - ∫ z, F θ z ∂P0|
      ≤ |empAvg Zs n (F θ) ω - empAvg Zs n (F d) ω| + |empAvg Zs n (F d) ω - ∫ z, F d z ∂P0| +
          |∫ z, F d z ∂P0 - ∫ z, F θ z ∂P0| := by
        have := abs_sub_le (empAvg Zs n (F θ) ω) (empAvg Zs n (F d) ω) (∫ z, F θ z ∂P0)
        have := abs_sub_le (empAvg Zs n (F d) ω) (∫ z, F d z ∂P0) (∫ z, F θ z ∂P0)
        linarith
    _ < ε := by rw [abs_sub_comm (∫ z, F d z ∂P0)]; linarith

end SLLN

/-! ### Relative entropy of a bounded density -/

section KL
variable {𝒵 : Type} [MeasurableSpace 𝒵]

lemma kl_density (ν : Measure 𝒵) [IsProbabilityMeasure ν] {φ : 𝒵 → ℝ} (hφ : Measurable φ) {m M : ℝ}
    (hm : 0 < m) (hφb : ∀ z, m ≤ φ z ∧ φ z ≤ M) (h1 : ∫ z, φ z ∂ν = 1) :
    klDiv (ν.withDensity fun z => ENNReal.ofReal (φ z)) ν ≠ ⊤ ∧
      (klDiv (ν.withDensity fun z => ENNReal.ofReal (φ z)) ν).toReal = ∫ z, φ z * Real.log (φ z) ∂ν := by
  set μ := ν.withDensity fun z => ENNReal.ofReal (φ z) with hμ
  have hpos : ∀ z, 0 < φ z := fun z => lt_of_lt_of_le hm (hφb z).1
  have hφi : Integrable φ ν := Integrable.of_bound hφ.aestronglyMeasurable (max |m| |M|)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (hpos z)]; exact (hφb z).2.trans (le_max_of_le_right (le_abs_self M)))
  have hexp : (fun z => ENNReal.ofReal (φ z)) = fun z => ENNReal.ofReal (Real.exp (Real.log (φ z))) := by
    funext z; rw [Real.exp_log (hpos z)]
  have hllr : llr μ ν =ᵐ[ν] fun z => Real.log (φ z) := by
    rw [hμ, hexp]; exact TauCeti.llr_withDensity_exp hφ.log.aemeasurable
  have hac : μ ≪ ν := withDensity_absolutelyContinuous _ _
  have hllrμ : llr μ ν =ᵐ[μ] fun z => Real.log (φ z) := hac.ae_le hllr
  have huniv : μ Set.univ = 1 := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hφi (Eventually.of_forall fun z => (hpos z).le), h1,
      ENNReal.ofReal_one]
  have : IsProbabilityMeasure μ := ⟨huniv⟩
  have hlogb : ∀ z, |Real.log (φ z)| ≤ |Real.log m| + |Real.log M| := by
    intro z
    have h1 := Real.log_le_log hm (hφb z).1
    have h2 := Real.log_le_log (hpos z) (hφb z).2
    rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log m), le_abs_self (Real.log M), abs_nonneg (Real.log M),
      abs_nonneg (Real.log m)]
  have hint : Integrable (llr μ ν) μ := by
    refine (Integrable.of_bound hφ.log.aestronglyMeasurable (|Real.log m| + |Real.log M|)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hlogb z)).congr hllrμ.symm
  refine ⟨klDiv_ne_top_iff.mpr ⟨hac, hint⟩, ?_⟩
  rw [toReal_klDiv_of_measure_eq hac (by rw [huniv, measure_univ]), integral_congr_ae hllrμ]
  have hd : (fun z => ENNReal.ofReal (φ z)) = fun z => (((φ z).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hμ, hd, integral_withDensity_eq_integral_smul hφ.real_toNNReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hpos z).le]

/-- `∫ (s/c) log(s/c) dν = ν(s log s)/c − log c` when `c = ∫ s dν > 0`. -/
lemma integral_density_log (ν : Measure 𝒵) [IsProbabilityMeasure ν] {s : 𝒵 → ℝ} (hs : Measurable s) {m M : ℝ}
    (hm : 0 < m) (hsb : ∀ z, m ≤ s z ∧ s z ≤ M) :
    ∫ z, s z / (∫ z', s z' ∂ν) * Real.log (s z / (∫ z', s z' ∂ν)) ∂ν =
      (∫ z, s z * Real.log (s z) ∂ν) / (∫ z', s z' ∂ν) - Real.log (∫ z', s z' ∂ν) := by
  set c := ∫ z', s z' ∂ν with hc
  have hpos : ∀ z, 0 < s z := fun z => lt_of_lt_of_le hm (hsb z).1
  have hsi : Integrable s ν := Integrable.of_bound hs.aestronglyMeasurable (max |m| |M|)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (hpos z)]; exact (hsb z).2.trans (le_max_of_le_right (le_abs_self M)))
  have hcpos : 0 < c := by
    have := integral_mono (integrable_const m) hsi fun z => (hsb z).1
    rw [integral_const, probReal_univ, one_smul] at this
    linarith
  have hlogb : ∀ z, |Real.log (s z)| ≤ |Real.log m| + |Real.log M| := by
    intro z
    have h1 := Real.log_le_log hm (hsb z).1
    have h2 := Real.log_le_log (hpos z) (hsb z).2
    rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log m), le_abs_self (Real.log M), abs_nonneg (Real.log M),
      abs_nonneg (Real.log m)]
  have hsl : Integrable (fun z => s z * Real.log (s z)) ν :=
    Integrable.of_bound (hs.mul hs.log).aestronglyMeasurable (max |m| |M| * (|Real.log m| + |Real.log M|))
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos z)]
        exact mul_le_mul ((hsb z).2.trans (le_max_of_le_right (le_abs_self M))) (hlogb z) (abs_nonneg _)
          (le_trans (abs_nonneg m) (le_max_left _ _)))
  have hexp : ∀ z, s z / c * Real.log (s z / c) = (s z * Real.log (s z)) / c - (Real.log c / c) * s z := by
    intro z
    rw [Real.log_div (hpos z).ne' hcpos.ne']
    field_simp
  simp_rw [hexp]
  rw [integral_sub (hsl.div_const c) (hsi.const_mul _), integral_div, integral_const_mul, ← hc]
  field_simp

end KL

/-! ### The empirical measure -/

section Emp
variable {Θ 𝒵 Ω : Type} [MeasurableSpace 𝒵] [MeasurableSingletonClass 𝒵]

lemma integral_empN (Zs : ℕ → Ω → 𝒵) (n : ℕ) (ω : Ω) (f : 𝒵 → ℝ) :
    ∫ z, f z ∂(empN Zs n ω) = empAvg Zs n f ω := by
  unfold empN empAvg
  rw [integral_smul_measure, integral_finsetSum_measure (fun j _ => integrable_dirac enorm_lt_top)]
  simp only [integral_dirac, smul_eq_mul]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast, ENNReal.toReal_one]

lemma isProb_empN (Zs : ℕ → Ω → 𝒵) (n : ℕ) (ω : Ω) : IsProbabilityMeasure (empN Zs n ω) := by
  constructor
  unfold empN
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  push_cast
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

lemma withDensity_finsetSum {ι : Type} (S : Finset ι) (μ : ι → Measure 𝒵) (f : 𝒵 → ℝ≥0∞) :
    (∑ j ∈ S, μ j).withDensity f = ∑ j ∈ S, (μ j).withDensity f := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    ext t ht
    simp [withDensity_apply _ ht]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, withDensity_add_measure, ih]

lemma muEmp_eq (s : Θ → 𝒵 → ℝ) (θ : Θ) (Zs : ℕ → Ω → 𝒵) (n : ℕ) (ω : Ω) (hpos : ∀ z, 0 < s θ z) :
    muEmp s θ Zs n ω = (empN Zs n ω).withDensity
      fun z => ENNReal.ofReal (s θ z / empAvg Zs n (s θ) ω) := by
  unfold muEmp empN
  rw [withDensity_smul_measure, withDensity_finsetSum]
  simp only [dirac_withDensity]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  have hS : 0 < ∑ i ∈ Finset.range (n + 1), s θ (Zs i ω) :=
    Finset.sum_pos (fun i _ => hpos _) ⟨0, by simp⟩
  unfold empAvg
  rw [show ((n : ℝ≥0∞) + 1)⁻¹ = ENNReal.ofReal (((n : ℝ) + 1)⁻¹) by
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]; norm_cast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end Emp

/-! ### Uniform convergence of `a/c − log c` -/

lemma abs_log_sub_log_le {x y m : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hm hy
  have h1 : Real.log x - Real.log y ≤ (x - y) / y := by
    rw [← Real.log_div hx0.ne' hy0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [sub_div, div_self hy0.ne'] at *; linarith
  have h2 : Real.log y - Real.log x ≤ (y - x) / x := by
    rw [← Real.log_div hy0.ne' hx0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [sub_div, div_self hx0.ne'] at *; linarith
  rw [abs_le]
  constructor
  · have : (y - x) / x ≤ |x - y| / m := by
      rw [abs_sub_comm]
      calc (y - x) / x ≤ |y - x| / x := div_le_div_of_nonneg_right (le_abs_self _) hx0.le
        _ ≤ |y - x| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hx
    linarith
  · calc Real.log x - Real.log y ≤ (x - y) / y := h1
      _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
      _ ≤ |x - y| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hy

lemma tendstoUniformly_kl {Θ : Type} {A C : Θ → ℝ} {An Cn : ℕ → Θ → ℝ} {m K : ℝ} (hm : 0 < m)
    (hA : TendstoUniformly An A atTop) (hC : TendstoUniformly Cn C atTop) (hCn : ∀ n θ, m ≤ Cn n θ)
    (hCb : ∀ θ, m ≤ C θ) (hAb : ∀ θ, |A θ| ≤ K) :
    TendstoUniformly (fun n θ => An n θ / Cn n θ - Real.log (Cn n θ))
      (fun θ => A θ / C θ - Real.log (C θ)) atTop := by
  rw [Metric.tendstoUniformly_iff] at *
  intro ε hε
  set L := 2 / m + |K| / m ^ 2 + 1 with hL
  have hLpos : 0 < L := by positivity
  set η := ε / L
  have hη : 0 < η := div_pos hε hLpos
  filter_upwards [hA η hη, hC η hη] with n hAn hCn' θ
  have ha := hAn θ
  have hc := hCn' θ
  rw [Real.dist_eq] at ha hc ⊢
  have hCθ := hCb θ
  have hCnθ := hCn n θ
  have hC0 : 0 < C θ := lt_of_lt_of_le hm hCθ
  have hCn0 : 0 < Cn n θ := lt_of_lt_of_le hm hCnθ
  have e1 : |A θ / C θ - An n θ / Cn n θ| ≤ |A θ - An n θ| / m + |K| * |C θ - Cn n θ| / m ^ 2 := by
    have : A θ / C θ - An n θ / Cn n θ = (A θ - An n θ) / Cn n θ + A θ * (Cn n θ - C θ) / (C θ * Cn n θ) := by
      field_simp; ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hCn0]; exact div_le_div_of_nonneg_left (abs_nonneg _) hm hCnθ
    · rw [abs_div, abs_mul, abs_of_pos (mul_pos hC0 hCn0), abs_sub_comm (Cn n θ)]
      have hmm : m ^ 2 ≤ C θ * Cn n θ := by nlinarith
      calc |A θ| * |C θ - Cn n θ| / (C θ * Cn n θ) ≤ |K| * |C θ - Cn n θ| / (C θ * Cn n θ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ((hAb θ).trans (le_abs_self K)) (abs_nonneg _))
              (by positivity)
        _ ≤ |K| * |C θ - Cn n θ| / m ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hmm
  have e2 := abs_log_sub_log_le hm hCθ hCnθ
  have hsplit : |A θ / C θ - Real.log (C θ) - (An n θ / Cn n θ - Real.log (Cn n θ))| ≤
      |A θ / C θ - An n θ / Cn n θ| + |Real.log (C θ) - Real.log (Cn n θ)| := by
    have := abs_sub (A θ / C θ - An n θ / Cn n θ) (Real.log (C θ) - Real.log (Cn n θ))
    calc _ = |(A θ / C θ - An n θ / Cn n θ) - (Real.log (C θ) - Real.log (Cn n θ))| := by ring_nf
      _ ≤ _ := this
  have hbound : |A θ - An n θ| / m + |K| * |C θ - Cn n θ| / m ^ 2 + |C θ - Cn n θ| / m ≤ η * L - η := by
    have h1 : |A θ - An n θ| / m ≤ η / m := div_le_div_of_nonneg_right ha.le hm.le
    have h2 : |K| * |C θ - Cn n θ| / m ^ 2 ≤ |K| * η / m ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc.le (abs_nonneg _)) (by positivity)
    have h3 : |C θ - Cn n θ| / m ≤ η / m := div_le_div_of_nonneg_right hc.le hm.le
    have : η * L - η = η / m + |K| * η / m ^ 2 + η / m := by rw [hL]; field_simp; ring
    linarith
  have hηL : η * L = ε := by simp only [η]; field_simp
  linarith

theorem e_normalizers : Claims.e_normalizers := by
  intro Θ 𝒵 Ω _ _ _ _ _ _ _ Pr _ P0 _ Zs s sm sp hZ hind hlaw hs hsm hsb
  have hpos : ∀ θ z, 0 < s θ z := fun θ z => lt_of_lt_of_le hsm (hsb θ z).1
  have hsθ : ∀ θ, Continuous (s θ) := fun θ => hs.comp (continuous_const.prodMk continuous_id)
  have hsθm : ∀ θ, Measurable (s θ) := fun θ => (hsθ θ).measurable
  have hZne : Nonempty 𝒵 := nonempty_of_isProbabilityMeasure P0
  obtain ⟨z0⟩ := id hZne
  -- normalisers stay in `[s₋, s₊]`
  have hcpop : ∀ θ, sm ≤ ∫ z, s θ z ∂P0 ∧ ∫ z, s θ z ∂P0 ≤ sp := by
    intro θ
    have hi : Integrable (s θ) P0 := Integrable.of_bound (hsθm θ).aestronglyMeasurable sp
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_pos (hpos θ z)]; exact (hsb θ z).2)
    have h1 := integral_mono (integrable_const sm) hi fun z => (hsb θ z).1
    have h2 := integral_mono hi (integrable_const sp) fun z => (hsb θ z).2
    simp only [integral_const, probReal_univ, one_smul] at h1 h2
    exact ⟨h1, h2⟩
  have hcemp : ∀ θ n ω, sm ≤ empAvg Zs n (s θ) ω ∧ empAvg Zs n (s θ) ω ≤ sp := by
    intro θ n ω
    unfold empAvg
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcard : ((Finset.range (n + 1)).card : ℝ) = (n : ℝ) + 1 := by simp
    constructor
    · have := Finset.card_nsmul_le_sum (Finset.range (n + 1)) (fun j => s θ (Zs j ω)) sm (fun j _ => (hsb θ _).1)
      rw [nsmul_eq_mul, hcard] at this
      rw [le_inv_mul_iff₀ hn]; linarith
    · have := Finset.sum_le_card_nsmul (Finset.range (n + 1)) (fun j => s θ (Zs j ω)) sp (fun j _ => (hsb θ _).2)
      rw [nsmul_eq_mul, hcard] at this
      rw [inv_mul_le_iff₀ hn]; linarith
  -- the density bounds
  have hdens : ∀ (θ : Θ) (c : ℝ), sm ≤ c → c ≤ sp → ∀ z, sm / sp ≤ s θ z / c ∧ s θ z / c ≤ sp / sm := by
    intro θ c hc1 hc2 z
    have hc0 : 0 < c := lt_of_lt_of_le hsm hc1
    have hsp : 0 < sp := lt_of_lt_of_le (hpos θ z) (hsb θ z).2
    constructor
    · exact div_le_div₀ (hpos θ z).le (hsb θ z).1 hc0 hc2
    · exact div_le_div₀ hsp.le (hsb θ z).2 hsm hc1
  have hm : ∀ θ : Θ, 0 < sm / sp := fun θ => div_pos hsm (lt_of_lt_of_le (hpos θ z0) (hsb θ z0).2)
  -- population KL
  have hpop : ∀ θ, klDiv (muPop s θ P0) P0 ≠ ⊤ ∧ (klDiv (muPop s θ P0) P0).toReal =
      (∫ z, s θ z * Real.log (s θ z) ∂P0) / (∫ z, s θ z ∂P0) - Real.log (∫ z, s θ z ∂P0) := by
    intro θ
    have hc := hcpop θ
    have h1 : ∫ z, s θ z / (∫ z', s θ z' ∂P0) ∂P0 = 1 := by
      rw [integral_div]; exact div_self (lt_of_lt_of_le hsm hc.1).ne'
    have hk := kl_density P0 ((hsθm θ).div_const _) (hm θ) (hdens θ _ hc.1 hc.2) h1
    refine ⟨hk.1, ?_⟩
    unfold muPop
    rw [hk.2, integral_density_log P0 (hsθm θ) hsm (hsb θ)]
  -- empirical KL
  have hemp : ∀ θ n ω, klDiv (muEmp s θ Zs n ω) (empN Zs n ω) ≠ ⊤ ∧
      (klDiv (muEmp s θ Zs n ω) (empN Zs n ω)).toReal =
        empAvg Zs n (fun z => s θ z * Real.log (s θ z)) ω / empAvg Zs n (s θ) ω -
          Real.log (empAvg Zs n (s θ) ω) := by
    intro θ n ω
    have := isProb_empN Zs n ω
    have hc := hcemp θ n ω
    have h1 : ∫ z, s θ z / empAvg Zs n (s θ) ω ∂(empN Zs n ω) = 1 := by
      rw [integral_div, integral_empN]; exact div_self (lt_of_lt_of_le hsm hc.1).ne'
    have hk := kl_density (empN Zs n ω) ((hsθm θ).div_const _) (hm θ) (hdens θ _ hc.1 hc.2) h1
    rw [muEmp_eq s θ Zs n ω (hpos θ)]
    refine ⟨hk.1, ?_⟩
    rw [hk.2]
    have := integral_density_log (empN Zs n ω) (hsθm θ) hsm (hsb θ)
    simp only [integral_empN] at this ⊢
    exact this
  refine ⟨fun θ => (hpop θ).1, fun θ n ω => (hemp θ n ω).1, ?_⟩
  have hsl : Continuous (Function.uncurry fun θ z => s θ z * Real.log (s θ z)) :=
    hs.mul (hs.log fun p => (hpos p.1 p.2).ne')
  filter_upwards [uniform_slln hZ hind hlaw hs, uniform_slln hZ hind hlaw hsl] with ω h1 h2
  refine ⟨h1, ?_⟩
  obtain ⟨K, hK⟩ : ∃ K, ∀ θ, |∫ z, s θ z * Real.log (s θ z) ∂P0| ≤ K := by
    obtain ⟨K, hK⟩ := bound_of_continuous_compact hsl
    refine ⟨K, fun θ => (abs_integral_le_integral_abs).trans ?_⟩
    calc ∫ z, |s θ z * Real.log (s θ z)| ∂P0 ≤ ∫ _z, K ∂P0 :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun z => hK (θ, z))
      _ = K := by rw [integral_const, probReal_univ, one_smul]
  have := tendstoUniformly_kl hsm h2 h1 (fun n θ => (hcemp θ n ω).1) (fun θ => (hcpop θ).1) hK
  have e1 : (fun n θ => (klDiv (muEmp s θ Zs n ω) (empN Zs n ω)).toReal) = fun n θ =>
      empAvg Zs n (fun z => s θ z * Real.log (s θ z)) ω / empAvg Zs n (s θ) ω - Real.log (empAvg Zs n (s θ) ω) :=
    funext fun n => funext fun θ => (hemp θ n ω).2
  have e2 : (fun θ => (klDiv (muPop s θ P0) P0).toReal) = fun θ =>
      (∫ z, s θ z * Real.log (s θ z) ∂P0) / (∫ z, s θ z ∂P0) - Real.log (∫ z, s θ z ∂P0) :=
    funext fun θ => (hpop θ).2
  rw [e1, e2]
  exact this

end StatFormal.Wave20b
