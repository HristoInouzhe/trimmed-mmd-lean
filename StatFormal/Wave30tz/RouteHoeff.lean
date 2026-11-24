import StatFormal.Wave30tz.Statements
import StatFormal.Wave30tv.RouteSeq
import Mathlib.Probability.Moments.SubGaussian

/-!
# Wave 30tz route: the conditional Hoeffding lemma for a block pair, and Ville's inequality for products (untrusted)

* `two_point_hoeffding`: Hoeffding's lemma for the two-point law on `{−1, 1}` with mean `d`:
  `e^{−rd}(cosh r + d sinh r) ≤ e^{r²/2}` (Mathlib's `hasSubgaussianMGF_of_mem_Icc`).
* `hoeff_cond`: for the pair statistic `Z_k` and its conditional mean `Δ_k` given the coordinates known before pair `k`,
  and `V ≥ 0`, `r` bounded functions of those coordinates, `E[V e^{r(Z_k − Δ_k)}] ≤ E[V e^{r²/2}]`
  (convexity `e^{rz} ≤ cosh r + z sinh r` on `[−1,1]`, then `E[W Z_k] = E[W Δ_k]` by freezing, `integral_mul_pairZ`).
* `prod_ville`: nonnegative bounded factors `F_k`, functions of the coordinates known after pair `k`, with
  `E[V F_k] ≤ E[V]` for every bounded nonnegative function `V` of the coordinates known before pair `k`:
  `a · P(∃ t ≤ N, ∏_{k<t} F_k ≥ a) ≤ 1` (`betting_ville_pred` with `Λ_k = 1`, `Y_k = F_k − 1`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Betting

/-- Hoeffding's lemma for the two-point law `((1+d)/2) δ_1 + ((1−d)/2) δ_{−1}`. -/
lemma two_point_hoeffding {d : ℝ} (hd1 : -1 ≤ d) (hd2 : d ≤ 1) (r : ℝ) :
    (1 + d) / 2 * Real.exp (r * (1 - d)) + (1 - d) / 2 * Real.exp (r * (-1 - d)) ≤ Real.exp (r ^ 2 / 2) := by
  set p := (1 + d) / 2 with hpdef
  set q := (1 - d) / 2 with hqdef
  have hp : 0 ≤ p := by rw [hpdef]; linarith
  have hq : 0 ≤ q := by rw [hqdef]; linarith
  set μ : Measure ℝ := ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal q • Measure.dirac (-1) with hμ
  have hμp : IsProbabilityMeasure μ := by
    constructor
    simp only [hμ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp hq]
    have : p + q = 1 := by rw [hpdef, hqdef]; ring
    rw [this, ENNReal.ofReal_one]
  have hint : ∀ f : ℝ → ℝ, Integrable f μ := fun f => by
    have h1 : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun a =>
      (integrable_const (f a)).congr (ae_eq_dirac f).symm
    exact ((h1 1).smul_measure ENNReal.ofReal_ne_top).add_measure ((h1 (-1)).smul_measure ENNReal.ofReal_ne_top)
  have hI : ∀ f : ℝ → ℝ, ∫ x, f x ∂μ = p * f 1 + q * f (-1) := fun f => by
    have h1 : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun a =>
      (integrable_const (f a)).congr (ae_eq_dirac f).symm
    rw [hμ, integral_add_measure ((h1 1).smul_measure ENNReal.ofReal_ne_top)
      ((h1 (-1)).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, smul_eq_mul, smul_eq_mul]
  have hb : ∀ᵐ x ∂μ, (fun x : ℝ => x) x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hμ, ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      exact (ae_dirac_iff (p := fun x : ℝ => x ∈ Set.Icc (-1 : ℝ) 1) measurableSet_Icc).2 (by norm_num)
    · refine Measure.ae_smul_measure ?_ _
      exact (ae_dirac_iff (p := fun x : ℝ => x ∈ Set.Icc (-1 : ℝ) 1) measurableSet_Icc).2 (by norm_num)
  have hH := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun x : ℝ => x) aemeasurable_id' hb
  have hmgf := hH.mgf_le r
  have hmean : ∫ x, (fun x : ℝ => x) x ∂μ = d := by
    rw [hI]; rw [hpdef, hqdef]; ring
  have hlhs : mgf (fun x : ℝ => x - ∫ x, (fun x : ℝ => x) x ∂μ) μ r =
      p * Real.exp (r * (1 - d)) + q * Real.exp (r * (-1 - d)) := by
    rw [mgf, hmean, hI]
  have hc : (((‖(1 : ℝ) - -1‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 := by
    have : ‖(1 : ℝ) - -1‖₊ = 2 := by
      rw [show (1 : ℝ) - -1 = 2 by norm_num]
      ext; simp
    rw [this]; norm_num
  rw [hlhs, hc, one_mul] at hmgf
  exact hmgf

/-- Convexity of `exp` on `[−r, r]`: `e^{rz} ≤ cosh r + z sinh r` for `z ∈ [−1,1]`. -/
lemma exp_mul_le_cosh_add {z : ℝ} (hz1 : -1 ≤ z) (hz2 : z ≤ 1) (r : ℝ) :
    Real.exp (r * z) ≤ (Real.exp r + Real.exp (-r)) / 2 + z * ((Real.exp r - Real.exp (-r)) / 2) := by
  have h := convexOn_exp.2 (Set.mem_univ (-r)) (Set.mem_univ r) (show (0 : ℝ) ≤ (1 - z) / 2 by linarith)
    (show (0 : ℝ) ≤ (1 + z) / 2 by linarith) (by ring)
  simp only [smul_eq_mul] at h
  have he : (1 - z) / 2 * -r + (1 + z) / 2 * r = r * z := by ring
  rw [he] at h
  calc Real.exp (r * z) ≤ (1 - z) / 2 * Real.exp (-r) + (1 + z) / 2 * Real.exp r := h
    _ = _ := by ring

/-- The two-point bound in the form `e^{−rd}(cosh r + d sinh r) ≤ e^{r²/2}`. -/
lemma exp_neg_mul_cosh_add_le {d : ℝ} (hd1 : -1 ≤ d) (hd2 : d ≤ 1) (r : ℝ) :
    Real.exp (-(r * d)) * ((Real.exp r + Real.exp (-r)) / 2 + d * ((Real.exp r - Real.exp (-r)) / 2)) ≤
      Real.exp (r ^ 2 / 2) := by
  have h := two_point_hoeffding hd1 hd2 r
  have e1 : Real.exp (r * (1 - d)) = Real.exp r * Real.exp (-(r * d)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (r * (-1 - d)) = Real.exp (-r) * Real.exp (-(r * d)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2] at h
  calc _ = (1 + d) / 2 * (Real.exp r * Real.exp (-(r * d))) + (1 - d) / 2 * (Real.exp (-r) * Real.exp (-(r * d))) := by
        ring
    _ ≤ _ := h

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
variable {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
  {B : Fin N → Finset (Fin m)}

lemma abs_integral_le_one (ν : Measure 𝒳) [IsProbabilityMeasure ν] {f : 𝒳 → ℝ}
    (hf : ∀ t, f t ∈ Icc (0 : ℝ) 1) : |∫ t, f t ∂ν| ≤ 1 := by
  have hb : ∀ t, ‖f t‖ ≤ 1 := fun t => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hf t).1, (hf t).2]
  have h := norm_integral_le_of_norm_le_const (μ := ν) (C := 1) (ae_of_all _ hb)
  simpa [Real.norm_eq_abs] using h

lemma integral_mem_Icc (ν : Measure 𝒳) [IsProbabilityMeasure ν] {f : 𝒳 → ℝ}
    (hfm : Measurable f) (hf : ∀ t, f t ∈ Icc (0 : ℝ) 1) : ∫ t, f t ∂ν ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun t => (hf t).1, ?_⟩
  have hi : Integrable f ν := Integrable.of_mem_Icc 0 1 hfm.aemeasurable (ae_of_all _ hf)
  calc ∫ t, f t ∂ν ≤ ∫ _t, (1 : ℝ) ∂ν := integral_mono hi (integrable_const _) fun t => (hf t).2
    _ = 1 := by simp

/-- **Conditional Hoeffding lemma for a block pair**: for the pair statistic `Z_k` of a random function `G` of the
coordinates known before pair `k`, its conditional mean `Δ_k = E_P G − E_Q G`, and bounded functions `V ≥ 0`, `r` of
the same coordinates, `E[V e^{r(Z_k − Δ_k)}] ≤ E[V e^{r²/2}]`. -/
theorem hoeff_cond (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) (k : Fin N) {G : (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ}
    (hGm : Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => G p.1 p.2)
    (hGd : DepOn (predSet lx ly bat A B k) G) (hG01 : ∀ ω t, G ω t ∈ Icc (0 : ℝ) 1)
    {V r : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ} (hVm : Measurable V) (hVd : DepOn (predSet lx ly bat A B k) V)
    (hV0 : ∀ ω, 0 ≤ V ω) {K : ℝ} (hVb : ∀ ω, V ω ≤ K)
    (hrm : Measurable r) (hrd : DepOn (predSet lx ly bat A B k) r) {R : ℝ} (hrb : ∀ ω, |r ω| ≤ R) :
    ∫ ω, V ω * Real.exp (r ω * (pairZ (G ω) A B ω.1 ω.2 k - ((∫ t, G ω t ∂P) - ∫ t, G ω t ∂Q)))
        ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) ≤
      ∫ ω, V ω * Real.exp (r ω ^ 2 / 2) ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  set Z : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => pairZ (G ω) A B ω.1 ω.2 k with hZ
  set Δ : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => (∫ t, G ω t ∂P) - ∫ t, G ω t ∂Q with hΔ
  set ch : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => (Real.exp (r ω) + Real.exp (-r ω)) / 2 with hch
  set sh : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => (Real.exp (r ω) - Real.exp (-r ω)) / 2 with hsh
  set W : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => V ω * Real.exp (-(r ω * Δ ω)) * sh ω with hW
  have hK0 : 0 ≤ K := (hV0 (nonempty_of_isProbabilityMeasure μ).some).trans (hVb _)
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hrb (nonempty_of_isProbabilityMeasure μ).some)
  -- bounds
  have hZb : ∀ ω, Z ω ∈ Icc (-1 : ℝ) 1 := fun ω => pairZ_mem (hG01 ω) hpair.1 k ω.1 ω.2
  have hGmω : ∀ ω, Measurable (G ω) := fun ω => hGm.comp (measurable_const.prodMk measurable_id)
  have hΔb : ∀ ω, Δ ω ∈ Icc (-1 : ℝ) 1 := fun ω => by
    have h1 := integral_mem_Icc P (hGmω ω) (hG01 ω)
    have h2 := integral_mem_Icc Q (hGmω ω) (hG01 ω)
    simp only [hΔ]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hexpR : ∀ ω, Real.exp (r ω) ≤ Real.exp R ∧ Real.exp (-r ω) ≤ Real.exp R := fun ω => by
    have := abs_le.1 (hrb ω)
    exact ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_exp.2 (by linarith)⟩
  have hexpD : ∀ ω, Real.exp (-(r ω * Δ ω)) ≤ Real.exp R := fun ω => by
    refine Real.exp_le_exp.2 ?_
    have h1 : |r ω * Δ ω| ≤ R := by
      rw [abs_mul]
      have := abs_le.2 ⟨(hΔb ω).1, (hΔb ω).2⟩
      calc |r ω| * |Δ ω| ≤ R * 1 := mul_le_mul (hrb ω) this (abs_nonneg _) hR0
        _ = R := mul_one R
    linarith [neg_abs_le (r ω * Δ ω)]
  have hchb : ∀ ω, |ch ω| ≤ Real.exp R := fun ω => by
    have := hexpR ω
    rw [abs_of_nonneg (by simp only [hch]; positivity)]
    simp only [hch]; linarith
  have hshb : ∀ ω, |sh ω| ≤ Real.exp R := fun ω => by
    have := hexpR ω
    have p1 := Real.exp_pos (r ω)
    have p2 := Real.exp_pos (-r ω)
    rw [abs_le]; simp only [hsh]; constructor <;> linarith
  -- measurability and dependence
  have hZm : Measurable Z := by
    simp only [hZ]
    unfold pairZ blockMean
    refine Measurable.sub (Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _)
      (Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _)
    · exact hGm.comp (measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst))
    · exact hGm.comp (measurable_id.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hIP : Measurable fun ω => ∫ t, G ω t ∂P := (hGm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hIQ : Measurable fun ω => ∫ t, G ω t ∂Q := (hGm.stronglyMeasurable.integral_prod_right' (ν := Q)).measurable
  have hΔm : Measurable Δ := hIP.sub hIQ
  have hΔd : DepOn (predSet lx ly bat A B k) Δ := fun ω ω' h => by
    simp only [hΔ]; rw [hGd ω ω' h]
  have hchm : Measurable ch := ((Real.measurable_exp.comp hrm).add (Real.measurable_exp.comp hrm.neg)).div_const _
  have hshm : Measurable sh := ((Real.measurable_exp.comp hrm).sub (Real.measurable_exp.comp hrm.neg)).div_const _
  have hEm : Measurable fun ω => Real.exp (-(r ω * Δ ω)) := Real.measurable_exp.comp (hrm.mul hΔm).neg
  have hWm : Measurable W := (hVm.mul hEm).mul hshm
  have hWd : DepOn (predSet lx ly bat A B k) W := fun ω ω' h => by
    simp only [hW, hsh]; rw [hVd ω ω' h, hrd ω ω' h, hΔd ω ω' h]
  have hWb : ∀ ω, |W ω| ≤ K * Real.exp R * Real.exp R := fun ω => by
    simp only [hW]
    rw [abs_mul, abs_mul, abs_of_nonneg (hV0 ω), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hVb ω) (hexpD ω) (Real.exp_pos _).le hK0) (hshb ω) (abs_nonneg _)
      (mul_nonneg hK0 (Real.exp_pos _).le)
  -- the freezing identity `E[W Z] = E[W Δ]`
  have hEq := integral_mul_pairZ P Q (C := predSet lx ly bat A B k) k (hpair.1.1 k) (hpair.1.2.1 k)
    (fun i hi => notMem_predSet_of_mem_blockSet hpair k (Or.inl ⟨i, by exact_mod_cast hi, rfl⟩))
    (fun j hj => notMem_predSet_of_mem_blockSet hpair k (Or.inr ⟨j, by exact_mod_cast hj, rfl⟩))
    hWm hWd hWb hGm hGd hG01
  -- integrability
  set A1 : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => V ω * Real.exp (-(r ω * Δ ω)) * ch ω with hA1
  have hA1m : Measurable A1 := (hVm.mul hEm).mul hchm
  have hA1i : Integrable A1 μ := integrable_of_abs_le hA1m (K * Real.exp R * Real.exp R) fun ω => by
    simp only [hA1]
    rw [abs_mul, abs_mul, abs_of_nonneg (hV0 ω), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hVb ω) (hexpD ω) (Real.exp_pos _).le hK0) (hchb ω) (abs_nonneg _)
      (mul_nonneg hK0 (Real.exp_pos _).le)
  have hWZi : Integrable (fun ω => W ω * Z ω) μ :=
    integrable_of_abs_le (hWm.mul hZm) (K * Real.exp R * Real.exp R * 1) fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hWb ω) (abs_le.2 ⟨(hZb ω).1, (hZb ω).2⟩) (abs_nonneg _) ((abs_nonneg _).trans (hWb ω))
  have hWΔi : Integrable (fun ω => W ω * Δ ω) μ :=
    integrable_of_abs_le (hWm.mul hΔm) (K * Real.exp R * Real.exp R * 1) fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hWb ω) (abs_le.2 ⟨(hΔb ω).1, (hΔb ω).2⟩) (abs_nonneg _) ((abs_nonneg _).trans (hWb ω))
  have hLm : Measurable fun ω => V ω * Real.exp (r ω * (Z ω - Δ ω)) :=
    hVm.mul (Real.measurable_exp.comp (hrm.mul (hZm.sub hΔm)))
  have hLi : Integrable (fun ω => V ω * Real.exp (r ω * (Z ω - Δ ω))) μ := by
    refine integrable_of_abs_le hLm (K * Real.exp (R * 2)) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (hV0 ω), abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hVb ω) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hK0
    have h1 : |Z ω - Δ ω| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [(hZb ω).1, (hZb ω).2, (hΔb ω).1, (hΔb ω).2]
    calc r ω * (Z ω - Δ ω) ≤ |r ω * (Z ω - Δ ω)| := le_abs_self _
      _ = |r ω| * |Z ω - Δ ω| := abs_mul _ _
      _ ≤ R * 2 := mul_le_mul (hrb ω) h1 (abs_nonneg _) hR0
  have hRi : Integrable (fun ω => V ω * Real.exp (r ω ^ 2 / 2)) μ := by
    refine integrable_of_abs_le (hVm.mul (Real.measurable_exp.comp ((hrm.pow_const 2).div_const 2)))
      (K * Real.exp (R ^ 2 / 2)) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (hV0 ω), abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hVb ω) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hK0
    have h1 : r ω ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hrb ω) 2
    linarith
  -- the chain of inequalities
  have step1 : ∀ ω, V ω * Real.exp (r ω * (Z ω - Δ ω)) ≤ A1 ω + W ω * Z ω := fun ω => by
    have hc := exp_mul_le_cosh_add (hZb ω).1 (hZb ω).2 (r ω)
    have he : Real.exp (r ω * (Z ω - Δ ω)) = Real.exp (-(r ω * Δ ω)) * Real.exp (r ω * Z ω) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    simp only [hA1, hW, hch, hsh]
    have hVE : 0 ≤ V ω * Real.exp (-(r ω * Δ ω)) := mul_nonneg (hV0 ω) (Real.exp_pos _).le
    calc V ω * (Real.exp (-(r ω * Δ ω)) * Real.exp (r ω * Z ω))
        = V ω * Real.exp (-(r ω * Δ ω)) * Real.exp (r ω * Z ω) := by ring
      _ ≤ V ω * Real.exp (-(r ω * Δ ω)) * ((Real.exp (r ω) + Real.exp (-r ω)) / 2 +
          Z ω * ((Real.exp (r ω) - Real.exp (-r ω)) / 2)) := mul_le_mul_of_nonneg_left hc hVE
      _ = _ := by ring
  have step3 : ∀ ω, A1 ω + W ω * Δ ω ≤ V ω * Real.exp (r ω ^ 2 / 2) := fun ω => by
    have h := exp_neg_mul_cosh_add_le (hΔb ω).1 (hΔb ω).2 (r ω)
    simp only [hA1, hW, hch, hsh]
    calc V ω * Real.exp (-(r ω * Δ ω)) * ((Real.exp (r ω) + Real.exp (-r ω)) / 2) +
          V ω * Real.exp (-(r ω * Δ ω)) * ((Real.exp (r ω) - Real.exp (-r ω)) / 2) * Δ ω
        = V ω * (Real.exp (-(r ω * Δ ω)) * ((Real.exp (r ω) + Real.exp (-r ω)) / 2 +
          Δ ω * ((Real.exp (r ω) - Real.exp (-r ω)) / 2))) := by ring
      _ ≤ V ω * Real.exp (r ω ^ 2 / 2) := mul_le_mul_of_nonneg_left h (hV0 ω)
  have hEq' : ∫ ω, W ω * Z ω ∂μ = ∫ ω, W ω * Δ ω ∂μ := hEq
  calc ∫ ω, V ω * Real.exp (r ω * (Z ω - Δ ω)) ∂μ ≤ ∫ ω, (A1 ω + W ω * Z ω) ∂μ :=
        integral_mono hLi (hA1i.add hWZi) step1
    _ = ∫ ω, A1 ω ∂μ + ∫ ω, W ω * Z ω ∂μ := integral_add hA1i hWZi
    _ = ∫ ω, A1 ω ∂μ + ∫ ω, W ω * Δ ω ∂μ := by rw [hEq']
    _ = ∫ ω, (A1 ω + W ω * Δ ω) ∂μ := (integral_add hA1i hWΔi).symm
    _ ≤ ∫ ω, V ω * Real.exp (r ω ^ 2 / 2) ∂μ := integral_mono (hA1i.add hWΔi) hRi step3

/-- **Ville's inequality for products of predictable supermartingale factors.** -/
theorem prod_ville (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hmono : Monotone bat) (F : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ)
    (hFm : ∀ k, Measurable (F k)) (hFd : ∀ k : Fin N, DepOn (predSet lx ly bat A B (k + 1)) (F k))
    {B0 : ℝ} (hFb : ∀ k ω, 0 ≤ F k ω ∧ F k ω ≤ B0)
    (hmean : ∀ k : Fin N, ∀ V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ, Measurable V →
      DepOn (predSet lx ly bat A B k) V → (∀ ω, 0 ≤ V ω) → (∃ C, ∀ ω, V ω ≤ C) →
      ∫ ω, V ω * F k ω ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) ≤
        ∫ ω, V ω ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
    {a : ℝ} (ha : 0 < a) :
    a * ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real
      {ω | ∃ t ≤ N, a ≤ ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), F k ω} ≤ 1 := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  set 𝒢 := seqFiltration (𝒳 := 𝒳) lx ly bat A B hmono with h𝒢
  have hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (fun ω => F k ω - 1) := fun k =>
    measurable_coordSigma_of_depOn ((hFm k).sub_const 1) fun ω ω' h => by
      show F k ω - 1 = F k ω' - 1
      rw [hFd k ω ω' h]
  have hYb : ∀ k ω, |(fun k ω => F k ω - 1) k ω| ≤ B0 + 1 := fun k ω => by
    have := hFb k ω
    rw [abs_le]; constructor <;> simp only <;> linarith [this.1, this.2]
  have hfac : ∀ k ω, 0 ≤ 1 + (fun (_ : Fin N) (_ : (Fin n → 𝒳) × (Fin m → 𝒳)) => (1 : ℝ)) k ω *
      (fun k ω => F k ω - 1) k ω := fun k ω => by
    simp only [one_mul]; linarith [(hFb k ω).1]
  have hmean' : ∀ k : Fin N, ∀ V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ, Measurable[𝒢 k] V → (∀ ω, 0 ≤ V ω) →
      (∃ C, ∀ ω, V ω ≤ C) → ∫ ω, V ω * (fun k ω => F k ω - 1) k ω ∂μ ≤ 0 := by
    intro k V hV hV0 ⟨C, hC⟩
    have hVd : DepOn (predSet lx ly bat A B k) V := depOn_of_measurable hV
    have hVm : Measurable V := hV.mono (𝒢.le k) le_rfl
    have hC0 : 0 ≤ C := (hV0 (nonempty_of_isProbabilityMeasure μ).some).trans (hC _)
    have hVi : Integrable V μ := integrable_of_abs_le hVm C fun ω => by rw [abs_of_nonneg (hV0 ω)]; exact hC ω
    have hVFi : Integrable (fun ω => V ω * F k ω) μ := integrable_of_abs_le (hVm.mul (hFm k)) (C * B0) fun ω => by
      rw [abs_mul, abs_of_nonneg (hV0 ω), abs_of_nonneg (hFb k ω).1]
      exact mul_le_mul (hC ω) (hFb k ω).2 (hFb k ω).1 hC0
    have h := hmean k V hVm hVd hV0 ⟨C, hC⟩
    have hs : (fun ω => V ω * (fun k ω => F k ω - 1) k ω) = fun ω => V ω * F k ω - V ω := by
      funext ω; simp only; ring
    rw [hs, integral_sub hVFi hVi]
    linarith
  have hV := betting_ville_pred 𝒢 (fun _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) (fun k ω => F k ω - 1)
    measurable_const (fun _ => ⟨zero_le_one, le_rfl⟩) hY (fun _ => measurable_const) (L := 1)
    (fun _ _ => ⟨zero_le_one, le_rfl⟩) hYb hfac hmean' ha
  have hset : {ω | ∃ t ≤ N, a ≤ (fun _ => (1 : ℝ)) ω *
      wealthP (fun _ _ => (1 : ℝ)) (fun k ω => F k ω - 1) t ω} =
      {ω | ∃ t ≤ N, a ≤ ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), F k ω} := by
    ext ω
    simp only [wealthP, one_mul, add_sub_cancel, Set.mem_ofPred_eq]
  rw [hset] at hV
  simpa using hV

end StatFormal.Wave30tz
