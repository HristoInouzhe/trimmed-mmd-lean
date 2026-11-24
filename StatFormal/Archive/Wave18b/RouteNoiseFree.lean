import StatFormal.Archive.Wave18b.RouteExcess

/-!
# Route: SB `prop:noisefree` (untrusted)

* `W₂(N(M,v), N(M,w)) = |√v − √w|` (`w2_gauss_same_mean`): the comonotone coupling `(M + √v Z, M + √w Z)` gives
  `≤`; for any coupling, with `p = x − M`, `q = y − M`, `ab(p − q)² + b²p²·… ` — precisely
  `(p − q)² + (b/a)p² + (a/b)q² ≥ p² + q²` (it is `(bp − aq)²/(ab) ≥ 0`), integrated against the marginals,
  gives `E(x − y)² ≥ a² + b² − 2ab`.
* The bridge marginals share the mean `(1−t)a_s + ta⋆`; `v_ε − v_0 = t(1−t)(κ_ε − 2στ)` and
  `κ_ε − 2στ = ε²/(κ_ε + 2στ)`; the additive law is `N(M, v_0 + εt(1−t))` (`gaussianReal_conv_gaussianReal`).
* Limits by continuity of `κ_ε`, `v_ε` in `ε` at `0`; the `Θ`'s from the positive limits.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal

namespace StatFormal.Wave18b

open StatFormal.Wave9b StatFormal.SBFairness

lemma lintegral_sq_centered (M : ℝ) (v : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal ((z - M) ^ 2) ∂(gaussianReal M v) = ENNReal.ofReal v := by
  have hm2 : MemLp (fun z : ℝ => z - M) 2 (gaussianReal M v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const M)
  rw [← ofReal_integral_eq_lintegral_ofReal hm2.integrable_sq (Eventually.of_forall fun z => sq_nonneg _)]
  congr 1
  have h := variance_fun_id_gaussianReal (μ := M) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  exact h

lemma gauss_affine (M : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun z => M + √(v : ℝ) * z) = gaussianReal M v := by
  have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (√(v : ℝ))
  have hc : (fun z => M + √(v : ℝ) * z) = (fun z => M + z) ∘ (fun z => √(v : ℝ) * z) := rfl
  rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_const_add]
  congr 1
  · simp
  · ext; simp [Real.sq_sqrt v.coe_nonneg]

lemma w2_sq_gauss (M : ℝ) (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w) :
    wassersteinEDist 2 (gaussianReal M v) (gaussianReal M w) ^ (2 : ℝ) =
      ENNReal.ofReal ((√(v : ℝ) - √(w : ℝ)) ^ 2) := by
  set a := √(v : ℝ) with ha
  set b := √(w : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hb0 : 0 < b := Real.sqrt_pos.2 (by exact_mod_cast hw)
  have haa : a ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  have hbb : b ^ 2 = w := Real.sq_sqrt w.coe_nonneg
  rw [w2_sq_eq_transportCost]
  apply le_antisymm
  · -- the comonotone coupling
    set γ := (gaussianReal 0 1).map (fun z => (M + a * z, M + b * z)) with hγ
    have hγm : Measurable fun z : ℝ => (M + a * z, M + b * z) := by fun_prop
    have hc : IsCoupling γ (gaussianReal M v) (gaussianReal M w) := by
      constructor
      · rw [Measure.fst, hγ, Measure.map_map measurable_fst hγm]
        exact gauss_affine M v
      · rw [Measure.snd, hγ, Measure.map_map measurable_snd hγm]
        exact gauss_affine M w
    refine (iInf₂_le γ hc).trans (le_of_eq ?_)
    rw [hγ, lintegral_map (by fun_prop) hγm]
    simp only [edist_rpow_two]
    have : ∀ z : ℝ, (M + a * z - (M + b * z)) ^ 2 = (a - b) ^ 2 * (z - 0) ^ 2 := fun z => by ring
    simp_rw [this, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_sq_centered]
    simp
  · refine le_iInf₂ fun π hπ => ?_
    by_cases htop : ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂π = ⊤
    · rw [htop]; exact le_top
    have hpt : ∀ z : ℝ × ℝ, ENNReal.ofReal ((z.1 - M) ^ 2) + ENNReal.ofReal ((z.2 - M) ^ 2) ≤
        edist z.1 z.2 ^ (2 : ℝ) + ENNReal.ofReal (b / a) * ENNReal.ofReal ((z.1 - M) ^ 2) +
          ENNReal.ofReal (a / b) * ENNReal.ofReal ((z.2 - M) ^ 2) := by
      intro z
      rw [edist_rpow_two, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← ENNReal.ofReal_add (sq_nonneg _) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      set p := z.1 - M
      set q := z.2 - M
      have hpq : z.1 - z.2 = p - q := by simp only [p, q]; ring
      rw [hpq]
      have key : 0 ≤ (b * p - a * q) ^ 2 / (a * b) := by positivity
      have : (p - q) ^ 2 + b / a * p ^ 2 + a / b * q ^ 2 - (p ^ 2 + q ^ 2) = (b * p - a * q) ^ 2 / (a * b) := by
        field_simp; ring
      linarith
    have hm1 : Measurable fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - M) ^ 2) := by fun_prop
    have hm2 : Measurable fun z : ℝ × ℝ => ENNReal.ofReal ((z.2 - M) ^ 2) := by fun_prop
    have hmc : Measurable fun z : ℝ × ℝ => edist z.1 z.2 ^ (2 : ℝ) := continuous_cost2.measurable
    have hI1 : ∫⁻ z, ENNReal.ofReal ((z.1 - M) ^ 2) ∂π = ENNReal.ofReal v := by
      rw [← lintegral_sq_centered M v, ← hπ.fst_eq, Measure.fst, lintegral_map (by fun_prop) measurable_fst]
    have hI2 : ∫⁻ z, ENNReal.ofReal ((z.2 - M) ^ 2) ∂π = ENNReal.ofReal w := by
      rw [← lintegral_sq_centered M w, ← hπ.snd_eq, Measure.snd, lintegral_map (by fun_prop) measurable_snd]
    have hint := lintegral_mono (μ := π) hpt
    have hR : ∫⁻ z, (edist z.1 z.2 ^ (2 : ℝ) + ENNReal.ofReal (b / a) * ENNReal.ofReal ((z.1 - M) ^ 2) +
        ENNReal.ofReal (a / b) * ENNReal.ofReal ((z.2 - M) ^ 2)) ∂π =
        ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂π + ENNReal.ofReal (b / a) * ∫⁻ z, ENNReal.ofReal ((z.1 - M) ^ 2) ∂π +
          ENNReal.ofReal (a / b) * ∫⁻ z, ENNReal.ofReal ((z.2 - M) ^ 2) ∂π := by
      rw [lintegral_add_left (f := fun z : ℝ × ℝ => edist z.1 z.2 ^ (2 : ℝ) +
          ENNReal.ofReal (b / a) * ENNReal.ofReal ((z.1 - M) ^ 2)) (hmc.add (hm1.const_mul _)),
        lintegral_add_left (f := fun z : ℝ × ℝ => edist z.1 z.2 ^ (2 : ℝ)) hmc,
        lintegral_const_mul _ hm1, lintegral_const_mul _ hm2]
    rw [lintegral_add_left (f := fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - M) ^ 2)) hm1, hR, hI1, hI2] at hint
    beta_reduce
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hint
    have e1 : b / a * v = a * b := by rw [← haa]; field_simp
    have e2 : a / b * w = a * b := by rw [← hbb]; field_simp
    rw [e1, e2] at hint
    set I := ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂π
    have hsum : ENNReal.ofReal ((v : ℝ) + w) ≤ I + ENNReal.ofReal (2 * (a * b)) := by
      rw [ENNReal.ofReal_add v.coe_nonneg w.coe_nonneg, two_mul, ENNReal.ofReal_add (by positivity) (by positivity),
        ← add_assoc]
      exact hint
    have := tsub_le_iff_right.2 hsum
    rw [← ENNReal.ofReal_sub _ (by positivity)] at this
    calc ENNReal.ofReal ((a - b) ^ 2) = ENNReal.ofReal ((v : ℝ) + w - 2 * (a * b)) := by
          congr 1; rw [← haa, ← hbb]; ring
      _ ≤ I := this

lemma w2_gauss_same_mean (M : ℝ) (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w) :
    wassersteinEDist 2 (gaussianReal M v) (gaussianReal M w) = ENNReal.ofReal |√(v : ℝ) - √(w : ℝ)| := by
  have h := w2_sq_gauss M v w hv hw
  have h2 : (wassersteinEDist 2 (gaussianReal M v) (gaussianReal M w) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      wassersteinEDist 2 (gaussianReal M v) (gaussianReal M w) := by
    rw [← ENNReal.rpow_mul]; norm_num
  rw [← h2, h, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq_eq_abs]

/-! ### The Gaussian formulas -/

lemma kappa_zero {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : kappa 0 σ τ = 2 * σ * τ := by
  unfold kappa
  rw [show (0 : ℝ) ^ 2 + 4 * σ ^ 2 * τ ^ 2 = (2 * σ * τ) ^ 2 by ring, Real.sqrt_sq (by positivity)]

lemma kappa_pos {ε σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : 0 < kappa ε σ τ := by
  unfold kappa; apply Real.sqrt_pos.2; positivity

lemma kappa_sub {ε σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    kappa ε σ τ - 2 * σ * τ = ε ^ 2 / (kappa ε σ τ + 2 * σ * τ) := by
  have hk := kappa_pos (ε := ε) hσ hτ
  have hsq : kappa ε σ τ ^ 2 = ε ^ 2 + 4 * σ ^ 2 * τ ^ 2 := by
    unfold kappa; rw [Real.sq_sqrt (by positivity)]
  rw [eq_div_iff (by positivity)]
  nlinarith [hsq]

lemma v_zero {σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : v 0 σ τ t = geo σ τ t ^ 2 := by
  unfold v geo; rw [kappa_zero hσ hτ]; ring

lemma geo_pos {σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < geo σ τ t := by
  unfold geo; nlinarith [ht.1, ht.2]

lemma v_pos {ε σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < v ε σ τ t := by
  unfold v
  have := kappa_pos (ε := ε) hσ hτ
  have : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
  positivity

lemma v_sub {ε σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    v ε σ τ t - v 0 σ τ t = t * (1 - t) * (kappa ε σ τ - 2 * σ * τ) := by
  unfold v; rw [kappa_zero hσ hτ]; ring

lemma v_mono {ε σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    v 0 σ τ t ≤ v ε σ τ t := by
  have h := v_sub (ε := ε) (t := t) hσ hτ
  have : 0 ≤ kappa ε σ τ - 2 * σ * τ := by
    rw [kappa_sub hσ hτ]; have := kappa_pos (ε := ε) hσ hτ; positivity
  have : 0 ≤ t * (1 - t) := mul_nonneg ht.1.le (by linarith [ht.2])
  nlinarith

/-- `B(ε) = t(1−t)(κ_ε − 2στ)/(√v_ε + √v_0)`. -/
def bgap (ε σ τ t : ℝ) : ℝ := t * (1 - t) * (kappa ε σ τ - 2 * σ * τ) / (√(v ε σ τ t) + √(v 0 σ τ t))

/-- `A(ε) = √(v_0 + εt(1−t)) − √v_0`. -/
def agap (ε σ τ t : ℝ) : ℝ := √(v 0 σ τ t + ε * t * (1 - t)) - √(v 0 σ τ t)

lemma w2_bridge {ε σ τ a astar t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    wassersteinEDist 2 (muSB ε σ τ a astar t) (muSB 0 σ τ a astar t) = ENNReal.ofReal (bgap ε σ τ t) := by
  unfold muSB
  have hv1 := v_pos (ε := ε) hσ hτ ht
  have hv0 := v_pos (ε := 0) hσ hτ ht
  rw [w2_gauss_same_mean _ _ _ (by simpa using hv1) (by simpa using hv0),
    Real.coe_toNNReal _ hv1.le, Real.coe_toNNReal _ hv0.le]
  congr 1
  have hle : √(v 0 σ τ t) ≤ √(v ε σ τ t) := Real.sqrt_le_sqrt (v_mono hσ hτ ht)
  rw [abs_of_nonneg (by linarith), bgap, ← v_sub hσ hτ]
  have hs : 0 < √(v ε σ τ t) + √(v 0 σ τ t) := by
    have := Real.sqrt_pos.2 hv0; positivity
  rw [eq_div_iff hs.ne']
  have e1 := Real.sq_sqrt hv1.le
  have e0 := Real.sq_sqrt hv0.le
  nlinarith

lemma w2_additive {ε σ τ a astar t : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    wassersteinEDist 2 (muSB 0 σ τ a astar t ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
        (muSB 0 σ τ a astar t) = ENNReal.ofReal (agap ε σ τ t) := by
  unfold muSB
  have hv0 := v_pos (ε := 0) hσ hτ ht
  have hs : 0 ≤ ε * t * (1 - t) := mul_nonneg (mul_nonneg hε ht.1.le) (by linarith [ht.2])
  rw [gaussianReal_conv_gaussianReal, add_zero, ← Real.toNNReal_add hv0.le hs,
    w2_gauss_same_mean _ _ _ (by simpa using (by positivity : 0 < v 0 σ τ t + ε * t * (1 - t)))
      (by simpa using hv0), Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hv0.le]
  congr 1
  rw [agap, abs_of_nonneg (by have := Real.sqrt_le_sqrt (by linarith : v 0 σ τ t ≤ v 0 σ τ t + ε * t * (1 - t)); linarith)]

theorem noisefree_bridge_exact : Claims.noisefree_bridge_exact := by
  intro ε σ τ a astar t hε hσ hτ ht
  exact ⟨w2_bridge hσ hτ ht, kappa_sub hσ hτ⟩

theorem noisefree_additive_exact : Claims.noisefree_additive_exact := by
  intro ε σ τ a astar t hε hσ hτ ht
  exact w2_additive hε.le hσ hτ ht

lemma continuous_kappa (σ τ : ℝ) : Continuous fun ε => kappa ε σ τ := by unfold kappa; fun_prop

lemma continuous_v (σ τ t : ℝ) : Continuous fun ε => v ε σ τ t := by
  unfold v; have := continuous_kappa σ τ; fun_prop

/-- `B(ε)/(εt(1−t))² → 1/(8στ g t(1−t))`. -/
lemma tendsto_bgap {σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => bgap ε σ τ t / (ε * t * (1 - t)) ^ 2) (𝓝[>] 0)
      (𝓝 (1 / (8 * σ * τ * geo σ τ t * (t * (1 - t))))) := by
  have htt : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
  have hg := geo_pos hσ hτ ht
  -- the continuous expression
  set F : ℝ → ℝ := fun ε => 1 / (t * (1 - t) * (kappa ε σ τ + 2 * σ * τ) * (√(v ε σ τ t) + √(v 0 σ τ t)))
  have hFc : ContinuousAt F 0 := by
    have hk := continuous_kappa σ τ
    have hv := continuous_v σ τ t
    have hden : t * (1 - t) * (kappa 0 σ τ + 2 * σ * τ) * (√(v 0 σ τ t) + √(v 0 σ τ t)) ≠ 0 := by
      have := kappa_pos (ε := 0) hσ hτ
      have := Real.sqrt_pos.2 (v_pos (ε := 0) hσ hτ ht)
      positivity
    exact (continuousAt_const.div (by fun_prop) hden)
  have hF0 : F 0 = 1 / (8 * σ * τ * geo σ τ t * (t * (1 - t))) := by
    simp only [F]
    rw [kappa_zero hσ hτ, v_zero hσ hτ, Real.sqrt_sq hg.le]
    congr 1; ring
  rw [← hF0]
  refine (tendsto_nhdsWithin_of_tendsto_nhds hFc.tendsto).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [F, bgap]
  rw [kappa_sub hσ hτ]
  have hk := kappa_pos (ε := ε) hσ hτ
  have hs : 0 < √(v ε σ τ t) + √(v 0 σ τ t) := by
    have := Real.sqrt_pos.2 (v_pos (ε := 0) hσ hτ ht); positivity
  field_simp

/-- `A(ε)/(εt(1−t)) → 1/(2g)`. -/
lemma tendsto_agap {σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => agap ε σ τ t / (ε * t * (1 - t))) (𝓝[>] 0) (𝓝 (1 / (2 * geo σ τ t))) := by
  have htt : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
  have hg := geo_pos hσ hτ ht
  have hv0 := v_pos (ε := 0) hσ hτ ht
  set F : ℝ → ℝ := fun ε => 1 / (√(v 0 σ τ t + ε * t * (1 - t)) + √(v 0 σ τ t))
  have hFc : ContinuousAt F 0 := by
    have hden : √(v 0 σ τ t + 0 * t * (1 - t)) + √(v 0 σ τ t) ≠ 0 := by
      have := Real.sqrt_pos.2 hv0; simp only [zero_mul, add_zero]; positivity
    exact continuousAt_const.div (by fun_prop) hden
  have hF0 : F 0 = 1 / (2 * geo σ τ t) := by
    simp only [F, zero_mul, add_zero]
    rw [v_zero hσ hτ, Real.sqrt_sq hg.le]; ring
  rw [← hF0]
  refine (tendsto_nhdsWithin_of_tendsto_nhds hFc.tendsto).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [F, agap]
  have hs : 0 < ε * t * (1 - t) := by have := mul_pos hε htt; linarith [this, mul_assoc ε t (1 - t)]
  have hsq1 := Real.sq_sqrt (by positivity : 0 ≤ v 0 σ τ t + ε * t * (1 - t))
  have hsq0 := Real.sq_sqrt hv0.le
  have hp : 0 < √(v 0 σ τ t + ε * t * (1 - t)) + √(v 0 σ τ t) := by
    have := Real.sqrt_pos.2 hv0; positivity
  rw [div_eq_div_iff hp.ne' hs.ne']
  nlinarith

lemma bgap_nonneg {ε σ τ t : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ bgap ε σ τ t := by
  unfold bgap
  rw [kappa_sub hσ hτ]
  have := kappa_pos (ε := ε) hσ hτ
  have : 0 ≤ t * (1 - t) := mul_nonneg ht.1.le (by linarith [ht.2])
  positivity

lemma agap_nonneg {ε σ τ t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ agap ε σ τ t := by
  unfold agap
  have : 0 ≤ ε * t * (1 - t) := mul_nonneg (mul_nonneg hε ht.1.le) (by linarith [ht.2])
  have := Real.sqrt_le_sqrt (by linarith : v 0 σ τ t ≤ v 0 σ τ t + ε * t * (1 - t))
  linarith

/-- From `f/g → L > 0` (`g > 0` eventually), eventually `(L/2) g ≤ f ≤ 2L g`. -/
lemma theta_of_tendsto {f g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (h : Tendsto (fun ε => f ε / g ε) (𝓝[>] 0) (𝓝 L))
    (hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < g ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), L / 2 * g ε ≤ f ε ∧ f ε ≤ 2 * L * g ε := by
  have h1 := h.eventually (lt_mem_nhds (by linarith : L / 2 < L))
  have h2 := h.eventually (gt_mem_nhds (by linarith : L < 2 * L))
  filter_upwards [h1, h2, hg] with ε e1 e2 e3
  rw [lt_div_iff₀ e3] at e1
  rw [div_lt_iff₀ e3] at e2
  exact ⟨e1.le, e2.le⟩

lemma pos_sched {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε * t * (1 - t) := by
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have := mul_pos (mul_pos hε ht.1) (by linarith [ht.2] : (0 : ℝ) < 1 - t)
  exact this

theorem noisefree_bridge_theta : Claims.noisefree_bridge_theta := by
  intro σ τ a astar t hσ hτ ht
  have htt : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
  have hg := geo_pos hσ hτ ht
  set L := 1 / (8 * σ * τ * geo σ τ t * (t * (1 - t)))
  have hL : 0 < L := by positivity
  have hth := theta_of_tendsto hL (tendsto_bgap hσ hτ ht)
    ((pos_sched ht).mono fun ε h => pow_pos h 2)
  refine ⟨L / 2, 2 * L, by positivity, by positivity, ?_⟩
  filter_upwards [hth] with ε hε
  rw [w2_bridge hσ hτ ht]
  exact ⟨ENNReal.ofReal_le_ofReal hε.1, ENNReal.ofReal_le_ofReal hε.2⟩

theorem noisefree_additive_theta : Claims.noisefree_additive_theta := by
  intro σ τ a astar t hσ hτ ht
  have hg := geo_pos hσ hτ ht
  set L := 1 / (2 * geo σ τ t)
  have hL : 0 < L := by positivity
  have hth := theta_of_tendsto hL (tendsto_agap hσ hτ ht) (pos_sched ht)
  refine ⟨L / 2, 2 * L, by positivity, by positivity, ?_⟩
  filter_upwards [hth, self_mem_nhdsWithin] with ε hε (hε0 : 0 < ε)
  rw [w2_additive hε0.le hσ hτ ht]
  exact ⟨ENNReal.ofReal_le_ofReal hε.1, ENNReal.ofReal_le_ofReal hε.2⟩

theorem noisefree_limits : Claims.noisefree_limits := by
  intro σ τ a astar t hσ hτ ht
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (wassersteinEDist 2 (muSB ε σ τ a astar t) (muSB 0 σ τ a astar t)).toReal = bgap ε σ τ t :=
    Eventually.of_forall fun ε => by rw [w2_bridge hσ hτ ht, ENNReal.toReal_ofReal (bgap_nonneg hσ hτ ht)]
  have ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (wassersteinEDist 2 (muSB 0 σ τ a astar t ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
        (muSB 0 σ τ a astar t)).toReal = agap ε σ τ t := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [w2_additive hε.le hσ hτ ht, ENNReal.toReal_ofReal (agap_nonneg hε.le ht)]
  have hB := tendsto_bgap hσ hτ ht
  have hA := tendsto_agap hσ hτ ht
  refine ⟨hB.congr' (hb.mono fun ε h => by simp only [h]), hA.congr' (ha.mono fun ε h => by simp only [h]), ?_⟩
  -- ratio: B/A = (B/s²) · s / (A/s), s = εt(1−t) → 0
  have hs : Tendsto (fun ε : ℝ => ε * t * (1 - t)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => ε * t * (1 - t)) (𝓝 0) (𝓝 (0 * t * (1 - t))) := by
      exact ((continuous_id.mul continuous_const).mul continuous_const).tendsto 0
    rw [zero_mul, zero_mul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hg := geo_pos hσ hτ ht
  have hlim := (hB.mul hs).div hA (by positivity)
  rw [mul_zero, zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [hb, ha, pos_sched ht, self_mem_nhdsWithin] with ε e1 e2 e3 (hε : 0 < ε)
  simp only [Pi.div_apply]
  rw [e1, e2]
  have h1 : ε ≠ 0 := hε.ne'
  have h2 : t ≠ 0 := ht.1.ne'
  have h3 : 1 - t ≠ 0 := by linarith [ht.2]
  have hAp : 0 < agap ε σ τ t := by
    unfold agap
    have := Real.sqrt_lt_sqrt (v_pos (ε := 0) hσ hτ ht).le (by linarith : v 0 σ τ t < v 0 σ τ t + ε * t * (1 - t))
    linarith
  field_simp

theorem noisefree_constants : Claims.noisefree_constants := by
  unfold Claims.noisefree_constants geo
  norm_num

end StatFormal.Wave18b
