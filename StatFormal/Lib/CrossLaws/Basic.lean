import StatFormal.Lib.MomentTrim.Crossing
import StatFormal.Lib.MomentTrim.Region
import StatFormal.Lib.MomentTrim.Signed
import StatFormal.Lib.Distances.TV

/-!
# Crossing density pairs on the line: local and tail facts (library, untrusted)

Small general facts used to compose the main-text propositions of the trimmed-mmd paper (Propositions 5.5 and 5.6, the
"laws of Proposition 5.5": densities `p, q` continuous near `x₀`, `p ≥ q` a.e. on the right, `p ≤ q` a.e. on the left,
`(p − q)′(x₀) = ℓ₀ > 0`, `p(x₀) > 0`, exponential tails of `|P − Q|`).

* `abs_le_of_hasDerivAt`: a function vanishing at `x₀` with derivative `ℓ₀ ≥ 0` there satisfies `|e(x)| ≤ (ℓ₀ + η)|x − x₀|`
  near `x₀`, for every `η > 0`;
* `tv_pos_lt_one`: `0 < TV(P, Q) < 1` for Lebesgue densities when `p − q` is bounded below by a positive linear function on an
  interval and `min(p, q)` is bounded below by a positive constant there (given the density formulas for `TV`, `P ∧ Q`);
* `tailOut_le`, `tailPlus_le`: from `μ({t < |x − x₀|}) ≤ C′e^{−t/C′}` (all `t > 0`) to the tail forms `μ(ℝ ∖ B_{ρ−1}(x₀))`
  (`ρ ≥ 1`) and `μ((x₀ + t, ∞))` (`t > 0`);
* `absPQ_le_add`: the total variation of `P − Q` is at most `P + Q`;
* `uPath_le_Dpop`, `Dpop_le_uPath_div`: `(1 − α)D_α ≤ D_α ≤ (1 − α⋆)^{−1}(1 − α)D_α` for `0 ≤ α ≤ α⋆ < 1`
  (the latter adapted from `Wave31tq.RouteT.Dpop_le_uPath_div` of chunk T);
* `false_of_lower_upper`: `c₀ε^{γ′} ≤ f(ε) ≤ Kε^γ` on `(0, ε₀]` with `c₀ > 0`, `γ′ < γ` is impossible;
* `mul_log_inv_le`, `exp_le_of_log_bound`: `ε log(1/ε) ≤ 2√ε`, and a bound
  `log(1/u) ≤ m/ε + log(1/ε) + C log log(1/ε)` with `m < c` gives `e^{−c/ε} ≤ u` for small `ε`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.CrossLaws

/-- **Local Lipschitz bound at a zero.** If `e(x₀) = 0` and `e′(x₀) = ℓ₀ ≥ 0`, then for every `η > 0` there is `w ∈ (0, 1]` with
`|e(x)| ≤ (ℓ₀ + η)|x − x₀|` for `|x − x₀| ≤ w`. -/
theorem abs_le_of_hasDerivAt {e : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hd : HasDerivAt e ℓ₀ x₀) (he : e x₀ = 0) (hℓ : 0 ≤ ℓ₀) {η : ℝ}
    (hη : 0 < η) : ∃ w : ℝ, 0 < w ∧ w ≤ 1 ∧ ∀ x, |x - x₀| ≤ w → |e x| ≤ (ℓ₀ + η) * |x - x₀| := by
  obtain ⟨δ, hδ, h⟩ := StatFormal.MomentTrim.exists_deriv_bound hd he hη
  refine ⟨min (δ / 2) 1, lt_min (half_pos hδ) one_pos, min_le_right _ _, fun x hx => ?_⟩
  have hlt : |x - x₀| < δ := lt_of_le_of_lt (hx.trans (min_le_left _ _)) (by linarith)
  have h1 := h x hlt
  calc |e x| = |(e x - ℓ₀ * (x - x₀)) + ℓ₀ * (x - x₀)| := by rw [sub_add_cancel]
    _ ≤ |e x - ℓ₀ * (x - x₀)| + |ℓ₀ * (x - x₀)| := abs_add_le _ _
    _ ≤ η * |x - x₀| + ℓ₀ * |x - x₀| := by rw [abs_mul, abs_of_nonneg hℓ]; linarith
    _ = (ℓ₀ + η) * |x - x₀| := by ring

/-- A Lebesgue density of a probability measure is integrable. -/
theorem integrable_of_density {P : Measure ℝ} [IsProbabilityMeasure P] {p : ℝ → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (p x))) : Integrable p := by
  refine ⟨hpm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hp0)).mpr ?_⟩
  have h := congrArg (fun μ : Measure ℝ => μ univ) hP
  simp only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [← h]
  exact ENNReal.one_lt_top

/-- **`0 < TV(P, Q) < 1` at a transversal crossing.** For Lebesgue densities with the density formulas
`TV(P,Q) = ∫ (p − q)₊`, `P ∧ Q = min(p, q)·Leb` and `(P ∧ Q)(ℝ) = 1 − TV(P,Q)`, a linear lower bound `p − q ≥ ℓ(x − a)` (`ℓ > 0`)
and a constant lower bound `min(p, q) ≥ m > 0` on an interval `(a, a + δ)` give `0 < TV(P, Q) < 1`. -/
theorem tv_pos_lt_one {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (htv : StatFormal.Distances.tvDist P Q = ∫ x, max (p x - q x) 0)
    (hmin : P ⊓ Q = volume.withDensity (fun x => ENNReal.ofReal (min (p x) (q x))))
    (hmass : (P ⊓ Q) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q))
    {a δ ℓ m : ℝ} (hδ : 0 < δ) (hℓ : 0 < ℓ) (hm : 0 < m)
    (hlin : ∀ x ∈ Ioo a (a + δ), ℓ * (x - a) ≤ p x - q x)
    (hminpos : ∀ x ∈ Ioo a (a + δ), m ≤ min (p x) (q x)) :
    0 < StatFormal.Distances.tvDist P Q ∧ StatFormal.Distances.tvDist P Q < 1 := by
  have hvol : 0 < volume (Ioo a (a + δ)) := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
  constructor
  · rw [htv]
    have hint : Integrable (fun x => max (p x - q x) 0) := by
      refine (integrable_of_density hpm hp0 hP).mono' ((hpm.sub hqm).max measurable_const).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hq0 x]) (hp0 x)
    refine (integral_pos_iff_support_of_nonneg (fun x => le_max_right _ _) hint).mpr
      (lt_of_lt_of_le hvol (measure_mono fun x hx => ?_))
    have h1 := hlin x hx
    have h2 : 0 < ℓ * (x - a) := mul_pos hℓ (by linarith [hx.1])
    exact (lt_of_lt_of_le (lt_of_lt_of_le h2 h1) (le_max_left _ _)).ne'
  · have hlow : ENNReal.ofReal m * volume (Ioo a (a + δ)) ≤ (P ⊓ Q) univ := by
      rw [hmin, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← lintegral_indicator_const measurableSet_Ioo]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ Ioo a (a + δ)
      · rw [indicator_of_mem hx]; exact ENNReal.ofReal_le_ofReal (hminpos x hx)
      · rw [indicator_of_notMem hx]; exact bot_le
    have hpos : 0 < (P ⊓ Q) univ :=
      lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hm).ne' hvol.ne') hlow
    rw [hmass] at hpos
    linarith [ENNReal.ofReal_pos.mp hpos]

/-- The total variation of `P − Q` is at most `P + Q` (minimality of the Jordan decomposition). -/
theorem absPQ_le_add {α : Type*} [MeasurableSpace α] (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] (s : Set α) :
    (P.toSignedMeasure - Q.toSignedMeasure).totalVariation s ≤ P s + Q s := by
  have h := StatFormal.MomentTrim.totalVariation_le_of_eq_sub _ P Q rfl
  exact (h s).trans (le_of_eq (Measure.add_apply _ _ _))

/-- **The tail `T(ρ)` from the exponential tail.** If `μ({t < |x − x₀|}) ≤ C′e^{−t/C′}` for every `t > 0`, `C′ > 0`, then
`μ(ℝ ∖ B_{ρ−1}(x₀)) ≤ C_T e^{−ρ/a}` for `ρ ≥ 1`, with `a = 2C′` and `C_T = C′e^{1/(2C′)} + μ(ℝ)e^{1/C′}`. -/
theorem tailOut_le (μ : Measure ℝ) [IsFiniteMeasure μ] {x₀ C' : ℝ} (hC' : 0 < C')
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < |x - x₀|} ≤ ENNReal.ofReal (C' * Real.exp (-t / C'))) :
    ∃ CT a : ℝ, 0 < CT ∧ 0 < a ∧ ∀ ρ : ℝ, 1 ≤ ρ → (μ (Metric.ball x₀ (ρ - 1))ᶜ).toReal ≤ CT * Real.exp (-ρ / a) := by
  set M := (μ univ).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  refine ⟨C' * Real.exp (1 / (2 * C')) + M * Real.exp (1 / C'), 2 * C', by positivity, by positivity, fun ρ hρ => ?_⟩
  have he1 : 0 < Real.exp (-ρ / (2 * C')) := Real.exp_pos _
  rcases le_or_gt ρ 2 with hρ2 | hρ2
  · -- `ρ ∈ [1, 2]`: the whole mass
    have h1 : (μ (Metric.ball x₀ (ρ - 1))ᶜ).toReal ≤ M :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
    have h2 : M ≤ M * Real.exp (1 / C') * Real.exp (-ρ / (2 * C')) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 0 ≤ 1 / C' + -ρ / (2 * C') := by
        rw [div_add_div _ _ hC'.ne' (by positivity), le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith [Real.one_le_exp this]
    nlinarith [mul_pos (mul_pos hC' (Real.exp_pos (1 / (2 * C')))) he1]
  · -- `ρ > 2`: the tail at `t = (ρ − 1)/2`
    have ht : 0 < (ρ - 1) / 2 := by linarith
    have hsub : (Metric.ball x₀ (ρ - 1))ᶜ ⊆ {x | (ρ - 1) / 2 < |x - x₀|} := by
      intro x hx
      simp only [mem_compl_iff, Metric.mem_ball, not_lt, Real.dist_eq] at hx
      simp only [mem_ofPred_eq]
      linarith
    have h1 : (μ (Metric.ball x₀ (ρ - 1))ᶜ).toReal ≤ C' * Real.exp (-((ρ - 1) / 2) / C') :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_mono hsub).trans (htail _ ht))
    have h2 : C' * Real.exp (-((ρ - 1) / 2) / C') = C' * Real.exp (1 / (2 * C')) * Real.exp (-ρ / (2 * C')) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      field_simp
      ring
    rw [h2] at h1
    nlinarith [mul_nonneg (mul_nonneg hM0 (Real.exp_pos (1 / C')).le) he1.le]

/-- **The one-sided tail `T₊(t)` from the exponential tail.** -/
theorem tailPlus_le (μ : Measure ℝ) {x₀ C' : ℝ} (hC' : 0 < C')
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < |x - x₀|} ≤ ENNReal.ofReal (C' * Real.exp (-t / C'))) :
    ∀ t : ℝ, 0 < t → (μ (Ioi (x₀ + t))).toReal ≤ C' * Real.exp (-t / C') := by
  intro t ht
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_mono fun x hx => ?_).trans (htail t ht))
  simp only [mem_Ioi] at hx
  simp only [mem_ofPred_eq]
  rw [abs_of_pos (by linarith)]
  linarith

section Path

open StatFormal.TrimmedMMD.Unconditional

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `(1 − α)D_α ≤ D_α` for `α ≥ 0`. -/
theorem uPath_le_Dpop (φ : 𝒳 → H) (P Q : Measure 𝒳) {α : ℝ} (hα : 0 ≤ α) :
    StatFormal.Wave31ti.uPath φ P Q α ≤ Dpop φ P Q α := by
  have hD := StatFormal.MomentTrim.Dpop_nonneg φ P Q α
  unfold StatFormal.Wave31ti.uPath
  nlinarith

/-- `D_{a−ε} ≤ (1 − a)^{−1}(1 − (a − ε))D_{a−ε}` for `ε ≥ 0`, `a < 1` (adapted from chunk T's `RouteT.Dpop_le_uPath_div`). -/
theorem Dpop_le_uPath_div (φ : 𝒳 → H) (P Q : Measure 𝒳) {a ε : ℝ} (ha : a < 1) (hε : 0 ≤ ε) :
    Dpop φ P Q (a - ε) ≤ (1 - a)⁻¹ * StatFormal.Wave31ti.uPath φ P Q (a - ε) := by
  have h1a : 0 < 1 - a := by linarith
  have hD := StatFormal.MomentTrim.Dpop_nonneg φ P Q (a - ε)
  unfold StatFormal.Wave31ti.uPath
  rw [le_inv_mul_iff₀ h1a]
  nlinarith

end Path

/-- **No smaller exponent.** `c₀ε^{γ′} ≤ f(ε) ≤ Kε^γ` for all `ε ∈ (0, ε₀]`, with `c₀ > 0` and `γ′ < γ`, is impossible. -/
theorem false_of_lower_upper {f : ℝ → ℝ} {c₀ K γ γ' ε₀ : ℝ} (hc₀ : 0 < c₀) (hγ : γ' < γ) (hε₀ : 0 < ε₀)
    (hlow : ∀ e ∈ Ioc (0 : ℝ) ε₀, c₀ * e ^ γ' ≤ f e) (hup : ∀ e ∈ Ioc (0 : ℝ) ε₀, f e ≤ K * e ^ γ) : False := by
  have hδ : 0 < γ - γ' := by linarith
  have hlim : Tendsto (fun e : ℝ => K * e ^ (γ - γ')) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (γ - γ') (Or.inr hδ.le)).tendsto
    rw [Real.zero_rpow hδ.ne'] at h
    simpa using (h.mono_left nhdsWithin_le_nhds).const_mul K
  have hev1 : ∀ᶠ e in 𝓝[>] (0 : ℝ), K * e ^ (γ - γ') < c₀ := hlim.eventually (gt_mem_nhds hc₀)
  have hev2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), e ∈ Ioc (0 : ℝ) ε₀ := Ioc_mem_nhdsGT hε₀
  obtain ⟨e, he1, he2⟩ := (hev1.and hev2).exists
  have hpow : e ^ γ = e ^ (γ - γ') * e ^ γ' := by rw [← Real.rpow_add he2.1, sub_add_cancel]
  have hγ'pos : 0 < e ^ γ' := Real.rpow_pos_of_pos he2.1 _
  have hchain : c₀ * e ^ γ' ≤ K * e ^ (γ - γ') * e ^ γ' := by
    calc c₀ * e ^ γ' ≤ f e := hlow e he2
      _ ≤ K * e ^ γ := hup e he2
      _ = K * e ^ (γ - γ') * e ^ γ' := by rw [hpow]; ring
  exact lt_irrefl _ (lt_of_le_of_lt hchain (mul_lt_mul_of_pos_right he1 hγ'pos))

/-- `ε log(1/ε) ≤ 2√ε` for `ε > 0`. -/
theorem mul_log_inv_le {ε : ℝ} (hε : 0 < ε) : ε * Real.log (1 / ε) ≤ 2 * √ε := by
  have hy : 0 < 1 / ε := by positivity
  have h1 : Real.log (1 / ε) = 2 * Real.log √(1 / ε) := by rw [Real.log_sqrt hy.le]; ring
  have h2 : Real.log √(1 / ε) ≤ √(1 / ε) := by
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
    linarith
  have h3 : ε * √(1 / ε) = √ε := by
    rw [Real.sqrt_div' _ hε.le, Real.sqrt_one, mul_one_div, Real.div_sqrt]
  rw [h1]
  nlinarith

/-- **From the logarithmic bound to an exponential margin.** If `0 < ε < e^{−1}`, `m < c`, `ε ≤ ((c − m)/(2(1 + |C|)))²` and
`log(1/u) ≤ m/ε + log(1/ε) + C log log(1/ε)` with `u > 0`, then `e^{−c/ε} ≤ u`. -/
theorem exp_le_of_log_bound {u ε m c C : ℝ} (hu : 0 < u) (hε : 0 < ε) (hεe : ε < Real.exp (-1)) (hmc : m < c)
    (hsmall : ε ≤ ((c - m) / (2 * (1 + |C|))) ^ 2)
    (hlog : Real.log (1 / u) ≤ m / ε + Real.log (1 / ε) + C * Real.log (Real.log (1 / ε))) :
    Real.exp (-c / ε) ≤ u := by
  set L := Real.log (1 / ε) with hL
  have hL1 : 1 < L := by
    have h := Real.log_lt_log hε hεe
    rw [Real.log_exp] at h
    rw [hL, one_div, Real.log_inv]
    linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL1
  have hlogL' : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L)]
  have hCL : C * Real.log L ≤ |C| * L := by
    calc C * Real.log L ≤ |C| * Real.log L := mul_le_mul_of_nonneg_right (le_abs_self C) hlogL.le
      _ ≤ |C| * L := mul_le_mul_of_nonneg_left hlogL' (abs_nonneg C)
  have hC1 : 0 < 1 + |C| := by positivity
  have hsq : √ε ≤ (c - m) / (2 * (1 + |C|)) := by
    have := Real.sqrt_le_sqrt hsmall
    rwa [Real.sqrt_sq (div_nonneg (by linarith) (by positivity))] at this
  have hεL : ε * L ≤ 2 * √ε := mul_log_inv_le hε
  have hkey : ε * ((1 + |C|) * L) ≤ c - m := by
    calc ε * ((1 + |C|) * L) = (1 + |C|) * (ε * L) := by ring
      _ ≤ (1 + |C|) * (2 * √ε) := mul_le_mul_of_nonneg_left hεL hC1.le
      _ ≤ (1 + |C|) * (2 * ((c - m) / (2 * (1 + |C|)))) := by gcongr
      _ = c - m := by field_simp
  have hbound : m / ε + L + C * Real.log L ≤ c / ε := by
    have : (1 + |C|) * L ≤ (c - m) / ε := by rw [le_div_iff₀ hε]; linarith
    have e1 : (c - m) / ε = c / ε - m / ε := by ring
    linarith
  have h1 : Real.log (1 / u) ≤ c / ε := hlog.trans hbound
  rw [one_div, Real.log_inv] at h1
  have h2 : -c / ε ≤ Real.log u := by rw [neg_div]; linarith
  exact (Real.le_log_iff_exp_le hu).mp h2

end StatFormal.CrossLaws
