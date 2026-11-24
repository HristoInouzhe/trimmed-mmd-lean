import StatFormal.Lib.LaplaceDev.Pieces

set_option linter.style.longLine false

/-!
# One-sample deviation of a function with square-root variation (library, untrusted)

For laws `μ̃, μ` on `ℝ` satisfying the interval event `IntervalDev μ̃ μ ε ζ` and the localized deviation bound
`LocalDev μ̃ μ ε ζ`, and a continuous `f` with `|f| ≤ 1`, `osc(f) ≤ 1` and variation at most `(2λ)^{1/2}N` on every
interval of length `λ` (the functions of the unit ball of the Laplace RKHS scaled by `N`, `eq:laphone` of trimmed-mmd), this
file bounds `|∫ f d(μ̃ − μ)|` as in the proof of Lemma S4.25 of trimmed-mmd, one sample at a time:

* `localDev_piece`: the localized bound on one bounded interval `I` with `Ī ⊆ [a,b]`, for `h = c − f` or `h = f − c` with
  values in `[0,1]`, in terms of any `V ≥ (2(b−a))^{1/2}N` and any bound `B ≥ ∫_I h dμ`;
* `one_sample_a`: (a), the window `W = [x₀−K, x₀+K]`: `f = m + h` on `W` (`m = inf f`), the event on `W` and on the two
  half-lines off `W`:
  `|∫ f d(μ̃−μ)| ≤ (2ε)^{1/2} + ζ + (2(2K^{1/2}N+1)ε)^{1/2} + (2K^{1/2}N+1)ζ + 2μ(|z−x₀|>K) + 2ε^{1/2} + 2ζ`;
* `one_sample_b`: (b), the half-lines `R₊ = (x₀,∞)`, `R₋ = (−∞,x₀]`: `f = M − h` on `R₊`, `f = m + h` on `R₋`, each split
  into a short interval of width `w`, an interval out to `x₀ ± K` and a tail; with `μ` of the short intervals at most `B₁`
  and `∫ h dμ` on the two middle intervals at most `B₂`:
  `|∫ f d(μ̃−μ)| ≤ (2ε)^{1/2} + ζ + 2[(2(√(2w)N+1)B₁ε)^{1/2} + (√(2w)N+1)ζ] + 2[(2(√(2K)N+1)B₂ε)^{1/2} + (√(2K)N+1)ζ]
  + 2μ(|z−x₀|>K) + 2ε^{1/2} + 2ζ`.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.LaplaceDev

variable {μt μ : Measure ℝ} [IsProbabilityMeasure μt] [IsProbabilityMeasure μ] {ε ζ : ℝ}

omit [IsProbabilityMeasure μt] [IsProbabilityMeasure μ] in
/-- The localized bound on one bounded interval `I` with `Ī ⊆ [a, b]`, for a `[0,1]`-valued `h` whose variation is at most
that of `f`, with any `V ≥ (2(b−a))^{1/2}N` and any `B ≥ ∫_I h dμ`. -/
theorem localDev_piece (hbv : LocalDev μt μ ε ζ) (hε : 0 ≤ ε) {f : ℝ → ℝ} {N : ℝ} (hN : 0 ≤ N)
    (hvar : ∀ a b, a ≤ b → eVariationOn f (Icc a b) ≤ ENNReal.ofReal (√(2 * (b - a)) * N))
    {h : ℝ → ℝ} (hhc : Continuous h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1) (hhv : ∀ s, eVariationOn h s ≤ eVariationOn f s)
    {I : Set ℝ} (hIo : I.OrdConnected) (hIb : Bornology.IsBounded I) {a b : ℝ} (hab : a ≤ b) (hcl : closure I ⊆ Icc a b)
    {V B : ℝ} (hV : √(2 * (b - a)) * N ≤ V) (hB : ∫ z in I, h z ∂μ ≤ B) :
    |(∫ z in I, h z ∂μt) - ∫ z in I, h z ∂μ| ≤ √(2 * (V + 1) * B * ε) + (V + 1) * ζ := by
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  have hvarI : eVariationOn h (closure I) ≤ ENNReal.ofReal V :=
    ((eVariationOn.mono h hcl).trans (hhv _)).trans ((hvar a b hab).trans (ENNReal.ofReal_le_ofReal hV))
  refine (hbv I h V hIo hIb hh01 hhc.continuousOn hV0 hvarI).trans (add_le_add_left (Real.sqrt_le_sqrt ?_) _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by linarith)) hε

/-- Boundedness facts for `|f| ≤ 1`, `osc f ≤ 1`: `m ≤ f ≤ M`, `|m| ≤ 1`, `0 ≤ M − m ≤ 1`. -/
theorem bdd_facts {f : ℝ → ℝ} (hf1 : ∀ z, |f z| ≤ 1) (hosc : (⨆ z, f z) - (⨅ z, f z) ≤ 1) :
    (∀ z, (⨅ y, f y) ≤ f z) ∧ (∀ z, f z ≤ ⨆ y, f y) ∧ |⨅ y, f y| ≤ 1 ∧ 0 ≤ (⨆ y, f y) - (⨅ y, f y) ∧
      (⨆ y, f y) - (⨅ y, f y) ≤ 1 := by
  have hbA : BddAbove (range f) := ⟨1, by rintro _ ⟨z, rfl⟩; exact (abs_le.1 (hf1 z)).2⟩
  have hbB : BddBelow (range f) := ⟨-1, by rintro _ ⟨z, rfl⟩; exact (abs_le.1 (hf1 z)).1⟩
  have hmf : ∀ z, (⨅ y, f y) ≤ f z := fun z => ciInf_le hbB z
  have hfM : ∀ z, f z ≤ ⨆ y, f y := fun z => le_ciSup hbA z
  refine ⟨hmf, hfM, abs_le.2 ⟨le_ciInf fun z => (abs_le.1 (hf1 z)).1, (hmf 0).trans (abs_le.1 (hf1 0)).2⟩,
    by linarith [hmf 0, hfM 0], hosc⟩

/-- Lemma S4.25 (a) of trimmed-mmd, one sample: the window `[x₀−K, x₀+K]` and the two half-lines off it. -/
theorem one_sample_a (hI : IntervalDev μt μ ε ζ) (hbv : LocalDev μt μ ε ζ) (hε : 0 ≤ ε)
    {f : ℝ → ℝ} (hfc : Continuous f) (hf1 : ∀ z, |f z| ≤ 1) (hosc : (⨆ z, f z) - (⨅ z, f z) ≤ 1)
    {N : ℝ} (hN : 0 ≤ N) (hvar : ∀ a b, a ≤ b → eVariationOn f (Icc a b) ≤ ENNReal.ofReal (√(2 * (b - a)) * N))
    (x₀ : ℝ) {K : ℝ} (hK : 1 ≤ K) :
    |(∫ z, f z ∂μt) - ∫ z, f z ∂μ| ≤
      √(2 * ε) + ζ + (√(2 * (2 * √K * N + 1) * 1 * ε) + (2 * √K * N + 1) * ζ) +
        (2 * μ.real {z | K < |z - x₀|} + 2 * √ε + 2 * ζ) := by
  obtain ⟨hmf, hfM, hm1, -, -⟩ := bdd_facts hf1 hosc
  set m := ⨅ z, f z with hm
  have hh01 : ∀ z, 0 ≤ f z - m ∧ f z - m ≤ 1 := fun z => ⟨sub_nonneg.2 (hmf z), by linarith [hfM z]⟩
  have hhc : Continuous fun z => f z - m := hfc.sub continuous_const
  have hh1 : ∀ z, |f z - m| ≤ 1 := fun z => abs_le.2 ⟨by linarith [(hh01 z).1], (hh01 z).2⟩
  have hK0 : (0 : ℝ) ≤ K := by linarith
  set W := Icc (x₀ - K) (x₀ + K) with hWdef
  have hsplit : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ∫ z, f z ∂ν =
      m * ν.real W + ∫ z in W, (f z - m) ∂ν + ∫ z in Iio (x₀ - K), f z ∂ν + ∫ z in Ioi (x₀ + K), f z ∂ν := by
    intro ν _
    rw [integral_window_split hfc hf1 hK0]
    have : ∫ z in W, (f z - m) ∂ν = ∫ z in W, f z ∂ν - ν.real W * m := by
      rw [integral_sub (integrable_of_bdd hfc hf1).integrableOn (integrable_const m), setIntegral_const, smul_eq_mul]
    rw [this]; ring
  have key : (∫ z, f z ∂μt) - ∫ z, f z ∂μ =
      (m * μt.real W - m * μ.real W) + ((∫ z in W, (f z - m) ∂μt) - ∫ z in W, (f z - m) ∂μ) +
        ((∫ z in Iio (x₀ - K), f z ∂μt) - ∫ z in Iio (x₀ - K), f z ∂μ) +
        ((∫ z in Ioi (x₀ + K), f z ∂μt) - ∫ z in Ioi (x₀ + K), f z ∂μ) := by
    rw [hsplit μt, hsplit μ]; ring
  -- the constant part on the window
  have hWm : |m * μt.real W - m * μ.real W| ≤ √(2 * ε) + ζ := by
    rw [← mul_sub, abs_mul]
    have h1 : √(2 * μ.real W * ε) ≤ √(2 * ε) := by
      apply Real.sqrt_le_sqrt
      have := measureReal_le_one (μ := μ) (s := W)
      have := measureReal_nonneg (μ := μ) (s := W)
      nlinarith
    have h2 := hI W ordConnected_Icc
    calc |m| * |μt.real W - μ.real W| ≤ 1 * |μt.real W - μ.real W| := mul_le_mul_of_nonneg_right hm1 (abs_nonneg _)
      _ ≤ _ := by linarith
  -- the window, by the localized bound
  have hlen : √(2 * (x₀ + K - (x₀ - K))) * N ≤ 2 * √K * N := by
    have : √(2 * (x₀ + K - (x₀ - K))) = 2 * √K := by
      rw [show 2 * (x₀ + K - (x₀ - K)) = 2 ^ 2 * K by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [this]
  have hint : ∫ z in W, (f z - m) ∂μ ≤ 1 := by
    have h1 := abs_setIntegral_le (ν := μ) hh1 W
    have h2 := measureReal_le_one (μ := μ) (s := W)
    have h3 := le_abs_self (∫ z in W, (f z - m) ∂μ)
    nlinarith
  have hWb := localDev_piece hbv hε hN hvar hhc hh01 (fun s => eVariationOn_sub_const_le f m s) ordConnected_Icc
    (Metric.isBounded_Icc _ _) (by linarith) (closure_minimal subset_rfl isClosed_Icc) hlen hint
  -- the two half-lines off the window
  have htL := abs_setIntegral_sub_le (ν₁ := μt) (ν₂ := μ) hf1 (Iio (x₀ - K))
  have htR := abs_setIntegral_sub_le (ν₁ := μt) (ν₂ := μ) hf1 (Ioi (x₀ + K))
  have ht := tails_le hI x₀ hK0
  rw [key]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add_left (abs_add_le _ _) _).trans ?_
  have := abs_add_le (m * μt.real W - m * μ.real W) ((∫ z in W, (f z - m) ∂μt) - ∫ z in W, (f z - m) ∂μ)
  linarith

/-- Lemma S4.25 (b) of trimmed-mmd, one sample: the half-lines `(x₀, ∞)` and `(−∞, x₀]`, each split into a short interval of
width `w`, an interval out to `x₀ ± K` and a tail. -/
theorem one_sample_b (hI : IntervalDev μt μ ε ζ) (hbv : LocalDev μt μ ε ζ) (hε : 0 ≤ ε)
    {f : ℝ → ℝ} (hfc : Continuous f) (hf1 : ∀ z, |f z| ≤ 1) (hosc : (⨆ z, f z) - (⨅ z, f z) ≤ 1)
    {N : ℝ} (hN : 0 ≤ N) (hvar : ∀ a b, a ≤ b → eVariationOn f (Icc a b) ≤ ENNReal.ofReal (√(2 * (b - a)) * N))
    (x₀ : ℝ) {K w B₁ B₂ : ℝ} (hK : 1 ≤ K) (hw : 0 < w) (hw1 : w ≤ 1)
    (h1R : μ.real (Ioc x₀ (x₀ + w)) ≤ B₁) (h1L : μ.real (Ioc (x₀ - w) x₀) ≤ B₁)
    (h2R : ∫ z in Ioc (x₀ + w) (x₀ + K), ((⨆ y, f y) - f z) ∂μ ≤ B₂)
    (h2L : ∫ z in Icc (x₀ - K) (x₀ - w), (f z - ⨅ y, f y) ∂μ ≤ B₂) :
    |(∫ z, f z ∂μt) - ∫ z, f z ∂μ| ≤
      √(2 * ε) + ζ + 2 * (√(2 * (√(2 * w) * N + 1) * B₁ * ε) + (√(2 * w) * N + 1) * ζ) +
        2 * (√(2 * (√(2 * K) * N + 1) * B₂ * ε) + (√(2 * K) * N + 1) * ζ) +
        (2 * μ.real {z | K < |z - x₀|} + 2 * √ε + 2 * ζ) := by
  obtain ⟨hmf, hfM, -, hMm0, hMm1⟩ := bdd_facts hf1 hosc
  set M := ⨆ z, f z with hM
  set m := ⨅ z, f z with hm
  have hp01 : ∀ z, 0 ≤ M - f z ∧ M - f z ≤ 1 := fun z => ⟨sub_nonneg.2 (hfM z), by linarith [hmf z]⟩
  have hn01 : ∀ z, 0 ≤ f z - m ∧ f z - m ≤ 1 := fun z => ⟨sub_nonneg.2 (hmf z), by linarith [hfM z]⟩
  have hpc : Continuous fun z => M - f z := continuous_const.sub hfc
  have hnc : Continuous fun z => f z - m := hfc.sub continuous_const
  have hp1 : ∀ z, |M - f z| ≤ 1 := fun z => abs_le.2 ⟨by linarith [(hp01 z).1], (hp01 z).2⟩
  have hn1 : ∀ z, |f z - m| ≤ 1 := fun z => abs_le.2 ⟨by linarith [(hn01 z).1], (hn01 z).2⟩
  have hwK : w ≤ K := by linarith
  have hsplit : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ∫ z, f z ∂ν =
      M * ν.real (Ioi x₀) - (∫ z in Ioc x₀ (x₀ + w), (M - f z) ∂ν + ∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) ∂ν +
        ∫ z in Ioi (x₀ + K), (M - f z) ∂ν) +
      (m * (1 - ν.real (Ioi x₀)) + (∫ z in Ioc (x₀ - w) x₀, (f z - m) ∂ν + ∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) ∂ν +
        ∫ z in Iio (x₀ - K), (f z - m) ∂ν)) := by
    intro ν _
    have hfi := integrable_of_bdd (ν := ν) hfc hf1
    rw [← setIntegral_Ioi_split hpc hp1 hw.le hwK, ← setIntegral_Iic_split hnc hn1 hw.le hwK,
      integral_eq_Ioi_add_Iic hfc hf1 x₀]
    have hc : ν.real (Iic x₀) = 1 - ν.real (Ioi x₀) := by
      rw [← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi]
    rw [integral_sub (integrable_const M).integrableOn hfi.integrableOn, setIntegral_const, smul_eq_mul,
      integral_sub hfi.integrableOn (integrable_const m).integrableOn, setIntegral_const, smul_eq_mul, hc]
    ring
  set dR := μt.real (Ioi x₀) - μ.real (Ioi x₀) with hdR
  have key : (∫ z, f z ∂μt) - ∫ z, f z ∂μ =
      (M - m) * dR -
        (((∫ z in Ioc x₀ (x₀ + w), (M - f z) ∂μt) - ∫ z in Ioc x₀ (x₀ + w), (M - f z) ∂μ) +
          ((∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) ∂μt) - ∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) ∂μ) +
          ((∫ z in Ioi (x₀ + K), (M - f z) ∂μt) - ∫ z in Ioi (x₀ + K), (M - f z) ∂μ)) +
        (((∫ z in Ioc (x₀ - w) x₀, (f z - m) ∂μt) - ∫ z in Ioc (x₀ - w) x₀, (f z - m) ∂μ) +
          ((∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) ∂μt) - ∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) ∂μ) +
          ((∫ z in Iio (x₀ - K), (f z - m) ∂μt) - ∫ z in Iio (x₀ - K), (f z - m) ∂μ)) := by
    rw [hsplit μt, hsplit μ, hdR]; ring
  -- the mass of the right half-line
  have hR0 : |(M - m) * dR| ≤ √(2 * ε) + ζ := by
    rw [abs_mul, abs_of_nonneg hMm0]
    have h1 : √(2 * μ.real (Ioi x₀) * ε) ≤ √(2 * ε) := by
      apply Real.sqrt_le_sqrt
      have := measureReal_le_one (μ := μ) (s := Ioi x₀)
      have := measureReal_nonneg (μ := μ) (s := Ioi x₀)
      nlinarith
    have h2 := hI (Ioi x₀) ordConnected_Ioi
    calc (M - m) * |dR| ≤ 1 * |dR| := mul_le_mul_of_nonneg_right hMm1 (abs_nonneg _)
      _ ≤ _ := by rw [hdR]; linarith
  -- the short intervals
  have hint1 : ∀ S : Set ℝ, ∀ {h : ℝ → ℝ}, (∀ z, |h z| ≤ 1) → μ.real S ≤ B₁ → ∫ z in S, h z ∂μ ≤ B₁ := by
    intro S h hh hS
    have := abs_setIntegral_le (ν := μ) hh S
    have := le_abs_self (∫ z in S, h z ∂μ)
    linarith
  have hsw : √(2 * (x₀ + w - x₀)) * N ≤ √(2 * w) * N := by rw [add_sub_cancel_left]
  have hsw' : √(2 * (x₀ - (x₀ - w))) * N ≤ √(2 * w) * N := by rw [sub_sub_cancel]
  have hsK : √(2 * (x₀ + K - (x₀ + w))) * N ≤ √(2 * K) * N :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hN
  have hsK' : √(2 * (x₀ - w - (x₀ - K))) * N ≤ √(2 * K) * N :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hN
  have hI1 := localDev_piece hbv hε hN hvar hpc hp01 (fun s => eVariationOn_const_sub_le f M s) ordConnected_Ioc
    (Metric.isBounded_Ioc _ _) (by linarith : x₀ ≤ x₀ + w) (closure_minimal Ioc_subset_Icc_self isClosed_Icc) hsw
    (hint1 _ hp1 h1R)
  have hI2 := localDev_piece hbv hε hN hvar hpc hp01 (fun s => eVariationOn_const_sub_le f M s) ordConnected_Ioc
    (Metric.isBounded_Ioc _ _) (by linarith : x₀ + w ≤ x₀ + K) (closure_minimal Ioc_subset_Icc_self isClosed_Icc) hsK h2R
  have hJ1 := localDev_piece hbv hε hN hvar hnc hn01 (fun s => eVariationOn_sub_const_le f m s) ordConnected_Ioc
    (Metric.isBounded_Ioc _ _) (by linarith : x₀ - w ≤ x₀) (closure_minimal Ioc_subset_Icc_self isClosed_Icc) hsw'
    (hint1 _ hn1 h1L)
  have hJ2 := localDev_piece hbv hε hN hvar hnc hn01 (fun s => eVariationOn_sub_const_le f m s) ordConnected_Icc
    (Metric.isBounded_Icc _ _) (by linarith : x₀ - K ≤ x₀ - w) (closure_minimal subset_rfl isClosed_Icc) hsK' h2L
  -- the tails
  have htR := abs_setIntegral_sub_le (ν₁ := μt) (ν₂ := μ) hp1 (Ioi (x₀ + K))
  have htL := abs_setIntegral_sub_le (ν₁ := μt) (ν₂ := μ) hn1 (Iio (x₀ - K))
  have ht := tails_le hI x₀ (by linarith : (0 : ℝ) ≤ K)
  rw [key]
  set a1 := (∫ z in Ioc x₀ (x₀ + w), (M - f z) ∂μt) - ∫ z in Ioc x₀ (x₀ + w), (M - f z) ∂μ
  set a2 := (∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) ∂μt) - ∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) ∂μ
  set a3 := (∫ z in Ioi (x₀ + K), (M - f z) ∂μt) - ∫ z in Ioi (x₀ + K), (M - f z) ∂μ
  set b1 := (∫ z in Ioc (x₀ - w) x₀, (f z - m) ∂μt) - ∫ z in Ioc (x₀ - w) x₀, (f z - m) ∂μ
  set b2 := (∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) ∂μt) - ∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) ∂μ
  set b3 := (∫ z in Iio (x₀ - K), (f z - m) ∂μt) - ∫ z in Iio (x₀ - K), (f z - m) ∂μ
  have e1 := abs_sub ((M - m) * dR) (a1 + a2 + a3)
  have e2 := abs_add_le ((M - m) * dR - (a1 + a2 + a3)) (b1 + b2 + b3)
  have e3 := abs_add_le (a1 + a2) a3
  have e4 := abs_add_le a1 a2
  have e5 := abs_add_le (b1 + b2) b3
  have e6 := abs_add_le b1 b2
  linarith

end StatFormal.LaplaceDev
