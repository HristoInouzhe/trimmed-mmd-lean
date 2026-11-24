import StatFormal.Lib.MollifierNorm.Tail
import StatFormal.Lib.MollifierNorm.Shells
import StatFormal.Lib.MollifierNorm.Laplacian
import StatFormal.Lib.FourierOps.Mollify
import StatFormal.Wave31tp.RouteF

/-!
# The Sobolev norm of a mollified translation-Lipschitz indicator (library, untrusted)

Let `V` be a real inner-product space of dimension `d ≥ 1`, `E ⊆ V` bounded and measurable with the translation bound
`Leb(E △ (E + h)) ≤ Π‖h‖` (`Π ≥ 0`), `b ∈ C_c^∞(V)` a probability density supported in the closed unit ball,
`b_w = w^{−d} b(·/w)` and `f_w = 1_E ∗ b_w`. For `s > 1/2`, `m ∈ ℕ` with `4m > 2s − 1` and `0 < w ≤ 1`, in Mathlib's Fourier
convention (`𝓕 g(η) = ∫ g(x) e^{−2πi⟪x, η⟫} dx`, Sobolev functional `∫ |𝓕 f|² (1 + 4π²‖η‖²)^s`, `Wave31tp.sobolevS`):
`∫ |𝓕 f_w(η)|² (1 + 4π²‖η‖²)^s dη ≤ 2^s Leb(E) + 2^{3s} Π/(2c_d) · w^{1−2s} [1/(1 − 2^{1−2s}) + C_b²/(1 − 2^{−(4m+1−2s)})]`,
`c_d = 1 − sup_{y ≥ 1} j_d(y)`, `C_b = ‖Δ^m b‖_{L¹}` (Lemma S4.9 of trimmed-mmd, whose angular form differs by the change of
variables `ξ = 2πη`, `lintegral_comp_inv_smul`).

Proof: `𝓕 f_w(η) = 𝓕 1_E(η) 𝓕 b(wη)` (`FourierOps.mollify_smooth_facts`); `∫ |𝓕 1_E|² = Leb(E)` (Plancherel); the Fourier tail
of `1_E` beyond `2π‖η‖ ≥ t` is at most `Π/(2c_d t)` (`lintegral_fourier_tail_le`); `|𝓕 b| ≤ 1` and
`|𝓕 b(wη)| ≤ C_b (2πw‖η‖)^{−2m}` (`norm_fourier_ofReal_le_laplacian`); the dyadic shells in the radius `u = 2π‖η‖`
(`lintegral_shells_le`). A set with a negative translation constant is null (`volume_eq_zero_of_translation_neg`).
-/

noncomputable section
open MeasureTheory Set Metric FourierTransform Laplacian
open scoped InnerProductSpace RealInnerProductSpace ENNReal ContDiff symmDiff

namespace StatFormal.MollifierNorm

open StatFormal.Wave31tp (sobolevS mollify dilateR ft2 jBall)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Scaling of a lower integral**: `∫⁻ g(ξ/c) dξ = c^d ∫⁻ g` for `c > 0`, `d = finrank ℝ V` (from `Measure.map_addHaar_smul`). -/
theorem lintegral_comp_inv_smul (g : V → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    ∫⁻ ξ, g (c⁻¹ • ξ) = ENNReal.ofReal (c ^ Module.finrank ℝ V) * ∫⁻ η, g η := by
  have hmap := Measure.map_addHaar_smul (volume : Measure V) hc.ne'
  have hcoe : (⇑(MeasurableEquiv.smul₀ c hc.ne' : V ≃ᵐ V) : V → V) = (c • ·) := rfl
  have h1 : ∫⁻ η, g η = ∫⁻ ξ, g (c⁻¹ • ξ) ∂(Measure.map (c • ·) volume) := by
    rw [← hcoe, lintegral_map_equiv (fun ξ => g (c⁻¹ • ξ)) (MeasurableEquiv.smul₀ c hc.ne')]
    simp [hcoe, smul_smul, inv_mul_cancel₀ hc.ne']
  rw [h1, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- A bounded set whose translation bound has a negative constant is null: for `h` longer than twice a bound of `E`, the sets
`E` and `E + h` are disjoint, so `Leb(E) ≤ Leb(E △ (E + h)) ≤ ofReal(Π‖h‖) = 0`. -/
theorem volume_eq_zero_of_translation_neg [Nontrivial V] {E : Set V} (hEb : Bornology.IsBounded E) {Per : ℝ}
    (hPer : Per < 0) (htr : ∀ h : V, volume (E ∆ ((· - h) ⁻¹' E)) ≤ ENNReal.ofReal (Per * ‖h‖)) : volume E = 0 := by
  obtain ⟨R, hR⟩ := hEb.subset_closedBall 0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set h : V := ((2 * |R| + 1) / ‖v‖) • v
  have hh : ‖h‖ = 2 * |R| + 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv)]
  have hsub : E ⊆ E ∆ ((· - h) ⁻¹' E) := by
    intro x hx
    refine Or.inl ⟨hx, fun hxh => ?_⟩
    have h1 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    have h2 : ‖x - h‖ ≤ R := mem_closedBall_zero_iff.1 (hR hxh)
    have : ‖h‖ ≤ ‖x‖ + ‖x - h‖ := by
      calc ‖h‖ = ‖x - (x - h)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - h‖ := norm_sub_le _ _
    rw [hh] at this
    linarith [le_abs_self R]
  refine le_antisymm ((measure_mono hsub).trans ((htr h).trans ?_)) bot_le
  exact (ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonpos_of_nonneg hPer.le (norm_nonneg _))).le

variable {d : ℕ} [NeZero d]

/-- **The Sobolev bound of a mollified indicator** (Lemma S4.9 of trimmed-mmd in Mathlib's convention): for `E` bounded,
measurable, with `Leb(E △ (E + h)) ≤ Π‖h‖`, `Π ≥ 0`, and `b ∈ C_c^∞` a probability density in the closed unit ball,
`sobolevS s (1_E ∗ b_w) ≤ 2^s Leb(E) + 2^{3s} (Π/(2c_d)) w^{1−2s} [1/(1 − 2^{1−2s}) + C_b²/(1 − 2^{−(4m+1−2s)})]` for
`s > 1/2`, `4m > 2s − 1`, `0 < w ≤ 1`. -/
theorem sobolevS_mollify_le (hd : Module.finrank ℝ V = d) {s Per w : ℝ} {E : Set V} {b : V → ℝ} {m : ℕ}
    (hs : 1 / 2 < s) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) (hPer : 0 ≤ Per)
    (htr : ∀ h : V, volume (E ∆ ((· - h) ⁻¹' E)) ≤ ENNReal.ofReal (Per * ‖h‖))
    (hb : ContDiff ℝ ∞ b) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∫ x, b x = 1) (hbs : Function.support b ⊆ closedBall 0 1)
    (hm : 2 * s - 1 < 4 * m) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    sobolevS s (fun x => (mollify E (dilateR w b) x : ℂ)) ≤
      ENNReal.ofReal (2 ^ s * (volume E).toReal) +
      ENNReal.ofReal (2 ^ (3 * s) * (Per / (2 * (1 - sSup (jBall d '' Ici 1)))) * (w ^ (1 - 2 * s) *
        (1 / (1 - (2 : ℝ) ^ (1 - 2 * s)) + (∫ x, |((Δ : (V → ℝ) → (V → ℝ))^[m] b) x|) ^ 2 /
          (1 - (2 : ℝ) ^ (-(4 * m + 1 - 2 * s)))))) := by
  obtain ⟨-, -, -, -, -, hint, hL2, hF⟩ := FourierOps.mollify_smooth_facts hE hEb hb hb0 hb1 hbs hw0
  set f : V → ℂ := fun x => (mollify E (dilateR w b) x : ℂ) with hfdef
  have hf1 : Integrable f := hint.ofReal
  have hf2 : MemLp f 2 := hL2.ofReal
  set g : V → ℂ := fun x => ((E.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) with hgdef
  have hg_eq : g = E.indicator (fun _ => (1 : ℂ)) := by
    funext x; by_cases hx : x ∈ E <;> simp [g, hx]
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hg1 : Integrable g := by rw [hg_eq]; exact (integrable_indicator_iff hE).2 (integrableOn_const hEfin)
  have hg2 : MemLp g 2 := by rw [hg_eq]; exact memLp_indicator_const 2 hE.nullMeasurableSet _ (Or.inr hEfin)
  set bc : V → ℂ := fun x => (b x : ℂ) with hbc
  set Cb : ℝ := ∫ x, |((Δ : (V → ℝ) → (V → ℝ))^[m] b) x|
  have hCb : 0 ≤ Cb := integral_nonneg fun x => abs_nonneg _
  have hbcs : HasCompactSupport b :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun x hx => Function.notMem_support.1 fun h => hx (hbs h)
  have hbint : Integrable b := hb.continuous.integrable_of_hasCompactSupport hbcs
  have hbc_norm : ∫ x, ‖bc x‖ = 1 := by
    simp only [bc, Complex.norm_real, Real.norm_eq_abs]
    rw [← hb1]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => abs_of_nonneg (hb0 x))
  -- the integrand
  have hft : ft2 f =ᵐ[volume] 𝓕 f := by
    rw [Wave31tp.RouteF.ft2_eq hf2]; exact FourierL2.fourier_toLp_ae hf1 hf2
  have hcongr : ∀ᵐ η ∂volume, ‖ft2 f η‖ₑ ^ 2 * ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ s) =
      ENNReal.ofReal (‖𝓕 g η‖ ^ 2) * ENNReal.ofReal (‖𝓕 bc (w • η)‖ ^ 2) *
        ENNReal.ofReal ((1 + (2 * Real.pi * ‖η‖) ^ 2) ^ s) := by
    filter_upwards [hft] with η hη
    rw [hη, hF η, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow, ← norm_mul, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
    congr 3
    ring
  unfold sobolevS
  rw [lintegral_congr_ae hcongr]
  -- the hypotheses of the shell bound
  set cd : ℝ := 1 - sSup (jBall d '' Ici 1)
  have hcd0 : 0 < cd := by linarith [JBall.sSup_jBall_Ici_one_lt_one (d := d)]
  have htot : ∫⁻ η, ENNReal.ofReal (‖𝓕 g η‖ ^ 2) ≤ ENNReal.ofReal (volume E).toReal := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_fourier_sq hg1 hg2)
      (Filter.Eventually.of_forall fun η => sq_nonneg _), (FourierL2.plancherel_L1L2 hg1 hg2 hg1 hg2).2.1]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    have : (fun x => ‖g x‖ ^ 2) = E.indicator (1 : V → ℝ) := by
      funext x; by_cases hx : x ∈ E <;> simp [g, hx]
    rw [this, integral_indicator_one hE, measureReal_def]
  have htr2 : ∀ h : V, ∫ x, ‖g (x + h) - g x‖ ^ 2 ≤ Per * ‖h‖ := by
    intro h
    rw [hg_eq, FourierOps.integral_norm_indicator_increment_sq hE h, FourierOps.volume_symmDiff_add_eq_sub E h]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (htr h)
  have htail : ∀ t : ℝ, 0 < t → ∫⁻ η in {η | t ≤ 2 * Real.pi * ‖η‖}, ENNReal.ofReal (‖𝓕 g η‖ ^ 2) ≤
      ENNReal.ofReal (Per / (2 * cd) / t) := by
    intro t ht
    rw [div_div]
    exact lintegral_fourier_tail_le hd hg1 hg2 hPer htr2 ht
  have hB1 : ∀ η : V, ENNReal.ofReal (‖𝓕 bc (w • η)‖ ^ 2) ≤ 1 := by
    intro η
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have := FourierOps.norm_fourier_le_integral_norm bc (w • η)
    rw [hbc_norm] at this
    nlinarith [norm_nonneg (𝓕 bc (w • η))]
  have hB2 : ∀ η : V, 0 < 2 * Real.pi * ‖η‖ → ENNReal.ofReal (‖𝓕 bc (w • η)‖ ^ 2) ≤
      ENNReal.ofReal (Cb ^ 2 * ((w * (2 * Real.pi * ‖η‖)) ^ (4 * m))⁻¹) := by
    intro η hη
    refine ENNReal.ofReal_le_ofReal ?_
    have hη0 : η ≠ 0 := by rintro rfl; simp at hη
    have hwη : w • η ≠ 0 := smul_ne_zero hw0.ne' hη0
    have h := norm_fourier_ofReal_le_laplacian hb hbcs m hwη
    have hX : 0 < w * (2 * Real.pi * ‖η‖) := mul_pos hw0 hη
    have heq : ((4 * Real.pi ^ 2 * ‖w • η‖ ^ 2)⁻¹) ^ m = ((w * (2 * Real.pi * ‖η‖)) ^ (2 * m))⁻¹ := by
      rw [norm_smul, Real.norm_of_nonneg hw0.le, inv_pow, pow_mul]
      congr 2; ring
    rw [heq] at h
    calc ‖𝓕 bc (w • η)‖ ^ 2 ≤ (Cb * ((w * (2 * Real.pi * ‖η‖)) ^ (2 * m))⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = Cb ^ 2 * ((w * (2 * Real.pi * ‖η‖)) ^ (4 * m))⁻¹ := by
          rw [mul_pow, inv_pow, ← pow_mul]; ring_nf
  exact lintegral_shells_le volume (u := fun η : V => 2 * Real.pi * ‖η‖) (by fun_prop) (fun η => by positivity)
    hs hm hw0 hw1 (by positivity) htot htail hB1 hB2

end StatFormal.MollifierNorm
