import StatFormal.Lib.NativeChar.Reflect
import StatFormal.Lib.TIKernel.Native

/-!
# The native space of a translation-invariant kernel: the characterisation (library, untrusted)

Wendland, *Scattered Data Approximation*, Thm 10.12 (eq:newnative with `=`). Let `k₀ : V → ℝ` be continuous and integrable and
`φ : V → H` a feature map with `⟪φ x, φ y⟫ = k₀ (x − y)`; write `s = 𝓕k₀` (the spectral density), `μ_s = s · vol` and
`Ψ x = 𝐞(−⟪x, ·⟫) ∈ L²(μ_s; ℂ)` (the Fourier feature map, same Gram function).

* (a) For every `g : H`, `f = ⟪g, φ ·⟫` is continuous and square integrable, and `∫ |𝓕₂ f|²/s ≤ ‖g‖²`, with equality when `g`
  lies in the closed span of `φ(V)` (`native_le_norm`).
* (b) A continuous `f` is represented iff `f ∈ L²` and `∫ |𝓕₂ f|²/s < ∞`, and then the projection of any representer onto the
  closed span of `φ(V)` is a representer of minimal norm, with squared norm `∫ |𝓕₂ f|²/s` (`native_char_rep`).

Route for (a). The Gram isometry `U` maps `P g` (`P` the projection onto the closed span of `φ(V)`) to `G ∈ L²(μ_s)` with
`⟪G, Ψ x⟫ = ⟪g, φ x⟫` and `‖G‖ = ‖P g‖ ≤ ‖g‖`; `G` lies in the closed real span of `Ψ`, so `G(−ξ) = conj G(ξ)` `μ_s`-a.e.
(`NativeChar.Reflect`). For such a symmetric `G`, `h = s G` is in L¹ ∩ L² (`s ≤ ∫|k₀|`), `f = 𝓕⁻ h` everywhere (the symmetry
makes `𝓕⁻ h` real and equal to `⟪G, Ψ ·⟫`), hence `𝓕₂ f = h` a.e. and `∫ |𝓕₂ f|²/s = ∫ s |G|² = ‖G‖²` (`native_of_symm`).
(b) follows from (a) and the inclusion L17 (`TIKernel.native_incl_facts`).
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.NativeChar

open StatFormal.Wave31tp StatFormal.TIKernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The pointwise identity `‖t a‖²/t = t ‖a‖²` in `[0, ∞]` for `t ≥ 0` (both sides vanish at `t = 0`). -/
lemma pt_native_mul {a : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    ‖(t : ℂ) * a‖ₑ ^ 2 / ENNReal.ofReal t = ENNReal.ofReal (t * ‖a‖ ^ 2) := by
  rw [pt_native ht (fun h0 => by rw [h0, Complex.ofReal_zero, zero_mul])]
  rcases ht.lt_or_eq with hp | rfl
  · have hne : (t : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    rw [mul_div_cancel_left₀ a hne]
  · simp

/-- The spectral density is bounded by `∫ |k₀|` (`|𝓕 k₀| ≤ ‖k₀‖₁`). -/
lemma specDens_le (k₀ : V → ℝ) (ξ : V) : specDens k₀ ξ ≤ ∫ x, |k₀ x| := by
  refine (Complex.re_le_norm _).trans ?_
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs]

section Fourier

variable {s : V → ℝ} (hsc : Continuous s) (hs0 : ∀ ξ, 0 ≤ s ξ) (hsi : Integrable s) (hsev : ∀ ξ, s (-ξ) = s ξ)
  {C : ℝ} (hsb : ∀ ξ, s ξ ≤ C)
include hsc hs0 hsi hsev hsb

/-- **The native functional of a symmetric Fourier representer.** Let `s ≥ 0` be continuous, integrable, even and bounded,
and let `G ∈ L²(s · vol; ℂ)` satisfy `G(−ξ) = conj G(ξ)` a.e. Then `f = ⟪G, Ψ ·⟫` (`Ψ` the Fourier feature map of `s`) is the
inverse transform of `s G ∈ L¹ ∩ L²`; hence `f ∈ L²`, `𝓕₂ f = s G` a.e. and `∫ |𝓕₂ f|²/s = ∫ s |G|² = ‖G‖²`. -/
theorem native_of_symm (G : Lp ℂ 2 (specMeas s)) (hsym : ∀ᵐ ξ ∂(specMeas s), G (-ξ) = conj (G ξ)) :
    MemLp (fun x => ⟪G, fourierFeature s x⟫) 2 ∧
      ∫⁻ ξ, ‖ft2 (fun x => ((⟪G, fourierFeature s x⟫ : ℝ) : ℂ)) ξ‖ₑ ^ 2 / ENNReal.ofReal (s ξ) =
        ENNReal.ofReal (‖G‖ ^ 2) := by
  have := specMeas_finite hsi
  have hGm : StronglyMeasurable (G : V → ℂ) := Lp.stronglyMeasurable G
  have hG2 : MemLp (G : V → ℂ) 2 (specMeas s) := Lp.memLp G
  -- `s ‖G‖` and `s ‖G‖²` are integrable
  have hsG1 : Integrable (fun ξ => s ξ * ‖G ξ‖) := by
    have h1 := (integrable_withDensity_iff_integrable_smul (μ := volume) hsc.measurable.real_toNNReal
      (g := fun ξ => ‖G ξ‖)).1 (hG2.integrable one_le_two).norm
    refine h1.congr (Eventually.of_forall fun ξ => ?_)
    simp [NNReal.smul_def, Real.coe_toNNReal _ (hs0 ξ)]
  have hsG2 : Integrable (fun ξ => s ξ * ‖G ξ‖ ^ 2) := by
    have h1 := (integrable_withDensity_iff_integrable_smul (μ := volume) hsc.measurable.real_toNNReal
      (g := fun ξ => ‖G ξ‖ ^ 2)).1 ((memLp_two_iff_integrable_sq_norm hGm.aestronglyMeasurable).1 hG2)
    refine h1.congr (Eventually.of_forall fun ξ => ?_)
    simp [NNReal.smul_def, Real.coe_toNNReal _ (hs0 ξ)]
  -- `h = s G ∈ L¹ ∩ L²`
  set h : V → ℂ := fun ξ => (s ξ : ℂ) * G ξ with hh_def
  have hhm : StronglyMeasurable h := (Complex.continuous_ofReal.comp hsc).stronglyMeasurable.mul hGm
  have hnh : ∀ ξ, ‖h ξ‖ = s ξ * ‖G ξ‖ := fun ξ => by
    simp only [hh_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0 ξ)]
  have hh1 : Integrable h :=
    hsG1.mono' hhm.aestronglyMeasurable (Eventually.of_forall fun ξ => (hnh ξ).le)
  have hh2 : MemLp h 2 := by
    rw [memLp_two_iff_integrable_sq_norm hhm.aestronglyMeasurable]
    refine (hsG2.const_mul C).mono' (hhm.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hnh]
    calc (s ξ * ‖G ξ‖) ^ 2 = s ξ * (s ξ * ‖G ξ‖ ^ 2) := by ring
      _ ≤ C * (s ξ * ‖G ξ‖ ^ 2) := mul_le_mul_of_nonneg_right (hsb ξ) (mul_nonneg (hs0 ξ) (sq_nonneg _))
  -- the symmetry on the Lebesgue side: `s conj G = h ∘ neg` a.e.
  have hsym' : ∀ᵐ ξ ∂(volume : Measure V), (s ξ : ℂ) * conj (G ξ) = h (-ξ) := by
    have h0 := (ae_withDensity_iff (μ := volume) (ENNReal.measurable_ofReal.comp hsc.measurable)).1 hsym
    filter_upwards [h0] with ξ hξ
    simp only [hh_def, hsev]
    rcases (hs0 ξ).lt_or_eq with hp | he
    · rw [hξ (ENNReal.ofReal_pos.mpr hp).ne']
    · rw [← he]; simp
  -- `f = 𝓕⁻ h` everywhere
  have hF : ∀ x, ((⟪G, fourierFeature s x⟫ : ℝ) : ℂ) = 𝓕⁻ h x := by
    intro x
    have hI : 𝓕⁻ h x = ∫ ξ, (𝐞 ⟪ξ, x⟫ : ℂ) * h ξ := by rw [Real.fourierInv_eq]; rfl
    have hint := integrable_char_mul hh1 (fun ξ => ⟪ξ, x⟫) (continuous_id.inner continuous_const)
    set J : V → ℂ := fun ξ => conj ((𝐞 ⟪ξ, x⟫ : ℂ) * h ξ) with hJ_def
    have hJ : Integrable J :=
      hint.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hint.1)
        (Eventually.of_forall fun ξ => by simp only [hJ_def, Complex.norm_conj, le_refl])
    have hJe : ∀ ξ, J ξ = (s ξ : ℂ) * conj (G ξ) * (𝐞 (-⟪x, ξ⟫) : ℂ) := fun ξ => by
      show conj ((𝐞 ⟪ξ, x⟫ : ℂ) * ((s ξ : ℂ) * G ξ)) = _
      rw [map_mul, map_mul, Complex.conj_ofReal, conj_fourierChar, real_inner_comm]
      ring
    have e1 : 𝓕⁻ h x = ∫ ξ, J ξ := by
      rw [hI, ← integral_neg_eq_self (fun ξ => (𝐞 ⟪ξ, x⟫ : ℂ) * h ξ)]
      refine integral_congr_ae ?_
      filter_upwards [hsym'] with ξ hξ
      show (𝐞 ⟪-ξ, x⟫ : ℂ) * h (-ξ) = J ξ
      rw [hJe, ← hξ, inner_neg_left, real_inner_comm]
      ring
    have e2 : conj (𝓕⁻ h x) = ∫ ξ, J ξ := by
      rw [hI, ← integral_conj]
    have e3 : ⟪G, fourierFeature s x⟫ = (∫ ξ, J ξ).re := by
      have ere := (integral_re hJ).symm
      simp only [RCLike.re_to_complex] at ere
      rw [ere, L2.inner_def]
      calc ∫ ξ, ⟪G ξ, (fourierFeature s x : V → ℂ) ξ⟫ ∂(specMeas s)
          = ∫ ξ, (conj (G ξ) * (𝐞 (-⟪x, ξ⟫) : ℂ)).re ∂(specMeas s) := by
            refine integral_congr_ae ?_
            filter_upwards [fourierFeature_ae s hsi x] with ξ hξ
            rw [hξ, Complex.inner, mul_comm]
        _ = ∫ ξ, s ξ * (conj (G ξ) * (𝐞 (-⟪x, ξ⟫) : ℂ)).re := integral_specMeas hsc.measurable hs0 _
        _ = ∫ ξ, (J ξ).re := by
            refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
            simp only [hJe, mul_assoc, Complex.re_ofReal_mul]
    have hreal : (((𝓕⁻ h x).re : ℝ) : ℂ) = 𝓕⁻ h x := Complex.conj_eq_iff_re.mp (e2.trans e1.symm)
    rw [e3, ← e1, hreal]
  -- `𝓕₂ f = h` a.e.
  have hFeq : (fun x => ((⟪G, fourierFeature s x⟫ : ℝ) : ℂ)) = 𝓕⁻ h := funext hF
  have hinvae := FourierL2.fourierInv_toLp_ae hh1 hh2
  have hF2 : MemLp (𝓕⁻ h) 2 := (Lp.memLp _).ae_eq hinvae
  have hft : ft2 (𝓕⁻ h) =ᵐ[volume] h := by
    rw [ft2_eq' hF2]
    have hlp : hF2.toLp (𝓕⁻ h) = 𝓕⁻ (hh2.toLp h) := Lp.ext (hF2.coeFn_toLp.trans hinvae.symm)
    rw [hlp, fourier_fourierInv_eq]
    exact hh2.coeFn_toLp
  have hn : ‖G‖ ^ 2 = ∫ ξ, s ξ * ‖G ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_specMeas hsc.measurable hs0]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [real_inner_self_eq_norm_sq]
  refine ⟨?_, ?_⟩
  · have hre : (fun x => ⟪G, fourierFeature s x⟫) = fun x => RCLike.re (𝓕⁻ h x) :=
      funext fun x => by rw [← hF x, RCLike.re_to_complex, Complex.ofReal_re]
    rw [hre]
    exact hF2.re
  · rw [hFeq]
    have e : ∀ᵐ ξ ∂(volume : Measure V),
        ‖ft2 (𝓕⁻ h) ξ‖ₑ ^ 2 / ENNReal.ofReal (s ξ) = ENNReal.ofReal (s ξ * ‖G ξ‖ ^ 2) := by
      filter_upwards [hft] with ξ hξ
      rw [hξ]
      exact pt_native_mul (hs0 ξ)
    rw [lintegral_congr_ae e, ← ofReal_integral_eq_lintegral_ofReal hsG2
      (Eventually.of_forall fun ξ => mul_nonneg (hs0 ξ) (sq_nonneg _)), hn]

end Fourier

section Feature

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀)
include hφ hc hi

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] hφ hc hi in
/-- The projection onto the closed span of `φ(V)` does not change the represented function. -/
lemma inner_proj_phi (g : H) (x : V) : ⟪((spanCl φ).orthogonalProjectionOnto g : H), φ x⟫ = ⟪g, φ x⟫ := by
  have := (spanCl φ).inner_starProjection_left_eq_right g (φ x)
  rw [Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr (mem_spanCl φ x)] at this
  exact this

/-- **Wave31tp L18 (a)** (Wendland Thm 10.12): every `f = ⟪g, φ ·⟫` is continuous, square integrable, with native functional
`∫ |𝓕₂ f|²/𝓕k₀ ≤ ‖g‖²`, and with equality when `g` lies in the closed span of `φ(V)`. -/
theorem native_le_norm (g : H) :
    Continuous (fun x => ⟪g, φ x⟫) ∧ MemLp (fun x => ⟪g, φ x⟫) 2 ∧
      nativeN k₀ (fun x => ((⟪g, φ x⟫ : ℝ) : ℂ)) ≤ ENNReal.ofReal (‖g‖ ^ 2) ∧
      (g ∈ spanCl φ → nativeN k₀ (fun x => ((⟪g, φ x⟫ : ℝ) : ℂ)) = ENNReal.ofReal (‖g‖ ^ 2)) := by
  obtain ⟨hsc, hsev, hs0, hsi, -, hΨ⟩ := feature_exists_facts hc hi (gram_posdef hφ)
  have hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪fourierFeature (specDens k₀) x, fourierFeature (specDens k₀) y⟫ :=
    fun x y => by rw [hΨ, hφ]
  set Pg : spanCl φ := (spanCl φ).orthogonalProjectionOnto g
  set G := gramIso hG Pg
  have hrep : ∀ x, ⟪G, fourierFeature (specDens k₀) x⟫ = ⟪g, φ x⟫ := fun x => by
    rw [inner_gramIso_phi]
    exact inner_proj_phi g x
  have hsym := ae_symm_of_mem_spanCl hsc.measurable hsev hsi (gramIso_mem_spanCl hG Pg)
  obtain ⟨hm, hN⟩ := native_of_symm hsc hs0 hsi hsev (specDens_le k₀) G hsym
  have hGn : ‖G‖ = ‖Pg‖ := LinearIsometry.norm_map _ _
  have hfeq : (fun x => ⟪g, φ x⟫) = fun x => ⟪G, fourierFeature (specDens k₀) x⟫ := funext fun x => (hrep x).symm
  have hfeqC : (fun x => ((⟪g, φ x⟫ : ℝ) : ℂ)) = fun x => ((⟪G, fourierFeature (specDens k₀) x⟫ : ℝ) : ℂ) :=
    funext fun x => by rw [hrep x]
  have hNeq : nativeN k₀ (fun x => ((⟪g, φ x⟫ : ℝ) : ℂ)) = ENNReal.ofReal (‖Pg‖ ^ 2) := by
    unfold nativeN
    rw [hfeqC, hN, hGn]
  have hφc : Continuous φ := ((gram_cont_iff hφ).1).2 hc.continuousAt
  refine ⟨continuous_const.inner hφc, by rw [hfeq]; exact hm, ?_, fun hg => ?_⟩
  · rw [hNeq]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) ((spanCl φ).norm_orthogonalProjectionOnto_apply_le g) 2)
  · have hP : Pg = ⟨g, hg⟩ := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨g, hg⟩
    rw [hNeq, hP]
    rfl

/-- **Wave31tp L18 (b)** (Wendland Thm 10.12): a continuous `f` is represented iff `f ∈ L²` with finite native functional, and
then the projection of any representer onto the closed span of `φ(V)` is a representer of minimal norm whose squared norm is
the native functional. -/
theorem native_char_rep (f : V → ℝ) (hfc : Continuous f) :
    ((∃ g : H, ∀ x, ⟪g, φ x⟫ = f x) ↔ (MemLp f 2 ∧ nativeN k₀ (fun x => (f x : ℂ)) < ⊤)) ∧
      ((∃ g : H, ∀ x, ⟪g, φ x⟫ = f x) →
        ∃ g₀ : H, (∀ x, ⟪g₀, φ x⟫ = f x) ∧ ENNReal.ofReal (‖g₀‖ ^ 2) = nativeN k₀ (fun x => (f x : ℂ)) ∧
          ∀ g : H, (∀ x, ⟪g, φ x⟫ = f x) → ‖g₀‖ ≤ ‖g‖) := by
  have key : ∀ g : H, (∀ x, ⟪g, φ x⟫ = f x) → (fun x => ⟪g, φ x⟫) = f := fun g hg => funext hg
  have keyC : ∀ g : H, (∀ x, ⟪g, φ x⟫ = f x) → (fun x => ((⟪g, φ x⟫ : ℝ) : ℂ)) = fun x => (f x : ℂ) :=
    fun g hg => funext fun x => by rw [hg x]
  refine ⟨⟨fun ⟨g, hg⟩ => ?_, fun ⟨hf2, hN⟩ => ?_⟩, fun ⟨g, hg⟩ => ?_⟩
  · obtain ⟨-, hm, hle, -⟩ := native_le_norm hφ hc hi g
    rw [key g hg] at hm
    rw [keyC g hg] at hle
    exact ⟨hm, hle.trans_lt ENNReal.ofReal_lt_top⟩
  · obtain ⟨g, hg, -⟩ := (native_incl_facts hφ hc hi f).1 hfc hf2 hN
    exact ⟨g, hg⟩
  · set g₀ : H := ((spanCl φ).orthogonalProjectionOnto g : H)
    have hg₀ : ∀ x, ⟪g₀, φ x⟫ = f x := fun x => by rw [← hg x]; exact inner_proj_phi g x
    have hmem : g₀ ∈ spanCl φ := ((spanCl φ).orthogonalProjectionOnto g).2
    have heq := (native_le_norm hφ hc hi g₀).2.2.2 hmem
    rw [keyC g₀ hg₀] at heq
    refine ⟨g₀, hg₀, heq.symm, fun g' hg' => ?_⟩
    have hle := (native_le_norm hφ hc hi g').2.2.1
    rw [keyC g' hg', heq, ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

end Feature

end StatFormal.NativeChar
